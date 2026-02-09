import std/[options, sequtils, strformat, unicode, tables, sets]
import std/strutils except alignLeft
import fusion/matching
import results
include karax/prelude

import ./expression


type
  ConvertProc = proc(expr: Expr): Option[Expr]

  ConvertRule = object
    desc: (Expr, Expr)
    convert: ConvertProc

  ConvertStepRules = object
    case stepwise: bool
    of true:
      rules: seq[ConvertRule]
    of false:
      rule: ConvertRule

  ConvertStep = object
    desc: seq[(Expr, Expr)]
    expr: Expr

  Conversion* = object
    expr*: Expr
    steps*: seq[ConvertStep]

  ConvertAlgo* = enum caDnf="DNF", caCnf="CNF", caNand="NAND"

func res*(conv: Conversion): Expr =
  if len(conv.steps) > 0: conv.steps[^1].expr
  else: conv.expr

const ruleDescPadding = 32

func `$`*(step: ConvertStep): string =
  step.desc.mapIt(&"{it[0]} ≡ {it[1]}").join(", ").alignLeft(ruleDescPadding) & $step.expr

func `$`*(conv: Conversion): string =
  result = ' '.repeat(ruleDescPadding) & $conv.expr & "\n"
  for step in conv.steps:
    result.add $step & "\n"



proc newConvertRule(desc: (string, string), convert: ConvertProc): ConvertRule =
  ConvertRule(
    desc: (parseExpr(desc[0]).get, parseExpr(desc[1]).get),
    convert: convert
  )

proc newConvertAlgo*(rules: varargs[seq[ConvertRule]]): seq[ConvertStepRules] =
  for rules in rules:
    result.add ConvertStepRules(stepwise: true, rules: rules)

proc convert*(expr: Expr, rules: seq[ConvertRule]): seq[ConvertStep] =

  proc step(expr: Expr): Option[ConvertStep] =
    result =
      case expr.kind
      of ekVal, ekVar: none(ConvertStep)
      of ekNot: step(expr.inner)
      of ekBinOp:
        var desc: seq[(Expr, Expr)]
        let operands = expr.operands.mapIt:
          if Some(@step) ?= step(it):
            desc.add step.desc
            step.expr
          else: it
        if len(desc) > 0:
          some(ConvertStep(desc: desc.deduplicate, expr: exprBinOp(expr.op, operands)))
        else:
          none(ConvertStep)

    if result.isNone:
      for rule in rules:
        if result.isSome: break
        let desc = rule.desc
        result = rule.convert(expr).map do (expr: Expr) -> ConvertStep:
          ConvertStep(desc: @[desc], expr: expr)

  var expr = expr
  while Some(@step) ?= step(expr):
    expr = step.expr
    step.expr = simplify(expr)
    result.add step

proc convert*(expr: Expr, rules: seq[ConvertStepRules]): Conversion =
  result.expr = expr
  var expr = expr
  for rules in rules:
    if rules.stepwise:
      result.steps.add convert(expr, rules.rules)
    elif Some(@expr) ?= rules.rule.convert(expr):
      result.steps.add ConvertStep(desc: @[rules.rule.desc], expr: expr)
    if len(result.steps) > 0:
      expr = result.steps[^1].expr


let resolveBiImpl* = newConvertRule(
  ("a=b", "(a>b)&(b>a)"),
  proc(expr: Expr): Option[Expr] =
    if expr =: boBiImpl:
      let a = expr.lhs
      let b = exprBinOp(boBiImpl, expr.rhs)
      return some(exprBinOp(boAnd,
        exprBinOp(boImpl, a, b),
        exprBinOp(boImpl, b, a)
      ))
)

let resolveImpl* = newConvertRule(
  ("a>b", "!a|b"),
  proc(expr: Expr): Option[Expr] =
    if expr =: boImpl:
      let a = expr.lhs
      let b = expr.rhs
      return some(exprBinOp(boOr, exprNot(a), b))
)

let resolveDoubleNegation* = newConvertRule(
  ("!!a", "a"),
  proc(expr: Expr): Option[Expr] =
    if expr =: ekNot and expr.inner =: ekNot:
      return some(expr.inner.inner)
)

template buildDeMorgan(fromAnd: static bool): ConvertProc =
  proc(expr: Expr): Option[Expr] =
    const (fromOp, toOp) =
      if fromAnd: (boAnd, boOr )
      else:       (boOr,  boAnd)
    if expr =: ekNot and expr.inner =: fromOp:
      return some(exprBinOp(toOp, expr.inner.operands.map(exprNot)))

let deMorganAnd* = newConvertRule(
  ("!(a&b)", "!a|!b"),
  buildDeMorgan(true)
)

let deMorganOr* = newConvertRule(
  ("!(a|b)", "!a&!b"),
  buildDeMorgan(false)
)

template buildFactorOut(fromAnd: static bool): ConvertProc =
  proc(expr: Expr): Option[Expr] =
    const (outOp, inOp) =
      if fromAnd: (boAnd, boOr )
      else:       (boOr,  boAnd)
    if expr =: outOp:
      var
        parenExpr: Expr
        parenExprId = -1
        parenExprLen = high(int)
      for i, op in expr.operands:
        if op =: inOp and (let operands = op.operands; len(operands) < parenExprLen):
          parenExpr = op
          parenExprId = i
          parenExprLen = len(operands)
      if parenExprId >= 0:
        var operands = expr.operands
        operands.delete parenExprId, parenExprId
        return some(exprBinOp(inOp, parenExpr.operands.mapIt(exprBinOp(outOp, operands & it))))

let factorOutAnd* = newConvertRule(
  ("a&(b|c)", "a&b|a&c"),
  buildFactorOut(true)
)

let factorOutOr* = newConvertRule(
  ("a|b&c", "(a|b)&(a|c)"),
  buildFactorOut(false)
)

let forcedDeMorganOr = newConvertRule(
  ("a|b", "!(!a&!b)"),
  proc(expr: Expr): Option[Expr] =
    if expr =: boOr:
      return some(exprNot(exprBinOp(boAnd, expr.operands.map(exprNot))))
)

proc negateEverywhereProc(expr: Expr): Option[Expr] =
  proc rec(expr: Expr): Option[Expr] =
    case expr.kind
    of ekVal, ekVar: discard
    of ekNot: assert false
    of ekBinOp:
      var changed = false
      let operands = expr.operands.mapIt:
        if Some(@expr) ?= negateEverywhereProc(it):
          changed = true
          expr
        else: it
      if changed:
        return some(exprBinOp(expr.op, operands))

  if expr =: ekNot:
    proc unpackNeg(expr: Expr): Option[Expr] =
      if expr =: ekNot:
        unpackNeg(expr.inner).map do (expr: Expr) -> Expr:
          exprNot(expr)
      else: rec(expr)
    unpackNeg(expr)
  else:
    some: exprNot: exprNot:
      if Some(@expr) ?= rec(expr): expr
      else: expr

let negateEverywhere = newConvertRule(
  ("a", "!!a"),
  negateEverywhereProc
)


proc convert*(expr: Expr, algo: ConvertAlgo): Conversion =
  convert(expr):
    case algo
    of caDnf:
      newConvertAlgo(
        @[resolveBiImpl, resolveImpl],
        @[resolveDoubleNegation, deMorganAnd, deMorganOr],
        @[factorOutAnd]
      )
    of caCnf:
      newConvertAlgo(
        @[resolveBiImpl, resolveImpl],
        @[resolveDoubleNegation, deMorganAnd, deMorganOr],
        @[factorOutOr]
      )
    of caNand:
      @[
        ConvertStepRules(
          stepwise: true,
          rules: @[resolveBiImpl, resolveImpl]
        ),
        ConvertStepRules(
          stepwise: true,
          rules: @[forcedDeMorganOr]
        ),
        ConvertStepRules(
          stepwise: false,
          rule: negateEverywhere
        )
      ]


proc draw*(conv: Conversion): VNode =
  if len(conv.steps) == 0:
    draw(conv.expr)

  else:
    buildHtml(table(class = "conversion")):
      tr:
        th: text "Rules"
        td: draw(conv.expr)

      for step in conv.steps:
        tr:
          td: table(class = "rules"):
            for desc in step.desc:
              tr:
                td: draw(desc[0])
                td: text "≡"
                td: draw(desc[1])
          td: draw(step.expr)