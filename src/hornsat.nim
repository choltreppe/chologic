import std/[sugar, options, sets, sequtils, algorithm]
import fusion/matching
include karax/prelude

import ./utils, ./expression, ./truthtable, ./conversion, ./sat


type
  HornClauseKind = enum hckDefinite, hckFact, hckGoal
  HornClause = object
    case kind: HornClauseKind
    of hckDefinite:
      vars: seq[string]
      imply: string
    of hckFact:
      fact: string
    of hckGoal:
      goals: seq[string]
  HornFormula = seq[HornClause]
  HornSat* = object
    formula: HornFormula
    conversion: Option[Conversion]
    vars: seq[string]
    steps: seq[seq[string]]
    sat: bool


func toHornClause(expr: Expr): Option[HornClause] =
  if expr =: boImpl:
    if expr.lhs =: ekVal and expr.lhs.val and expr.rhs =: ekVar:
      return some HornClause(kind: hckFact, fact: expr.rhs.name)

    elif expr.lhs =: boAnd or expr.lhs =: ekVar:
      template collectVars: untyped =
        var vars {.inject.}: seq[string]
        if expr.lhs =: ekVar:
          vars = @[expr.lhs.name]
        else:
          for expr in expr.lhs.operands:
            if expr =: ekVar: vars.add expr.name
            else: return

      if expr.rhs =: ekVal and not expr.rhs.val:
        collectVars()
        return some HornClause(kind: hckGoal, goals: vars)

      elif expr.rhs =: ekVar:
        collectVars()
        return some HornClause(kind: hckDefinite, vars: vars, imply: expr.rhs.name)

  elif expr =: ekVar:
    return some HornClause(kind: hckFact, fact: expr.name)

  elif expr =: ekNot and expr.inner =: ekVar:
    return some HornClause(kind: hckGoal, goals: @[expr.inner.name])

  elif expr =: boOr:
    block createClause:
      var
        normVar: Option[string]
        notVars: seq[string]
      for expr in expr.operands:
        if expr =: ekVar and normVar.isNone:
          normVar = some expr.name
        elif expr =: ekNot and expr.inner =: ekVar:
          notVars.add expr.inner.name
        elif expr =: ekVal:
          if expr.val:
            break createClause
        else:
          return

      return some:
        if normVar.isNone:
          HornClause(kind: hckGoal, goals: notVars)
        elif len(notVars) == 0:
          HornClause(kind: hckFact, fact: get normVar)
        else:
          HornClause(kind: hckDefinite, vars: notVars, imply: get normVar)

func toHornFormula(expr: Expr): Option[HornFormula] =
  if expr =: boAnd:
    var formula: seq[HornClause]
    for expr in expr.operands:
      if Some(@clause) ?= expr.toHornClause:
        formula.add clause
      else: return
    return some formula
  elif Some(@clause) ?= expr.toHornClause:
    return some @[clause]


proc doHornSat*(expr: Expr): Option[HornSat] =

  var res =
    if Some(@formula) ?= expr.toHornFormula:
      HornSat(formula: formula, vars: expr.vars.toSeq.sorted)
    else:
      let
        conv = expr.convert(caCnf)
        expr = conv.res
      if Some(@formula) ?= expr.toHornFormula:
        HornSat(formula: formula, vars: expr.vars.toSeq.sorted, conversion: some conv)
      else:
        return none HornSat

  var marked = collect:
    for clause in res.formula:
      if clause.kind == hckFact:
        clause.fact

  res.sat = true
  var markedNew = true
  while markedNew:
    res.steps.add marked
    if res.formula.anyIt(it.kind == hckGoal and it.goals.allIt(it in marked)):
      res.sat = false
      break
    markedNew = false
    let markedPrev = dup marked
    for clause in res.formula:
      if clause.kind == hckDefinite and
         clause.vars.allIt(it in markedPrev) and
         clause.imply notin marked:
        marked.add clause.imply
        markedNew = true

  some res


proc draw(formula: HornFormula, marked: seq[string] = @[]): VNode =

  proc varHtml(name: string): VNode =
    buildHtml:
      tdiv(class = "".concatIf(name in marked, "marked")):
        text name

  proc varsHtml(vars: seq[string]): seq[VNode] =
    for i, name in vars:
      if i > 0:
        result.add draw(boAnd)
      result.add varHtml(name)

  buildHtml(tdiv(class = "expr")):
    for i, clause in formula:
      if i > 0:
        draw(boAnd)

      text "("

      case clause.kind
      of hckDefinite:
        for n in varsHtml(clause.vars): n
        draw(boImpl)
        varHtml(clause.imply)
      of hckFact:
        text "1"
        draw(boImpl)
        varHtml(clause.fact)
      of hckGoal:
        for n in varsHtml(clause.goals): n
        draw(boImpl)
        text "0"

      text ")"

proc draw*(algo: HornSat): VNode =
  buildHtml(tdiv(id = "horn-sat-container", class = "box")):
    if Some(@conv) ?= algo.conversion:
      tdiv(class = "group"):
        tdiv(class = "title"): text "Conversion"
        tdiv(class = "content"): draw(conv)

    tdiv(id = "horn-sat"):
      table:
        tr:
          for name in algo.vars:
            th: text name
        for step in algo.steps:
          tr:
            for name in algo.vars:
              td(class = "".concatIf(name in step, "marked"))
            td: draw(algo.formula, step)

      tdiv: satResultHtml(algo.sat)


proc draw*(algo: Option[HornSat]): VNode =
  if Some(@algo) ?= algo: draw(algo)
  else:
    buildHtml(tdiv(class = "info-box")):
      tdiv(class = "title"): text "No Horn Formula"
      tdiv(class = "content"):
        text "The expression isn't a hornformula."
        br()
        text "It also doesn't seem to be able to convert into a hornformula."
        br()
        text "If it is actually convertable into a hornformula, a bug report would be much appriciated."