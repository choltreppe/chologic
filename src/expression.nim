import std/[strformat, strutils, sequtils, parseutils, unicode, sets, tables, sugar]
import fusion/matching
include karax/prelude
import ./utils


type
  ExprKind* = enum ekVal, ekVar, ekNot="¬", ekBinOp
  BinOp* = enum boAnd="∧", boOr="∨", boBiImpl="↔", boImpl="→"
  Expr* = ref object
    case kind*: ExprKind
    of ekVal: val*: bool
    of ekVar: name*: string
    of ekNot: inner*: Expr
    of ekBinOp:
      op*: BinOp
      lhs*, rhs*: Expr

  ExprError* = ref object of CatchableError
    pos*: int

const allowedSymbolsBinOp* = [
  boAnd   : @["&&", "&", "∧", "*", "⋅"],
  boOr    : @["||", "|", "∨", "+"],
  boBiImpl: @["<->", "<>", "=", "↔"],
  boImpl  : @["->", ">", "→"]
]

const allowedSymbolsNot* = @["!", "~", "¬"]

const opPrecedence = block:
  var pmap: array[BinOp, int]
  pmap[boImpl]   = 1
  pmap[boBiImpl] = 1
  pmap[boOr]     = 2
  pmap[boAnd]    = 3
  pmap

func `=:`*(expr: Expr, kind: ExprKind): bool {.inline.} =
  expr.kind == kind

func `=:`*(expr: Expr, op: BinOp): bool {.inline.} =
  expr.kind == ekBinOp and expr.op == op

func exprVal*(val: bool): Expr =
  Expr(kind: ekVal, val: val)

func exprVar*(name: string): Expr =
  Expr(kind: ekVar, name: name)

func exprNot*(inner: Expr): Expr =
  Expr(kind: ekNot, inner: inner)

func `not`*(expr: Expr): Expr =
  if expr =: ekNot: expr.inner
  else            : exprNot(expr)

func exprBinOp*(op: BinOp, operands: varargs[Expr]): Expr =
  if len(operands) == 0: exprVal(op != boOr)
  elif op == boImpl:
    assert len(operands) == 2
    Expr(kind: ekBinOp, op: op, lhs: operands[0], rhs: operands[1])
  else:
    operands.toSeq.foldl(Expr(kind: ekBinOp, op: op, lhs: a, rhs: b))

func operands*(expr: Expr): seq[Expr] =
  assert expr.kind == ekBinOp
  if expr.op == boImpl:
    @[expr.lhs, expr.rhs]
  else:
    let op = expr.op
    proc collectOps(expr: Expr): seq[Expr] =
      if expr =: op: collectOps(expr.lhs) & collectOps(expr.rhs)
      else: @[expr]
    collectOps(expr)

proc `operands=`*(expr: var Expr, operands: seq[Expr]) =
  assert expr.kind == ekBinOp and len(operands) >= 2
  if expr.op == boImpl:
    assert len(operands) == 2
  expr = exprBinOp(expr.op, operands)


func eval*(expr: Expr, vals: Table[string, bool]): bool =
  func evalRec(expr: Expr): bool =
    case expr.kind
    of ekVal: expr.val
    of ekVar: vals[expr.name]
    of ekNot: not evalRec(expr.inner)
    of ekBinOp:
      case expr.op
      of boAnd:    evalRec(expr.lhs) and evalRec(expr.rhs)
      of boOr:     evalRec(expr.lhs) or  evalRec(expr.rhs)
      of boBiImpl: evalRec(expr.lhs) ==  evalRec(expr.rhs)
      of boImpl: not evalRec(expr.lhs) or evalRec(expr.rhs)

  evalRec expr


func vars*(expr: Expr): HashSet[string] =
  var collected = initHashSet[string]()
  proc collect(expr: Expr) =
    case expr.kind
    of ekVal: discard
    of ekVar: collected.incl(expr.name)
    of ekNot: collect(expr.inner)
    of ekBinOp:
      for o in expr.operands: collect(o)
  collect(expr)
  collected


func len*(expr: Expr): Natural =
  case expr.kind
  of ekVal, ekVar: 1
  of ekNot: len(expr.inner)
  of ekBinOp: expr.operands.foldl(a + len(b), 0)


func `==*`*(a,b: Expr): bool =
  if a.kind != b.kind: false
  else:
    case a.kind
    of ekVal: a.val == b.val
    of ekVar: a.name == b.name
    of ekNot: a.inner == b.inner
    of ekBinOp: a.op == b.op and a.lhs ==* b.lhs and a.rhs ==* b.rhs

func contains*(exprs: seq[Expr], expr: Expr): bool =
  for e in exprs:
    if e ==* expr: return true
  false

func simplify*(expr: Expr): Expr =
  case expr.kind
  of ekVal, ekVar: expr
  of ekNot:
    let expr = simplify(expr.inner)
    case expr.kind
    of ekVal: exprVal(not expr.val)
    of ekNot: expr.inner
    else: exprNot(expr)
  of ekBinOp:
    if expr.op == boImpl:
      exprBinOp(boImpl, simplify(expr.lhs), simplify(expr.rhs))
    else:
      var operands = expr.operands.map(simplify)
      let
        isAnd = expr.op == boAnd
        isOr  = expr.op == boOr

      if isAnd or isOr:
        template isOtherOp(operand: Expr): bool =
          (isAnd and operand =: boOr) or (isOr and operand =: boAnd)

        var i = 0
        while i < len(operands):
          let operand = operands[i]

          # x & 1  ==  x
          # x & 0  ==  0
          # x | 1  ==  1
          # x | 0  ==  x
          if operand =: ekVal:
            operands.delete(i)
            if not operand.val == isAnd:
              return exprVal(isOr)

          # (a&b)|b  ==  b
          # (a|b)&(a|b|c) == a|b  
          elif operand.isOtherOp and
               operands.pairs.toSeq.anyIt(
                  it[0] != i and (
                    it[1].isOtherOp and it[1].operands.allIt(it in operand.operands) or
                    it[1] in operand.operands
                  )
               ) or
               operands.pairs.toSeq.anyIt(it[0] != i and it[1] ==* operand):
            operands.delete(i)

          # a & !a  ==  0
          # a | !a  ==  1
          elif operands.anyIt((not it) ==* operand):
            return exprVal(isOr)

          else:
            inc i

      case len(operands):
      of 0: exprVal(isAnd)
      of 1: operands[0]
      else: exprBinOp(expr.op, operands)


proc parseExpr*(code: string): Expr =
  var i = 0

  const unaryExprsStr = "variable, value or negation"
  const binaryOpsStr = "a binary operator"

  proc raiseError(found, expected: string) {.noreturn.} =
    raise ExprError(pos: i, msg: &"unexpected {found}. expected {expected}.")

  proc skipSpaces(expectAfter: string) =
    i += code.skipWhitespace(i)
    if i >= len(code):
      raiseError("EOL", expectAfter)

  proc checkOpSkip(syms: seq[string]): bool =
    for sym in syms:
      if code.continuesWith(sym, i):
        i += len(sym)
        return true
    false

  proc parseExpr: Expr
  proc parseExprUnary: Expr =
    skipSpaces(expectAfter = unaryExprsStr)
    case code[i]
    of '(': inc i; parseExpr()
    of '0': exprVal(false)
    of '1': exprVal(true)
    elif checkOpSkip(allowedSymbolsNot): exprNot(parseExprUnary())
    else:
      if code[i] notin IdentStartChars:
        raiseError(&"'{code.runeAt(i)}'", unaryExprsStr)
      var name: string
      i += code.parseWhile(name, IdentChars, i)
      exprVar(name)

  proc parseExpr: Expr =
    let parenStart = i
    result = parseExprUnary()
    var isFirstIter = true
    while i < len(code):
      skipSpaces(expectAfter = binaryOpsStr)
      if code[i] == ')':
        if parenStart == 0:
          raise ExprError(pos: i, msg: "found ')' with no coresponding '('.")
        inc i
        return

      var op: BinOp
      block getOp:
        for checkOp, syms in allowedSymbolsBinOp:
          if checkOpSkip(syms):
            op = checkOp
            break getOp
        raiseError(&"'{code.runeAt(i)}'", binaryOpsStr)

      let rhs = parseExprUnary()
      result = 
        if isFirstIter or (result.kind == ekBinOp and opPrecedence[op] <= opPrecedence[result.op]): 
          exprBinOp(op, result, rhs)
        else:
          exprBinOp(result.op, result.lhs, exprBinOp(op, result.rhs, rhs))

      isFirstIter = false

    if parenStart != 0:
      raise ExprError(pos: high(code), msg: "not all parentheses were closed.")

  parseExpr()


proc draw*(op: BinOp): VNode =
  buildHtml(tdiv(class = "op".concatIf(op != boAnd, "big"))): text $op

proc drawNotOp*: VNode = buildHtml(tdiv(class = "op")): text $ekNot

proc draw*(expr: Expr): VNode =

  var node = buildHtml(tdiv(class = "expr"))

  template inParenIf(cond: bool, cmd) =
    if cond:
      node &= text "("
      cmd
      node &= text ")"
    else:
      cmd

  proc collect(expr: Expr) =
    if expr != nil:
      case expr.kind:
      of ekVal: node &= text $*expr.val
      of ekVar: node &= text expr.name

      of ekNot:
        node &= drawNotOp()
        inParenIf(expr.inner =: ekBinOp):
          collect(expr.inner)

      of ekBinOp:
        let prec = opPrecedence[expr.op]

        if expr.op == boImpl:
          inParenIf(expr.lhs =: ekBinOp and opPrecedence[expr.lhs.op] < prec):
            collect(expr.lhs)

          node &= draw(expr.op)

          inParenIf(expr.rhs =: ekBinOp and opPrecedence[expr.rhs.op] <= prec):
            collect(expr.rhs)

        else:
          var first = true
          for operand in expr.operands:
            if not first:
              node &= draw(expr.op)
            first = false
            inParenIf(operand =: ekBinOp and opPrecedence[operand.op] < prec):
              collect(operand)

  collect(expr)
  node


func `$`*(expr: Expr): string =
  if expr == nil: return ""
  case expr.kind:
  of ekVal: $*expr.val
  of ekVar: expr.name
  of ekNot: &"{ekNot}{expr.inner}"
  of ekBinOp: &"({expr.lhs} {expr.op} {expr.rhs})"