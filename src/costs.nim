import std/[sequtils, strutils, tables, sets, options, sugar]
import fusion/matching
include karax/prelude

import ./expression, ./conversion


type
  Cost* = object
    conversion: Option[Conversion]
    binOps: array[boAnd..boOr, Table[Natural, seq[Expr]]]
    notOp: seq[Expr]
    all: Natural


func `==**`(a, b: Expr): bool =
  if a.kind != b.kind: return false
  case a.kind
  of ekVal: a.val == b.val
  of ekVar: a.name == b.name
  of ekNot: a.inner == b.inner
  of ekBinOp:
    if a.op != b.op: return false
    var oa = a.operands
    var ob = b.operands
    if len(oa) != len(ob): return false
    for oa in oa:
      var i = 0
      while not (ob[i] ==** oa):
        inc i
        if i > high(ob): return false
      ob.delete(i)
    true

let conversionRules = newConvertAlgo(@[resolveBiImpl, resolveImpl])

proc getCost*(expr: Expr): Cost =
  var cost: Cost

  proc collectCost(expr: Expr) =
    case expr.kind
    of ekNot:
      if not cost.notOp.anyIt(it ==** expr.inner):
        cost.notOp.add expr.inner
      collectCost expr.inner
    of ekBinOp:
      assert expr.op in {boAnd..boOr}
      let operands = expr.operands
      if len(operands) in cost.binOps[expr.op]:
        if not cost.binOps[expr.op][len(operands)].anyIt(it ==** expr):
          cost.binOps[expr.op][len(operands)].add expr
      else:
        cost.binOps[expr.op][len(operands)] = @[expr]
      for operand in operands:
        collectCost operand
    else: discard

  let conv = expr.convert(conversionRules)
  if len(conv.steps) == 0:
    collectCost expr
  else:
    cost.conversion = some conv
    collectCost conv.res

  cost.all = len(cost.notOp)
  for table in cost.binOps:
    for size, exprs in table:
      cost.all += size * len(exprs)
  
  cost


func `$`(cost: Cost): string =
  result = collect(
    for op, table in cost.binOps:
      for size, exprs in table:
        $len(exprs) & "*" & [boAnd: "AND", boOr: "OR"][op] & $size
  ).join(" + ")
  if len(cost.notOp) > 0:
    result.add " + " & $len(cost.notOp) & "*NOT"
  result.add " = " & $cost.all

proc draw*(cost: Cost): VNode =
  buildHtml(tdiv(id = "gates-cost")):
    if Some(@conv) ?= cost.conversion:
      tdiv(class = "group"):
        tdiv(class = "title"): text "Conversion"
        tdiv(class = "content"):
          draw(conv)
    text $cost