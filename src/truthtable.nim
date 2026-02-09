import std/[dom, sequtils, options, bitops, sugar, tables, sets, algorithm]
import fusion/matching
import results
include karax/prelude

import ./utils, ./expression, ./junction


type
  TruthTable* = ref object of RootObj
    vars*: seq[string]
    results*: seq[Option[bool]]

  TruthTableEdit* = ref object of TruthTable
    newVarOrder: seq[string]

converter toTruthTableEdit*(table: TruthTable): TruthTableEdit =
  result = TruthTableEdit(table)
  result.newVarOrder = table.vars

func `[]`*(table: TruthTable, inputs: varargs[bool]): Option[bool] =
  var id = 0
  for i, input in inputs:
    if input:
      id += 1 shl (len(inputs)-1-i)
  table.results[id]

func collectResults(expr: Expr, vars: seq[string]): seq[Option[bool]] =
  var assign: Table[string, bool]
  let l = len(vars)
  for row in 0 ..< 1 shl l:
    for i in 0 ..< l:
      assign[vars[i]] = row.testBit(l-1-i)
    result.add some(expr.eval(assign))

func toTruthTable*(expr: Expr): TruthTable =
  result = TruthTable(vars: expr.vars.toSeq)
  sort result.vars
  result.results = collectResults(expr, result.vars)

func toTruthTable*(expr: Expr, vars: seq[string]): Result[TruthTable, HashSet[string]] =
  let exprVars = expr.vars.toSeq
  if vars.sorted != exprVars.sorted:
    err(vars.toHashSet - exprVars.toHashSet)
  else:
    ok(TruthTable(vars: vars, results: collectResults(expr, vars)))

proc reorderVars*(table: TruthTable, newVarOrder: seq[string]) =
  var results: seq[Option[bool]]
  for row in 0 ..< len(table.results):
    var orgRow = 0
    for i, v in newVarOrder:
      if row.testBit(high(newVarOrder) - i):
        orgRow += 1 shl (high(newVarOrder) - table.vars.find(v))
    results &= table.results[orgRow]
  table.vars = newVarOrder
  table.results = results

proc reorderVars*(table: TruthTableEdit) {.inline.} =
  reorderVars(TruthTable(table), table.newVarOrder)

func getNormalform*(table: TruthTable, kind: JunctionKind): Expr =
  exprBinOp(
    ( case kind
      of jkConj: boAnd
      of jkDisj: boOr
    ),
    collect(
      for rowi, row in table.results:
        if row == some(kind == jkDisj):
          exprBinOp(
            ( case kind
              of jkConj: boOr
              of jkDisj: boAnd
            ),
            collect(
              for vari, name in table.vars:
                if rowi.testBit(len(table.vars)-1-vari) == (kind == jkDisj):
                  exprVar(name)
                else:
                  exprNot(exprVar(name))
            )
          )
    )
  )

func getNormalforms*(table: TruthTable): array[JunctionKind, Expr] =
  for kind in JunctionKind:
    result[kind] = table.getNormalform(kind)


proc draw*(table: TruthTableEdit): VNode =
  var invalidVars = initHashSet[string]()
  if table.newVarOrder != table.vars:
    invalidVars = cmpVars(table.vars, table.newVarOrder)
    if len(invalidVars) == 0:
      table.reorderVars()

  buildHtml(table(
    id = "truthtable",
    class = if len(invalidVars) == 0: ""
            else: "outdated"
  )):
    tr:
      for i, name in table.newVarOrder:
        capture(i, buildHtml(th) do:
          input(
            `type` = "text",
            class = "var-input".concatIf(name in invalidVars, "invalid"),
            value = name
          ):
            proc oninput(_: Event, n: VNode) =
              table.newVarOrder[i] = n.inputValue
        )

    for i, res in table.results:
      tr:
        for v in countdown(len(table.vars)-1, 0):
          td:
            text $*i.testBit(v)
        td()
        td:
          text $*res

proc draw*(nfs: array[JunctionKind, Expr]): VNode =
  buildHtml(tdiv(id = "normalforms")):
    for (kind, name) in {jkDisj: "DNF", jkConj: "CNF"}:
      tdiv:
        bold: text name
        draw(nfs[kind])
