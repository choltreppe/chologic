import std/[sugar, sequtils, strformat, options, bitops, algorithm, sets]
import fusion/matching
import results
include karax/prelude
import karax/vstyles

import ./utils
import ./junction, ./truthtable, ./expression
from ./qmc import Impli, QmcResult, minimize


type
  Solution = QmcResult

  Karnaugh* = ref object
    table: TruthTable
    rowVars, colVars: seq[string]
    solutions: array[JunctionKind, seq[Solution]]

  ImpliMap = seq[seq[seq[int]]]  # (row, col) -> seq[impli-id]


converter toInt(b: seq[bool]): int =
  result = 0
  for b in b:
    result = (result shl 1) and ord(b)


func genIds(n: int): seq[seq[bool]] =
  result.add @[]
  for _ in 0 ..< n:
    result =
      result.mapIt(false & it) &
      result.reversed.mapIt(true & it)

func genImpliMap(implis: seq[Impli], rowIds, colIds: seq[seq[bool]], table: TruthTable): ImpliMap =
  rowIds.map(row =>
    colIds.map(col => (
      let input = row&col
      collect:
        for i, impli in implis:
          if (0 ..< len(impli)).toSeq.all(i => impli[i].isNone or impli[i].get == input[i]):
            i
    ))
  )

proc genSolutions(karnaugh: Karnaugh) =
  for kind, solution in karnaugh.solutions.mpairs:
    solution = karnaugh.table.minimize(kind)

func toKarnaugh*(table: TruthTable, mid: int): Karnaugh =
  result = Karnaugh(
    table: table,
    rowVars: table.vars[0 ..< mid],
    colVars: table.vars[mid .. ^1]
  )
  result.genSolutions()

func toKarnaugh*(table: TruthTable): Karnaugh {.inline.} =
  table.toKarnaugh(len(table.vars) div 2)

proc recompute(karnaugh: Karnaugh) =
  karnaugh.table.reorderVars(karnaugh.rowVars & karnaugh.colVars)
  karnaugh.genSolutions()


proc drawImpliMap(
  table: TruthTable,
  implis: seq[Impli],
  rowVarCount: int,
  onClickCell: proc(id: seq[bool]) = nil
): tuple[
  map, implis: VNode
] =
  let rowIds = genIds(rowVarCount)
  let colIds = genIds(len(table.vars) - rowVarCount)

  var colorsImpli, colorsText: seq[VStyle]
  for i in 0 ..< len(implis):
    let hue = (i * 360) div len(implis)
    colorsImpli &= style(
      (borderColor, kstring &"hsl({hue},100%,70%)"),
      (backgroundColor, kstring &"hsla({hue},100%,50%,0.2)")
    )
    colorsText &= style(
      (color, kstring &"color: hsl({hue},100%,70%)")
    )

  let filled: seq[tuple[row,col: bool]] =
    implis.mapIt((
      it[0 ..< rowVarCount].allIt(it.isNone),
      it[rowVarCount .. ^1].allIt(it.isNone)))

  let
    map = genImpliMap(implis, rowIds, colIds, table)
    rowLen = len(map)
    colLen = len(map[0])

  let markerMargin = "4px"

  proc genMarkers(row,col,i: int): VNode =
    var style = style()

    if not (
        row >  0 and i in map[row-1][col] or
        row == 0 and i in map[rowLen-1][col] and not filled[i].row
       ):
      style.setAttr(marginTop, markerMargin)

    if not (
        row+1 <  rowLen and i in map[row+1][col] or
        row+1 == rowLen and i in map[0][col] and not filled[i].row
       ):
      style.setAttr(marginBottom, markerMargin)

    if not (
        col >  0 and i in map[row][col-1] or
        col == 0 and i in map[row][colLen-1] and not filled[i].col
       ):
      style.setAttr(marginLeft, markerMargin)

    if not (
        col+1 <  colLen and i in map[row][col+1] or
        col+1 == colLen and i in map[row][0] and not filled[i].col
       ):
      style.setAttr(marginRight, markerMargin)

    buildHtml(tdiv(class = "mark", style = colorsImpli[i] & style))

  result.map =
    buildHtml(table(class = "kmap")):
      tr:
        th()
        for id in colIds:
          th: #TODO single text node
            for bit in id:
              text $*bit

      for row, rowId in rowIds:
        tr:
          th: #TODO single text node
            for bit in rowId:
              text $*bit
          for col, colId in colIds:
            td:
              for i in map[row][col]:
                genMarkers(row, col, i)
              let i = rowId&colId
              capture(i, buildHtml(tdiv) do:
                text $*table[i]
                if onClickCell != nil:
                  proc onclick = onClickCell(i)
              )

  result.implis =
    buildHtml(tdiv(class = "implis")):
      table:
        tr:
          for name in table.vars:
            th: text name
        for i, impli in implis:
          tr(style = colorsText[i]):
            for v in impli:
              td: text $*v

proc draw(karnaugh: Karnaugh, kind: JunctionKind, solutionId: int): VNode =
  let vars = karnaugh.rowVars & karnaugh.colVars

  var invalidVars = initHashSet[string]()
  if vars != karnaugh.table.vars:
    invalidVars = cmpVars(karnaugh.table.vars, vars)
    if len(invalidVars) == 0:
      karnaugh.recompute()

  proc drawVars(class: string, editVars, otherVars: ptr seq[string]): VNode =
    buildHtml(tdiv(class = "vars " & class)):
      for i, v in editVars[]:
        capture(i,
          buildHtml(input(
            `type` = "text",
            value = v,
            class = "var-input".concatIf(v in invalidVars, "invalid")
          )) do:
            proc oninput(_: Event, n: VNode) =
              editVars[i] = n.inputValue
        )
      if len(otherVars[]) > 1:
        tdiv(class = "icon button add"):
          proc onclick =
            editVars[] &= pop otherVars[]
            karnaugh.recompute()

  let solution = karnaugh.solutions[kind][solutionId]
  let (mapHtml, impliHtml) = drawImpliMap(
    karnaugh.table,
    solution.implis,
    len(karnaugh.rowVars)
  )

  buildHtml(tdiv(class = "karnaugh".concatIf(len(invalidVars) > 0, "outdated"))):
    drawVars("row", addr karnaugh.rowVars, addr karnaugh.colVars)
    drawVars("col", addr karnaugh.colVars, addr karnaugh.rowVars)
    mapHtml
    impliHtml
    draw(solution.expr)

proc draw*(karnaugh: Karnaugh, kind: JunctionKind): VNode =
  let solutions = karnaugh.solutions[kind]
  if len(solutions) == 1:
    draw(karnaugh, kind, 0)
  else:
    buildHtml(tdiv(id = "karnaugh-options")):
      for i in 0 ..< len(solutions):
        tdiv(class = "group"):
          tdiv(class = "title"): text "Option " & $(i+1)
          tdiv(class = "content"): draw(karnaugh, kind, i)


type  KarnaughLiveMin* = ref object
  table: TruthTable
  rowVarCount: int
  kind*: JunctionKind
  solution: Solution

proc recompute*(karnaugh: KarnaughLiveMin) =
  karnaugh.solution = karnaugh.table.minimize(karnaugh.kind)[0]

func newKarnaughLiveMin*(varCount: int): KarnaughLiveMin =
  result = KarnaughLiveMin(
    table: newTruthTable(varCount),
    rowVarCount: varCount div 2,
    kind: jkConj
  )
  result.table.results[0] = some(true)
  result.recompute()

proc draw*(karnaugh: KarnaughLiveMin): VNode =

  let invalidVars = findDupAndEmpty(karnaugh.table.vars)

  proc drawVars(class: string, slice: Slice[int]): VNode =
    buildHtml(tdiv(class = "vars " & class)):
      for i, v in karnaugh.table.vars[slice]:
        capture(i,
          buildHtml(input(
            `type` = "text",
            value = v,
            class = "var-input".concatIf(v in invalidVars, "invalid")
          )) do:
            proc oninput(_: Event, n: VNode) =
              karnaugh.table.vars[i+slice.a] = n.inputValue
        )
      tdiv(class = "icon button add"):
        proc onclick =
          karnaugh.table.vars.insert("", slice.b)
          karnaugh.table.results &= repeat(some(false), len(karnaugh.table.results))
          karnaugh.recompute()

  let (mapHtml, impliHtml) = drawImpliMap(
    karnaugh.table,
    karnaugh.solution.implis,
    karnaugh.rowVarCount
  ) do(id: seq[bool]):
    karnaugh.table[id] =
      if Some(@v) ?= karnaugh.table[id]:
        if v: none(bool)
        else: some(true)
      else: some(false)
    karnaugh.recompute()

  buildHtml(tdiv(id = "karnaugh-live")):

    tdiv(id = "result-menu"):
      for (kind, name) in {jkDisj: "DNF", jkConj: "CNF"}:
        tdiv(class = if karnaugh.kind == kind: "selected" else: ""):
          text name
      proc onclick =
        karnaugh.kind = not karnaugh.kind
        karnaugh.recompute()

    tdiv(class = "karnaugh"):
      drawVars("row", 0 .. karnaugh.rowVarCount-1)
      drawVars("col", karnaugh.rowVarCount .. len(karnaugh.table.vars)-1)
      mapHtml
      impliHtml
      draw(karnaugh.solution.expr)

    tdiv(class = "info-box single-line"):
      tdiv(class = "title"): text "Help"
      tdiv(class = "content"): text "click on the table cells to toggle between false / true / dont-care"
