import std/[sugar, sequtils, strformat, options, bitops, algorithm, sets]
import fusion/matching
import results
include karax/prelude
import karax/vstyles

import ./utils
import ./junction, ./truthtable, ./expression
from ./qmc import Impli, minimize


const maxTotalImplis = 32

type
  KMap = object
    map: seq[seq[(Option[bool], seq[int])]]
    implis: seq[Impli]
    expr: Expr

  KMaps = object
    kmaps: seq[KMap]
    omittedKmapsCount: int  # if too many possibilities, not all are included

  Karnaugh* = ref object
    table: TruthTable
    rowVars, colVars: seq[string]
    rowIds , colIds: seq[seq[bool]]
    kmaps: array[JunctionKind, KMaps]


func genIds(n: int): seq[seq[bool]] =
  result.add @[]
  for _ in 0 ..< n:
    result =
      result.mapIt(false & it) &
      result.reversed.mapIt(true & it)

func genMap(implis: seq[Impli], rowIds, colIds: seq[seq[bool]], table: TruthTable): seq[seq[(Option[bool], seq[int])]] =
  rowIds.map(row =>
    colIds.map(col => (
      let input = row & col
      (
        table[input],
        collect(
          for i, impli in implis:
            if (0 ..< len(impli)).toSeq.all(i => impli[i].isNone or impli[i].get == input[i]):
              i
        )
      )
    ))
  )


proc genKMaps(karnaugh: Karnaugh) =
  karnaugh.rowIds  = genIds(len(karnaugh.rowVars))
  karnaugh.colIds  = genIds(len(karnaugh.colVars))
  for kind in JunctionKind:
    let (results, omittedCount) = karnaugh.table.minimize(kind)
    karnaugh.kmaps[kind].omittedKmapsCount = omittedCount
    karnaugh.kmaps[kind].kmaps = @[]
    var totalImplis = 0
    for i, (implis, expr) in results:
      totalImplis += len(implis)
      if totalImplis > maxTotalImplis:
        karnaugh.kmaps[kind].omittedKmapsCount += len(results) - i
        break
      karnaugh.kmaps[kind].kmaps &= KMap(
        implis: implis,
        expr: expr,
        map: genMap(implis, karnaugh.rowIds, karnaugh.colIds, karnaugh.table)
      )

func toKarnaugh*(table: TruthTable, mid: int): Karnaugh =
  result = Karnaugh(
    table: table,
    rowVars: table.vars[0 ..< mid],
    colVars: table.vars[mid .. ^1]
  )
  result.genKMaps()

func toKarnaugh*(table: TruthTable): Karnaugh {.inline.} =
  table.toKarnaugh(len(table.vars) div 2)

proc recompute(karnaugh: Karnaugh) =
  karnaugh.table.reorderVars(karnaugh.rowVars & karnaugh.colVars)
  karnaugh.genKMaps()


proc draw(karnaugh: Karnaugh, kind: JunctionKind, i: int): VNode =
  let vars = karnaugh.rowVars & karnaugh.colVars

  var invalidVars = initHashSet[string]()
  if vars != karnaugh.table.vars:
    invalidVars = cmpVars(karnaugh.table.vars, vars)
    if len(invalidVars) == 0:
      karnaugh.recompute()

  let kmap = karnaugh.kmaps[kind].kmaps[i]

  var colorsImpli, colorsText: seq[VStyle]
  for i in 0 ..< len(kmap.implis):
    let hue = (i * 360) div len(kmap.implis)
    colorsImpli &= style(
      (borderColor, kstring &"hsl({hue},100%,70%)"),
      (backgroundColor, kstring &"hsla({hue},100%,50%,0.2)")
    )
    colorsText &= style(
      (color, kstring &"color: hsl({hue},100%,70%)")
    )

  let rowvarLen = len(karnaugh.rowVars)
  let filled: seq[tuple[row,col: bool]] =
    kmap.implis.mapIt((
      it[0 ..< rowvarLen].allIt(it.isNone),
      it[rowVarLen .. ^1].allIt(it.isNone)))

  let
    rowLen = len(kmap.map)
    colLen = len(kmap.map[0])

  let markerMargin = "4px"

  proc genMarkers(row,col,i: int): VNode =
    var style = style()

    if not (
        row >  0 and i in kmap.map[row-1][col][1] or
        row == 0 and i in kmap.map[rowLen-1][col][1] and not filled[i].row
       ):
      style.setAttr(marginTop, markerMargin)

    if not (
        row+1 <  rowLen and i in kmap.map[row+1][col][1] or
        row+1 == rowLen and i in kmap.map[0][col][1] and not filled[i].row
       ):
      style.setAttr(marginBottom, markerMargin)

    if not (
        col >  0 and i in kmap.map[row][col-1][1] or
        col == 0 and i in kmap.map[row][colLen-1][1] and not filled[i].col
       ):
      style.setAttr(marginLeft, markerMargin)

    if not (
        col+1 <  colLen and i in kmap.map[row][col+1][1] or
        col+1 == colLen and i in kmap.map[row][0][1] and not filled[i].col
       ):
      style.setAttr(marginRight, markerMargin)

    buildHtml(tdiv(class = "mark", style = colorsImpli[i] & style))

  let htmlKMap =
    buildHtml(table(class = "kmap")):
      tr:
        th()
        for id in karnaugh.colIds:
          th:
            for bit in id:
              text $*bit

      for rowi, row in kmap.map.pairs:
        tr:
          th:
            for v in karnaugh.rowIds[rowi]:
              text $*v
          for coli, val in row.pairs:
            td:
              for i in val[1]:
                genMarkers(rowi, coli, i)
              tdiv:
                text $*val[0]

  let htmlImplis =
    buildHtml(tdiv(class = "implis")):
      table:
        tr:
          for name in vars:
            th: text name
        for i, impli in kmap.implis.pairs:
          tr(style = colorsText[i]):
            for v in impli:
              td: text $*v

  proc genVarsHtml(class: string, editVars, otherVars: ptr seq[string]): VNode =
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

  buildHtml(tdiv(class = "karnaugh".concatIf(len(invalidVars) > 0, "outdated"))):
    genVarsHtml("col", addr karnaugh.colVars, addr karnaugh.rowVars)
    genVarsHtml("row", addr karnaugh.rowVars, addr karnaugh.colVars)
    htmlKMap
    htmlImplis
    draw(kmap.expr)

proc draw*(karnaugh: Karnaugh, kind: JunctionKind): VNode =
  let kmaps = karnaugh.kmaps[kind]
  if len(kmaps.kmaps) == 1:
    draw(karnaugh, kind, 0)
  else:
    buildHtml(tdiv(id = "karnaugh-options")):
      for i in 0 ..< len(kmaps.kmaps):
        tdiv(class = "group"):
          tdiv(class = "title"): text "Option " & $(i+1)
          tdiv(class = "content"): draw(karnaugh, kind, i)