import std/[sugar, sequtils, strutils, options, bitops, enumerate]
import fusion/matching
include karax/prelude

import ./utils
import ./expression, ./junction, ./truthtable


const maxMinimisedImplisCount = 8

type
  MTerms = set[uint8]

  Impli* = seq[Option[bool]]

  ImpliMterms = object of RootObj
    impli: Impli
    mterms: MTerms

  QmcRow = object of ImpliMTerms
    used: bool
  QmcGroup = seq[QmcRow]
  QmcStep = seq[QmcGroup]

  ImpliTable = object
    title: string
    mterms: MTerms
    rows: seq[ImpliMTerms]
    uniqueTerms: seq[MTerms]

  Qmc = object
    steps: seq[QmcStep]
    impliTables: seq[ImpliTable]
    results: seq[tuple[inplis: seq[Impli], expr: Expr]]  # all minimal impli combinations with expression
    omittedResultsCount: int  # if too many possibilities, not all are included
  Qmcs* = object
    vars: seq[string]
    qmcs: array[JunctionKind, Qmc]


func toExpr(implis: seq[Impli], vars: seq[string], kind: JunctionKind): Expr =
  exprBinOp(
    (
      case kind
      of jkDisj: boOr
      of jkConj: boAnd
    ),
    implis.map(impli =>
      exprBinOp(
        (
          case kind
          of jkDisj: boAnd
          of jkConj: boOr
        ),
        collect(
          for i, v in impli:
            if Some(@v) ?= v:
              if v == (kind == jkDisj):
                exprVar(vars[i])
              else:
                exprNot(exprVar(vars[i]))
        )
      )
    )
  )


func doQmc(table: TruthTable, kind: JunctionKind): Qmc =
  
  block:
    # get min-/maxterms and initial groups
    result.impliTables &= ImpliTable(title: "prime-implicant chart")
    var groups = newSeq[QmcGroup](len(table.vars)+1)
    for i, res in table.results.pairs:
      if res.isNone: discard
      elif res.unsafeGet != (kind == jkConj):
        result.impliTables[0].mterms.incl i.uint8
      else: continue
      groups[countSetBits(i)] &= QmcRow(
        mterms: {uint8 i},
        impli: collect(
          for b in countdown(len(table.vars)-1, 0):
            some(i.testBit(b))
      ))


    while len(groups) > 1 and groups.anyIt(len(it) > 0):
      result.steps &= move(groups)
      groups = newSeq[QmcGroup](len(result.steps[^1])-1)

      # find combined implis for next groups
      for i, group in groups.mpairs:
        for rid1, row1 in result.steps[^1][i]:
          for rid2, row2 in result.steps[^1][i+1]:
            var foundDiff = false
            block tryCombineTerms:
              var newRow: QmcRow
              for i in 0 ..< len(table.vars):
                newRow.impli.add:
                  if row1.impli[i] == row2.impli[i]: row1.impli[i]
                  elif foundDiff: break tryCombineTerms
                  else:
                    foundDiff = true
                    none(bool)
                newRow.mterms.incl row1.mterms + row2.mterms
              group.add newRow
              result.steps[^1][i][rid1].used = true
              result.steps[^1][i+1][rid2].used = true
      
  # build initial prime-implicants table
  block:
    var implisCovered: seq[Impli]
    for step in result.steps:
      for group in step:
        for row in group:
          if not row.used and row.impli notin implisCovered:
            implisCovered &= row.impli
            result.impliTables[0].rows &= ImpliMTerms(
              impli: row.impli,
              mterms: row.mterms * result.impliTables[0].mterms
            )

  var essentialImplis: seq[Impli]
  
  # find all neccesary implis
  block:
    template prevTable: var ImpliTable = result.impliTables[^1]
    template buildTable(titleStr: string, body) =
      block:
        var table {.inject.} = ImpliTable(title: titleStr)
        body
        result.impliTables &= table

    var reducedImplis = true
    while reducedImplis:
      reducedImplis = false

      prevTable.uniqueTerms.setLen len(prevTable.rows)
      var essCoveredTerms: MTerms
      for mterm in prevTable.mterms:
        block findUniqueRow:
          var uniqueRow = -1
          for rowi, row in prevTable.rows:
            if mterm in row.mterms:
              if uniqueRow >= 0: break findUniqueRow
              else: uniqueRow = rowi
          if uniqueRow >= 0:
            prevTable.uniqueTerms[uniqueRow].incl mterm
            essCoveredTerms.incl prevTable.rows[uniqueRow].mterms

      buildTable("delete essential implicants"):
        table.mterms = prevTable.mterms - essCoveredTerms
        for i, row in prevTable.rows:
          if len(prevTable.uniqueTerms[i]) > 0:
            essentialImplis.add row.impli
            reducedImplis = true
          else:
            table.rows &= row
            table.rows[^1].mterms.excl essCoveredTerms

      buildTable("delete dominated rows"):
        var deletedRows = false
        for row in prevTable.rows:
          if prevTable.rows.anyIt(row.mterms < it.mterms):
            deletedRows = true
          else:
            table.rows &= row
        if not deletedRows:
          break
        reducedImplis = true
        var emptyCols: MTerms
        for mterm in prevTable.mterms:
          if table.rows.allIt(mterm notin it.mterms):
            emptyCols.incl mterm
        table.mterms = prevTable.mterms - emptyCols

      buildTable("delete dominant columns"):
        let cols = collect:
          for mterm in prevTable.mterms:
            var col: set[uint8]
            for i, row in prevTable.rows:
              if mterm in row.mterms:
                col.incl i.uint8
            col
        var dominantCols: MTerms
        for i, mterm in enumerate(prevTable.mterms):
          let col = cols[i]
          if cols.anyIt(col > it):
            dominantCols.incl mterm
        if len(dominantCols) == 0:
          break 
        reducedImplis = true
        table.mterms = prevTable.mterms - dominantCols
        table.rows = prevTable.rows
        for row in table.rows.mitems:
          row.mterms.excl dominantCols

  # build minimal impli combination options
  block:
    let impliTable = result.impliTables[^1]
    let mterms = impliTable.mterms.toSeq
    proc getOptions(i = 0): seq[seq[Impli]] =
      if i == len(mterms): return @[essentialImplis]
      let mterm = mterms[i]
      let options = getOptions(i+1)
      for row in impliTable.rows:
        if mterm in row.mterms:
          for option in options:
            result &= row.impli & option
    var options = getOptions()
    if len(options) > maxMinimisedImplisCount:
      result.omittedResultsCount = len(options) - maxMinimisedImplisCount
      options.setLen maxMinimisedImplisCount
    result.results = options.mapIt((it, it.toExpr(table.vars, kind)))

func doQmc*(table: TruthTable): Qmcs =
  result.vars = table.vars
  for kind, qmc in result.qmcs.mpairs:
    qmc = doQmc(table, kind)


func minimize*(
  table: TruthTable,
  kind: JunctionKind
): tuple[
  results: seq[(seq[Impli], Expr)],
  omittedResultsCount: int
] {.inline.} =
  let qmc = doQmc(table, kind)
  (qmc.results, qmc.omittedResultsCount)



proc draw(mterms: MTerms, kind: JunctionKind): VNode =
  buildHtml(text):
    (if kind == jkDisj: "m" else: "M") &
    "(" & collect(for t in mterms: $t).join(",") & ")"
    # TODO: render as suffix

iterator drawTableRow(impli: Impli): VNode =
  for i, v in impli:
    yield buildHtml(td(class = if i == 0: "" else: "impli-cell")):
      text $*v

proc draw(step: QmcStep, vars: seq[string], kind: JunctionKind, i: int): VNode =
  buildHtml(table(class = "step")):
    tr:
      th(class = "title", colspan = $(len(vars) + 1)):
        text $i & "-Cubes"
    tr:
      th(rowspan = "2"):
        text (if kind == jkDisj: "Minterm" else: "Maxterm")
      th(colspan = $len(vars)):
        text "Implicants"
      th(rowspan = "2")
    tr:
      for name in vars:
        td(class = "impli-varname"):
          text name

    for gi, group in step:
      for ri, row in group:
        tr(class = if gi > 0 and ri == 0: "group-start" else: ""):
          td: draw(row.mterms, kind)
          for item in drawTableRow(row.impli): item
          td(class = if row.used: "used" else: "")

proc draw(table: ImpliTable, vars: seq[string]): Option[VNode] =
  if len(table.mterms) == 0: return
  let withUniqueTermsMarked = table.uniqueTerms.anyIt(len(it) > 0)

  some: buildHtml(table(class = "impli-table")):
    tr:
      th(
        class = "title",
        colspan = $(len(vars) + len(table.mterms) + withUniqueTermsMarked.int)
      ): text table.title

    tr:
      th(colspan = $len(vars))
      if withUniqueTermsMarked:
        th(class = "essential-marker-col", rowspan = "2")
      for mterm in table.mterms:
        th(rowspan = "2"): text $mterm
    tr:
      for name in vars:
        td(class = "impli-varname"):
          text name

    for i, row in table.rows:
      tr:
        for item in drawTableRow(row.impli): item
        if withUniqueTermsMarked:
          td:
            if len(table.uniqueTerms[i]) > 0:
              text "*"
        for mterm in table.mterms:
          td:
            if mterm in row.mterms:
              tdiv(
                class = "covered-mterm".concatIf(
                  withUniqueTermsMarked and mterm in table.uniqueTerms[i],
                  " unique"
              ))

proc draw*(qmcs: Qmcs, kind: JunctionKind): VNode =
  let qmc = qmcs.qmcs[kind]
  buildHtml(tdiv(id = "qmc")):
    tdiv:
      for i, step in qmc.steps:
        draw(step, qmcs.vars, kind, i)
    tdiv:
      for table in qmc.impliTables:
        if Some(@node) ?= draw(table, qmcs.vars):
          node

    tdiv(id = "qmc-results"):
      tdiv(class = "title"): text "Result"
      tdiv(class = "content"):
        draw(qmc.results[0].expr)
        for (_, expr) in qmc.results[1..^1]:
          bold: text "or"
          draw(expr)
        if qmc.omittedResultsCount > 0:
          bold: text ".. " & $qmc.omittedResultsCount & " more"