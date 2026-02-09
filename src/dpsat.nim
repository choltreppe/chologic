import std/[options, sequtils, sets, algorithm, sugar, strformat]
import fusion/matching
include karax/prelude

import ./utils, ./expression, ./conversion, ./sat


type
  Clause = seq[tuple[name: string, polarity: bool]]

  ClauseId = Natural

  Resolution = object
    left, right, res: ClauseId

  DpSat* = object
    conversion: Option[Conversion]
    clauses: seq[Clause]
    startClauses: seq[ClauseId]
    steps: seq[tuple[
      choosenVar: string,
      resolutions: seq[Resolution],
      newClauses: seq[ClauseId],
      removedClauses: seq[ClauseId]
    ]]
    sat: bool
  

func toClauseSet(expr: Expr): Option[seq[Clause]] =
  template getVarWithPolarity(expr: Expr): tuple[name: string, polarity: bool] =
    if expr =: ekNot and expr.inner =: ekVar:
      (expr.inner.name, false)
    elif expr =: ekVar:
      (expr.name, true)
    else: return

  template getClause(expr: Expr): Clause =
    if expr =: boOr:
      expr.operands.mapIt(getVarWithPolarity(it))
    else:
      @[getVarWithPolarity(expr)]

  if expr =: boAnd:
    return some(
      expr.operands.mapIt(getClause(it)),
    )
  some(@[getClause(expr)])


proc doDpSat*(expr: Expr): DpSat =

  result.clauses =
    if Some(@clauses) ?= expr.toClauseSet(): clauses
    else:
      result.conversion = some expr.convert(caCnf)
      let res = result.conversion.unsafeGet.res
      if res =: ekVal:
        result.sat = res.val
        return
      res.toClauseSet.get

  proc isNormalform(clause: Clause): bool =
    for i in 0 ..< high(clause):
      let (n1, p1) = clause[i]
      for (n2, p2) in clause[i+1 .. ^1]:
        if n1 == n2 and p1 != p2:
          return false
    true

  result.clauses.keepIf(isNormalform)

  let vars = collect(
    for clause in result.clauses:
      for (name, _) in clause: name
  )
  .deduplicate
  .sorted

  var curClauseIds = collect(for i, _ in result.clauses: Natural(i))

  result.startClauses = curClauseIds
  result.sat = true

  for name in vars:

    if not result.sat: break

    var inclVarNormal, inclVarInvert: seq[ClauseId]
    for clauseId in curClauseIds:
      let clause = result.clauses[clauseID]
      if   (name, true ) in clause: inclVarNormal &= clauseID
      elif (name, false) in clause: inclVarInvert &= clauseID

    if len(inclVarNormal) > 0 and len(inclVarInvert) > 0:
      curClauseIds.keepItIf(it notin inclVarNormal&inclVarInvert)
      let resolutions = collect(
        for a in inclVarNormal:
          for b in inclVarInvert:
            result.clauses &= (result.clauses[a] & result.clauses[b]).filterIt(it.name != name).deduplicate()
            curClauseIds &= high(result.clauses)
            if len(result.clauses[^1]) == 0: result.sat = false
            Resolution(left: a, right: b, res: high(result.clauses))
      )
      var removedClauses: seq[ClauseId]
      curClauseIds.keepItIf:
        if result.clauses[it].isNormalform: true
        else: removedClauses &= it; false

      result.steps &= (name, resolutions, curClauseIds, removedClauses)



proc draw*(algo: DpSat, useClauseNames: bool): VNode =
  
  proc draw(clause: Clause): VNode =
    buildHtml(tdiv(class = "clause")):
      text "{"
      for i, v in clause:
        if i > 0: text ","
        draw(
          if v.polarity: exprVar(v.name)
          else:  exprNot(exprVar(v.name))
        )
      text "}"

  proc draw(id: ClauseId): VNode =
    if useClauseNames:
      buildHtml(span): text cstring(&"C{id+1}")
    else:
      draw(algo.clauses[id])

  proc draw(resolution: Resolution): VNode =
    buildHtml(tdiv(class = "resolution")):
      tdiv:
        draw(resolution.left)
        draw(resolution.right)

      if useClauseNames:
        tdiv(class = "result-with-naming"):
          draw(algo.clauses[resolution.res])
          span: text "=:"
          draw(resolution.res)
      else:
        draw(resolution.res)

  proc draw(clauses: seq[ClauseId], areStartClauses = false): VNode =
    let withClauseNames = areStartClauses and useClauseNames

    buildHtml:
      tdiv(class = "clause-set".concatIf(withClauseNames, "with-names")):
        text "Φ = {"
        for i, clauseId in clauses:
          if i > 0: text ","
          if withClauseNames:
            tdiv(class = "clause-with-name"):
              draw(algo.clauses[clauseId])
              draw(clauseId)
          else:
            draw(clauseId)
        text "}"

  buildHtml(tdiv(id = "dp-sat-container", class = "box")):
    if Some(@conv) ?= algo.conversion:
      tdiv(class = "group"):
        tdiv(class = "title"): text "Conversion"
        tdiv(class = "content"): draw(conv)

    tdiv(class = "dp-sat".concatIf(useClauseNames, "named-clauses")):
      draw(algo.startClauses, areStartClauses = true)

      for step in algo.steps:
        tdiv(class = "group"):
          tdiv(class = "title"): text cstring("choose " & step.choosenVar)
          tdiv(class = "content"):
            if len(step.resolutions) > 0:
              tdiv(class = "resolutions"):
                for resolution in step.resolutions:
                  draw(resolution)
            draw(step.newClauses)
            if len(step.removedClauses) > 0:
              tdiv(class = "warning-box"):
                text "eliminated clauses not in normal form: "
                for i, clause in step.removedClauses:
                  if i > 0: text ", "
                  draw(clause)

      satResultHtml(algo.sat, "Φ")