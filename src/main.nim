import std/[dom, options, sequtils, strutils, sets, math, sugar]
import fusion/matching
import results
include karax/prelude

import ./utils, ./selections
import ./junction, ./expression, ./conversion, ./truthtable, ./karnaugh, ./qmc, ./cmos, ./costs, ./hornsat, ./dpsat


type
  Problem = enum
    pTruthTable  = "TruthTable"
    pNfFromTable = "DNF/CNF from Table"
    pKarnaugh    = "Karnaugh Min."
    pQmc         = "Quine-McCluskey"
    pCmos        = "CMOS"
    pCost        = "Logicgate Costs"
    pHornSat     = "Horn SAT"
    pDpSat       = "Davis-Putnam"
    pConvertNand = "Convert to NAND-NAND"
    pConvertDnf  = "Convert to DNF"
    pConvertCnf  = "Convert to CNF"

  TableCompatProblem = range[pTruthTable .. pQmc]

  InputKind = enum
    iKarnaugh   = "Karnaugh Map"
    iExpression = "Logic Expression"
    iTruthTable = "TruthTable"
    iMinMaxTerm = "Min-/Max-Term"

  MTermKind = enum minTerm, maxTerm

  MinMaxTermsInput = ref object
    kind: MTermKind
    strVals: tuple[mterms, dontcare: string]
    intVals: tuple[mterms, dontcare: seq[int]]
    mtermDontcareCollisions: seq[int]

  Input = ref object
    problem: Problem
    case kind: InputKind
    of iExpression:
      expr: string
      error: Option[ExprError]
    of iMinMaxTerm: minMaxTerms: MinMaxTermsInput
    of iTruthTable: table: TruthTable
    of iKarnaugh: karnaugh: KarnaughLiveMin

  ProblemResult = object
    case problem: Problem
    of pTruthTable:
      table: TruthTableEdit
    of pNfFromTable:
      nfs: array[JunctionKind, Expr]
    of pKarnaugh:
      karnaugh: Karnaugh
      kmapKind: JunctionKind
    of pQmc:
      qmcs: Qmcs
      qmcKind: JunctionKind
    of pCmos: cmos: Cmos
    of pCost: cost: Cost
    of pHornSat: hornSat: Option[HornSat]
    of pDpSat:
      dpSat: DpSat
      useClauseNames: bool
    else:
      conv: Conversion

  Stage = enum selectProblem, selectInput, problemInput, problemResult
  State = object
    case stage: Stage
    of selectProblem: discard
    of selectInput: problem: Problem
    of problemInput: input: Input
    of problemResult: result: ProblemResult

var state = State()

func newInputState(problem: Problem, kind: InputKind): State =
  result = State(stage: problemInput, input: Input(problem: problem, kind: kind))
  case result.input.kind
  of iMinMaxTerm:
    result.input.minMaxTerms = MinMaxTermsInput()
  of iTruthTable:
    result.input.table = newTruthTable(3)
  of iKarnaugh:
    result.input.karnaugh = newKarnaughLiveMin(4)
  else: discard

# debug:
#state = newInputState(pDpSat, iExpression)

func `not`(kind: MTermKind): MTermKind {.inline.} =
  MTermKind(1 - kind.int)

proc update(input: MinMaxTermsInput) =
  template updateIntVals(field: untyped) =
    input.intVals.field = collect:
      block:
        let s = input.strVals.field
        input.strVals.field = ""
        var prevComma = true
        for c in s:
          case c
          of '0'..'9':
            prevComma = false
          of ',':
            if prevComma: continue
            prevComma = true
          of ' ':
            if not prevComma: continue
          else: continue
          input.strVals.field &= c

      for s in input.strVals.field.split(','):
        let s = s.strip()
        if s != "":
          parseInt(s)

  updateIntVals mterms
  updateIntVals dontcare

  input.mtermDontcareCollisions = @[]
  for t in input.intVals.mterms:
    if t in input.intVals.dontcare and t notin input.mtermDontcareCollisions:
      input.mtermDontcareCollisions &= t


converter toState(res: ProblemResult): State =
  State(stage: problemResult, result: res)

proc computeFromTable(table: TruthTable, problem: TableCompatProblem): ProblemResult =
  result = ProblemResult(problem: problem)
  case problem
  of pTruthTable: result.table = table
  of pNfFromTable: result.nfs = table.getNormalforms
  of pKarnaugh:
    result.karnaugh = table.toKarnaugh
    result.kmapKind = jkDisj
  of pQmc:
    result.qmcs = doQmc(table)
    result.qmcKind = jkDisj
  else: assert false

proc computeFromExpr(exprStr: string, problem: Problem): Result[ProblemResult, ExprError] =
  parseExpr(exprStr).map do(expr: Expr) -> ProblemResult:
    case problem
    of pTruthTable .. pQmc:
      return computeFromTable(expr.toTruthTable, problem)
    else:
      result = ProblemResult(problem: problem)
      case problem
      of pCmos: result.cmos = genCmos(expr)
      of pCost: result.cost = getCost(expr)
      of pHornSat: result.hornSat = doHornSat(expr)
      of pDpSat: result.dpSat = doDpSat(expr)
      else: result.conv = convert(expr):
        case problem
        of pConvertNand: caNand
        of pConvertDnf:  caDnf
        of pConvertCnf:  caCnf
        else: assert false; return

proc computeFromMinMaxTerm(input: MinMaxTermsInput, problem: TableCompatProblem): ProblemResult =
  if len(input.mtermDontcareCollisions) > 0: return

  let mtermResVal = input.kind == minTerm
  let varCount = int log2(float max(input.intVals.mterms & input.intVals.dontcare) + 1).ceil
  
  var table = TruthTable(
    vars: collect(for i in countdown(varCount, 1): "x" & $i),
    results: newSeqWith(1 shl varCount, some(not mtermResVal))
  )

  for mterm in input.intVals.mterms:
    table.results[mterm] = some(mtermResVal)
  for d in input.intVals.dontcare:
    if (Some(@v) ?= table.results[d]) and v != mtermResVal:
      table.results[d] = none(bool)

  computeFromTable(table, problem)


proc drawMenuItem(problem: Problem): VNode =
  buildHtml(tdiv):
    text $problem
    proc onclick =
      state = 
        if problem in {pTruthTable .. pQmc}:
          State(stage: selectInput, problem: problem)
        else:
          newInputState(problem, iExpression)

proc drawMenuItem(kind: InputKind): VNode =
  buildHtml(tdiv):
    text $kind
    proc onclick =
      state = newInputState(state.problem, kind)

proc draw(input: TruthTable, problem: Problem): VNode =
  let invalidVars = findDupAndEmpty(input.vars)

  buildHtml(form(id = "input-truthtable")):
    proc onsubmit(e: Event, _: VNode) =
      preventDefault e
      state = computeFromTable(input, problem)

    table:
      tr:
        for i, name in input.vars:
          capture(i, buildHtml(th) do:
            if len(input.vars) > 2:
              tdiv(class = "icon button delete"):
                proc onclick =
                  let stepSize = 1 shl (high(input.vars) - i)
                  let stepCount = 1 shl i
                  input.vars.delete(i)
                  var i = 0
                  for _ in 0 ..< stepCount:
                    for _ in 0 ..< stepSize:
                      input.results.delete(i)
                    i += stepSize
            input(
              `type` = "text",
              class = "var-input".concatIf(name in invalidVars, "invalid"),
              value = $name
            ):
              proc oninput(_: Event, n: VNode) =
                input.vars[i] = n.inputValue
          )
        td: tdiv(class = "icon button add", title = "add variable"):
          proc onclick =
            input.vars &= ""
            let res = input.results
            reset input.results
            for val in res:
              input.results &= @[val, val]

      for i, res in input.results:
        tr:
          for p in 0 ..< len(input.vars):
            td: text $((i shr (high(input.vars) - p)) and 1)
          td:
            tdiv(class = "result-select"):
              for val in [some(false), some(true), none(bool)]:
                capture(i, val, buildHtml(tdiv) do:
                  input(`type` = "radio", value = $*val, checked = res == val):
                    proc onclick(_: Event, n: VNode) =
                      input.results[i] = toBoolOption(n.inputValue)
                  tdiv:
                    text  if Some(@val) ?= val: $*val
                          else: "d"
                )
    button(class = "action", disabled = len(invalidVars) > 0):
      text "compute"

proc draw(input: MinMaxTermsInput, problem: TableCompatProblem): VNode =
  let isInvalid = len(input.mtermDontcareCollisions) > 0
  let isEmpty = len(input.intVals.mterms) + len(input.intVals.dontcare) == 0

  template drawEdit(v: string): VNode =
    buildHtml(input(`type` = "text", value = v, size = "1", placeholder = "Enter comma-seperated list")):
      proc oninput(_: Event, n: VNode) =
        v = n.inputValue
        input.update()
        n.dom.InputElement.value = v.cstring  # to ensure update even if `v` didnt change (override value set by browser)

  buildHtml(form(id = "input-minmaxterm")):
    proc onsubmit(e: Event, _: VNode) =
      preventDefault e
      state = computeFromMinMaxTerm(input, problem)

    tdiv(class = "inputs"):
      tdiv(class = "mterms"):
        tdiv(class = "selected"): text $input.kind
        tdiv:
          text $(not input.kind)
          proc onclick =
            input.kind = not input.kind
      drawEdit(input.strVals.mterms)

      tdiv(class = "dontcare"): text "don't care"
      drawEdit(input.strVals.dontcare)

    button(class = "action", disabled = isInvalid or isEmpty): text "compute"

proc draw(input: Input): VNode =
  case input.kind
  of iExpression:

    proc getExprInput: InputElement =
      document.querySelector("""#input-expression input[type="text"]""").InputElement

    buildHtml(tdiv(id = "input-expression")):
      form:
        proc onsubmit(e: Event, n: VNode) =
          preventDefault e
          let res = computeFromExpr(input.expr, input.problem)
          if res.isOk:
            state = res.get
          else:
            let err = res.error
            input.error = some(err)
            let exprInput = getExprInput()
            focus exprInput
            exprInput.selection = err.pos

        input(
          `type` = "text",
          placeholder = "Enter logic expression",
          size = "1",
          class = if input.error.isSome: "mark-error" else: "",
          value = input.expr
        ):
          proc oninput(e: Event, n: VNode) =
            reset input.error
            input.expr = n.inputValue
            # if its a clauseset notation, transform into logic expression
            if input.expr.startsWith("{{") and input.expr.endsWith("}}"):
              input.expr =
                input.expr[2 ..< ^2].split("},{").mapIt(
                  "(" & it.split(',').mapIt(it.strip).join(" ∨ ") & ")"
                ).join(" ∧ ")

          proc onclick =
            reset input.error

        input(
          `type` = "submit",
          value = "compute",
          class = "action",
          disabled = len(input.expr) == 0
        )

      if Some(@e) ?= input.error:
        tdiv(class = "error-box"): text e.msg

      tdiv(id = "extra-keyboard"):
        for sym in ["¬", "∧", "∨", "↔", "→", "(", ")"]:
          button:
            text sym
            proc onclick(e: Event, n: VNode) {.noredraw.} =
              preventDefault e
              let key = n.dom.innerHtml
              let inputElem = getExprInput()
              let oldSelection = inputElem.selection
              inputElem.value[oldSelection] = $key
              focus inputElem
              inputElem.selection = newSelection(oldSelection.a + len(key))
              input.expr = $inputElem.value

      tdiv(class = "info-box"):
        tdiv(class = "title"): text "Help"
        tdiv(class = "content"):

          func drawRow(syms: seq[string], desc: string): VNode =
            buildHtml(tr):
              th:
                for sym in syms:
                  tdiv: text sym
              td:
                text desc

          table:
            drawRow(allowedSymbolsNot, "not / negation")
            for op, desc in [boAnd: "and / conjunction", boOr: "or / disjunction", boBiImpl: "bi-directional implication", boImpl: "implication"]:
              drawRow(allowedSymbolsBinOp[op], desc)

          p:
            text "You can use "
            span: text "( )"
          p:
            text "All variable names that match "
            span(class = "nowrap"): text r"[a-zA-Z_][a-zA-Z0-9_]*"
            text " are allowed"

  of iTruthTable: draw(input.table, input.problem)
  of iMinMaxTerm: draw(input.minMaxTerms, input.problem)
  
  of iKarnaugh:
    assert input.problem == pKarnaugh
    draw(input.karnaugh)

proc createDom: VNode =
  template res: var ProblemResult = state.result

  buildHtml(tdiv):
    tdiv(id = "header"):
      case state.stage
      of problemInput:
        if state.input.kind == iKarnaugh:
          tdiv(id = "header-menu"):
            for (kind, name) in {jkDisj: "DNF", jkConj: "CNF"}:
              tdiv(class = if state.input.karnaugh.kind == kind: "selected" else: ""):
                text name
            proc onclick =
              state.input.karnaugh.kind = not state.input.karnaugh.kind
              state.input.karnaugh.recompute()

      of problemResult:
        case res.problem
        of pKarnaugh:
          tdiv(id = "header-menu"):
            for (kind, name) in {jkDisj: "DNF", jkConj: "CNF"}:
              tdiv(class = if res.kmapKind == kind: "selected" else: ""):
                text name
            proc onclick =
              res.kmapKind = not res.kmapKind

        of pQmc:
          tdiv(id = "header-menu"):
            for kind in JunctionKind:
              tdiv(class = if res.qmcKind == kind: "selected" else: ""):
                text $kind
            proc onclick =
              res.qmcKind = not res.qmcKind

        of pDpSat:
          tdiv(id = "header-config-option"):
            input(`type` = "checkbox", checked = res.useClauseNames):
              proc onclick =
                res.useClauseNames = not res.useClauseNames
            tdiv: text "Named Clauses"

        else: discard
      else: discard

    tdiv(id = "content"):
      case state.stage
      of selectProblem:
        tdiv(id = "menu"): tdiv:
          for problem in Problem:
            drawMenuItem(problem)
      
      of selectInput:
        tdiv(id = "menu"):
          tdiv(class = "title"): text "input as"
          tdiv:
            if state.problem == pKarnaugh:
              drawMenuItem(iKarnaugh)
            for kind in InputKind.iExpression .. iMinMaxTerm:
              drawMenuItem(kind)
      
      of problemInput: draw(state.input)

      of problemResult:
        case res.problem
        of pTruthTable: draw(res.table)
        of pNfFromTable: draw(res.nfs)
        of pKarnaugh: draw(res.karnaugh, res.kmapKind)
        of pQmc: draw(res.qmcs, res.qmcKind)
        of pCmos: draw(res.cmos)
        of pCost: draw(res.cost)
        of pHornSat: draw(res.hornSat)
        of pDpSat: draw(res.dpSat, res.useClauseNames)
        else: draw(res.conv)
      

setRenderer createDom