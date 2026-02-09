import std/[sequtils, strformat, options]
import fusion/matching
include karax/prelude
import karax/vstyles

import ./expression, ./conversion


type
  MosKind = enum mkPmos="pmos", mkNmos="nmos"

  MosConj = ref object
    elems: seq[MosDisj]

  MosDisj = ref object
    case isInput: bool
    of true:
      name: string
      polarity: bool
    else:
      elems: seq[MosConj]

  Cmos* = object
    conversion: Option[Conversion]
    pmos, nmos: MosConj


let conversionRules = newConvertAlgo(@[
  resolveBiImpl, resolveImpl,
  deMorganAnd, deMorganOr
])

proc genCmos*(expr: Expr): Cmos =

  proc genMos(expr: Expr, kind: MosKind): MosConj =
    let (opConj, opDisj) =
      case kind
      of mkPmos: (boAnd, boOr)
      of mkNmos: (boOr, boAnd)

    proc genDisj(expr: Expr): MosDisj

    proc genConj(expr: Expr): MosConj =
      MosConj(elems:
        if expr =: opConj:
          expr.operands.map(genDisj)
        else:
          @[genDisj(expr)]
      )

    proc genDisj(expr: Expr): MosDisj =
      func newInput(name: string, polarity: bool): MosDisj {.inline.} =
        MosDisj(isInput: true, name: name, polarity: polarity)

      if expr =: ekNot and expr.inner =: ekVar:
        newInput(expr.inner.name, true)
      elif expr =: ekVar:
        newInput(expr.name, false)

      else:
        MosDisj(isInput: false, elems:
          if expr =: opDisj:
            expr.operands.map(genConj)
          elif expr =: opConj:
            @[genConj(expr)]

          else: raise ValueError.newException("expected and, or, var")
        )

    genConj(expr)

  template genCmos(expr: Expr) =
    if expr.kind != ekVal:
      result.pmos = genMos(expr, mkPmos)
      result.nmos = genMos(expr, mkNmos)

  let conv = expr.convert(conversionRules)
  if len(conv.steps) == 0:
    genCmos expr
  else:
    result.conversion = some conv
    genCmos conv.res



type PositionedVNode = object
  node: VNode
  dist: tuple[left,right: int]

func positioned(node: VNode): PositionedVNode =
  result.node = node

func margins(left,right: int): VStyle =
  style(
    (marginLeft,  cstring &left  & "px"),
    (marginRight, cstring &right & "px")
  )

func connectionWithMargins(left,right: int): VNode =
  buildHtml(tdiv(class = "connection", style = margins(left, right)))

proc conjElems(elems: varargs[PositionedVNode]): PositionedVNode =
  for elem in elems:
    result.dist.left  = max(result.dist.left,  elem.dist.left )
    result.dist.right = max(result.dist.right, elem.dist.right)
  result.node =
    buildHtml(tdiv(class = "conj")):
      for elem in elems:
        tdiv(
          style = margins(
            result.dist.left  - elem.dist.left,
            result.dist.right - elem.dist.right
          )
        ): elem.node

proc disjElems(elems: varargs[PositionedVNode]): PositionedVNode =
  let left = elems[0].dist.left
  let right = elems[^1].dist.right
  let width = elems.foldl(a + b.dist.left + b.dist.right, 0)
  let centerDist = (width - left - right) div 2
  result.dist.left  = centerDist + left
  result.dist.right = centerDist + right
  result.node =
    buildHtml(tdiv(class = "disj")):
      connectionWithMargins(left, right)
      tdiv(class = "conjs"):
        for elem in elems: elem.node
      connectionWithMargins(left, right)

proc draw*(cmos: Cmos): VNode =

  const transistorWidth = 90

  proc draw(conj: MosConj, kind: MosKind): PositionedVNode =
  
    proc draw(disj: MosDisj): PositionedVNode

    proc draw(conj: MosConj): PositionedVNode =
      conjElems(conj.elems.map(draw))
      
    proc draw(disj: MosDisj): PositionedVNode =
      if disj.isInput:
        result.dist.left = transistorWidth
        result.node =
          buildHtml(tdiv(
            class = "transistor-container",
            style = style((width, cstring $transistorWidth & "px"))
          )):
            tdiv(class = "connection")
            tdiv(class = "transistor-with-invar"):
              draw(
                if disj.polarity: exprVar(disj.name)
                else:     exprNot(exprVar(disj.name))
              )
              tdiv(class = &"transistor {kind}")
            tdiv(class = "connection")

      else: result = disjElems(disj.elems.map(draw))

    if len(conj.elems) == 1: draw(conj.elems[0])
    else:                    draw(conj)

  proc voltElem(name: string): PositionedVNode =
    PositionedVNode(dist: (15, 15), node: buildHtml(tdiv(class = name)))

  buildHtml(tdiv(id = "cmos-container", class = "box")):
    if Some(@conv) ?= cmos.conversion:
      tdiv(class = "group"):
        tdiv(class = "title"): text "Conversion"
        tdiv(class = "content"): draw(conv)

    if cmos.nmos != nil and cmos.pmos != nil:
      let
        pmosElem = cmos.pmos.draw(mkPmos)
        nmosElem = cmos.nmos.draw(mkNmos)
        outElem = block:
          let right = max(pmosElem.dist.right, nmosElem.dist.right) + 20
          let node =
            buildHtml(tdiv(class = "out")):
              tdiv(style = style((width, cstring $right & "px")))
          PositionedVNode(dist: (0, right), node: node)

      conjElems(voltElem("vcc"), pmosElem, outElem, nmosElem, voltElem("gnd")).node