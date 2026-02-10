import std/[dom, sets, algorithm, options]
from karax/vdom import VNode
from karax/jdict import JSeq
import fusion/matching


template `?`*[T](val: Option[T]): untyped =
  if val.isSome: val.get
  else: return


func `$*`*(v: bool): string = $int(v)

func `$*`*(v: Option[bool]): string =
  if Some(@v) ?= v: $*v
  else            : "-"

func toBoolOption*(s: string): Option[bool] =
  case s
  of "1": some true
  of "0": some false
  else  : none bool

func toBoolOption*(c: char): Option[bool] =
  toBoolOption($c)
  

func concatIf*(base: string, cond: bool, s: string): string {.inline.} =
  result = base
  if cond: result.add ' ' & s


func cmpVars*(a,b: seq[string]): HashSet[string] =
  let a = a.sorted
  let b = b.sorted
  var ai, bi = 0
  while ai < len(a) and bi < len(b):
    if a[ai] == b[bi]:
      inc ai
      inc bi
    elif a[ai] < b[bi]:
      result.incl a[ai]
      inc ai
    else:
      result.incl b[bi]
      inc bi
  result.incl a[ai..^1].toHashSet
  result.incl b[bi..^1].toHashSet

func findDupAndEmpty*(x: seq[string]): HashSet[string] =
  result = initHashSet[string]()
  var found: seq[string]
  for x in x:
    if x == "": result.incl ""
    if x in found:
      result.incl x
    else:
      found.add x


func inputValue*(n: VNode): string {.inline.} =
  $n.dom.InputElement.value


func `&`*[T](a, b: JSeq[T]): JSeq[T] {.importcpp: "#.concat(#)".}