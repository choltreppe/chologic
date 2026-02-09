import std/options


type JunctionKind* = enum jkDisj="disjunctive", jkConj="conjunctive"

func toJunctionKind*(s: string): Option[JunctionKind] =
  case s
  of $jkConj: some jkConj
  of $jkDisj: some jkDisj
  else: none JunctionKind

func `not`*(kind: JunctionKind): JunctionKind =
  case kind
  of jkConj: jkDisj
  of jkDisj: jkConj