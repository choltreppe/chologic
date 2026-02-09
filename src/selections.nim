import std/[dom, unicode]


type Selection* = object
  a*,b*: int

func newSelection*(i: int): Selection =
  Selection(a: i, b: i)

converter toSelection*(slice: Slice[int]): Selection =
  Selection(a: slice.a, b: slice.b + 1)

proc `+`*(selection: Selection, i: (int, int)): Selection =
  Selection(
    a: selection.a + i[0],
    b: selection.b + i[1]
  )

proc `+=`*(selection: var Selection, i: (int, int)) =
  selection.a += i[0]
  selection.b += i[1]

proc `+=`*(selection: var Selection, i: int) =
  selection += (i, i)

func `[]`*(s: string|cstring, selection: Selection): string =
  if selection.b <= selection.a: ""
  else: ($s)[selection.a ..< selection.b]

proc `[]=`*(cs: var cstring, selection: Selection, replace: string) =
  let s = $cs
  cs = cstring(s[0 ..< selection.a] & replace & s[selection.b .. ^1])


proc runeLen(s: string, section: Slice[int]): int =
  var i = section.a
  while i <= section.b:
    inc i:
      if uint(s[i]) <= 127: 1
      elif uint(s[i]) shr 5 == 0b110: 2
      elif uint(s[i]) shr 4 == 0b1110: 3
      elif uint(s[i]) shr 3 == 0b11110: 4
      elif uint(s[i]) shr 2 == 0b111110: 5
      elif uint(s[i]) shr 1 == 0b1111110: 6
      else: 1
    inc result

proc selection*(n: TextAreaElement|InputElement): Selection =
  let s = $n.value
  proc posOf(i: int): int =
    result = s.runeOffset(i)
    if result < 0:
      result = len(s)
  Selection(
    a: posOf(n.selectionStart),
    b: posOf(n.selectionEnd)
  )

proc `selection=`*(n: TextAreaElement|InputElement, selection: Selection) =
  let s = $n.value
  let start = runeLen(s, 0 ..< selection.a)
  n.selectionStart = start
  n.selectionEnd   = start + runeLen(s, selection.a ..< selection.b)

template withSelection*(n: TextAreaElement|InputElement, body: untyped) =
  block withSelectionBlock:
    var selection {.inject.} = n.selection
    body
    n.selection = selection