include karax/prelude
import ./utils

proc satResultHtml*(sat: bool, what = ""): VNode =
  buildHtml(tdiv(class = "sat".concatIf(not sat, "notin"))):
    let sym = if sat: "∈"
              else:   "∉"
    text what & " " & sym & " SAT"