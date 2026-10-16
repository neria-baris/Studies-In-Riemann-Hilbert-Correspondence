#let preamble(body) = {

  show outline.entry: it => {
    if it.element.depth == 1 {
      let line = []

      line += link(
        it.element.location(),
        if it.element.numbering != none {
          let supplement = if it.element.supplement == [Appendix] { [Appendix] } else { [Chapter] }
          [#supplement #numbering(it.element.numbering, ..counter(heading).at(it.element.location())):]
        } + [ #it.body()]
      )

      line += box(width: 1fr, repeat[ ])
      line += link((page: it.element.location().page(), x: 0pt, y: 0pt), it.page())

      text(
        weight: "bold",
        box(inset: (top: 2em), line)
      )
    } else {
      it
    }
  }

  body
}
