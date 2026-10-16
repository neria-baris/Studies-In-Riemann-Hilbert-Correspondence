#import "numbers.typ"

#let preamble(body) = {
  show heading.where(level: 1): it => if it.numbering != none {
    set heading(supplement: [Chapter])
    it
  } else { it }

  // References to numbered top-level headings use the heading's own
  // supplement. This is "Chapter" in the main matter and "Appendix" after
  // `#show: appendices`.
  show ref: it => {
    if it.element != none and it.element.func() == heading and it.element.level == 1 and it.element.numbering != none {
      let supplement = if it.element.supplement == [Appendix] { [Appendix] } else { [Chapter] }
      if it.supplement != supplement {
        ref(it.target, form: it.form, supplement: supplement)
      } else { it }
    } else { it }
  }

  body
}

#let title-page(
  title,
  author,
  college,
  year,
  degree,
) = {
  align(center + horizon)[
    // #v(1fr)
    // *#text(24.88pt)[#title]*
    *#text(23pt)[#title]*
    #v(35mm)
    #image("oxlogo.svg", width: 60mm)
    #v(20mm)
    #set par(leading: 1.2em)
    #text(17.28pt)[#author] \
    #set text(14.4pt)
    #if college != none [#college \ ] else {} 
    University of Oxford
    #v(25mm)
    A thesis submitted for the degree of \
    #text(style: "italic")[#degree] \
    Trinity #year
    #pagebreak()
  ]
}

/// Show rule for level 1 headings to display as chapters.
#let chapter(it) = {
  set text(weight: "regular")
  set par(justify: false)

  pagebreak(weak: true)

  let head-size = 24.88pt

  // When numbering is set, top level headings are chapters
  if it.numbering != none {
    v(1cm)
    [
      #text(head-size)[#counter(heading).display(it.numbering) ]
      #h(0.25em)
      #text(head-size, baseline: 0pt)[#it.body]
    ]
    v(10em)
    counter(figure.where(kind: "theorem")).update(0)
  }
  else {
    text(head-size)[#it.body]
  }
}

#let footer() = context {
  let curr = here().page()
  let headings = query(selector(heading.where(level: 1)))

  // identifies if the current page is before any chapter
  let is-before-chapter = headings.filter(it => it.location().page() <= curr).len() == 0

  if not is-before-chapter {
    grid(
      columns: (1fr, auto, 1fr),
      [],
      [#curr],
      [],
    )
  }
}

// Second level headings have underlines
#let section(it) = {
  block(breakable: false)[
    #set text(size: 1.1em)
    #it
    #v(-0.6em)
    #line(length: 100%, stroke: 0.75pt)
    #v(0.5em)
  ]
}

// Headings below the second level
#let subsection(it) = {
  set text(size: 1.1em)
  it
}

#let subsubsections(it) = {
  it
}
