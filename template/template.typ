// ============================================================================
//  template.typ  --  Oxford thesis design
//
//  Same commands, same names, same call signatures as before.  Nothing in
//  Thesis.typ, Macros.typ or any chapter file has to change.
//
//      #def(title: "...")[...]   #thm[...]   #proof[...]   #diagrambox[...]
//
//  What changed is the design.  The coloured thmbox boxes are gone; results
//  are now set the way an Oxford thesis sets them -- bold run-in heading,
//  italic statement -- on A4, in New Computer Modern, with chapter openings,
//  underlined section headings and cascade numbering.
//
//  The layout comes from the Oxford Typst thesis template, vendored unchanged
//  under oxford/.  This file is only the adapter between your command names
//  and that template.
// ============================================================================

#import "oxford/outlining.typ"
#import "oxford/numbers.typ"
#import "oxford/util.typ"
#import "oxford/callouts.typ"
#import "oxford/proof.typ" as proofs
#import "oxford/figures.typ"
// Aliased: the bare name `layout` would shadow Typst's own `layout()`.
#import "oxford/layout.typ" as oxlayout
#import "oxford/equations.typ"
#import "oxford/meta.typ"
#import "oxford/preamble.typ" as frontpages

// ---------------------------------------------------------------------
// 1. Re-exports from the Oxford template
// ---------------------------------------------------------------------

/// `#proof[...]`, `#proof()[...]` and `#proof(supplement: [of @thm:x])[...]`
/// all work.  The closing square is added automatically.
#let proof = proofs.proof
#let proofsketch = proofs.proof-sketch
/// Restates a numbered result without advancing the counter.
#let restate = callouts.restate

#let splitcases = util.splitcases
#let print = meta.print
#let digital = meta.digital
#let num-pages = meta.num-pages
#let preamble-page = frontpages.preamble-page

/// Switch all following top-level headings to appendices A, B, ... .
/// Use once in the master file, immediately before the first appendix:
///
///   #show: appendices
///   #include "chapters/appendices/homological-algebra.typ"
///
/// Results, figures, tables and equations inherit the letter automatically.
/// With `levels: 1` in `setup` they are A.1, A.2, ...; with `levels: 2`
/// they are A.1.1, A.1.2, ... within sections.
#let appendices(body) = {
  counter(heading).update(0)
  set heading(numbering: "A.1")
  show heading.where(level: 1): set heading(supplement: [Appendix])
  body
}

/// A q.e.d. square, in case a proof needs one by hand.
#let qed() = { h(1fr); sym.space.nobreak; $square.stroked$ }

// ---------------------------------------------------------------------
// 2. content → str  and  the automatic label
//    Copied verbatim from the previous version of this file: eleven
//    cross-references in the thesis point at labels generated from titles,
//    so the slugs have to come out byte-identical.
// ---------------------------------------------------------------------

#let to-str(c) = {
  if type(c) == str { c }
  else if type(c) != content { str(c) }
  else if c.has("text") { c.text }
  else if c.has("children") { c.children.map(to-str).join("") }
  else if c.has("body") { to-str(c.body) }
  else { "" }
}

// "Decomposition Theorem" → "thm:decomposition-theorem"
#let slug(prefix, title) = {
  let out = ""
  for ch in lower(to-str(title)).clusters() {
    if ch.match(regex("[a-z0-9]")) != none { out += ch }
    else if ch in (" ", "-", "_", ".") { out += "-" }
  }
  while out.contains("--") { out = out.replace("--", "-") }
  prefix + ":" + out.trim("-")
}

// ---------------------------------------------------------------------
// 3. The environment factory
//    Same signature as before:
//      #thm(title: "Decomposition Theorem")[...]  →  <thm:decomposition-theorem>
//      #thm[Decomposition Theorem][...]              same, positional
//      #thm(label: <thm:BBD>)[...]                   explicit label
//      #thm[...]                                     no title, no label
// ---------------------------------------------------------------------

#let env(name, prefix, numbered: true) = (title: none, label: auto, ..args) => {
  let pa = args.pos()
  let title = if pa.len() >= 2 { pa.at(0) } else { title }
  let body = if pa.len() > 0 { pa.at(-1) } else { [] }

  // Numbered results pass no `numbering:` argument at all: an explicit
  // argument would beat the `set` rule in oxford/callouts.typ, and the number
  // would come out as a running "Definition 7" instead of the cascade
  // "Definition 1.4".  Hence the spread rather than an if/else around two
  // `figure` calls -- one call means one source span, and so one "labelled
  // multiple times" warning instead of two.
  let b = figure(
    body,
    kind: "theorem",
    supplement: name,
    caption: title,
    ..(if numbered { (:) } else { (numbering: none) }),
  )

  let lab = if label != auto { label } else if title != none {
    std.label(slug(prefix, title))
  } else { none }

  if lab == none { b } else { [#b#lab] }
}

#let def = env("Definition", "def")
#let lem = env("Lemma", "lem")
#let claim = env("Claim", "clm")
#let prop = env("Proposition", "prop")
#let thm = env("Theorem", "thm")
#let cor = env("Corollary", "cor")

#let rmrk = env("Remark", "rem", numbered: false)
#let exmp = env("Example", "ex")
#let slogan = env("Slogan", "slg", numbered: false)

// ---------------------------------------------------------------------
// 4. A displayed diagram: centred, with a small caption above.
//    Not numbered and not referenceable, exactly as before.
// ---------------------------------------------------------------------

#let diagrambox(title: none, body) = block(
  width: 100%,
  above: 1.3em,
  below: 1.3em,
  breakable: false,
  {
    set align(center)
    if title != none {
      text(size: 9pt, style: "italic", title)
      v(0.5em, weak: true)
    }
    body
  },
)

// ---------------------------------------------------------------------
// 5. Oversized figures
//    A few diagrams were drawn for the old US-letter text block and are a
//    little wider than the A4 one.  Rather than edit the chapters, any
//    figure whose body overflows is scaled down to the text width.  The
//    caption is left at its normal size, which is why the figure is rebuilt
//    by hand here instead of scaling the whole thing.
// ---------------------------------------------------------------------

#let fit-oversized(it) = context layout(size => {
  let m = measure(it.body)
  if m.width > size.width and m.width > 0pt {
    let f = size.width / m.width
    block(width: 100%, breakable: false, {
      align(center, block(
        width: size.width,
        scale(it.body, x: f * 100%, y: f * 100%, reflow: true, origin: center + top),
      ))
      if it.caption != none {
        v(0.65em, weak: true)
        align(center, it.caption)
      }
    })
  } else { it }
})

// ---------------------------------------------------------------------
// 6. Compatibility shims
//    Nothing in the thesis uses these any more, but they are kept so that
//    an old `#show figure.where(kind: "thmbox"): thmbox-frame` line, or a
//    reference to the old palette, still compiles.
// ---------------------------------------------------------------------

#let thmbox-frame(it) = it

#let TurqBg = rgb("E0F2F1");       #let TurqFrame = rgb("00897B")
#let BlueLemmaBg = rgb("F3F9FF");  #let BlueLemmaFrame = rgb("64B5F6")
#let BlueClaimBg = rgb("E3F2FD");  #let BlueClaimFrame = rgb("1E88E5")
#let BlueThmBg = rgb("BBDEFB");    #let BlueThmFrame = rgb("0D47A1")
#let RemarkBg = rgb("FFF8E1");     #let RemarkFrame = rgb("F57F17")
#let ExampleBg = rgb("F8F8F8");    #let ExampleFrame = rgb("757575")
#let GrayDiagBg = rgb("FAFAFA");   #let GrayDiagFrame = rgb("EEEEEE")
#let SloganBg = rgb("F3E5F5");     #let SloganFrame = rgb("8E24AA")

#let palette = (
  "Definition":  (TurqBg,      TurqFrame),
  "Lemma":       (BlueLemmaBg, BlueLemmaFrame),
  "Claim":       (BlueClaimBg, BlueClaimFrame),
  "Proposition": (BlueClaimBg, BlueClaimFrame),
  "Theorem":     (BlueThmBg,   BlueThmFrame),
  "Corollary":   (BlueThmBg,   BlueThmFrame),
  "Remark":      (RemarkBg,    RemarkFrame),
  "Example":     (ExampleBg,   ExampleFrame),
  "Slogan":      (SloganBg,    SloganFrame),
  "Notation":    (RemarkBg,    RemarkFrame),
  "Note":        (RemarkBg,    RemarkFrame),
)

// ---------------------------------------------------------------------
// 7. The template.  Called from Thesis.typ as  #show: setup
//
//    `#show: setup` on its own still works and gives the full Oxford design
//    without a title page.  To get the title page, give it the details:
//
//      #show: setup.with(
//        title: "...",
//        author: "...",
//        college: "...",
//        degree: "MSc Mathematics and Foundations of Computer Science",
//        abstract: [...],
//        acknowledgements: [...],
//      )
// ---------------------------------------------------------------------

#let setup(
  title: none,
  author: none,
  college: none,
  degree: none,
  date: datetime.today(),
  /// Version number, for the PDF metadata.
  version: none,
  /// Title for the PDF metadata, when the real title contains content that
  /// does not serialise well as text.
  metadata-title: auto,
  /// `true` widens the inner margin and narrows the outer one, for a bound
  /// copy.  `false` centres the text block, for reading on screen.
  print: false,
  /// Figure kinds whose numbering cascades as chapter.n.
  figure-kinds: (image, table, raw),
  /// How many heading levels the numbering of results, figures and equations
  /// is nested under.  1 gives "Definition 2.7" and "Figure 2.3".
  levels: 1,
  abstract: none,
  acknowledgements: none,
  doc,
) = {
  let metadata-title = if metadata-title == auto { title } else { metadata-title }

  set document(
    title: metadata-title,
    author: if author != none { author } else { () },
    date: date,
    keywords: if version != none { ("v" + version,) } else { () },
  )

  // Text.  New Computer Modern ships with Typst, so nothing has to be
  // installed -- this replaces the Palatino Linotype that was never found.
  set text(font: "New Computer Modern", size: 12pt, lang: "en")
  show regex("--"): [–]
  set par(justify: true, leading: 0.8em)
  set enum(numbering: "1.a.i.")

  // A4, not US letter.
  set page(
    paper: "a4",
    margin: (
      y: 34.2mm,
      inside: if print { 28.8mm + 8.382mm } else { 28.8mm },
      outside: if print { 28.8mm - 2.032mm } else { 28.8mm },
    ),
    footer: oxlayout.footer(),
  )

  show: numbers.preamble

  show heading.where(level: 1): oxlayout.chapter.with()
  show heading.where(level: 2): oxlayout.section
  show heading: it => if it.level == 3 { oxlayout.subsection(it) } else { it }
  show heading: it => if it.level >= 4 { oxlayout.subsubsections(it) } else { it }

  show: equations.preamble.with(levels: levels)
  show: figures.preamble.with(kinds: figure-kinds, levels: levels)
  show: callouts.preamble.with(levels: levels)

  // Shrink any figure that is wider than the text block.  Restricted to the
  // ordinary kinds: results (kind "theorem") are laid out by callouts.typ.
  show figure.where(kind: image): fit-oversized
  show figure.where(kind: table): fit-oversized
  show figure.where(kind: raw): fit-oversized
  show: oxlayout.preamble

  // Empty set as a diameter, and the bullet markers of the Oxford template.
  show sym.emptyset: it => sym.diameter
  set list(marker: ([•], [◦], [–]))

  show: outlining.preamble

  // Metadata, readable from the command line or elsewhere in the document.
  context [
    #metadata(metadata-title) <meta:title>
    #metadata(print) <meta:print>
    #metadata(counter(page).final().first()) <meta:pages>
  ]

  if title != none and author != none and degree != none {
    oxlayout.title-page(title, author, college, date.year(), degree)
  }

  if abstract != none { frontpages.preamble-page([Abstract], abstract) }
  if acknowledgements != none {
    frontpages.preamble-page([Acknowledgements], acknowledgements)
  }

  doc
}
