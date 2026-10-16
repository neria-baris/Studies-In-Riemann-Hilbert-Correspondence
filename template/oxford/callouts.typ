#import "numbers.typ"
#import "util.typ"

/// The function that displays the callout itself. This is not to be called
/// directly, as it doesn't handle automatic numbering or references.
#let _callout(supplement, body, number: none, caption: none) = [
  #strong({
    supplement
    number
    if caption != none [ (#caption) ]
  })
  #emph(body)
]

#let preamble(body, levels: 1) = {
  show figure.where(kind: "theorem"): it => align(left, {
    context {
      _callout(
        it.supplement,
        it.body,
        number: if it.numbering != none {
          [ ]
          it.counter.display(it.numbering)
        },
        caption: if it.caption != none { it.caption.body } else { none },
      )
    }
  })

  show figure.where(kind: "theorem"): set figure(
    numbering: count => context {
      numbers.cascade(count, here(), levels: levels)
    }
  )

  show ref: it => if it.element != none and it.element.func() == figure and it.element.kind == "theorem" {
    let el = it.element;
    link(el.location(),
      // If a supplement is given in the reference then it should be the primary text
      // with the additional text in parenthesis.
      // If just a link is desired, one can use the link function as #link(<label>, "text")
      if it.supplement == auto [#el.supplement #numbers.cascade(
          ..counter(figure.where(kind: el.kind)).at(el.location()),
          el.location(),
          levels: levels,
      )] else [#it.supplement (#el.supplement #numbers.cascade(
          ..counter(figure.where(kind: el.kind)).at(el.location()),
          el.location(),
          levels: levels,
      ))]
    )
  } else { it }

  show: util.reset-counter-at-heading.with(figure.where(kind: "theorem"), levels)

  body
}

#let callout-env(kind) = (title: none, body) => figure(
  body,
  kind: "theorem",
  supplement: upper(kind.at(0)) + kind.slice(1),
  caption: title,
)

// restates theorem with the same numbering as it originally had,
// and without incrementing the number
// TODO monitor this, and make sure it is correct, since it is new and experimental
#let restate(lab) = {

  context {
    let it = query(lab).first()

    _callout(
      it.supplement,
      it.body,
      number: if it.numbering != none {
        [ ]
        numbering(it.numbering, ..it.counter.at(it.location()))
      },
      caption: if it.caption != none { it.caption.body } else { none },
    )
  }
}
