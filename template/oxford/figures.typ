/// This module is for the handling of other figures.

#import "util.typ"
#import "numbers.typ"

/// This should be called before any specific figure handling, such as what
/// is done with callouts.
#let preamble(levels: 1, kinds: (), body) = {
  let kinds = if type(kinds) == type("") { (kinds,) } else { kinds }

  show: body => {
    for kind in kinds {
      body = {
        show figure.where(kind: kind): set figure(numbering: count => context {
          numbers.cascade(count, here(), levels: levels)
        })
        show: util.reset-counter-at-heading.with(figure.where(kind: kind), levels)

        show ref: it => if it.element != none and it.element.func() == figure and it.element.kind == kind {
          let el = it.element;

          // this is the same procedure for references as was performed for callouts
          link(el.location(),
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

        body
      }
    }
    body
  }

  body
}
