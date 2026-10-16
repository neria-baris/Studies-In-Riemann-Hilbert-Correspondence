/// This module handles numbering and referencing of equations, as well as
/// various features of how equations look.

#import "util.typ"
#import "numbers.typ"

/// Simply include `#show equations.preamble` to correctly include numbering
/// code below
///
/// Note: This adds content to headings, and thus any show rules which don't
/// directly include the original heading itself should appear _before_ this
/// rule.
///
/// The `levels` argument determines how many levels of heading the equation
/// numbering is nested under.
#let preamble(body, levels: 1) = {
  // show math.equation: set block(breakable: true)
  // NOTE: equations are breakable because of:
  // https://github.com/typst/typst/pull/4226
  // however, currently that fix has the problem of duplicate numbering on each
  // side of the page break.
  // this can be fixed with https://typst.app/universe/package/equate/, although
  // it seems best to wait for https://github.com/typst/typst/issues/380

  // Use cascade numbering by default.
  show math.equation.where(block: true): set math.equation(numbering: count => context [
    (#numbers.cascade(count, here(), levels: levels))
  ])

  // Then turn off numbering on unlabelled equations. It is important that the
  // show rule for references sees that the equation is labelled in order for
  // the reference to be correct, and because of the ordering of applying show
  // rules, this is not always the case. For this reason, it is preferable to
  // have labelled be the default, and turn it off when appropriate. This is
  // also because setting the labelling on can be done with
  // `show: ... set: ...` whereas this needs a nested set rule.
  show math.equation.where(block: true): it => if not it.has("label") and it.numbering != none {
    math.equation(it.body, block: true, numbering: none)
    counter(math.equation).update(v => v - 1)
  } else { it }

  show ref: it => if it.element != none and it.element.func() == math.equation and it.element.block {
    let el = it.element;
    link(el.location())[
      (#numbers.cascade(
        ..counter(math.equation).at(el.location()),
        el.location(),
        levels: levels,
    ))]
  } else { it }

  show: util.reset-counter-at-heading.with(math.equation, levels)

  body
}
