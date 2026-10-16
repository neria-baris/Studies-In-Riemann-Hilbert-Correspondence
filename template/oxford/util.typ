/// Display cases with conditional statements and the appropriate spacing.
#let splitcases(..cases, word: none, reverse: false) = {
  let extract(rem) = {
    cases.pos()
      .enumerate()
      .filter(((index, _)) => calc.rem(index, 2) == rem)
      .map(((_, element)) => element)
  }

  let cases = extract(0).zip(extract(1))
    .map(((value, condition)) => {
      $#value quad & #condition$
    })

  math.cases(reverse: reverse, ..cases)
}

/// If we have the numbering occur under level 2 for instance, then we want
/// the numbering to still work gracefully at the top level. We do this by
/// resetting the numbering at all higher levels. Since a show rule only
/// applies in scope, we need to do a bit of a special trick here to append
/// the rules to the body.
#let reset-counter-at-heading(key, up-to, body) = {
  show: body => {
    for level in range(1, up-to + 1) {
      body = {
        show heading.where(level: level): it => {
          counter(key).update(0)
          it
        }
        body
      }
    }
    body
  }

  body
}

