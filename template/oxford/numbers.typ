/// The form of numbering used by headings.
#let headings = "1.1"

#let preamble(body) = {
  set heading(numbering: headings)
  body
}

/// Return the numbering pattern of the top-level heading governing `el-loc`.
/// This keeps cascade numbers in step when the document switches from numbered
/// chapters (`1.1`) to lettered appendices (`A.1`).
#let heading-numbering-at(el-loc) = {
  let roots = query(selector(heading.where(level: 1)).before(el-loc))
  if roots.len() == 0 or roots.last().numbering == none {
    headings
  } else {
    roots.last().numbering
  }
}

/// For a handling a very general form of double numbering. In particular,
/// the number of levels specified is taken from the heading numbering (or
/// as many as is available, whichever is smaller), followed by the number
/// given by `count`.
#let cascade(count, el-loc, levels: 1) = {
  let counter = counter(heading).at(el-loc)
  let heading-numbering = heading-numbering-at(el-loc)

  numbering(
    heading-numbering,
    ..counter.slice(0, count: calc.min(levels, counter.len()))
  )
  if type(heading-numbering) == type("") and heading-numbering.ends-with(".") [] else [.]
  numbering(
    "1",
    count,
  )
}
