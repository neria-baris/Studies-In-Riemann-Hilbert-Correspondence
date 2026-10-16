/// Display the provided content in the print version of the book only.
#let print(body) = context {
  if query(<meta:print>).first().value {
    body
  }
}

/// Display the provided content in the digital version of the book only.
#let digital(body) = context {
  if not query(<meta:print>).first().value {
    body
  }
}

/// Provides the total number of pages.
#let num-pages() = context {
  query(<meta:pages>).first().value
}
