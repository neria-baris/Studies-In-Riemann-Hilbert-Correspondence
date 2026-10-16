#let _proof-env(supplement, body, alt-box) = block(breakable: true, spacing: 11.5pt, {
  emph[#supplement.]
  [ ] + body
  h(1fr)
  sym.space.nobreak
  if alt-box { $square.filled$ } else { $square.stroked$ }
})

/// Standard mathematical proof environment.
/// Inspired by the suggestions at
/// https://forum.typst.app/t/how-can-i-right-align-the-qed-symbol-after-a-proof/948/4
///
/// Note this still does occasionally have problems pushing the box to the
/// next line, which need to be fixed.
#let proof(body, supplement: none, alt-box: false) = {
  let name = "Proof" + if supplement != none { [ (] + supplement + [)] } else { [] }
  _proof-env(name, body, alt-box)
}

#let proof-sketch(body, supplement: none, alt-box: false) = {
  let name = "Proof sketch" + if supplement != none { [ (] + supplement + [)] } else { [] }
  _proof-env(name, body, alt-box)
}