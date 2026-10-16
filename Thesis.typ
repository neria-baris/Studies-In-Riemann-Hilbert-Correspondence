#import "template/template.typ": *
#import "template/macros.typ": *

#show: setup.with(
  title: "Studies In Riemann-Hilbert Correspondence",
  author: "Neria Baris",
  degree: "MSc Mathematics and Foundations of Computer Science",
  print: true,
   acknowledgements: [
    I would like to thank my supervisor, Professor Vidit Nanda, for his guidance throughout this project and for his wonderful ability to take the most complex ideas and motivate them step by step, so that their construction comes to seem simple and inevitable. In this work, I have tried to follow a similar approach, in order to create an introductory text accessible to (almost) anyone. It was a lovely fantasy, but sometimes one needs to admit his limits.

    I would also like to thank my parents, who supported me as this project grew to dangerous proportions and my sleeping hours dwindled.
  ],
)

#pagebreak(weak: true)

#align(center + horizon)[
  #block(width: 78%)[
    #align(left)[
      Und die Stärke des Fadens liegt nicht darin, daß irgendeine
      Faser durch seine ganze Länge läuft, sondern darin, daß viele
      Fasern einander übergreifen.

      #v(0.8em)

      #text(style: "italic")[
        The strength of a thread lies not in a single fibre running
        through its whole length, but in the overlapping of many fibres.
      ]

      #v(0.6em)

      #align(right)[
        — Ludwig Wittgenstein, _Philosophische Untersuchungen_, §67
      ]
    ]

    #v(4em)

    #align(right)[
      #text(font: "Alef", lang: "he", dir: rtl)[
        הַזֹּרְעִים בְּדִמְעָה בְּרִנָּה יִקְצֹרוּ׃ \
        הָלוֹךְ יֵלֵךְ וּבָכֹה נֹשֵׂא מֶשֶׁךְ־הַזָּרַע \
        בֹּא־יָבוֹא בְרִנָּה נֹשֵׂא אֲלֻמֹּתָיו׃
      ]
    ]

    #v(0.8em)

    #align(left)[
      #text(style: "italic")[
        Those who sow in tears shall reap with rejoicing.
        He goes forth weeping, bearing seed for sowing;
        he shall surely return with rejoicing, bearing his sheaves.
      ]

      #v(0.6em)

      #align(right)[
        — Psalms 126:5–6
      ]
    ]
  ]
]

#pagebreak()

// Front matter: contents.
#outline(title: [Contents], depth: 2, indent: auto)
#pagebreak()

// Top-level headings are chapters; references to them read "Chapter n".
#show heading.where(level: 1): set heading(supplement: [Chapter])
#show heading.where(level: 2): set heading(supplement: [Section])
#show heading.where(level: 3): set heading(supplement: [Section])
#show figure.where(kind: "thmbox"): set block(breakable: true)



#include "chapters/00-introduction.typ"
#pagebreak()

// The unnumbered introduction must not advance the chapter counter.
#counter(heading).update(0)

#include "chapters/01-sheaves.typ"
#pagebreak()
#include "chapters/02-sheaf-cohomology.typ"
#pagebreak()
#include "chapters/03-verdier-duality.typ"
#pagebreak()
#include "chapters/04-perverse-sheaves.typ"
#pagebreak()
#include "chapters/05-differential-equations-and-dmodules.typ"
#pagebreak()
#include "chapters/06-riemann-hilbert.typ"

// Appendices: everything after this switch is lettered A, B, ...
#show: appendices

#include "chapters/A-homological-algebra.typ"
#pagebreak()
#include "chapters/B-derived-categories.typ"

#bibliography("bib_thesis.yml")
