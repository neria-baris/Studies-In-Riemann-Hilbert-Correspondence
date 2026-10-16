# Studies In Riemann-Hilbert Correspondence

**Neria Baris** · MSc Mathematics and Foundations of Computer Science, University of Oxford · Trinity 2026
Supervisor: Professor Vidit Nanda

An introduction to the Riemann–Hilbert correspondence that tries to make each idea needed to reach it feel motivated, starting from the linear-algebra picture of a map, its kernel and its cokernel, and building up through sheaves, constructible complexes, Verdier duality and perverse sheaves to $\mathcal{D}$-modules and the correspondence itself.

**[Read the thesis (PDF, 204 pages)](Thesis.pdf)**

---

## How to read it

The compiled thesis is [`Thesis.pdf`](Thesis.pdf). GitHub shows it in the browser. For the clickable table of contents and cross-references, download it (the *Download raw file* button) and open it in a PDF reader. Every "Chapter n", "Section n.m", theorem and citation in the text is a link.

### Contents

| Part | Pages | What it does |
| --- | --- | --- |
| Introduction | 7 | Sets out the whole route on worked examples: solutions vs. obstructions, local solutions and gluing, monodromy on the punctured disc, singular points, and why complexes and duality are needed. |
| 1 Sheaves (and stratification) | 15 | Sheaves as the bookkeeping of local solutions; basic operations; stratifications and constructibility; cellular sheaves. |
| 2 Sheaf Cohomology and Constructible Complexes | 46 | Complexes of sheaves, sheaf cohomology, cellular calculations, local cohomology and costalks, derived Hom, constructible complexes. |
| 3 Verdier Duality | 61 | Duality that keeps track of location and support; computing duals; restriction, extension and recollement; support dimension. |
| 4 Perverse Sheaves | 78 | Re-centring degrees by the dimension of each stratum; the perverse $t$-structure; extension across a boundary; intersection complexes; simple perverse sheaves. |
| 5 Differential Equations and Their Solution | 99 | Local solution data; from systems of equations to $\mathcal{D}$-modules; the derived solution complex; characteristic geometry; extension and operations; regularity. |
| 6 The Riemann–Hilbert Correspondence | 126 | The de Rham complex; compatibility with the operations; full faithfulness and essential surjectivity; finite cellular models; the perverse heart; further directions. |
| Appendix A Basic Homological Algebra (Briefly) | 146 | Abelian categories, exact sequences and functors, chain complexes, projective and injective objects, derived functors, Tor and Ext. |
| Appendix B Derived Categories | 170 | The cone, the homotopy category and its triangulated structure, the derived category, injective models, derived functors, truncations. |
| Bibliography | 203 | |

### Suggested reading order

**1. Start with the Introduction.** It is the map of the thesis. It frames every later chapter as the answer to a problem raised by a concrete differential equation, so the rest makes more sense once you've read it.

**2. Decide whether you need the appendices.** The appendices are not afterthoughts. They are background, written so the thesis can be read without prior homological algebra. The Introduction calls them **Chapters −2 and −1** (with the Introduction as Chapter 0). Read them **as a single unit, A then B**.
- If kernels, cokernels, exact sequences, derived functors and the derived category are new to you, or rusty, read **Appendix A → Appendix B** before Chapter 1. The examples in them, starting from $0 \to \mathbb{Z} \xrightarrow{\cdot 2} \mathbb{Z} \to \mathbb{Z}/2 \to 0$, are the basis for the examples in the main chapters.
- If you are comfortable with derived categories, skip them and come back when a chapter points you there.

**3. Read Chapters 1 → 6 in order.** Each chapter depends on the ones before it:

```
            Introduction (Ch. 0)
                    │
   Appendix A ──► Appendix B        (background: Ch. −2, −1)
                    │
   1 Sheaves ──► 2 Sheaf cohomology ──► 3 Verdier duality ──► 4 Perverse sheaves
                                                                     │
                     5 D-modules and solution complexes ◄────────────┘
                                    │
                     6 The Riemann–Hilbert correspondence
```

Chapters 1–4 build the *solution side* (sheaves, constructible complexes, duality, perverse sheaves). Chapter 5 builds the *equation side* ($\mathcal{D}$-modules, holonomicity, regularity). Chapter 6 joins the two.

**A shortcut for the computational thread:** where a stratification has a compatible finite cell decomposition, constructible complexes reduce to finite linear algebra on cells. That thread runs through Section 1.5 (*Cellular sheaves*) and Section 2.4 (*Cellular calculations*), and Section 6.5 (*Finite cellular models of constructible complexes*) applies it to the de Rham and solution complexes. It is a good way in if you prefer computing examples to reading general theory.

Results are numbered within chapters (Definition 1.4, Theorem 3.2, …) and within appendices (Definition A.3, …).

---

## Building from source

The thesis is written in [Typst](https://typst.app) and compiles with **Typst 0.15.1**.

```sh
typst compile --root . --font-path fonts Thesis.typ Thesis.pdf
```

- `--root .` lets the chapter files import the template from `../template/`.
- `--font-path fonts` supplies **Alef**, the Hebrew font used for the epigraph (included under the SIL Open Font License, see `fonts/OFL.txt`). Everything else uses New Computer Modern and New Computer Modern Math, which ship with Typst.
- On first compile Typst downloads one package from the Typst package registry: `@preview/fletcher:0.5.8` (commutative diagrams), together with its dependencies `cetz:0.3.4` and `oxifmt:0.2.1`. An offline machine needs these in its local Typst package cache.

A full build takes about 20 seconds and produces 204 A4 pages. It gives one harmless warning ("content labelled multiple times"), which comes from theorem environments receiving both an automatic and a manual label. The manual label is the one used.

### Repository layout

```
Thesis.typ                 master file: front matter, chapter order, appendices, bibliography
Thesis.pdf                 compiled thesis
bib_thesis.yml             bibliography (Hayagriva format)
chapters/
  00-introduction.typ
  01-sheaves.typ
  02-sheaf-cohomology.typ
  03-verdier-duality.typ
  04-perverse-sheaves.typ
  05-differential-equations-and-dmodules.typ
  06-riemann-hilbert.typ
  A-homological-algebra.typ    Appendix A
  B-derived-categories.typ     Appendix B
  figures/                     raster figures used in Chapter 1
template/
  template.typ             theorem environments and page design (adapter onto the Oxford layout)
  macros.typ               mathematical notation shared by all chapters
  oxford/                  Oxford thesis layout (title page, headings, numbering)
fonts/                     Alef (Hebrew), SIL OFL
```

Compile `Thesis.typ`, not individual chapters. The chapters cite each other and the bibliography, so a chapter compiled on its own fails on unresolved references.
