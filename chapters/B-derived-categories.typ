#import "../template/template.typ": *
#import "../template/macros.typ": *

// Shared local corrections and chapter notation (see Thesis.typ).
#let cohsh(n, K) = $cal(H)^(#n) (#K)$
#let vee = $or$
#let pjl = math.attach($j_!$, tl: [p])
#let pjs = math.attach($j_*$, tl: [p])
#let gray8(x) = text(8pt, fill: luma(110))[#x]
#let IH = math.op("IH")
#let sSol = math.op($cal(S)o l$)

= Derived Categories<chap:derived-categories>
== Motivation<sec:motivation-derived>

@chap:homological-algebra culminated in the definition of derived functors in their classical form. However, the output is a graded family of cohomology objects. The complex from which they were obtained, and the way in which the different degrees are organized within it, are not retained as part of the output object. The connecting morphisms in long exact sequences require a separate construction, and there is no single object that represents the action of the functor in every degree and on which further derived constructions can be performed.

To understand what information is retained in a complex, we begin with a morphism between complexes and attach another complex to it. The cohomology of this complex records the kernels and cokernels of the maps induced on cohomology and measures their failure to be isomorphisms. To turn cohomology-preserving morphisms into isomorphisms, we proceed in two stages. First, we seek a category in which homotopy-equivalent resolutions become isomorphic, so that we can retain the complex obtained from a resolution. However, the map from an object to its resolution is generally a quasi-isomorphism and is not necessarily a homotopy equivalence. For the resolution to represent the object itself, we therefore pass to a category in which quasi-isomorphisms become invertible. This passage will require an explicit description of the morphisms in the new category and a way to identify the morphisms that we seek to invert.

The resulting category allows us to replace the family $R^n F(A)_n$ by a single object $R F(A)$. Passing to a single object effectively gives us a new derived functor, $R F$, that is defined without taking cohomology; taking its cohomology recovers the classical derived functors. Under suitable conditions, further derived constructions can be applied to these objects and functors can be composed. This category is not abelian, but one can isolate within it objects that form an abelian subcategory equivalent to the original category.

Throughout, $cA$ is an abelian category and $Cx(cA)$ denotes its category of cohomological complexes. Thus $d_A^n : A^n -> A^(n + 1)$ and
$ H^n (A^bullet) = Ker(d_A^n) \/ im(d_A^(n - 1)). $
Morphisms of complexes, cochain homotopies, acyclic complexes, and quasi-isomorphisms were defined in @sec:cohomology. We write $Cx^+(cA)$, $Cx^-(cA)$, and $Cx^b(cA)$ for complexes that vanish in all sufficiently negative degrees, all sufficiently positive degrees, and all but finitely many degrees, respectively. We use the analogous notation for homotopy and derived categories. No boundedness hypothesis is imposed on finite direct sums, shifts, or cones; assumptions needed for resolutions or totalizations will be stated where they are used.

Finally, an object $X in cA$ is often to be regarded as a complex with $X$ in a single degree $n$ and zero elsewhere. We write $placed(X, n)$ for that complex, the degree appearing as a bracketed subscript. This is only a shorthand for a shift of $X$ placed in degree $0$, but writing it as a shift forces the reader to negate an index in order to read off a position, and positions are what the truncation and $t$-structure arguments are about.


== The Cone<sec:cone>

To begin, let us eye the following morphism in *$"Ab"$* - $ u:ZZ \/4ZZ->ZZ \/4ZZ, quad u(x)=2x $ This morphism is neither a monomorphism nor an epimorphism. Its kernel, image, and cokernel are all isomorphic to $ZZ \/ 2 ZZ$, but this information is divided between two short exact sequences:
$ 0 -> Ker(u) -> ZZ \/ 4 ZZ -> im(u) -> 0, $
$ 0 -> im(u) -> ZZ \/ 4 ZZ -> coker(u) -> 0. $
The mapping cone will replace these two pieces of information by the cohomology of one complex attached directly to $u$.


An immediate observation is that although we can analyze every morphism in *$"Ab"$*, with two short exact sequences for that. Degreewise kernels and cokernels of a morphism of complexes are not invariant under homotopy: replacing $f$ by a homotopic $g$ can change $Ker(f^n)$ and $coker(f^n)$ altogether, so neither can descend to the homotopy category, and neither computes anything a derived construction is allowed to depend on. The cone, by contrast, will be shown in @prop:homotopic-morphisms-have-isomorphic-cones to depend on $f$ only through its homotopy class. 

The total complex (@def:total-complex) construction of @chap:homological-algebra already explains how several graded directions can be combined into one complex. For the cone the source complex must first be shifted by one degree.

#def(title: "Shift of a complex")[
Let $A^bullet in Cx(cA)$ and $r in ZZ$. The shift $shift(A,r)$ is the complex defined by
$ shift(A,r)^n = A^(n+r), quad d_(shift(A,r))^n = (-1)^r d_A^(n+r). $
For a morphism $f colon A^bullet -> B^bullet$, define
$shift(f,r)^n = f^(n+r). $
]


#prop(title: "Cohomology of a shift")[
For every $A^bullet in Cx(cA)$ and every $n,r in ZZ$, there is a natural isomorphism
$ H^n (shift(A,r)) iso H^(n+r)(A). $
]



#proof()[Multiplying a differential by $(-1)^r$ changes neither its kernel nor its image.
]

// #proof()[
// In degree $n$ the complex $shift(A,r)$ has the object $A^(n + r)$ and the differentials $(-1)^r d_A^(n + r - 1)$ and $(-1)^r d_A^(n + r)$. A global sign changes neither a kernel nor an image, so the subquotient computed at $n$ is the one computed at $n + r$ in $A^bullet$.
// ]

In particular $shift(-,1)$ moves an object concentrated in degree $0$ to degree $-1$: the shift lowers the degree in which a complex sits by one, in the direction opposite to the one the notation may suggest.

Let $f : A^bullet -> B^bullet$ be a morphism of complexes. In degree $n$, the cone places $B^n$ beside $A^(n + 1)$. The morphism $f^(n + 1)$ is then inserted as an off-diagonal component of the new differential:

#figure(
  diagram(
    spacing: 1.5cm,
    node((0, 0), $B^n$),
    node((2, 0), $B^(n + 1)$),
    node((0, 1.2), $A^(n + 1)$),
    node((2, 1.2), $A^(n + 2)$),
    edge((0, 0), (2, 0), "->", label: $d_B^n$),
    edge((0, 1.2), (2, 1.2), "->", label: $-d_A^(n + 1)$),
    edge((0, 1.2), (2, 0), "->", label: $f^(n + 1)$, label-side: left),
  ),
  caption: [The components of the cone differential from degree $n$ to degree $n + 1$.]
)

//check

Return to $f colon ZZ \/ 4 ZZ ->^2 ZZ \/ 4 ZZ$, with both groups regarded as complexes concentrated in degree $0$. The shifted complex $shift(ZZ \/ 4 ZZ, 1)$ is concentrated in degree $-1$, so the graded object $ZZ \/ 4 ZZ ds shift(ZZ \/ 4 ZZ, 1)$ has one copy of $ZZ \/ 4 ZZ$ in degree $-1$ and another in degree $0$.
#def(title: "Mapping cone")[
The mapping cone of $f : A^bullet -> B^bullet$ is the complex $cone(f)$ defined by
$ cone(f)^n := B^n ds A^(n + 1), $
with differential
$ d_(cone(f))^n := mat(d_B^n, f^(n + 1); 0, -d_A^(n + 1)). $
Equivalently,
$ d_(cone(f))^n (b,a) = (d_B^n (b) + f^(n + 1) (a),-d_A^(n + 1) (a)). $
The canonical maps are
$ i_f : B^bullet -> cone(f), quad i_f (b) = (b,0), $
$ p_f : cone(f) -> shift(A,1), quad p_f (b,a) = a. $
]
<def:mapping-cone>


// The two components of this formula have distinct roles. The second component, $-d_A^(n+1)(a)$, is simply the differential on the shifted copy of $A^bullet$. The first component contains both $d_B^n (b)$ and $f^(n+1)(a)$. The latter term is exactly what inserts the morphism $f$ into the new complex. 

The matrix formula displays why the sign and the off-diagonal entry are necessary.
$ d_(cone(f))^(n + 1) compose d_(cone(f))^n = mat(d_B^2, d_B f - f d_A; 0, d_A^2) = 0. $
Thus the condition that $f$ commute with the differentials is what makes the cone differential square to zero.

For the $f colon ZZ \/ 4 ZZ ->^2 ZZ \/ 4 ZZ$, the source and target have zero differentials, so the cone is the two-term complex
$ dots.c -> 0 -> ZZ \/ 4 ZZ ->^2 ZZ \/ 4 ZZ -> 0 -> dots.c, $
concentrated in degrees $-1$ and $0$. 
The original morphism has become the differential of one complex.


// #exmp(title: "The two-term complex associated with an automorphism")[
// Let $V$ be a finite-dimensional vector space and let $T : V -> V$ be an automorphism. The endomorphism $T - id_V$ gives the two-term complex
// $ K_T := [V ->^(T - id_V) V] $
// concentrated in degrees $0$ and $1$. Equivalently, $K_T iso shift(cone(T - id_V),-1)$. Its cohomology is
// $ H^0(K_T) iso Ker(T - id_V), quad H^1(K_T) iso coker(T - id_V). $
// The first space consists of the vectors fixed by $T$; the second measures the obstruction to solving $(T - id_V) v = w$. In the next chapter, this same complex will compute the cohomology of a local system on the circle with monodromy $T$; the computation is @Dimca2004[Example 2.5.7], where $H^0$ and $H^1$ come out as exactly the two objects above.
// ]
// <exmp:two-term-shifted-cone>

// #text(fill: red)[TODO: sortenes, and change location.
// ]

// #text(fill: red)[Why does the cone project onto $shift(A,1)$ rather than onto $A^bullet$ itself? Because of the isomorphism $H^n (shift(A,1)) iso H^(n+1)(A)$, (@prop:cohomology-of-a-shift) a morphism *into* $shift(A,1)$ induces maps on cohomology that raise degree by one. The projection $p_f$ is therefore precisely the kind of morphism that can carry connecting homomorphisms: it is how the maps $H^n -> H^(n+1)$ of a long exact sequence will eventually be represented by a single morphism of complexes. This is the structural reason for the shift in the fourth vertex of every triangle in this chapter. ]


// #rmrk(title: "The cone as a two-column totalization")[
// The cone may also be viewed as the totalization of the two-column diagram determined by $f$. This interpretation explains why $B^n$ and $A^(n+1)$ occur in the same degree. General double complexes and their totalizations will be introduced later, when they are required for the construction of resolutions of complexes.
// ]

== The cone triangle<sec:cone-triangle>
In order to establish a full replacement for short exact sequences, we need to show that we could use those cones in order to reproduce long exact sequences. 

Note that  the cone diagram $ A^bullet ->^f B^bullet ->^(i_f) underbrace(cone(f),B^bullet ds shift(A,1))  ->^(p_f) shift(A,1) $ form a degreewise-split short exact sequence of complexes:
$ 0 -> B^bullet ->^(i_f) cone(f) ->^(p_f) shift(A,1) -> 0. $

// For $ZZ \/ 4 ZZ ->^2 ZZ \/ 4 ZZ$, its cone always belongs to the degreewise-split short exact sequence:
// $ 0 -> ZZ \/ 4 ZZ[0] -> cone(2) -> shift(ZZ \/ 4 ZZ[0],1) -> 0. $
// The price is that the third term is no longer an ordinary group concentrated in degree $0$, but a complex carrying information in two adjacent degrees.

Applying the long exact cohomology sequence (@thm:long-exact-sequence-in-homology) to our short exact sequence, and using the identification $H^n (shift(A,1)) iso H^(n+1)(A)$, gives one sequence containing all cohomological defects of $f$.

#thm(title: "Long exact cohomology sequence of a cone")[
For every morphism $f : A^bullet -> B^bullet$, there is a natural long exact sequence
$ dots.c -> H^n (A) ->^(H^n (f)) H^n (B) -> H^n (cone(f)) -> H^(n + 1)(A) ->^(H^(n + 1)(f)) H^(n + 1)(B) -> dots.c. $
]
<lem:cone-les>

See @Goresky2026[Lemma A.9], @Dimca2004[Prop. 1.1.21], and @KashiwaraSchapira1990[Prop. I.3.6].

The final map $p_f : cone(f) -> shift(A,1)$ explains the shift in the fourth vertex of the later triangle. Since its target is shifted, the induced cohomology maps raise degree by one. The connecting morphisms are therefore represented by one degree-zero morphism of complexes.

For multiplication by $2$, the relevant part of the long exact sequence is
$ 0 -> H^(-1)(cone(2)) -> ZZ \/ 4 ZZ ->^2 ZZ \/ 4 ZZ -> H^0(cone(2)) -> 0. $
Hence
$ H^(-1)(cone(2)) iso Ker(2) iso ZZ \/ 2 ZZ, $
$ H^0(cone(2)) iso coker(2) iso ZZ \/ 2 ZZ. $
The kernel and cokernel have not disappeared; the cone has reorganized them as adjacent cohomology objects of one complex.

// The pattern is general. The two short exact sequences above may be spliced into the five-term exact sequence $ 0 -> Ker(f) -> A ->^f B -> coker(f) -> 0 $. When $A$ and $B$ are regarded as complexes concentrated in degree $0$, the long exact sequence of the cone reduces precisely to $ 0 -> H^(-1)(cone(f)) -> A ->^f B -> H^0(cone(f)) -> 0 $. Hence $ H^(-1)(cone(f)) iso Ker(f), quad "and" H^0(cone(f)) iso coker(f) $

The long exact sequence yields the following statement.
#prop(title: "Cohomology of the cone")[
For every morphism $f colon A^bullet -> B^bullet$ and every $n in ZZ$, there is a natural short exact sequence
$ 0 -> coker(H^n (f)) -> H^n (cone(f)) -> Ker(H^(n+1)(f)) -> 0. $
]<prop:cohomology-of-cone>


The proposition converts the two failures of $H^n (f)$ into the cohomology of one object. In particular:

#cor(title: "Quasi-isomorphisms and acyclic cones")[
A morphism $f : A^bullet -> B^bullet$ is a quasi-isomorphism if and only if $cone(f)$ is acyclic.
]
<cor:cone-quasi-isomorphism>

#proof()[
If every $H^n (f)$ is an isomorphism, both outer terms in @prop:cohomology-of-cone vanish. Conversely, if the cone is acyclic, the same short exact sequence shows that every $H^n (f)$ is both monic and epic.
]
// Thus, $H^n (cone(f))$ simultaneously records the failure of $H^n (f)$ to be surjective and the failure of $H^(n+1)(f)$ to be injective. #text(fill: red)[The cone is therefore acyclic precisely when neither failure occurs in any degree.]

// #prop(title: "The cone recovers kernels and cokernels")[
// Let $f colon A^bullet -> B^bullet$ be a morphism of complexes.

// If $f$ is a monomorphism in every degree, the morphism
// $ q_f colon cone(f) -> coker(f), quad q_f^n (b,a)=[b], $
// is a quasi-isomorphism.

// If $f$ is an epimorphism in every degree, the morphism
// $ j_f colon shift(Ker(f),1) -> cone(f), quad j_f^n (a)=(0,a), $
// is a quasi-isomorphism.
// ]

// _Proof_. In the monomorphism case, compare the long exact sequence of the cone with the long exact sequence associated with
// $ 0 -> A^bullet ->^f B^bullet -> coker(f) -> 0. $
// The induced morphism $q_f$ is an isomorphism on cohomology. The epimorphism case follows dually from
// $ 0 -> Ker(f) -> A^bullet ->^f B^bullet -> 0. $

// In particular, if $ 0 -> A^bullet ->^i B^bullet ->^q C^bullet -> 0 $
// is a short exact sequence of complexes, then the canonical morphism
// $ cone(i) -> C^bullet, quad (b,a) |-> q(b) $ is a quasi-isomorphism. We will return to this observation after constructing the derived category.


// In particular, if $0 -> A^bullet ->^i B^bullet ->^q C^bullet -> 0$ is a short exact sequence of complexes, then the canonical morphism $ cone(i) -> C^bullet, quad (b,a) |-> q(b) $
// is a quasi-isomorphism. We will return to this observation after constructing the derived category: there, it will turn the cone triangle of $i$ into a distinguished triangle $A -> B -> C -> shift(A,1)$, so that every short exact sequence of complexes gives rise to a triangle.

// The short exact sequence just established has a further consequence, which will be decisive throughout the chapter: it converts a property of a morphism into a property of a single object.

// #prop(title: "The cone detects quasi-isomorphisms")[
// A morphism $f colon A^bullet -> B^bullet$ is a quasi-isomorphism if and only if $cone(f)$ is acyclic.
// ]

// Proof. If $f$ is a quasi-isomorphism, then both the cokernel of $H^n (f)$ and the kernel of $H^(n+1)(f)$ vanish for every $n$, so the preceding short exact sequence gives
// $ H^n (cone(f)) = 0. $
// Conversely, if $cone(f)$ is acyclic, exactness of the cone long exact sequence implies that each $H^n (f)$ is both a monomorphism and an epimorphism, hence an isomorphism.

// #cor(title: "Acyclity and quasi-isomorphism")[
//   The cone therefore converts a property of a morphism into a property of a single object:
//   $ f " is a quasi-isomorphism"  <==> cone(f)  "is acyclic". $
// ]<cor:cone-quasi-isomorphism>


A short exact sequence of complexes also fits naturally into the cone construction. If
$ 0 -> A^bullet ->^i B^bullet ->^q C^bullet -> 0 $
is exact, then
$ phi : cone(i) -> C^bullet, quad phi(b,a) = q(b) $
is a morphism of complexes and a quasi-isomorphism. Thus $cone(i)$ is a canonical complex attached to the injection, while $C^bullet$ is a quasi-isomorphic replacement for it.Thus the cone triangle $A^bullet -> B^bullet -> op("Cone")(i) -> A^bullet[1]$ has a third term quasi-isomorphic to $C^bullet$.



// #rmrk(title: "Relation with the Snake Lemma")[
// The long exact sequence above is still obtained by the classical abelian mechanism: the degreewise-split short exact sequence $0 -> B^bullet -> cone(f) -> shift(A,1) -> 0$ produces connecting homomorphisms by the long exact sequence theorem, whose proof rests on the Snake Lemma. The new feature is not a different diagram chase but a different organization of its output. The Snake Lemma constructs a separate connecting homomorphism $H^n (shift(A,1)) -> H^(n+1)(B)$ in every degree; the cone triangle packages the source of all these maps into one diagram of complexes. This is the last time in the chapter that the Snake Lemma is applied directly — a point we return to in the closing remark of @sec:derived-category.
// ]




== Homotopy Category<sec:homotopy-category>

The cone construction answers the first guiding question. We now address the non-uniqueness of resolutions. Given a morphism $u : A -> B$ and injective resolutions of $A$ and $B$, the Comparison Theorem produces a morphism between the resolutions extending $u$, but that lift is unique only up to cochain homotopy. Literal chain maps therefore distinguish choices that derived constructions must regard as equivalent.

Recall that $f,g : A^bullet -> B^bullet$ are cochain-homotopic if there is a family $h^n : A^n -> B^(n-1)$ such that
$ f - g = d_B compose h + h compose d_A $
We write $f tilde g$. A morphism homotopic to zero is called *null-homotopic*.

Homotopies add, so the relation $tilde$ is compatible with addition. It is also compatible with composition: if $f-g=d_B h+h d_A$, then for cochain maps $u:A' -> A$ and $v:B -> B'$ we have $v f u-v g u=d_(B')(v h u)+(v h u)d_(A')$. Composition therefore descends to homotopy classes.



// #def(title: "Null-homotopic morphisms")[
// For complexes $A^bullet,B^bullet in Cx(cA)$, let
// $ cal(N)(A,B) = {f in Hom_(Cx(cA))(A,B) mid f tilde 0}. $
// ]


#def(title: "Homotopy category")[
The homotopy category $Kcat(cA)$ has the same objects as $Cx(cA)$. Its morphisms are homotopy classes of morphisms of complexes
$ Hom_(Kcat(cA))(A^bullet,B^bullet) := Hom_(Cx(cA))(A^bullet,B^bullet) slash tilde $
The class of $f$ is denoted $[f]$, as usual.
]
<def:homotopy-category>



The passage $Cx(cA) -> Kcat(cA)$ changes only the morphisms. Keeps the complexes unchanged and replaces cochain maps by their homotopy classes. Addition and shifts descend to the quotient, as does cohomology, since homotopic maps induce the same maps on cohomology by @lem:chain-homotopy-and-homology and its cochain version in @sec:cohomology.


#prop(title: "Homotopy equivalences and contractible complexes")[
A morphism of complexes is a homotopy equivalence if and only if its homotopy class is an isomorphism in $Kcat(cA)$. Consequently, a complex $C^bullet$ is contractible if and only if it is isomorphic to the zero object in $Kcat(cA)$.
]<prop:homotopy-equivalence-contractible>

#proof()[
By @def:homotopy-category, $[f]$ is invertible when there is $g$ with $g f tilde id$ and $f g tilde id$, which is the definition of a homotopy equivalence. Applying this to $M^bullet -> 0$: the composites are $0 tilde id_(M^bullet)$ and $id_0$, and the first says precisely that $id_(M^bullet)$ is null-homotopic, that is, that $M^bullet$ is contractible.
]

For example, the two-term complex $dots.c -> 0 -> M ->^id M -> 0 -> dots.c$ is generally not the zero complex in $Cx(cA)$, but it is contractible and hence isomorphic to zero in $Kcat(cA)$. The homotopy category therefore cleanly removes parts of a complex that can be contracted without changing its cohomology.


More fundamentally, the homotopy category removes the non-uniqueness that appeared in the construction of resolutions.
//calso make sure that the comparison-theore has uniquness clause)
#cor(title: "Uniqueness of injective resolutions in the homotopy category")[
Let
$A->I^bullet,  quad  A->J^bullet$
be injective resolutions. There is a unique isomorphism
$
  I^bullet->J^bullet
$
in $Kcat^+(cA)$ represented by a comparison morphism extending $id_A$.
]<cor:injective-resolutions-homotopy-category>

// #proof()[
// The dual form of the Comparison Theorem (@thm:the-comparison-theorem), applied to $id_A$, gives morphisms of complexes
// $u colon I^bullet -> J^bullet,
//   quad
//   v colon J^bullet -> I^bullet
// $
// satisfying
// $
//   u^0 compose eta_I = eta_J,
//   quad
//   v^0 compose eta_J = eta_I.
// $

// Both $v compose u$ and $id_(I^bullet)$ extend $id_A$. By the uniqueness clause of the Comparison Theorem,
// $
//   v compose u tilde id_(I^bullet), quad "and"

//   u compose v tilde id_(J^bullet)
// $
// Hence $[u]$ and $[v]$ are inverse isomorphisms in $Kcat^+(cA)$.

// Finally, any two comparison morphisms $I^bullet -> J^bullet$ extending $id_A$ are homotopic, again by the uniqueness clause. Therefore they determine the same morphism in the homotopy category.
// ]
#proof()[
The Comparison Theorem gives maps $I^bullet -> J^bullet$ and $J^bullet -> I^bullet$ extending $id_A$. Their composites are homotopic to the relevant identity maps, and any two comparison morphisms extending $id_A$ are homotopic.
]

The cone was defined for a morphism of complexes, but $Kcat(cA)$ has only homotopy classes. To formulate cone diagrams intrinsically in $Kcat(cA)$, we must verify that the cone does not depend on the chosen chain-level representative.

#prop(title: "Homotopic morphisms have isomorphic cones")[
If $f,g : A^bullet -> B^bullet$ are homotopic, then $cone(f)$ and $cone(g)$ are isomorphic as complexes.
]
<prop:homotopic-morphisms-have-isomorphic-cones>

Compare @Dimca2004[Lemma 1.1.20(iii)].

#proof()[
Choose $h$ with $f - g = d_B h + h d_A$. The block matrix
$ Phi_h^n := mat(id_(B^n),h^(n + 1);0,id_(A^(n + 1))) $
defines a chain isomorphism $cone(f) -> cone(g)$, with inverse $Phi_(-h)$.
]

The resulting isomorphism depends on the chosen homotopy. Consequently, the cone of a morphism in $Kcat(cA)$ is defined only up to noncanonical isomorphism.

For a strictly commutative square of chain maps
$ b compose f=f' compose a $
in $Cx(cA)$, the block map
$ mat(b,0;0,a):cone(f)->cone(f') $
is canonical. A square that commutes in $Kcat(cA)$ supplies only a homotopy between $b f$ and $f'a$. Choosing such a homotopy gives the required off-diagonal entry in a map between the cones, and different choices can give different maps.

Consequently, a morphism in $Kcat(cA)$ has a cone determined up to isomorphism, while a functorial choice of cone would require additional data. see @Dimca2004[Remark 1.2.7] and @KashiwaraSchapira1990[Lemma I.4.2].

The homotopy category solves the correct uniqueness problem, but it does not yet invert every quasi-isomorphism.

#lem(title: "Split exact sequences and contractible complexes")[
Let
$ 0 -> A ->^i B ->^p C -> 0 $
be a short exact sequence in $cA$, and let
$ E^bullet := [A ->^i B ->^p C] $
be the associated complex, concentrated in degrees $-1,0,1$. Then $E^bullet$ is contractible if and only if the short exact sequence splits.
]
<lem:split-exact-contractible>

This is the splitting lemma in complex form; see @Weibel1994[§1.4] and @splitting-lemma-doc.

#proof()[
If $E^bullet$ is contractible, a contracting homotopy gives maps $r : B -> A$ and $s : C -> B$ with $r i = id_A$ and $p s = id_C$, so the sequence splits. Conversely, a splitting gives maps satisfying $i r + s p = id_B$; these maps form a contracting homotopy of $E^bullet$.
]
#exmp(title: "An acyclic complex that is not contractible")[
Consider the extension of @ex:nonsplit-z4-extension
$ 0 -> ZZ \/ 2 ZZ ->^iota ZZ \/ 4 ZZ ->^pi ZZ \/ 2 ZZ -> 0 $
 The associated complex
$ E^bullet = [ZZ \/ 2 ZZ ->^iota ZZ \/ 4 ZZ ->^pi ZZ \/ 2 ZZ] $
is acyclic because the sequence is exact. It is not contractible by @lem:split-exact-contractible, since the short exact sequence does not split. Hence $E^bullet$ is nonzero in $Kcat(Ab)$ even though $E^bullet -> 0$ is a quasi-isomorphism. Compare @Goresky2026[Appendix A.18], where the same two maps appear as an injective resolution over $ZZ \/ 4 ZZ$.
]
<exmp:acyclic-noncontractible>

This is the exact gap between $Kcat(cA)$ and $D(cA)$. The homotopy category kills contractible complexes but not all acyclic complexes.

// Every homotopy equivalence is a quasi-isomorphism, since an isomorphism in $Kcat(cA)$ is sent by each $H^n$ to an isomorphism in $cA$. The converse, however, is false. This is the precise reason that the homotopy category is not yet the derived category. We will use the following lemma - 
// #lem(title: "Split exact sequences and contractible complexes")[
// Let
// $  0 -> A ->^i B ->^p C -> 0
// $
// be a short exact sequence in $cA$, and let
// $ E^bullet :=
  
//     dots.c -> 0 -> A ->^i B ->^p C -> 0 -> dots.c
  
// $
// be the associated complex, concentrated in degrees $-1,0,1$.

// Then $E^bullet$ is contractible if and only if the short exact sequence splits.
// ]
// //maybe more simple one or find refernce/explanation
// #proof()[
// Suppose first that $E^bullet$ is contractible. Then there are morphisms
// $
//   h^0:B->A,
//   quad
//   h^1:C->B
// $
// such that
// $
//   id_E=d_E compose h+h compose d_E.
// $
// In degrees $-1$ and $1$, this identity gives
// $
//   h^0 compose i=id_A,
//   quad
//   p compose h^1=id_C.
// $
// Thus $h^0$ is a retraction of $i$ and $h^1$ is a section of $p$. By the Splitting Lemma (@lem:splitting-lemma), the short exact sequence splits.

// Conversely, suppose that the sequence splits. By the Splitting Lemma, there exist a retraction
// $r:B->A
// $
// and a section
// $s:C->B
// $
// such that
// $
//   r compose i=id_A,
//   quad
//   p compose s=id_C,
//   quad
//   i compose r+s compose p=id_B.
// $
// Set
// $h^0:=r,
//   quad
//   h^1:=s,
// $
// and let all other components of $h$ be zero. The three displayed identities give $d_E compose h+h compose d_E=id_E.
// $
// Hence $E^bullet$ is contractible.
// ]

// Now, we can analyze the exact sequence
// $ 0 -> ZZ \/ 2 ZZ ->^iota ZZ \/ 4 ZZ ->^pi ZZ \/ 2 ZZ -> 0, $
// where $iota([x]) = [2x]$ and $pi([x]) = [x] mod 2$.
// The associated complex $E^bullet$ is acyclic because the sequence is exact; consequently, the unique morphism $E^bullet -> 0$ is a quasi-isomorphism (@). However, it does not contractible since the sequence does not split and hence it does not vanish in $Kcat(Ab)$.

// Thus $Kcat(cA)$ makes all homotopy equivalences invertible, but not all quasi-isomorphisms. This requires the additional localization that yields the derived category.

// Finally, before returning to cone diagrams in the homotopy category, we verify that the isomorphism class of a cone depends only on the homotopy class of the morphism.

// #text(fill: red)[TODO: consider
// ]
// #prop(title: "Homotopic morphisms have isomorphic cones")[
// Let $f,g colon A^bullet -> B^bullet$ be homotopic morphisms. Then $cone(f)$ and $cone(g)$ are isomorphic as complexes.
// ]
// //notation - TODO: check
// #proof()[
// For a homotopy $h$ satisfying $f-g=d_B h+h d_A$, the morphism
// $
//   Phi_h (b,a)=(b+h(a),a)
// $
// is a chain isomorphism with inverse $Phi_(-h)$.
// ]

// Thus the isomorphism class of $cone(f)$ depends only on the homotopy class $[f]$. the isomorphism is not canonical: its construction depends on the chosen homotopy between the two representatives, and different homotopies may produce different isomorphisms in $Kcat(cA)$.

// //consider
// #text(fill: red)[More generally, the cone construction is functorial in $Cx(cA)$ for strictly commutative squares. A commutative square in $Kcat(cA)$ commutes only up to homotopy, and constructing the corresponding morphism between cones requires choosing such a homotopy. Consequently, the cone construction does not descend canonically to a functor
// $op("Arr")(Kcat(cA))->Kcat(cA).
// $]

// Nevertheless, a morphism in $Kcat(cA)$ has a cone well defined up to noncanonical isomorphism. This is sufficient for the theory of distinguished triangles, which is itself formulated up to isomorphism.

We have achieved three things. First, passing from $Cx(cA)$ to $Kcat(cA)$ makes morphisms between resolutions unique whenever they were previously unique up to homotopy. Second, homotopy equivalences become isomorphisms. Third, the cone of a morphism in $Kcat(cA)$ is well defined (up to noncanonical isomorphism).

This is enough to formulate cone triangles intrinsically in the homotopy category, as we wished. It is not yet enough to identify quasi-isomorphic complexes: the acyclic noncontractible complex above is nonzero in $Kcat(cA)$. Thus we still have two further steps. We first organize cone triangles into the triangulated structure of $Kcat(cA)$; we then invert quasi-isomorphisms to obtain the derived category.


== Triangulated Homotopy Category<sec:triangulated-homotopy-category>


Cone triangles in $Kcat(cA)$ already carry the long exact cohomology sequence proved in @sec:cone-triangle. Later we will use the same form of exactness in settings where an object is presented only inside a triangulated category. We therefore isolate the properties of cone triangles that can be formulated entirely in terms of objects, morphisms, shifts, and commutative diagrams.

We first specify the relevant diagrams and then verify four operations on them - Normalization, rotation, completion of a commutative square, and compatibility with composition. These become the axioms of a triangulated category.


// //consider
// #rmrk(title: "What changes when we pass to triangles")[
// The cone itself remains an object of $Cx(cA)$. What changes is the status of the diagram around it.


//   + In $Cx(cA)$, $cone(f)$ is a complex and $0 -> B -> cone(f) -> shift(A,1) -> 0$ is a short exact sequence used to prove the long exact cohomology sequence.

//   + After passing to $Kcat(cA)$, the diagram $A -> B -> cone(f) -> shift(A,1)$ is well defined up to isomorphism, and consecutive composites vanish as morphisms of the homotopy category.

//   + A distinguished triangle is any triangle isomorphic to one of these cone diagrams. The axioms of a triangulated category abstract their behaviour under identity maps, rotation, morphisms of diagrams, and composition.
// ]
// 

#figure(
  diagram(
    spacing: 1.2cm,
    node((0, 0), $A$),
    node((2.2, 0), $B$),
    node((1.1, 1.55), $C$),
    edge((0, 0), (2.2, 0), "->", label: $f$),
    edge((2.2, 0), (1.1, 1.55), "->", label: $g$),
    edge((1.1, 1.55), (0, 0), "->", label: $h$, label-side: left),
    node((0.18, 0.82), text(size: 8pt)[$[1]$]),
  ),
  caption: [
    Geometric notation for
    $A->B->C->shift(A,1)$. The label $[1]$ indicates the shifted target of
    the returning morphism.
  ],
)

#def(title: "Triangle and morphism of triangles")[
A *triangle* in $Kcat(cA)$ is a diagram
$ A^bullet ->^f B^bullet ->^g C^bullet ->^h shift(A^bullet,1). $
A *morphism* from this triangle to
$ A'^bullet ->^(f') B'^bullet ->^(g') C'^bullet ->^(h') shift(A'^bullet,1) $
is a triple $(a,b,c)$ such that
$ b f = f' a, quad c g = g' b, quad shift(a,1) h = h' c $
in $Kcat(cA)$.
]
<def:triangle-morphism>

#def(title: "Cone triangle and distinguished triangle")[
The *cone triangle* of $f : A^bullet -> B^bullet$ is
$ A^bullet ->^f B^bullet ->^(i_f) cone(f) ->^(p_f) shift(A^bullet,1). $
A triangle in $Kcat(cA)$ is *distinguished* if it is isomorphic, as a triangle, to a cone triangle.
]
<def:distinguished-triangle>

The closure under isomorphism is essential. The cone of a homotopy class is determined only up to noncanonical isomorphism, as we saw. Distinguishedness must therefore depend on the diagram in $Kcat(cA)$, not on a particular chain-level presentation.

#prop(title: "Cohomology of a distinguished triangle")[
Every distinguished triangle
$ A^bullet -> B^bullet -> C^bullet -> shift(A^bullet,1) $
induces a natural long exact sequence
$ dots.c -> H^n (A) -> H^n (B) -> H^n (C) -> H^(n + 1)(A) -> dots.c. $
]
<prop:cohomology-distinguished-triangle>

#proof()[
The result was proved for cone triangles in @lem:cone-les. Cohomology descends to $Kcat(cA)$, and isomorphic triangles induce isomorphic long exact sequences.
]

In particular, consecutive morphisms in a distinguished triangle compose to zero. The converse fails, and it fails already in the smallest case.

#exmp(title: "Vanishing composites do not suffice")[
In $Kcat(Ab)$ take
$ ZZ \/ 2 ZZ ->^0 ZZ \/ 2 ZZ ->^0 ZZ \/ 2 ZZ ->^0 shift(ZZ \/ 2 ZZ,1), $
all three objects concentrated in degree $0$ and all three morphisms zero. Consecutive composites vanish. If the triangle were distinguished, @prop:cohomology-distinguished-triangle would force
$ 0 -> ZZ \/ 2 ZZ ->^0 ZZ \/ 2 ZZ ->^0 ZZ \/ 2 ZZ -> 0 $
to be exact, which already fails at the first term. Vanishing consecutive composites are therefore necessary for distinguishedness. The additional condition is that applying cohomology produce the exact sequence of @lem:cone-les in every degree.
]
<exmp:zero-composites-not-distinguished>



=== Identity and normalization

#prop(title: "Normalization")[
The cone of $id_A$ is contractible, while
$ cone(0 : A -> B) = B ds shift(A,1). $
Hence the identity triangle is distinguished, and every morphism begins a distinguished triangle.
]
<prop:cone-normalization>

#proof()[
Both statements follow directly from the cone differential.
]

=== Rotation

The left rotation of
$ A ->^f B ->^g C ->^h shift(A,1) $
is
$ B ->^g C ->^h shift(A,1) ->^(-shift(f,1)) shift(B,1). $


#prop(title: "Rotation preserves distinguished triangles")[
A triangle is distinguished if and only if its left rotation is distinguished.
]
<prop:rotation-distinguished>

#proofsketch()[
For a cone triangle, $cone(i_f)$ is homotopy equivalent to $shift(A,1)$ after removing a contractible summand. Under this equivalence, its cone triangle becomes the left rotation. See @KashiwaraSchapira1990[Lemma I.4.2].
]

The long exact cohomology sequence of the rotated triangle is the same sequence with its starting point and indices shifted.

=== Completion of a square

Suppose $a : A -> A'$ and $b : B -> B'$ satisfy $b f = f' a$ in $Kcat(cA)$. Choosing a homotopy
$ b f - f' a = d_(B') s + s d_A $
defines a map
$ c^n = mat(b^n,s^(n+1);0,a^(n+1)) : cone(f)^n -> cone(f')^n. $

#figure(
  diagram(
    spacing: 1.55cm,
    node((0, 0), $A$), node((1.5, 0), $B$), node((3.2, 0), $cone(f)$), node((5, 0), $shift(A,1)$),
    node((0, 1.5), $A'$), node((1.5, 1.5), $B'$), node((3.2, 1.5), $cone(f')$), node((5, 1.5), $shift(A',1)$),
    edge((0, 0), (1.5, 0), "->", label: $f$),
    edge((1.5, 0), (3.2, 0), "->"),
    edge((3.2, 0), (5, 0), "->"),
    edge((0, 1.5), (1.5, 1.5), "->", label: $f'$),
    edge((1.5, 1.5), (3.2, 1.5), "->"),
    edge((3.2, 1.5), (5, 1.5), "->"),
    edge((0, 0), (0, 1.5), "->", label: $a$),
    edge((1.5, 0), (1.5, 1.5), "->", label: $b$),
    edge((3.2, 0), (3.2, 1.5), "->", label: $c$),
    edge((5, 0), (5, 1.5), "->", label: $shift(a,1)$),
  ),
  caption: [A commuting square in $Kcat(cA)$ completed to a morphism of cone triangles.]
)

#prop(title: "Completion to a morphism of triangles")[
Every commutative square between the first morphisms of two distinguished triangles extends to a morphism of triangles.
]
<prop:completion-morphism-triangles>

#proofsketch()[
Replace both triangles by cone triangles. The chosen homotopy $s$ gives the displayed map $c$, which completes the diagram.
]

The completion need not be unique: different choices of $s$ may produce different maps $c$. For conditions implying uniqueness, see @BBD1982[1.1.9--1.1.10].

=== Composition and the octahedron

Let $A ->^f B ->^g C$ be composable. Define
$ alpha(b,a) = (g(b),a), quad beta(c,a) = (c,f(a)), quad gamma(c,b) = (b,0). $
These maps compare the cones of $f$, $g$, and $g f$.

#prop(title: "The cone of a composition")[
The sequence
$ cone(f) ->^alpha cone(g f) ->^beta cone(g) ->^gamma shift(cone(f),1) $
is a distinguished triangle in $Kcat(cA)$.
]
<prop:cone-composition>

#proofsketch()[
The cone of $alpha$ splits, up to homotopy, as $cone(g)$ together with a contractible summand. Under this equivalence, the remaining maps become $beta$ and $gamma$; see @KashiwaraSchapira1990[Proposition I.4.4] and @Goresky2026[Appendix A.10--A.11].
]

#figure(
  diagram(
    spacing: 1.1cm,
    crossing-thickness: 5,
    label-size: 8pt,

    // The six vertices of the octahedron.
    node((0, 0), $cone(g f)$),
    node((-2.55, 1.55), $cone(f)$),
    node((2.55, 1.55), $cone(g)$),
    node((-2.55, 3.7), $A$),
    node((2.55, 3.7), $C$),
    node((0, 5.45), $B$),

    // The original composable morphisms.
    edge(
      (-2.55, 3.7),
      (0, 5.45),
      "->",
      label: $f$,
      label-side: right,
    ),
    edge(
      (0, 5.45),
      (2.55, 3.7),
      "->",
      label: $g$,
      label-side: right,
    ),
    edge(
      (-2.55, 3.7),
      (2.55, 3.7),
      "->",
      label: $g f$,
      label-side: left,
    ),

    // The triangle of f.
    edge(
      (0, 5.45),
      (-2.55, 1.55),
      "->",
      label: $i_f$,
      label-pos: 0.3,
      label-side: left,
      crossing: true,
    ),
    edge(
      (-2.55, 1.55),
      (-2.55, 3.7),
      "->",
      label: $p_f$,
      label-side: right,
    ),

    // The triangle of g.
    edge(
      (2.55, 3.7),
      (2.55, 1.55),
      "->",
      label: $i_g$,
      label-side: right,
    ),
    edge(
      (2.55, 1.55),
      (0, 5.45),
      "->",
      label: $p_g$,
      label-pos: 0.3,
      label-side: left,
      crossing: true,
    ),

    // The triangle of g f.
    edge(
      (2.55, 3.7),
      (0, 0),
      "->",
      label: $i_(g f)$,
      label-pos: 0.3,
      label-side: right,
      crossing: true,
    ),
    edge(
      (0, 0),
      (-2.55, 3.7),
      "->",
      label: $p_(g f)$,
      label-pos: 0.3,
      label-side: right,
      crossing: true,
    ),

    // The upper octahedral triangle.
    edge(
      (-2.55, 1.55),
      (0, 0),
      "->",
      label: $alpha$,
      label-side: left,
      stroke: (dash: "dashed"),
    ),
    edge(
      (0, 0),
      (2.55, 1.55),
      "->",
      label: $beta$,
      label-side: left,
      stroke: (dash: "dashed"),
    ),
    edge(
      (2.55, 1.55),
      (-2.55, 1.55),
      "->",
      label: $gamma$,
      label-side: left,
    ),

    // Shift markers: the geometrically repeated endpoint is shifted.
    node(
      (-2.88, 2.65),
      text(size: 8pt)[$[1]$],
    ),
    node(
      (-1.9, 3.05),
      text(size: 8pt)[$[1]$],
    ),
    node(
      (0.7, 4.75),
      text(size: 8pt)[$[1]$],
    ),
    node(
      (0, 1.22),
      text(size: 8pt)[$[1]$],
    ),
  ),
  caption: [
    The octahedral diagram associated with the composable morphisms
    $A arrow.r^f B arrow.r^g C$. The lower face records $f$, $g$, and
    $g f$, while the upper face is the distinguished triangle
    $cone(f) arrow.r^alpha cone(g f) arrow.r^beta cone(g)
    arrow.r^gamma shift(cone(f), 1)$. A label $[1]$ indicates that the
    endpoint represented at that vertex is shifted.
  ],
)

The distinguished triangle of @prop:cone-composition implies that if two of $cone(f)$, $cone(g)$, and $cone(g f)$ are acyclic, then so is the third. By @cor:cone-quasi-isomorphism, if any two of $f$, $g$, and $g f$ are quasi-isomorphisms, then the remaining morphism is also a quasi-isomorphism.


#def(title: "Triangulated category")[
A triangulated category consists of an additive category $cT$, an additive autoequivalence #footnote[An autoequivalence of a category is an equivalence from the category to itself.] $shift(-,1)$ with quasi-inverse $shift(-,-1)$, and a class of distinguished triangles satisfying:

- *(TR1)* Distinguished triangles are closed under isomorphism; $A ->^(id_A) A -> 0 -> shift(A,1)$ is distinguished; and every morphism begins a distinguished triangle.
- *(TR2)* A triangle is distinguished if and only if its left rotation is distinguished.
- *(TR3)* Every commutative square between the first morphisms of distinguished triangles extends to a morphism of triangles.
- *(TR4)* For composable morphisms $A ->^f B ->^g C$, the distinguished triangles #footnote[$A ->^f B ->^(i_f) C_f ->^(p_f) shift(A,1), $
  $B ->^g C ->^(i_g) C_g ->^(p_g) shift(B,1), $
  $A ->^(g f) C ->^(i_(g f)) C_(g f) ->^(p_(g f)) shift(A,1). $] 
   of $f$, $g$, and $g compose f$ can be completed to an octahedral diagram #footnote[I.e, there exist morphisms $u : C_f -> C_(g f)$ and $v : C_(g f) -> C_g$ such that $(id_A,g,u)$ and $(f,id_C,v)$ are morphisms of triangles, and
  $C_f ->^u C_(g f) ->^v C_g ->^(shift(i_f,1) compose p_g) shift(C_f,1)$
  is distinguished].
]
<def:triangulated-category>

  
  

These are Verdier's axioms. See @KashiwaraSchapira1990[Definition I.5.1], @HTT2008[Definition B.3.6] and @BBD1982[1.1.6--1.1.7].

#thm(title: "The homotopy category is triangulated")[
With the shift and distinguished triangles defined above, $Kcat(cA)$ is a triangulated category. The bounded subcategories $Kcat^+(cA)$, $Kcat^-(cA)$, and $Kcat^b(cA)$ are triangulated subcategories.
]
<thm:homotopy-category-triangulated>

#proofsketch()[
Normalization gives TR1, rotation gives TR2, completion of squares gives TR3, and the octahedral construction gives TR4. Shifts and mapping cones preserve bounded-below, bounded-above, and bounded complexes. The same constructions therefore restrict to each of the three bounded variants.
]


// A triangulated category is not an abelian category with short exact sequences renamed. Distinguished triangles need not determine kernels or cokernels, and completing a morphism to a triangle is not canonical. What the structure preserves is the stable exactness required for homological constructions: shifts, connecting morphisms, long exact cohomology sequences, and compatibility with maps and compositions.

// The homotopy category now has the correct replacement for exact sequences, but it still has the wrong isomorphisms. The acyclic noncontractible complex of @exmp:acyclic-noncontractible remains nonzero. We therefore turn to localization.


// #def(title: "Triangle; morphisms of triangles")[
// A *triangle* in $Kcat(cA)$ is a diagram
// $ A^bullet ->^f B^bullet ->^g C^bullet ->^h shift(A^bullet, 1). $
// A *morphism of triangles* from $(A, B, C, f, g, h)$ to $(A', B', C', f', g', h')$ is a triple of morphisms $a colon A^bullet -> A'^bullet$, $b colon B^bullet -> B'^bullet$, $c colon C^bullet -> C'^bullet$ making the three squares commute in $Kcat(cA)$:
// $ b compose f = f' compose a, quad c compose g = g' compose b, quad shift(a,1) compose h = h' compose c. $
// It is an *isomorphism of triangles* if $a$, $b$, $c$ are isomorphisms in $Kcat(cA)$.
// ]


// A triangle is only a diagram of a specified form; no exactness condition is included in the definition.

// We now isolate the specific triangles that will play the role of exact sequences.
// #def(title: "Distinguished triangle")[
// A triangle in $Kcat(cA)$ is *distinguished* if it is isomorphic, as a triangle, to the cone triangle of some morphism of complexes.
// ]

// #rmrk(title: "Why isomorphism is included")[
// A distinguished triangle need not literally be written using a mapping cone. It is enough that it be isomorphic in $Kcat(cA)$ to a cone triangle. Thus distinguishedness depends only on the objects and morphisms in the homotopy category, not on a particular presentation in $C(cA)$.
// ]

// Distinguished triangles inherit the long exact sequence of cone triangles.

// #prop(title: "Cohomology of a distinguished triangle")[
// Every distinguished triangle
// $ A^bullet ->^f B^bullet ->^g C^bullet ->^h shift(A^bullet, 1) $
// induces a natural long exact sequence
// $ dots.c -> H^n (A^bullet) ->^(H^n (f)) H^n (B^bullet) ->^(H^n (g)) H^n (C^bullet) ->^(H^n (h)) H^(n+1)(A^bullet) -> dots.c. $
// ]

// #proof()[
// We proved this for cone triangles (@:) in @sec:cone-triangle. Since the cohomology functors descend to $Kcat(cA)$ (@:) and the property is invariant under isomorphism of triangles, it transfers to all distinguished triangles.
// ]

// #cor(title: "Consecutive morphisms")[
// In every distinguished triangle
// $
//   A^bullet
//   ->^f B^bullet
//   ->^g C^bullet
//   ->^h shift(A^bullet,1),
// $
// the composites
// $g compose f,
//   quad
//   h compose g,
//   quad
//   shift(f,1) compose h
// $
// vanish in $Kcat(cA)$.
// ]

// The final morphism of a distinguished triangle is not an auxiliary decoration: as explained in @sec:cone, it records the connecting morphisms in cohomology, and it makes it possible to rotate the triangle:

// #def(title: "Rotation of a triangle")[
// The _left rotation_ of a triangle
// $
//   A^bullet
//   ->^f B^bullet
//   ->^g C^bullet
//   ->^h shift(A^bullet,1)
// $
// is the triangle
// $
//   B^bullet
//   ->^g C^bullet
//   ->^h shift(A^bullet,1)
//   ->^(-shift(f,1)) shift(B^bullet,1).
// $
// ]

// #prop(title: "Rotation preserves distinguished triangles")[
// A triangle is distinguished if and only if its left rotation is distinguished.
// ]

// For a cone triangle, the rotated triangle is isomorphic in $Kcat(cA)$ to the cone triangle of the morphism
// $
//   i_f:B^bullet->cone(f).
// $
// #proof()[
//   It suffices to show this for a standard cone triangle. An explicit, albeit tedious, matrix calculation provides a natural homotopy equivalence between $cone(i_f)$ and $shift(A^bullet, 1)$, proving that the rotated triangle is isomorphic in $Kcat(cA)$ to the cone triangle of the canonical inclusion $i_f$ [ref]. The inverse rotation follows by applying the same logic repeatedly. ]

// The sign in the final morphism is necessary for rotated cone triangles to remain distinguished - it is forced by the homotopy equivalence $cone(i_f) tilde.eq shift(A^bullet, 1)$.

// The compatibility of the cone construction with commutative squares provides morphisms between distinguished triangles.

// #prop(title: "Completion to a morphism of triangles")[
// Suppose
// $A^bullet ->^f B^bullet
// $
// and
// $A'^bullet ->^(f') B'^bullet
// $
// are morphisms in $Kcat(cA)$, and suppose that
// $b compose f=f' compose a
// $
// for morphisms
// $
//   a:A^bullet->A'^bullet,
//   quad
//   b:B^bullet->B'^bullet.
// $
// Then there exists a morphism
// $c:cone(f)->cone(f')
// $
// such that
// $(a,b,c)
// $
// is a morphism between the corresponding cone triangles.
// ]
// #proof()[ This is a direct consequence of the compatibility of the cone construction with commutative squares established in @sec:homotopy-category [ref].]
// //TODO: make sure

// The completing morphism $c$ is generally not unique. This is the same phenomenon as the noncanonicity of the isomorphism $Phi_h$ between cones of homotopic morphisms (@:). Triangulated categories guarantee the existence of completions, never a canonical choice.


// The relation between a morphism, its cone, and a composition of morphisms is governed by the octahedral diagram, which weaves three interacting cones together.

// #prop(title: "The cone of a composition")[
// Let $A^bullet ->^f B^bullet ->^g C^bullet$ be composable morphisms of complexes. There are natural morphisms
// $ cone(f) -> cone(g compose f) -> cone(g) -> shift(cone(f), 1) $
// which form a distinguished triangle in $Kcat(cA)$.
// ]
// #proof()[The morphisms connecting these cones are constructed via explicit matrix operations in $Cx(cA)$, and a lengthy algebraic verification proves their cone is contractible [ref].
// ]

// The meaning of the octahedral relation for us is ssimple. The three cones $cone(f)$, $cone(g)$, $cone(g compose f)$ measure the failures of $f$, $g$, and $g compose f$ to be quasi-isomorphisms. The distinguished triangle connecting them expresses the compatibility of these three failures. This relation is the concrete content of the octahedral axiom for the homotopy category.

// We now isolate the abstract structure exhibited by the shift and cone constructions.

// #def(title: "Triangulated category")[
// A *triangulated category* consists of:
// - an additive category $cT$;
// - an additive autoequivalence $shift(-,1) colon cT -> cT$; //I have not defined "autoequivalence"
// - a class of triangles, called *distinguished triangles*;
// subject to the following axioms.

// - *(TR1)* Every triangle isomorphic to a distinguished triangle is distinguished. For every object $A$, the triangle $ A ->^(id_A) A -> 0 -> shift(A,1) $ is distinguished, and every morphism $f colon A -> B$ occurs as the first morphism of a distinguished triangle.
// - *(TR2)* A triangle is distinguished if and only if its rotation is distinguished.
// - *(TR3)* Every commutative square formed by the first morphisms of two distinguished triangles can be completed to a morphism of triangles. [make sure that we connected to that]
// - *(TR4)* For every pair of composable morphisms $A ->^f B ->^g C$, the distinguished triangles associated with $f$, $g$, and $g compose f$ fit into an octahedral diagram; equivalently, their cones are connected by a distinguished triangle
//   $ cone(f) -> cone(g compose f) -> cone(g) -> shift(cone(f), 1). $
// ]
// #thm(title: "The homotopy category is triangulated")[
// Let $cA$ be an additive category. With the shift functor and the distinguished triangles defined above, the homotopy category
// $
//   Kcat(cA)
// $
// is a triangulated category.

// Moreover, the full subcategories
// $Kcat^+(cA),
//   quad
//   Kcat^-(cA),
//   quad
//   Kcat^b(cA)
// $
// are also triangulated subcategories.
// ]

// The proof is obtained from explicit calculations with mapping cones:

// - *(TR1)* follows from the definition of distinguished triangles and the existence of $cone(f)$;
// - *(TR2)* follows by comparing the rotation of a cone triangle with the cone of its second morphism;
// - *(TR3)* follows from the functoriality of cones with respect to commutative squares;
// - *(TR4)* follows from the explicit triangle relating the cones of $f$, $g$, and $g compose f$.
// //connect explicitly, with links, to the previous props




For every cohomological functor, a distinguished triangle induces a long exact sequence. Rotation reindexes that sequence, TR3 makes it natural with respect to commutative squares, and TR4 relates the sequences associated with a composition. A third vertex exists for every morphism, although its choice and the completion of a square are not canonical.

The acyclic noncontractible complex of @exmp:acyclic-noncontractible remains nonzero in $Kcat(cA)$. Localization is what we need to make it vanish.


// The homotopy category now has the correct replacement for exact sequences, but it still has the wrong isomorphisms. A quasi-isomorphism has an acyclic cone (@prop:homotopic-morphisms-have-isomorphic-cones), yet an acyclic complex need not be contractible ($E^bullet$ of @sec:homotopy-category); hence a quasi-isomorphism need not be invertible in $Kcat(cA)$. The derived category is obtained by formally inverting these morphisms while preserving the triangulated structure.

== The derived category <sec:derived-category>

We now invert the quasi-isomorphisms. The operation is the categorical analogue of inverting a set of elements in a ring - one adds formal inverses and asks that nothing else be identified.
This operation called "localization", and it is a universal property in the category of categories. 

#thm(title: "Existence of the localization")[
Let $cC$ be a category and $S$ a class of morphisms in $cC$. There is a category $cC[S^(-1)]$, possibly after passing to a larger universe, and a functor $Q : cC -> cC[S^(-1)]$ with the following universal property: $Q(s)$ is an isomorphism for every $s in S$, and every functor $F : cC -> cD$ such that $F(s)$ is an isomorphism for all $s in S$ factors as $F iso G compose Q$ for a functor $G$ that is unique up to natural isomorphism. The pair $(cC[S^(-1)],Q)$ is determined by this property up to equivalence.
]
<thm:localization-exists>
#figure(
  diagram(
    spacing: 1.6cm,
    node((0, 0), $Kcat(cA)$),
    node((2, 0), $D(cA)$),
    node((2, 1.3), $cD$),
    edge((0, 0), (2, 0), "->", label: $Q$),
    edge((0, 0), (2, 1.3), "->", label: $F$, label-side: right),
    edge((2, 0), (2, 1.3), "-->", label: $G$),
  )
)
See @KashiwaraSchapira1990[§I.6] and @HTT2008[Def. B.4.1].



We use @thm:localization-exists as stated and do not construct $cC[S^(-1)]$. The construction is delicate — the naive one produces morphism classes that need not be sets — and for the class of quasi-isomorphisms in $Kcat(cA)$ the difficulty is resolved by a calculus of fractions, which is what makes the roof description of the next subsection valid. @Goresky2026[Appendix A.23] gives the roof description directly, including the composition rule; @Dimca2004[Def. 1.3.1] states the universal property and refers to Verdier; the construction itself is carried out in @KashiwaraSchapira1990[§I.6--I.7]. None of the 'calculus of fractions' machinery is needed below, and we shall not introduce it.

#def(title: "Derived category")[
Let $S$ be the class of quasi-isomorphisms in $Kcat(cA)$. The *derived category* of $cA$ is
$ D(cA) := Kcat(cA)[S^(-1)]. $
Its bounded-below, bounded-above, and bounded versions are denoted $Dp(cA)$, $Dm(cA)$, and $Db(cA)$.
]
<def:derived-category>

The objects remain complexes, since the localization changes only the morphisms. Every quasi-isomorphism becomes invertible, so a resolution becomes isomorphic to the object it resolves. The graded family $(H^n (K))_n$ does not generally determine $K$ in $D(cA)$, since the morphisms joining its adjacent cohomological pieces also affect its isomorphism class.


By @cor:cone-quasi-isomorphism, a morphism belongs to $S$ precisely when its cone is acyclic. Thus the morphisms to be inverted are detected entirely by the triangulated structure already constructed.

However, a derived morphism may exist only after replacing its source by a quasi-isomorphic complex.


#def(title: "Roof")[
A *roof* from $A^bullet$ to $B^bullet$ is a diagram in $Kcat(cA)$
//fix it

#diagram(
  spacing: 1.5cm,
  node((0.75, 0), $X^bullet$),
  node((0, 0.5), $A^bullet$),
  node((1.5, 0.5), $B^bullet$),
  edge((0.75, 0), (1.5, 0.5), "->", label: $f$, label-side: left),
  edge((0.75, 0), (0, 0.5), "->", label: $s "(qis)"$, label-side: right),
)

where $s$ is a quasi-isomorphism. 
]

It represents the formal composite
$Q(f) compose Q(s)^(-1):A^bullet->B^bullet$ in $D(cA)$.




The intermediate complex $X^bullet$ is a replacement of $A^bullet$ by a quasi-isomorphic model from which an actual morphism to $B^bullet$ is available.

#prop(title: "Morphisms represented by roofs")[
Every morphism
$alpha:A^bullet->B^bullet$
in $D(cA)$ can be represented by a roof
$
  A^bullet
  <-^s X^bullet
  ->^f B^bullet
$
with $s$ a quasi-isomorphism.
]
This is the fraction description of the localization at quasi-isomorphisms; see @Goresky2026[Appendix A.23] and @KashiwaraSchapira1990[§I.6--I.7]. A morphism already represented by a map $A^bullet->B^bullet$ corresponds to the special roof with $X^bullet=A^bullet$ and $s=id_A$.

Different roofs may represent the same morphism. Their equality is determined by passing to a common refinement.

#figure(
  diagram(
    spacing: 1cm,
    crossing-thickness: 5,

    node((0, 2.6), $A^bullet$),
    node((4.4, 2.6), $B^bullet$),

    node((1.25, 1.35), $X^bullet$),
    node((3.15, 1.35), $Y^bullet$),

    node((2.2, 0), $Z^bullet$),

    edge((1.25, 1.35), (0, 2.6), "->", label: $s$, label-side: right),
    edge((1.25, 1.35), (4.4, 2.6), "->", label: $f$),

    edge(
      (3.15, 1.35),
      (0, 2.6),
      "->",
      label: $t$,
      label-side: right,
      crossing: true,
    ),
    edge((3.15, 1.35), (4.4, 2.6), "->", label: $g$),

    edge((2.2, 0), (1.25, 1.35), "->", label: $u$, label-side: right),
    edge((2.2, 0), (3.15, 1.35), "->", label: $v$),
  )
)
#def(title: "Equivalent roofs")[
Two roofs $A^bullet <-^s X^bullet ->^f B^bullet$ and $A^bullet <-^t Y^bullet ->^g B^bullet$ are *equivalent* if there exist a complex $Z^bullet$ and morphisms $u colon Z^bullet -> X^bullet$, $v colon Z^bullet -> Y^bullet$ such that
$ s compose u = t compose v, quad f compose u = g compose v, $
and the common morphism $s compose u = t compose v$ is a quasi-isomorphism.
]

The requirement that $s compose u = t compose v$ be a quasi-isomorphism excludes the trivial refinement $Z^bullet = 0$ which would identify every morphism with zero. The calculus of fractions for quasi-isomorphisms implies that the resulting relation is reflexive, symmetric, and transitive. Its equivalence classes are the morphisms of $D(cA)$.

Composition requires the same calculus of fractions. Given roofs
$A^bullet <-^s X^bullet ->^f B^bullet $
and
$B^bullet <-^t Y^bullet ->^g C^bullet, $
the arrows $f$ and $t$ cannot be concatenated. They must first be replaced by a commutative roof over their common target.

#figure(
  diagram(
    spacing: 0.7cm,
    node((2, -1.3), $W^bullet$),
    node((1, 0), $X^bullet$),
    node((3, 0), $Y^bullet$),
    node((0, 1.3), $A^bullet$),
    node((2, 1.3), $B^bullet$),
    node((4, 1.3), $C^bullet$),
    edge((2, -1.3), (1, 0), "->", label: $s'$, label-side: right),
    edge((2, -1.3), (3, 0), "->", label: $f'$),
    edge((1, 0), (0, 1.3), "->", label: $s$, label-side: right),
    edge((1, 0), (2, 1.3), "->", label: $f$),
    edge((3, 0), (2, 1.3), "->", label: $t$, label-side: right),
    edge((3, 0), (4, 1.3), "->", label: $g$),
  ),
  caption: [Composition of roofs. The upper roof $(W^bullet,s',f')$ satisfies $f s' = t f'$ with $s'$ a quasi-isomorphism; the composite is then $(W^bullet, s s', g f')$.]
)

Producing that upper roof for every pair is precisely the content of the calculus of fractions referred to after @thm:localization-exists; it is @KashiwaraSchapira1990[Def. I.6.1, conditions (S 1)--(S 4)]. We take it for granted. The injective model (@sec:injective-model) will remove the need for it entirely, by replacing roofs with ordinary homotopy classes of chain maps.

Before drawing any consequence we record that the exactness formalism of @sec:triangulated-homotopy-category survives the passage.

#def(title: "Distinguished triangles in the derived category")[
A triangle in $D(cA)$ is distinguished if it is isomorphic to the image of a distinguished triangle in $Kcat(cA)$ under the localization functor $Q$.
]
<def:derived-distinguished-triangle>

#thm(title: "The derived category is triangulated")[
The shift and distinguished triangles above make $D(cA)$ a triangulated category, and the localization functor $Q : Kcat(cA) -> D(cA)$ is triangulated. 
]
<thm:derived-category-triangulated>

The triangulated structure is obtained by localizing $Kcat(cA)$ along the triangulated subcategory of acyclic complexes; this is the Verdier localization described in @thm:derived-verdier-quotient below. See @KashiwaraSchapira1990[§I.7] for the construction.

Cohomology has a simpler consequence of the universal property. Each functor
$ H^n:Kcat(cA)->cA $
sends quasi-isomorphisms to isomorphisms, so it factors through $D(cA)$. We continue to denote the induced functor by $H^n$. Consequently, every distinguished triangle in $D(cA)$ gives the long exact cohomology sequence of @prop:cohomology-distinguished-triangle.

#prop(title: "Acyclic complexes vanish in the derived category")[
For a complex $A^bullet$, the following are equivalent:

- $A^bullet$ is acyclic;
- $0 -> A^bullet$ is a quasi-isomorphism;
- $A^bullet iso 0$ in $D(cA)$.
]
<prop:acyclic-vanish-derived>

#proof()[
The first two are the same statement, since $H^n (0) = 0$. If $0 -> A^bullet$ is a quasi-isomorphism it becomes invertible in $D(cA)$, giving the third. Conversely, if $A^bullet iso 0$ in $D(cA)$ then $H^n (A^bullet) iso H^n (0) = 0$ for all $n$, because $H^n$ is a functor on $D(cA)$.
]

Thus the complex $E^bullet$ of @exmp:acyclic-noncontractible, nonzero in $Kcat(Ab)$, becomes zero in $D(Ab)$. This was the gap of @sec:homotopy-category and now we closed it.

#prop(title: "Cohomology detects isomorphisms")[
A morphism $f : A^bullet -> B^bullet$ in $D(cA)$ is an isomorphism if and only if $H^n (f)$ is an isomorphism for every $n in ZZ$.
]
<prop:cohomology-detects-derived-isomorphisms>

#proof()[
By @thm:derived-category-triangulated we may complete $f$ to a distinguished triangle $A^bullet -> B^bullet -> C^bullet -> shift(A^bullet,1)$, and the associated long exact sequence shows that every $H^n (f)$ is an isomorphism precisely when $C^bullet$ is acyclic, hence precisely when $C^bullet iso 0$ by @prop:acyclic-vanish-derived. It remains to note that a morphism in a distinguished triangle is an isomorphism when the third vertex vanishes; this follows by applying $Hom_(D(cA))(W,-)$ to the triangle and using the five lemma, as in @KashiwaraSchapira1990[Cor. I.5.5].
]


// #proof()[ The first two conditions are equivalent by the definition of quasi-isomorphism. The localization functor sends a quasi-isomorphism to an isomorphism, so an acyclic complex becomes isomorphic to zero. Conversely, cohomology factors through $D(cA)$ and therefore sends every object isomorphic to zero to zero.]

// #text(fill: red)[In particular, the acyclic complex $E^bullet$ of @sec:homotopy-category — nonzero in $Kcat(Ab)$ — finally vanishes: $E^bullet iso 0$ in $D(Ab)$. Likewise, for our running morphism $2 colon ZZ \/ 4 ZZ -> ZZ \/ 4 ZZ$, the quasi-isomorphisms of @sec:cone-triangle identify $cone(2)$ with no single group, but its truncated pieces with $ZZ \/ 2 ZZ$ in two degrees; in $D(Ab)$ the cone is an honest object interpolating between $shift(Ker(2), 1)$ and $coker(2)$, and the triangle $ZZ \/ 4 ZZ ->^2 ZZ \/ 4 ZZ -> cone(2) -> shift(ZZ \/ 4 ZZ, 1)$ is the derived-category replacement of the two abelian short exact sequences we began the chapter with.]

// #text(fill: red)[TODO: add a diagram]
// #prop(title: "Derived isomorphisms")[
// If two complexes are connected by a finite zigzag of quasi-isomorphisms
// $
//   A^bullet
//   <-^~ C_1^bullet
//   ->^~ C_2^bullet
//   <-^~ dots.c
//   ->^~ B^bullet,
// $
// then they are isomorphic in $D(cA)$.
// ]
// //Exaplain

// The converse also holds in the usual localization construction: an isomorphism in the derived category expresses equality up to quasi-isomorphic replacement, not necessarily homotopy equivalence. //rephrase

// #rmrk(title: "Homotopy equivalence versus derived equivalence")[
// There are increasingly weaker relations:
// $
//   "isomorphic as complexes"
//   =>\ 
//   "homotopy equivalent"
//   =>\
//   "quasi-isomorphic"
//   =>\
//   "isomorphic in " D(cA).
// $
// The reverse implications fail in general.

// The passage from $C(cA)$ to $Kcat(cA)$ identifies homotopic morphisms. The passage from $Kcat(cA)$ to $D(cA)$ additionally makes all quasi-isomorphisms invertible.
// ]

// Since cohomology sends quasi-isomorphisms to isomorphisms, it descends through the localization - this is the first payoff of the universal property.

// #prop(title: "Cohomology on the derived category")[
// For every $n in ZZ$, there exists a unique functor
// $
//   H^n:D(cA)->cA
// $
// such that the composite
// $
//   Kcat(cA)
//   ->^q D(cA)
//   ->^(H^n) cA
// $
// is the ordinary cohomology functor on complexes.
// ]

// We use the same notation $H^n$ before and after localization. Hence a morphism in $D(cA)$ is an isomorphism whenever it induces isomorphisms on all cohomology objects.

// #prop(title: "Cohomology detects isomorphisms")[
// A morphism
// $
//   f:A^bullet->B^bullet
// $
// in $D(cA)$ is an isomorphism if and only if
// $
//   H^n (f):H^n (A^bullet)->H^n (B^bullet)
// $
// is an isomorphism for every $n in ZZ$.
// ]

// #proof()[If $f$ is an isomorphism, the claim follows by #text(fill: red)[functoriality]. Conversely, complete $f$ to a distinguished triangle
// $
//   A^bullet
//   ->^f B^bullet
//   -> C^bullet
//   -> shift(A^bullet,1).
// $
// The associated long exact sequence shows that $H^n (C^bullet)=0$ for every $n$. Thus $C^bullet$ is zero in $D(cA)$, and a morphism whose cone is zero is an isomorphism.]

// We must therefore transfer the cone triangles of $Kcat(cA)$ through the localization.

// #def(title: "Distinguished triangles in the derived category")[
// A triangle in $D(cA)$
// $
//   A^bullet
//   -> B^bullet
//   -> C^bullet
//   -> shift(A^bullet,1)
// $
// is *distinguished* if it is isomorphic to the image under
// $
//   q:Kcat(cA)->D(cA)
// $
// of a distinguished triangle in $Kcat(cA)$.
// ]


// #thm(title: "The derived category is triangulated")[
// The shift functor on $Kcat(cA)$ descends to an autoequivalence
// $
//   shift(-,1):D(cA)->D(cA).
// $
// Together with the distinguished triangles defined above, it makes $D(cA)$ into a triangulated category.

// Moreover, the localization functor
// $
//   q:Kcat(cA)->D(cA)
// $
// is a triangulated functor.
// ]

// The theorem is not automatic for an arbitrary localization of a triangulated category. It applies here because the quasi-isomorphisms are precisely the morphisms whose cones lie in a triangulated subcategory - i.e, the subcategory of acyclic complexes. [refernce, proof?]

// #def(title: "Acyclic subcategory")[
// Let
// $Kcat_"ac" (cA)
// $
// be the full subcategory of $Kcat(cA)$ consisting of acyclic complexes.
// ]

// #prop(title: "The acyclic complexes form a triangulated subcategory")[
// The subcategory $Kcat_"ac" (cA)$ is closed under shifts, isomorphisms, and distinguished triangles. In particular, if two objects in a distinguished triangle are acyclic, then so is the third.
// ]

// #proof()[
//   Shifts preserve cohomology up to reindexing. Closure under distinguished triangles follows from the associated long exact cohomology sequence.
//  ]

// This gives a second, equivalent description of the derived category.

// #thm(title: "Derived category as a Verdier quotient")[
// There is a canonical equivalence of triangulated categories
// $
//   D(cA)
//   equiv
//   Kcat(cA) slash Kcat_"ac" (cA).
// $]

// The two descriptions express the same operation from complementary viewpoints — the localization $Kcat(cA)[Q^(-1)]$ makes every quasi-isomorphism invertible, while the Verdier quotient $Kcat(cA) slash Kcat_"ac"(cA)$ makes every acyclic complex vanish — and they are equivalent by @cor:cone-quasi-isomorphism: inverting a morphism and killing its cone are the same demand.

// #text(fill: red)[again, not sure about that:
// ]
// #rmrk(title: "Terms versus cohomology")[
// An object of $D^b (cA)$ may be represented by a bounded complex. It may also be represented by an unbounded complex whose cohomology vanishes outside finitely many degrees, provided that this complex is quasi-isomorphic to a bounded one.

// This distinction will become important when using injective resolutions: a bounded complex need not admit a bounded injective resolution.
// ]

// #prop(title: "Embedding of the original category")[
// The inclusion of objects as complexes concentrated in degree zero induces a fully faithful functor
// $
//   cA->D(cA).
// $
// Its essential image consists of the objects $A^bullet$ satisfying
// $
//   H^n (A^bullet)=0
// $
// for every $n != 0$.
// ]
// [ref]

// The original abelian category is therefore contained in the derived category, but it is no longer the whole category. Derived objects may have cohomology in several degrees, and distinguished triangles connect those degrees through their boundary morphisms.

#thm(title: "Two descriptions of the derived category")[
Let $Kcat_"ac"(cA) subset.eq Kcat(cA)$ be the full subcategory of acyclic complexes. It is a triangulated subcategory, and there is an equivalence of triangulated categories
$ D(cA) equiv Kcat(cA) \/ Kcat_"ac"(cA) $
]
<thm:derived-verdier-quotient>

#proof()[
By @cor:cone-quasi-isomorphism a morphism of $Kcat(cA)$ is a quasi-isomorphism if and only if its cone is acyclic. Inverting the quasi-isomorphisms and killing the acyclic complexes are therefore two descriptions of one operation: a morphism becomes invertible when its third vertex becomes zero. For the verification that $Kcat_"ac"(cA)$ is triangulated and that the quotient carries the stated structure, see @KashiwaraSchapira1990[Def. I.7.1, with Props. I.6.7 and I.6.9], where the quotient description is taken as the definition.
]

#figure(
  diagram(
    spacing: 1cm,
    node((0, 0), $Kcat(cA)$),
    node((2.2, -0.8), $Kcat(cA)[Q^(-1)]$),
    node((2.2, 0.8), $Kcat(cA) \/ Kcat_"ac"(cA)$),
    node((4.6, 0), $D(cA)$),
    edge((0, 0), (2.2, -0.8), "->", label: $"invert " Q$),
    edge((0, 0), (2.2, 0.8), "->", label: $"kill " Kcat_"ac"(cA)$, label-side: right),
    edge((2.2, -0.8), (4.6, 0), "->", label: $iso$),
    edge((2.2, 0.8), (4.6, 0), "->", label: $iso$, label-side: right),
  ),
  caption: [Inverting the quasi-isomorphisms and killing the acyclic complexes give the same category, because a morphism is a quasi-isomorphism when its cone is acyclic.]
)
The long exact cohomology sequence of a cone was first obtained from a short exact sequence of complexes, using the Snake Lemma in the abelian setting of @chap:homological-algebra. It then descends to $op("K")(cal(A))$, because homotopic maps induce the same maps on cohomology, and to $D(cal(A))$, because quasi-isomorphisms induce cohomology isomorphisms. Thus the later categories retain these exact sequences without themselves being abelian. It remains to describe how their morphisms and derived functors can be computed using injective replacements.

// At this point the first four guiding questions have been answered. Mapping cones produce long exact sequences in $Cx(cA)$; homotopy classes remove the non-uniqueness of comparison maps; the triangulated axioms isolate the exactness that survives; and localization makes quasi-isomorphisms invertible without discarding it. What remains is the computation.

// The passage $Cx(cA) -> Kcat(cA) -> D(cA)$ preserves exact-sequence information even though the last two categories are not abelian. The long exact sequence of a cone was proved only in $Cx(cA)$, which is abelian: there, the degreewise-split short exact sequence $ 0 -> B^bullet -> cone(f) -> shift(A,1) -> 0 $ yields the long exact sequence by the classical argument based on the Snake Lemma (@lem:snake-lemma). We then passed to $Kcat(cA)$ by identifying homotopic morphisms; since homotopic morphisms induce the same maps on cohomology, every functor $H^n$ descends, and the long exact sequence remains attached to the corresponding cone triangle. Finally, we passed to $D(cA)$ by inverting quasi-isomorphisms; since cohomology already sends every quasi-isomorphism to an isomorphism, it descends once more.

// Thus the Snake Lemma is never applied inside $Kcat(cA)$ or $D(cA)$. It is used once, in the abelian category of complexes, to establish the basic exactness property of cone triangles; the homotopy and derived categories retain this property as part of their triangulated structure. The sequence $Cx(cA) -> Kcat(cA) -> D(cA)$ discards increasingly inessential chain-level information — first the distinction between homotopic morphisms, then the distinction between quasi-isomorphic complexes — without discarding the long exact cohomological information that motivated the entire construction.


== Injective model<sec:injective-model>

The localization $D(cA) = Kcat(cA)[Q^(-1)]$ gives the correct category, but its intrinsic description is not convenient for calculations. A morphism in $D(cA)$ is represented by a roof
$ K^bullet <-^s X^bullet ->^a L^bullet, $
with $s$ a quasi-isomorphism. Roofs are necessary for the universal definition of localization, but comparing roofs and composing them requires common refinements. For bounded-below complexes, injective replacements remove this difficulty: after replacing the target by a bounded-below complex of injective objects, every derived morphism is represented by an ordinary chain map, uniquely up to homotopy.

#thm(title: "Injective replacement theorem")[
Assume that $cA$ has enough injectives.

- Every bounded-below complex $K^bullet in Cx^+(cA)$ admits a quasi-isomorphism $K^bullet -> I_K^bullet$, where $I_K^bullet$ is bounded below and every $I_K^n$ is injective in $cA$.
- For every bounded-below complex $A^bullet$ and every bounded-below complex of injectives $I^bullet$, localization induces a natural isomorphism
$ Hom_(Kcat^+(cA))(A^bullet,I^bullet) iso Hom_(Dp(cA))(A^bullet,I^bullet). $
- Consequently, the localization functor induces an equivalence of triangulated categories
$ Kcat^+(op("Inj") cA) equiv Dp(cA), $
where $Kcat^+(op("Inj") cA)$ denotes the homotopy category of bounded-below complexes whose terms are injective.
]
<thm:injective-model>
We use the general injective replacement theorem without reproducing its full proof. The two-term construction below illustrates how the differential of a complex is lifted to resolutions and how the resulting data are assembled into one complex. For the general theorem, see #cite(<Goresky2026>, supplement: [Appendix A.16–A.23]), #cite(<Dimca2004>, supplement: [Props. 1.3.9–1.3.10]), and #cite(<KashiwaraSchapira1990>, supplement: [Props. I.7.7 and I.7.10]).

#rmrk(title: "Where the bounded-below hypothesis comes from")[
The role of the lower bound is visible for a two-term complex $K^bullet=[A attach(arrow.r.long, t: u) B]$ in degrees $0$ and $1$. Choose injective resolutions $A -> I^bullet$ and $B -> J^bullet$. By the dual Comparison Theorem (@thm:the-comparison-theorem) $u$ extends to a cochain map $f^bullet colon I^bullet -> J^bullet$, and totalizing the resulting two-column double complex gives
$ T^n=I^n plus.o J^(n-1), quad d_T^n=mat(d_I^n,0;f^n,-d_J^(n-1)) $
The resolution maps induce a cochain map $K^bullet -> T^bullet$. In the degreewise split short exact sequence
$0 -> shift(J^bullet,-1) -> T^bullet -> I^bullet -> 0, $
the connecting morphism $H^0 (I^bullet) -> H^0 (J^bullet)$ identifies with $u$. Hence $H^0 (T^bullet) iso Ker (u)$, $H^1 (T^bullet) iso coker (u)$, and all other cohomology vanishes. Thus $K^bullet -> T^bullet$ is a quasi-isomorphism, and every $T^n$ is injective.

For a general bounded-below complex, choose a degree $m$ below which $K^bullet$ vanishes. Starting in degree $m$, one constructs an injective replacement upward, at each stage embedding a suitable cokernel into an injective object. The lower bound gives this induction a starting point; for a complex unbounded below, this particular construction has none.

The lower bound enters a second time in the computation of derived morphisms. Every cochain map from an acyclic complex to a bounded-below complex of injectives is null-homotopic. The homotopy is constructed upward, again using injectivity at each stage. This is why morphisms into the replacement may be computed up to homotopy, as in @thm:injective-model.

For an unbounded complex of injectives, this null-homotopy property need not hold: injectivity of the individual terms is insufficient. A complex satisfying it is called K-injective, and K-injective replacements provide the corresponding method in the unbounded setting when they exist. The bounded-below theorem suffices for every derived-functor and derived-Hom construction in this chapter.
]

// #rmrk(title: "Where the bounded-below hypothesis comes from")[
// // The hypothesis is not a technical convenience. A complex of injectives is built degree by degree upward: having produced $I^bullet$ in degrees below $n$ together with a map from $K^bullet$, one embeds a suitable cokernel into an injective object and obtains $I^n$. The induction therefore needs a lowest degree at which to begin, and a complex unbounded below offers none. The same hypothesis makes the second statement of @thm:injective-model work, since it is proved by an induction of the same shape.

// // The bounded-below case suffices for every derived-functor and derived-Hom construction in this chapter. The unbounded derived category requires K-injective resolutions in place of injective ones; we shall not need them.
// For a bounded-below complex, the construction of an injective replacement can start at the lowest nonzero degree and proceed upward. The same boundedness assumption ensures that a bounded-below complex of injectives computes derived morphisms as in @thm:injective-model. For an unbounded complex, injectivity of the individual terms alone does not guarantee this property, and one uses K-injective replacements. However, the bounded-below theorem suffices for the constructions in this chapter.
// ]

The three categories of this chapter, and the shortcut between the two ends, may be displayed at once.

#figure(
  diagram(
    spacing: 1.7cm,
    node((0, 0), $Cx^+(cA)$),
    node((1.7, 0), $Kcat^+(cA)$),
    node((3.4, 0), $Dp(cA)$),
    node((1.7, 1.3), $Kcat^+(op("Inj") cA)$),
    edge((0, 0), (1.7, 0), "->", label: $"identify homotopic maps"$),
    edge((1.7, 0), (3.4, 0), "->", label: $Q$),
    edge((1.7, 1.3), (1.7, 0), "->"),
    edge((1.7, 1.3), (3.4, 0), "->", label: $iso$, label-side: right),
  ),
  caption: [The long route and the shortcut. Objects are unchanged along the top row; only the morphisms change. The injective model identifies the bottom vertex with the right-hand one, so a derived morphism may be computed as a homotopy class of chain maps.]
)

To see how the theorem removes roofs, choose a replacement $j_L : L^bullet -> I_L^bullet$. A roof from $K^bullet$ to $L^bullet$ determines a unique homotopy class of maps $g : K^bullet -> I_L^bullet$ satisfying $g s tilde j_L a$:

#figure(
  diagram(
    spacing: 1cm,
    node((1.5, 0), $X^bullet$),
    node((0, 1.1), $K^bullet$),
    node((3, 1.1), $L^bullet$),
    node((3, 2.2), $I_L^bullet$),
    edge((1.5, 0), (0, 1.1), "->", label: $s$, label-side: left),
    edge((1.5, 0), (3, 1.1), "->", label: $a$),
    edge((3, 1.1), (3, 2.2), "->", label: $j_L$, label-side: right),
    edge((0, 1.1), (3, 2.2), "->", label: $g$, bend: -18deg),
  ),
  caption: [A roof becomes an ordinary map after the target is replaced by a complex of injectives.]
)

Thus, for $K,L in Dp(cA)$ and an injective replacement $L -> I_L^bullet$,
$ Hom_(Dp(cA))(K,L) iso Hom_(Kcat^+(cA))(K^bullet,I_L^bullet). $
The left-hand side is intrinsic; the right-hand side is the form used in calculations.


== Derived functors<sec:derived-functors>

In @chap:homological-algebra, the classical right derived functors of a left-exact additive functor
$F colon cA -> cB
$
were defined term-by-term
$R^n F(A) := H^n (F(I^bullet)),
$
The derived category retains the entire complex $F(I^bullet)$ rather than only its individual cohomology objects, and allows the input itself to be a complex.

The same distinction between an implementation and its interface applies here. An injective resolution is an implementation of the derived functor: one chooses $A -> I^bullet$, applies $F$, and computes. The interface is the resulting object $R F(A)$, characterised up to canonical isomorphism and independent of the chosen resolution. Later arguments may use that interface without reopening the particular resolution that produced it, as the triangle axioms of @def:triangulated-category are used without reopening the cone construction behind them.

// TODO: לקצר - להחליט מה הכרחי כאן ומה מיותר
An additive functor acts termwise on complexes:
$
  F(A^bullet)^n := F(A^n),
  quad
  d_(F(A))^n := F(d_A^n).
$
The functor also acts termwise on cochain maps. Additivity carries a homotopy identity $f-g=d h+h d$ to $F(f)-F(g)=F(d)F(h)+F(h)F(d)$, so homotopic maps remain homotopic. It also preserves shifts and finite biproducts, and the cone differential gives a natural identification $F(op("Cone")(f)) approx op("Cone")(F(f))$. Thus termwise application induces a triangulated functor $F:op("K")^+(cal(A)) -> op("K")^+(cal(B))$.

In general, however, it does not descend directly to the derived categories. A non-exact functor need not preserve quasi-isomorphisms, so applying $F$ to an arbitrary representative of a derived object is not well defined. The injective model (@sec:injective-model) resolves this problem: first replace the complex by an injective representative, and only then apply $F$.

#exmp(title: "A functor that destroys a quasi-isomorphism")[
Let $cA = Ab$ and let $F = Hom_ZZ (ZZ \/ 2 ZZ,-)$, which is additive and left exact. Consider the complex
$P^bullet := [ZZ ->^2 ZZ] $
in degrees $-1$ and $0$. This is the projective resolution of $ZZ\/2ZZ$ used in
@ex:cyclic-extension-ext, now regarded as an object of $Cx (Ab)$. Since multiplication by $2$ is injective with cokernel $ZZ \/ 2 ZZ$, the reduction map
$P^bullet -> placed(ZZ \/ 2 ZZ, 0) $
is a quasi-isomorphism. Applying $F$ termwise gives $Hom_ZZ (ZZ \/ 2 ZZ,ZZ) = 0$ in both degrees, so $F(P^bullet) = 0$, while $F(placed(ZZ \/ 2 ZZ, 0)) = placed(ZZ \/ 2 ZZ, 0)$. The induced map
$ 0 -> placed(ZZ \/ 2 ZZ, 0) $
is not a quasi-isomorphism. Two representatives of one object of $Dp(Ab)$ therefore have non-isomorphic images under $F$, and $F$ cannot descend to $Dp(Ab)$ as it stands.
]
<exmp:functor-destroys-qis>

The injective replacement theorem solves this problem by restricting the calculation to representatives on which quasi-isomorphisms have already become homotopy equivalences.

#def(title: "Right derived functor")[
Let $F : cA -> cB$ be an additive functor, and assume that $cA$ has enough injectives. For $K in Dp(cA)$, choose an injective replacement
$K^bullet -> I_K^bullet. $
The *right derived functor* of $F$ is defined by
$R F(K) := F(I_K^bullet) $
as an object of $Dp(cB)$.
]
<def:right-derived-functor>

A morphism $u : K -> L$ in $Dp(cA)$ need not be represented by a chain map between the initially chosen complexes. Under @thm:injective-model, it is represented by a homotopy class of actual chain maps
$I_u : I_K^bullet -> I_L^bullet $
between injective replacements. This middle horizontal arrow is the chain-level morphism to which $F$ is applied.


#figure(
  diagram(
    spacing: (1.15cm, 1cm),

    node((0, 0), $K$),
    node((2, 0), $L$),

    node((0, 1.4), $I_K^bullet$),
    node((2, 1.4), $I_L^bullet$),

    node((0, 2.8), $underbrace(F(I_K^bullet), := R F(K))$),
    node((2, 2.8), $underbrace(F(I_L^bullet), :=R F(L) )$),

    edge((0, 0), (2, 0), "->", label: $u$),

    edge((0, 0), (0, 1.4), "->", label: $"qis"$, label-side: right),
    edge((2, 0), (2, 1.4), "->", label: $"qis"$),

    edge((0, 1.4), (2, 1.4), "->", label: $I_u$),

    edge((0, 1.4), (0, 2.8), "-->", label: $F$, label-side: right),
    edge((2, 1.4), (2, 2.8), "-->", label: $F$),

    edge((0, 2.8), (2, 2.8), "->", label: $R F(u) eq F(I_u)$),
  )
)


#thm(title: "Basic properties of the right derived functor")[
The object $R F(K)$ is independent of the chosen injective replacement up to a natural isomorphism. The construction on objects and on the chain maps $I_u$ defines a functor
$ R F : Dp(cA) -> Dp(cB), $
and this functor is triangulated.
]
<thm:properties-right-derived>

#proof()[
The equivalence $Kcat^+(op("Inj") cA) equiv Dp(cA)$ identifies different injective replacements in the homotopy category. Since an additive functor preserves homotopies, shifts, finite direct sums, and cone differentials, termwise application of $F$ is triangulated on injective representatives. Transport across the equivalence proves all three assertions.
]

The definition applies to an additive functor without assuming left exactness. Left exactness is needed when the derived object is compared with the classical right derived functors (@def:classical-right-derived-functors).

#prop(title: "Recovery of the classical derived functors")[
Let $F : cA -> cB$ be additive and left exact, and let $A in cA$ be regarded as a complex concentrated in degree $0$. Then, for every $n >= 0$,
$ H^n (R F(A)) iso R^n F(A). $
Moreover, $H^n (R F(A)) = 0$ for $n < 0$, and $H^0 (R F(A)) iso F(A)$.
]
<prop:derived-recovers-classical>

#proof()[
Choose an injective resolution $0 -> A -> I^0 -> I^1 -> dots$, with $I^bullet$ concentrated in nonnegative degrees. It is an injective replacement of $A[0]$, so $R F(A)$ is represented by $F(I^bullet)$. By the classical definition, $H^n(F(I^bullet))=R^n F(A)$ for $n>=0$, while the absence of negative terms gives $H^n(R F(A))=0$ for $n<0$. Finally, left exactness gives the exact sequence $0 -> F(A) -> F(I^0) -> F(I^1)$, so $H^0(F(I^bullet))=ker(F(I^0) -> F(I^1)) tilde.equiv F(A)$.
]

Derived functors compose under an additional acyclicity hypothesis. Let $cB$ have enough injectives, let
$F : cA -> cB, quad G : cB -> cC $
be left-exact additive functors, and assume that $F(I)$ is $G$-acyclic for every injective object $I in cA$. Then the canonical comparison morphism is an isomorphism
$ R(G compose F) iso R G compose R F.$
The individual derived functors are obtained by applying cohomology after this comparison. See @Dimca2004[Props. 1.3.18--1.3.19].


Derived functors also preserve the triangle formalism. If
$ A -> B -> C -> shift(A,1) $
is a distinguished triangle, then so is
$ R F(A) -> R F(B) -> R F(C) -> shift(R F(A),1). $
Applying cohomology produces the long exact sequence of the classical derived functors when $A,B,C$ are objects of the original abelian category.

Later chapters will apply the same derived-functor construction to sheaf functors such as $Gamma$, $f_*$, and $f_!$. Their derived versions will be introduced only after the underlying sheaf functors have been defined. The next section treats derived Hom directly in an abstract abelian category.
// The general form of "adapted" is the $F$-injective subcategory of @KashiwaraSchapira1990[Def. I.8.2, Prop. I.8.3] and @HTT2008[Def. B.5.4]; @Goresky2026[Appendix A.26--A.28] gives the sheaf-theoretic instances.

#rmrk(title: "Boundedness")[
The construction above naturally defines $R F : Dp(cA) -> Dp(cB)$. It does not automatically restrict to $Db(cA) -> Db(cB)$: the higher cohomology objects of $R F(K)$ may remain nonzero in arbitrarily high degrees. A bounded restriction requires a separate finite-cohomological-dimension or boundedness theorem for the particular functor. Such hypotheses will be stated when the sheaf operations are introduced; the relevant finiteness is the cohomological dimension of @Dimca2004[§3.1].
]
=== Derived Hom <sec:derived-hom>

The Hom complex was constructed in @chap:homological-algebra (@def:hom-complex). Its differential compares a degree-shifted family of maps with the differentials of the source and target complexes. The cocycle condition is therefore the chain-map condition into a shift, while a coboundary gives a null-homotopic map. The following lemma states this interpretation in the homotopy category.

#lem(title: "The Hom complex computes homotopy classes", label: <lem:hom-complex-homotopy-classes>)[
For all $K^bullet,L^bullet in Cx(cA)$ and every $n in ZZ$, $H^n (Hom_cA^bullet (K^bullet,L^bullet)) iso Hom_(Kcat(cA)) (K^bullet,shift(L^bullet,n))$.
]

#proof[
A degree-$n$ cocycle is a family $phi=(phi^p)_p$ satisfying $d_L^(p+n) compose phi^p=(-1)^n phi^(p+1) compose d_K^p$. This is the condition that $phi$ define a morphism of complexes $K^bullet -> shift(L^bullet,n)$. A degree-$n$ coboundary is a null-homotopic such morphism. Passing from cocycles to cohomology therefore passes from morphisms into the shift to their homotopy classes. See @Goresky2026[Lemma A.15] and @Dimca2004[Lemma 1.4.1].
]

The passage from homotopy classes to derived morphisms still requires inversion of quasi-isomorphisms. To obtain a construction intrinsic to the derived category, we replace the second variable by the injective model.

#def(title: "Derived Hom", label: <def:derived-hom>)[
Assume that $cA$ has enough injectives. Let $K in Db(cA)$ and $L in Dp(cA)$. Choose a bounded representative $K^bullet$ of $K$ and an injective replacement $L -> I_L^bullet$. Define $RHom_cA (K,L):=Hom_cA^bullet (K^bullet,I_L^bullet)$ as an object of $D(Ab)$.
]

Note that the second variable must be bounded below because that is where @thm:injective-model applies. The first variable is restricted so that each group
$ Hom_cA^n (K^bullet,I_L^bullet) = product_p Hom_cA (K^p,I_L^(p + n)) $
has only finitely many nonzero factors; with $K^bullet$ bounded and $I_L^bullet$ bounded below, all but finitely many indices $p$ give a zero factor, so the product is a finite direct sum and no convergence question arises. Bounded above would in fact suffice, and the natural domain of the bifunctor is $Dm(cA)^(op("op")) times Dp(cA)$, as in @Dimca2004[§1.4] and @KashiwaraSchapira1990[Example I.10.11]. Since $Db(cA) subset.eq Dm(cA)$, the definition above is a restriction of that bifunctor and not a different construction.

#thm(title: "Derived Hom represents shifted derived morphisms")[
The object $RHom_cA (K,L)$ is independent, up to natural isomorphism, of the chosen representatives. For every $n in ZZ$, there is a natural isomorphism
$ H^n (RHom_cA(K,L)) iso Hom_(D(cA))(K,shift(L,n)). $
]
<thm:derived-hom-represents>

#proof[
The Hom-complex interpretation (@lem:hom-complex-homotopy-classes) gives $H^n (Hom_cA^bullet (K^bullet,I_L^bullet)) iso Hom_(Kcat(cA)) (K^bullet,shift(I_L^bullet,n))$. The injective model (@thm:injective-model) identifies the latter group with $Hom_(D(cA)) (K,shift(L,n))$.

The same calculation proves independence of the representatives. If $q : K'^bullet -> K^bullet$ is a quasi-isomorphism between bounded representatives, precomposition induces
$ Hom_cA^bullet (K^bullet,I_L^bullet) -> Hom_cA^bullet (K'^bullet,I_L^bullet) $
By the isomorphism, this map induces an isomorphism on every cohomology group and is therefore a quasi-isomorphism. Zigzags of quasi-isomorphisms give the same conclusion for (arbitrary) bounded representatives.

If $I_L^bullet$ and $J_L^bullet$ are injective replacements of $L$, @thm:injective-model identifies them with the same object of $Dp(cA)$ and hence with each other in $Kcat^+(op("Inj") cA)$. A representing homotopy equivalence induces a homotopy equivalence
$ Hom_cA^bullet (K^bullet,I_L^bullet) -> Hom_cA^bullet (K^bullet,J_L^bullet). $
Thus $RHom_cA (K,L)$ is independent of both choices. See @Weibel1994[Chapter 10] and @KashiwaraSchapira1990[Example I.10.11].
]

#cor(title: "Ext as morphisms in the derived category", label: <cor:ext-derived-morphisms>)[
For objects $A,B in cA$ and every $n>=0$, $Ext_cA^n (A,B) iso H^n (RHom_cA (A,B)) iso Hom_(D(cA)) (A,shift(B,n))$.
]

#proof[
Choose an injective resolution $B -> I^bullet$. The Ext calculation (@sec:tor-ext) gives $Ext_cA^n (A,B)=Ker (d_H^n)\/im (d_H^(n-1))$, where $d_H^q (phi)=d_I^q compose phi$. An element of $Ker (d_H^n)$ is therefore a map $phi colon A -> I^n$ satisfying $d_I^n compose phi=0$. Since $A$ is concentrated in degree $0$, this is a morphism of complexes $placed(A,0) -> shift(I^bullet,n)$. Replacing $phi$ by $phi+d_I^(n-1) compose h$ changes this chain map by a null-homotopy, so passing to the quotient by $im (d_H^(n-1))$ gives its homotopy class. The injective model (@thm:injective-model) identifies these homotopy classes with $Hom_(D(cA)) (A,shift(B,n))$.
]


The nonzero class of @ex:cyclic-extension-ext determines the connecting morphism
$delta:ZZ\/2ZZ -> shift(ZZ\/2ZZ,1)
$
in the distinguished triangle associated with
$0 -> ZZ\/2ZZ -> ZZ\/4ZZ -> ZZ\/2ZZ -> 0.
$
By @cor:ext-derived-morphisms, this degree-$1$ morphism is precisely the corresponding element of
$
Ext_Ab^1(ZZ\/2ZZ,ZZ\/2ZZ).
$


#align(center)[
  #diagram(
    spacing: 1cm,
    node((0, 0), $ZZ \/ 2 ZZ$),
    node((2.2, 0), $ZZ \/ 4 ZZ$),
    node((1.1, 1.55), $ZZ \/ 2 ZZ$),
    edge((0, 0), (2.2, 0), "->", label: $iota$),
    edge((2.2, 0), (1.1, 1.55), "->", label: $pi$),
    edge((1.1, 1.55), (0, 0), "->", label: $delta$, label-side: left),
    node((0.18, 0.82), text(size: 8pt)[$[1]$]),
  )
]

The label $[1]$ on the returning edge indicates that its actual target is $shift(ZZ \/ 2 ZZ,1)$. Thus $delta$ is a degree-$1$ derived morphism, and the Ext interpretation (@cor:ext-derived-morphisms) identifies it with the class of the extension. See @BBD1982[1.1.8].

#exmp(title: "A complete derived-Hom calculation", label: <ex:derived-hom-z2>)[
In $Ab$, the divisible group $QQ \/ ZZ$ is injective, and
$0 -> ZZ \/ 2 ZZ -> QQ \/ ZZ ->^2 QQ \/ ZZ -> 0 $
is an injective resolution of $ZZ \/ 2 ZZ$. Applying $Hom_ZZ (ZZ \/ 2 ZZ,-)$ gives
$Hom_ZZ (ZZ \/ 2 ZZ,QQ \/ ZZ) iso ZZ \/ 2 ZZ. $
Multiplication by $2$ induces the zero map on this group, so
$RHom_Ab (ZZ \/ 2 ZZ,ZZ \/ 2 ZZ) $
is represented by
$[ZZ \/ 2 ZZ ->^0 ZZ \/ 2 ZZ] $
in degrees $0$ and $1$. Therefore
$ Ext_Ab^0(ZZ \/ 2 ZZ,ZZ \/ 2 ZZ) iso ZZ \/ 2 ZZ, quad Ext_Ab^1(ZZ \/ 2 ZZ,ZZ \/ 2 ZZ) iso ZZ \/ 2 ZZ, $
and $Ext_Ab^n (ZZ \/ 2 ZZ,ZZ \/ 2 ZZ)=0$ for $n>=2$.
]

The object $RHom_cA (K,L)$ is the external derived Hom: its value is a complex of abelian groups.

== Canonical truncations <sec:canonical-truncations>

The derived category keeps all cohomological degrees available at once. We now need a controlled way to separate a derived object into a lower and an upper range of degrees. Deleting terms at a chosen boundary can change the cohomology there, because the incoming and outgoing differentials still contribute to its kernel and image. Canonical truncation uses the relevant kernel or cokernel at the boundary and therefore preserves the cohomology on the selected side of the cut.

#def(title: "Canonical truncations")[
Let $K^bullet$ be a cohomological complex in $cA$, and let $n in ZZ$. Define the *canonical truncation from above* by
$ (tle(n) K)^i := cases(K^i & i < n, Ker(d_K^n) & i = n, 0 & i > n). $
Its differential agrees with $d_K$ below degree $n - 1$, and the final differential is the factorization $K^(n - 1) -> Ker(d_K^n)$ of $d_K^(n - 1)$.

Define the *canonical truncation from below* by
$ (tge(n) K)^i := cases(0 & i < n, coker(d_K^(n - 1)) & i = n, K^i & i > n). $
Its first differential is the morphism $coker(d_K^(n - 1)) -> K^(n + 1)$ induced by $d_K^n$.
]
<def:canonical-truncations>
Graphic, those cumbersome definitions are pretty simple:

#figure(
  diagram(
    spacing: 1.45cm,
    node((0, 0), $dots.c$),
    node((1.3, 0), $K^(n - 1)$),
    node((2.9, 0), $Ker(d_K^n)$),
    node((4.2, 0), $0$),
    node((0, 1.3), $dots.c$),
    node((1.3, 1.3), $K^(n - 1)$),
    node((2.9, 1.3), $K^n$),
    node((4.2, 1.3), $K^(n + 1)$),
    edge((0, 0), (1.3, 0), "->"),
    edge((1.3, 0), (2.9, 0), "->"),
    edge((2.9, 0), (4.2, 0), "->"),
    edge((0, 1.3), (1.3, 1.3), "->"),
    edge((1.3, 1.3), (2.9, 1.3), "->", label: $d_K^(n - 1)$),
    edge((2.9, 1.3), (4.2, 1.3), "->", label: $d_K^n$),
    edge((1.3, 0), (1.3, 1.3), "->", label: $id$),
    edge((2.9, 0), (2.9, 1.3), "->"),
    edge((4.2, 0), (4.2, 1.3), "->"),
  ),
  caption: [The natural inclusion $tle(n) K -> K$.]
)

#figure(
  diagram(
    spacing: 1.45cm,
    node((0, 0), $K^(n - 1)$),
    node((1.6, 0), $K^n$),
    node((3.2, 0), $K^(n + 1)$),
    node((4.5, 0), $dots.c$),
    node((0, 1.3), $0$),
    node((1.6, 1.3), $coker(d_K^(n - 1))$),
    node((3.2, 1.3), $K^(n + 1)$),
    node((4.5, 1.3), $dots.c$),
    edge((0, 0), (1.6, 0), "->", label: $d_K^(n - 1)$),
    edge((1.6, 0), (3.2, 0), "->", label: $d_K^n$),
    edge((3.2, 0), (4.5, 0), "->"),
    edge((0, 1.3), (1.6, 1.3), "->"),
    edge((1.6, 1.3), (3.2, 1.3), "->"),
    edge((3.2, 1.3), (4.5, 1.3), "->"),
    edge((0, 0), (0, 1.3), "->"),
    edge((1.6, 0), (1.6, 1.3), "->"),
    edge((3.2, 0), (3.2, 1.3), "->", label: $id$),
    edge((4.5, 0), (4.5, 1.3), "->"),
  ),
  caption: [The natural projection $K -> tge(n) K$.]
)

#prop(title: "Cohomology and the truncation triangle")[
Canonical truncations preserve quasi-isomorphisms and therefore define functors on $D(cA)$. Their cohomology is
$ H^i (tle(n) K) iso cases(H^i (K) & i <= n, 0 & i > n), $
$ H^i (tge(n) K) iso cases(0 & i < n, H^i (K) & i >= n). $
Moreover, the natural morphisms extend to a canonical distinguished triangle
$ tle(n) K -> K -> tge(n + 1) K -> shift(tle(n) K,1). $
]
<prop:canonical-truncation-properties>

#proofsketch()[
The definitions change the complex only at the boundary degree, where the kernel and cokernel preserve the appropriate cohomology. The displayed formulas follow directly, and they imply that a quasi-isomorphism $K^bullet -> L^bullet$ induces quasi-isomorphisms on both truncations, so the functors descend to $D(cA)$.
 
Finally, the cone of $tle(n) K -> K$ is naturally quasi-isomorphic to $tge(n + 1) K$, which gives the distinguished triangle. See @Dimca2004[Def. 1.1.14 with Remark 1.1.15], @Goresky2026[§19.1], and @KashiwaraSchapira1990[(I.3.10)--(I.3.11), Prop. I.3.7].
]

The content of the proposition is best seen degreewise. Each row below lists the cohomology of one of the three complexes in the triangle; the triangle says that the middle row is assembled from the other two, with the boundary degree $n$ falling entirely to the left.

#figure(
  table(
    columns: 6,
    align: center,
    inset: 6pt,
    stroke: 0.6pt,

    table.header(
      [*degree*], [$dots.c$], [$n - 1$], [$n$], [$n + 1$], [$dots.c$],
    ),

    [$tle(n) K$], [$dots.c$], [$H^(n - 1)(K)$], [$H^n (K)$], [$0$], [$0$],

    [$K$], [$dots.c$], [$H^(n - 1)(K)$], [$H^n (K)$], [$H^(n + 1)(K)$], [$dots.c$],

    [$tge(n + 1) K$], [$0$], [$0$], [$0$], [$H^(n + 1)(K)$], [$dots.c$],
  ),
  caption: [
    Cohomology of the truncation triangle
    $tle(n) K -> K -> tge(n + 1) K -> shift(tle(n) K,1)$.
    The two truncations partition the cohomology of $K$ at the cut between degrees
    $n$ and $n + 1$; no degree is lost and none is counted twice.
  ],
)

// #exmp(title: "Truncating the two-term complex of an automorphism")[
// For the recurring complex
// $ K_T = [V ->^(T - id_V) V] $
// concentrated in degrees $0$ and $1$, the two truncations at $n = 0$ are
// $ tle(0) K_T = placed(Ker(T - id_V), 0), quad tge(1) K_T = placed(coker(T - id_V), 1), $
// so the canonical triangle of @prop:canonical-truncation-properties reads
// $ placed(Ker(T - id_V), 0) -> K_T -> placed(coker(T - id_V), 1) -> shift(placed(Ker(T - id_V), 0),1). $
// It separates the invariant vectors from the obstruction space. It does not assert a canonical direct-sum decomposition of $K_T$: the triangle is split precisely when its connecting morphism vanishes, and by @cor:ext-derived-morphisms that morphism is an element of $Ext_cA^1(coker(T - id_V),Ker(T - id_V))$, which need not be zero.
// ]
// <exmp:truncation-monodromy>




Canonical truncation divides a derived object into a part with cohomology in low degrees and a part with cohomology in high degrees. The definition of a $t$-structure isolates the categorical properties that make such a division possible without referring to an underlying complex. This is needed because later the relevant notion of being concentrated in degree $0$ will not be the standard one.

#def(title: "t-structure")[
Let $cal(T)$ be a triangulated category. A *$t$-structure* on $cal(T)$ is a pair of full subcategories $(cal(T)^(<= 0),cal(T)^(>= 0))$, closed under isomorphisms, such that:

- $shift(cal(T)^(<= 0),1) subset.eq cal(T)^(<= 0)$ and $shift(cal(T)^(>= 0),-1) subset.eq cal(T)^(>= 0)$;
- $Hom_(cal(T))(A,B) = 0$ whenever $A in cal(T)^(<= 0)$ and $B in cal(T)^(>= 1)$, where $cal(T)^(>= 1) := shift(cal(T)^(>= 0),-1)$;
- for every $K in cal(T)$, there is a distinguished triangle
$ A -> K -> B -> shift(A,1) $
with $A in cal(T)^(<= 0)$ and $B in cal(T)^(>= 1)$.

For $n in ZZ$, set $cal(T)^(<= n) := shift(cal(T)^(<= 0),-n)$ and $cal(T)^(>= n) := shift(cal(T)^(>= 0),-n)$.
]
<def:t-structure>

The axioms have this shape since the two truncation functors attached to a $t$-structure are adjoint to the inclusions, and the decomposition triangle is unique up to unique isomorphism - see @BBD1982[1.3.3].

The first condition makes the two classes stable in the expected directions. The second says that the lower and upper parts do not admit morphisms across a positive degree gap. The third says that every object can actually be decomposed into such parts by a distinguished triangle.

We shall use the following notation throughout: $cal(H)$ denotes the heart, defined below, and for the standard $t$-structure the truncation functors of @def:canonical-truncations are the ones realizing the third axiom. //might ne problematic with the next chapter

#thm(title: "The standard t-structure")[
Define
$ Dle(0)(cA) := {K in D(cA) mid(|) H^i (K) = 0 " for every " i > 0}, $
$ Dge(0)(cA) := {K in D(cA) mid(|) H^i (K) = 0 " for every " i < 0}. $
Then $(Dle(0)(cA),Dge(0)(cA))$ is a $t$-structure on $D(cA)$ and on its bounded variants. It is called the *standard $t$-structure*.
]
<thm:standard-t-structure>

#proof()[
The shift conditions follow from @prop:cohomology-of-a-shift. The decomposition axiom is the canonical triangle
$ tle(0) K -> K -> tge(1) K -> shift(tle(0) K,1) $
of @prop:canonical-truncation-properties, whose first term lies in $Dle(0)(cA)$ and whose third lies in $Dge(1)(cA)$, again by that proposition.

For orthogonality, let $A in Dle(0)(cA)$, let $B in Dge(1)(cA)$, and let $f : A -> B$ be a morphism in $D(cA)$. Since $tle(0)$ is a functor on $D(cA)$ and the morphisms $epsilon_X : tle(0) X -> X$ are natural, the square
$ tle(0) A ->^(tle(0) f) tle(0) B, quad epsilon_A : tle(0) A -> A, quad epsilon_B : tle(0) B -> B $
commutes, that is, $f compose epsilon_A = epsilon_B compose tle(0) f$. Now $epsilon_A$ is an isomorphism: it induces an isomorphism on $H^i$ for $i <= 0$ by @prop:canonical-truncation-properties, and for $i > 0$ both sides vanish because $A in Dle(0)(cA)$, so @prop:cohomology-detects-derived-isomorphisms applies. On the other side, $B in Dge(1)(cA)$ gives $H^i(B) = 0$ for $i <= 0$, hence $H^i(tle(0) B) = 0$ for every $i$, so $tle(0) B$ is acyclic and therefore zero in $D(cA)$ by @prop:acyclic-vanish-derived. Consequently $f compose epsilon_A = 0$, and since $epsilon_A$ is invertible, $f = 0$.
]

see @Dimca2004[Example 5.1.3] and @HTT2008[Example 8.1.2].
After cones, roofs, and localizations, the category finally acquires a heart. We are almost in Oz.
#def(title: "Heart of a t-structure")[
The *heart* of a $t$-structure is the full subcategory
$ cal(H)^heart  := cal(T)^(<= 0) sect cal(T)^(>= 0). $
]
<def:heart>

An object of the heart is regarded as concentrated in degree $0$ relative to the chosen $t$-structure. The meaning of “degree $0$” therefore depends on the $t$-structure, not only on the triangulated category.

For the standard $t$-structure the intersection can be drawn. Each row records in which degrees an object of the indicated class is permitted to have nonzero cohomology.

#figure(
  table(
    columns: (auto, auto, auto, auto, auto, auto),
    align: center,
    inset: 6pt,
    stroke: (x, y) => if y == 1 { 0.9pt } else { 0.6pt },

    table.header(
      [*degree*], [$dots.c$], [$-1$], [$0$], [$1$], [$dots.c$],
    ),

    [$Dle(0)(cA)$], [$H^(-2)$], [$H^(-1)$], [$H^0$], [$0$], [$0$],

    [$Dge(0)(cA)$], [$0$], [$0$], [$H^0$], [$H^1$], [$H^2$],

    [$cal(H)^heart$], [$0$], [$0$], [$H^0$], [$0$], [$0$],
  ),
  caption: [
    The heart of the standard $t$-structure, as the overlap of the two classes.
    Only degree $0$ survives both conditions, and @prop:standard-heart identifies
    what survives with $cA$ itself. A different $t$-structure moves both boundaries
    at once, and the surviving column is then a different abelian category inside
    the same triangulated one.
  ],
)

#thm(title: "The heart is abelian")[
The heart of every $t$-structure is an abelian category. Its short exact sequences are precisely the sequences
$ 0 -> A -> B -> C -> 0 $
whose two internal morphisms can be completed to a distinguished triangle
$ A -> B -> C -> shift(A,1) $
in the ambient triangulated category.
]
<thm:heart-abelian>
//maybe a bit elaborate?
Given $f colon X -> Y$ in $cal(H)^heart$, complete it to a distinguished triangle with third vertex $Z$. Then $Z in cal(T)^(<= 0) inter cal(T)^(>= -1), $ and truncation gives
$ Ker(f) iso tle(0)(shift(Z,-1)), quad coker(f) iso tge(0) Z $
Hence kernels and cokernels in the heart are obtained from cones by truncation. See @BBD1982[1.2.2--1.2.5, Théorème 1.3.6], @KashiwaraSchapira1990[Prop. X.1.11], and @HTT2008[Thm. 8.1.9].

#prop(title: "The standard heart")[
The heart of the standard $t$-structure on $D(cA)$ is equivalent to $cA$. The equivalence is induced by $H^0$, and its quasi-inverse sends an object $A in cA$ to the complex concentrated in degree $0$ with value $A$.
]
<prop:standard-heart>

#proof()[
An object $K$ belongs to the standard heart when $H^i (K) = 0$ for every $i != 0$. For such a $K$, apply @prop:canonical-truncation-properties twice. The morphism $tle(0) K -> K$ is an isomorphism in every cohomological degree, hence an isomorphism in $D(cA)$ by @prop:cohomology-detects-derived-isomorphisms, and likewise for $tle(0) K -> tge(0) tle(0) K$. The composite functor $tge(0) tle(0)$ therefore carries $K$ to a complex concentrated in degree $0$ with value $H^0 (K)$, and the two natural morphisms give an isomorphism
$ K iso placed(H^0(K), 0) $
in $D(cA)$. Conversely, $placed(A, 0)$ has cohomology only in degree $0$ for every $A in cA$, so it lies in both $Dle(0)(cA)$ and $Dge(0)(cA)$. The two constructions are mutually inverse, and $H^0$ is fully faithful on the heart because it is inverse to a functor.
]


#pagebreak()
