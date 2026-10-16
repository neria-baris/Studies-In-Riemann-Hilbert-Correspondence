#import "../template/template.typ": *
#import "../template/macros.typ": *

// Shared local corrections and chapter notation (see Thesis.typ).
#let cohsh(n, K) = $cal(H)^(#n) (#K)$
#let vee = $or$
#let gray8(x) = text(8pt, fill: luma(110))[#x]
#let Dual = math.op("Dual")
#let Shk(X) = $op("Sh")(#X semi k)$

= The Riemann--Hilbert Correspondence <chap:riemann-hilbert>



Return to the Euler equation of @exmp:euler-monodromy
$ z u'(z)=alpha u(z) quad z in CC^times $
On $CC^times$ it determines a rank-one local system, but this local system alone does not determine an extension across the origin. A constructible extension may contain point-supported terms and morphisms attaching them to the generic local system. An extension of the corresponding differential module carries the analogous algebraic boundary data. Riemann--Hilbert identifies the two kinds of extension, together with their morphisms and extension classes.

Throughout, $X$ is a smooth complex algebraic variety of complex dimension $n$, and $X^"an"$ is its associated complex manifold. All coefficients are $CC$. The source is $D_"rh"^b (DX(X))$, defined in @sec:regularity-and-rh-class, and the target is the algebraically constructible category $Dbc(X^"an")$. We follow @HTT2008[§7.2]; the recollement and simple-perverse-object results used below are from @BBD1982[§1.4 and §4.3].

The proof uses three external results: Deligne's equivalence between regular algebraic connections and analytic local systems, compatibility of de Rham with the geometric operations used below, and constructibility and perversity of the normalised solution complex of a holonomic module. See @HTT2008[Chs. 4--7].


== The de Rham complex<sec:rh-de-rham>

The solution functor of @chap:solution-narrative is contravariant. We instead use the covariant normalised de Rham functor $DR_X$ of @def:de-rham-complex. For a bounded complex of left $DX(X)$-modules, it is obtained by totalising the de Rham complexes and shifting by $[n]$. This shift places a local system on a smooth $n$-dimensional stratum in perverse degree zero.

For an integrable connection $cE$ with horizontal local system $cL$, the holomorphic Poincaré lemma gives
$ DR_X(cE) iso shift(cL,n) $
Conversely, Deligne's theorem associates a unique regular algebraic integrable connection to every finite-rank local system on $X^"an"$; see @HTT2008[Thm. 5.3.8 and Cor. 5.3.10].


#exmp(title: "The Euler equation as the smooth model")[
For the Euler module $cM_alpha := DX(CC^times) \/ DX(CC^times) (z partial_z-alpha)$, the calculation of @exmp:euler-monodromy gives
$ Sol_(CC^times) (cM_alpha) iso cL_lambda, quad lambda := exp (2 pi i alpha). $
The de Rham complex uses the connection carried by the module itself. If $e=[1]$, then the relation $z partial_z e=alpha e$ gives
$ partial_z e=(alpha/z)e $
A local section $f e$ is therefore horizontal exactly when
$ d f+alpha f (d z)/z=0 $
Its monodromy is $lambda^(-1)$, and hence
$ DR_(CC^times) (cM_alpha) iso shift(cL_(lambda^(-1)),1) $
The solution local system is the dual of this horizontal local system, which accounts for the inverse monodromy.
]
<exmp:rh-euler>

On $CC^times$, the local system determines the regular connection. On $CC$, the same generic local system admits several extensions unless boundary data are specified. The singular case therefore requires compatibility with the operations that extend and restrict objects across strata.

The de Rham and solution descriptions are related by the two dualities developed on the two sides. Write $Dual_(cal(D), X)$ for the differential duality of @thm:dmodule-duality-holonomic and retain $VDX(X^"an")$ for Verdier duality.

#prop(title: "de Rham, solutions, and duality")[
For $cM^bullet in D_"rh"^b (DX(X))$ there are natural isomorphisms
$ VDX(X^"an") (DR_X (cM^bullet)) iso DR_X (Dual_(cal(D), X) (cM^bullet)) $
and
$ shift(Sol_X (cM^bullet), n) iso VDX(X^"an") (DR_X (cM^bullet)). $
]
<prop:rh-dr-sol-duality>

#proof[
The first is the compatibility of de Rham with duality. The second follows from it together with the standard identity
$ DR_X (cN^bullet) iso shift(Sol_X (Dual_(cal(D), X) (cN^bullet)), n) $
applied to $cN^bullet = Dual_(cal(D), X) (cM^bullet)$, and biduality for regular holonomic complexes. See @HTT2008[Prop. 4.2.1, Cor. 4.6.5 and §7.1].
]


== Compatibility<sec:rh-compatibility>

The smooth equivalence does not determine how the translation behaves under direct image, extraordinary inverse image, external product, or duality. These operations move smooth data between strata and assemble singular objects. The comparison theorem asserts that each operation commutes with the de Rham translation.

A basic case is already familiar. Let $i_0:{0} into CC$ be the origin and let $V$ be a finite-dimensional vector space regarded as a differential module on the point. Differential direct image produces a module supported at the origin; for $V=CC$ this is the module $delta_0$ of @sec:weyl-modules. On the sheaf side, direct image of the local system $V$ on the point is the skyscraper sheaf $push(i_0,V)$. Compatibility predicts
$ DR_CC (dint(i_0) (V)) iso push(i_0,V). $
Nothing propagates away from the origin on either side. The theorem below says that this agreement persists for general morphisms and derived objects, including situations where the fibres and the singular boundary have nontrivial cohomology.

We write $dint(f)$ for the derived direct image of differential modules and $dpull(f)$ for the extraordinary inverse image; their transfer-bimodule constructions are not developed here. We also write $cM ⊠ cN$ for the external product.

=== The common geometric calculus <sec:rh-common-calculus>

#def(title: "Derived tensor product", label: <def:derived-tensor-sheaves>)[
For $K,L in Db(Shk(X))$, totalise the degreewise tensor product by
$ (K otL L)^n:=bds_(p+q = n) K^p times.o_k L^q, $
with differential
$ d (a times.o b) = d_K (a) times.o b + (-1)^p a times.o d_L (b) $
for $a in K^p$ and $b in L^q$. This defines the derived tensor product $K otL L$.
]

Because the coefficients form a field, tensor product of sheaves of $k$-vector spaces is exact, so no flat replacement is required here.

#lem(title: "Derived tensor--Hom adjunction", label: <lem:derived-tensor-hom-adjunction>)[
For $K,L in Db(Shk(X))$ and $M in Dp(Shk(X))$ there is a natural isomorphism
$ Hom_(Dp(Shk(X))) (K otL L,M) iso Hom_(Dp(Shk(X))) (K,RsHom_X (L,M)). $
]

The degreewise tensor--Hom adjunction respects the differentials of the two total complexes and gives the displayed derived adjunction; see @KashiwaraSchapira1990[Prop. 2.6.3].

#def(title: "External product", label: <def:external-product>)[
Let $p_X:X times Y->X$ and $p_Y:X times Y->Y$ be the projections. For $K in Db(Shk(X))$ and $L in Db(Shk(Y))$, define
$ K ⊠ L:=invimg(p_X,K) otL invimg(p_Y,L). $
]

The two inverse images place the objects on $X times Y$, where the tensor product combines them while retaining the two geometric variables.

#prop(title: "Internal exceptional adjunction", label: <prop:internal-exceptional-adjunction>)[
Let $f:X->Y$ satisfy the hypotheses of @thm:exceptional-inverse-image. For $K in Db(Shk(X))$ and $L in Dp(Shk(Y))$ there is a natural isomorphism
$ Rpush(f) (RsHom_X (K,ushr(f) (L))) iso RsHom_Y (Rpushc(f) (K),L). $
]

Taking derived global sections recovers $R f_! tack.l f^!$. The sheaf-valued identity is the relative adjunction used to convert a supported pullback along the diagonal into an internal Hom; see @KashiwaraSchapira1990[Prop. 3.1.10], @Dimca2004[Thm. 3.2.3], and @Iversen1986[§VII.5].

#table(
  columns: (1.35fr, 1.15fr, 1.25fr, 2.15fr),
  inset: 5pt,
  align: left,
  [*Geometric task*], [*$cal(D)$-modules*], [*Sheaves*], [*Use below*],
  [Move from $X$ to $Y$], [$dint(f)$], [$Rpush(f)$], [Insert a stratum and push to a point],
  [Read from $Y$ on $X$ with support], [$dpull(f)$], [$ushr(f)$], [Restrict the comparison to the diagonal],
  [Keep two variables separate], [$⊠$], [$⊠$], [Place the source test and target on $X times X$],
  [Reverse the first input], [$Dual_(cal(D), X)$], [$VDX(X^"an")$], [Turn the source into the dual input of $RHom$],
)

// For a map $f:X->Y$, both $dpull(f)$ and $ushr(f)$ run from objects on $Y$ to objects on $X$; this contravariant direction is why they occur at the diagonal $Delta:X->X times X$. The full-faithfulness calculation dualises the source, separates the two variables, pulls the result back to the diagonal, and pushes it to a point. On the two sides the corresponding chains are
// $ Dual_(cal(D), X) arrow.r.long ⊠ arrow.r.long dpull(Delta) arrow.r.long dint(p) $
// and
// $ VDX(X^"an") arrow.r.long ⊠ arrow.r.long ushr(Delta) arrow.r.long Rpush(p). $

// No separate projection formula or base-change theorem is used in the proof presented below. The only reorganisation of operations in the diagonal calculation is supplied by tensor--Hom adjunction and internal exceptional adjunction; the remaining comparison maps are contained in the compatibility theorem.
#thm(title: "Compatibility of de Rham with the operations used below")[
Let $f:X -> Y$ be a morphism of smooth complex algebraic varieties. On regular holonomic complexes there are natural isomorphisms
$ DR_Y (dint(f) (cM^bullet)) iso Rpush(f) (DR_X (cM^bullet)), $
$ DR_X (dpull(f) (cN^bullet)) iso ushr(f) (DR_Y (cN^bullet)), $
$ DR_(X times Y) (cM^bullet ⊠ cN^bullet) iso DR_X (cM^bullet) ⊠ DR_Y (cN^bullet), $
and
$ DR_X (Dual_(cal(D), X) (cM^bullet)) iso VDX(X^"an") (DR_X (cM^bullet)). $
]
<thm:rh-compatibility>

This is @HTT2008[Thm. 7.1.1], together with the external-product compatibility of §4.7. Regularity is essential at singular boundaries. For an irregular module, direct image across an open embedding need not commute with de Rham; see @HTT2008[Rem. 7.1.2]. The exponential connection of @sec:localization-algebraic-d-modules exhibits the missing sectorial Stokes data.


== Full faithfulness <sec:rh-full-faithfulness>

Full faithfulness asks whether every map between differential systems can be recovered from the corresponding sheaf objects, and whether every sheaf-theoretic map comes from a unique differential one. Before introducing the diagonal, consider the degenerate case $X={*}$. Then $DX(X)=CC$ and $DR_X$ is the identity. For finite-dimensional vector spaces,
$ Hom_CC (V,W) iso V^vee times.o W $
and for bounded complexes the corresponding statement is
$ RHom_CC (V^bullet,W^bullet) iso RHom_CC (CC, (V^bullet)^vee times.o W^bullet) $
The dual of the first variable provides linear tests; tensoring with the second variable evaluates those tests against possible targets.

On a space $X$ the two variables may lie at different points, so the analogue first lives on $X times X$. The external product
$ VDX(X^"an") (K) ⊠ L $
contains a dual test for $K$ at the first point and a value of $L$ at the second. A morphism of sheaves must compare data over the same point, and the diagonal
$ Delta:X into X times X $
imposes that equality. Applying $ushr(Delta)$ keeps the supported part of the comparison along the diagonal, and the map $p:X->{*}$ then collects the local comparisons into the global derived Hom complex. The formula below is therefore the sheaf version of the elementary expression $V^vee times.o W$.

Let $p:X -> {*}$ be the map to a point. There are two parallel diagonal formulas. On the differential side,
$ RHom_(DX(X)) (cM^bullet, cN^bullet) iso dint(p) (dpull(Delta) (Dual_(cal(D), X) (cM^bullet) ⊠ cN^bullet)). $
On the sheaf side, for $K, L in Dbc(X^"an")$,
$ RHom_(Shk(X^"an")) (K,L) iso Rpush(p) (ushr(Delta) (VDX(X^"an") (K) ⊠ L)). $
The first is the differential tensor--Hom identity written on the diagonal; the second is its Verdier-dual analogue. Compare @HTT2008[Cor. 2.6.15 and equations (7.2.3)--(7.2.4)].

#prop(title: "Derived Hom is preserved by de Rham")[
For $cM^bullet, cN^bullet in D_"rh"^b (DX(X))$ there is a natural isomorphism
$ RHom_(DX(X)) (cM^bullet, cN^bullet) iso RHom_(Shk(X^"an")) (DR_X (cM^bullet), DR_X (cN^bullet)). $
Consequently $DR_X$ is fully faithful.
]
<prop:rh-full-faithfulness>

#proofsketch[
Start with the sheaf-side diagonal formula for $K = DR_X (cM^bullet)$ and $L = DR_X (cN^bullet)$. By @thm:rh-compatibility, Verdier duality of the first factor becomes the de Rham complex of $Dual_(cal(D), X) (cM^bullet)$, and the external product becomes the de Rham complex of the external product of the two differential objects. Compatibility with $ushr(Delta)$ then gives the de Rham complex of $dpull(Delta)$, and compatibility with $Rpush(p)$ gives the de Rham complex of $dint(p)$. Since the de Rham functor on a point is the identity, the resulting complex is
$ dint(p) (dpull(Delta) (Dual_(cal(D), X) (cM^bullet) ⊠ cN^bullet)), $
which is the differential-side diagonal formula for $RHom_(DX(X)) (cM^bullet, cN^bullet)$.

Taking degree-zero cohomology gives
$ Hom_(D_"rh"^b (DX(X))) (cM^bullet, cN^bullet) iso Hom_(Dbc(X^"an")) (DR_X (cM^bullet), DR_X (cN^bullet)), $
so $DR_X$ is fully faithful.
]

The diagonal calculation identifies the two derived Hom complexes. We take from the proof of @HTT2008[Thm. 7.2.2] the coherence of the comparison maps, and hence the identification of this isomorphism with the morphism induced by $DR_X$; see also @HTT2008[Rem. 7.2.3].


== Essential surjectivity <sec:rh-essential-surjectivity>

#exmp(title: "The two-stratum model on the line")[
Let $X=CC$, let $U=CC^times$ and $Z={0}$, and write $j:U into X$ and $i:Z into X$ for the inclusions. Let $K$ be constructible for this two-stratum decomposition and put
$ A:=ushr(i) (K) quad B:=invimg(j,K) $
The open--closed triangle of @thm:recollement is
$
Rpush(i) (A)
arrow.r.long
K
arrow.r.long
Rpush(j) (B)
arrow.r.long^delta
shift(Rpush(i) (A),1)
$
Thus $A$, $B$, and the connecting morphism
$ delta:Rpush(j) (B)->shift(Rpush(i) (A),1) $
determine $K$. In terms of the mapping cone,
$ K iso shift(cone(delta),-1) $

The open and closed pieces alone do not determine $K$. If $delta=0$ then
$ K iso Rpush(i) (A) plus.o Rpush(j) (B) $
and the open--closed triangle splits. A nonzero connecting morphism may produce a non-split object with the same pieces $A$ and $B$. Thus the connecting morphism records how the two strata are attached. Essential surjectivity must consequently lift $delta$ in addition to lifting the open and closed pieces. This is the role of full faithfulness in the construction below.

We first lift $B$. Its cohomology sheaves are finite-rank local systems on $U$. For each $m$, Deligne's theorem supplies a regular connection $cE_m$ whose horizontal local system is $cohsh(m,B)$; if this cohomology sheaf vanishes, take $cE_m=0$. Since $dim_CC U=1$,
$ DR_U (cE_m) iso shift(cohsh(m,B),1) $
Therefore
$ cN_m:=shift(cE_m,-m-1) $
satisfies
$ DR_U (cN_m) iso shift(cohsh(m,B),-m) $

Let $a$ be the lowest degree with nonzero cohomology. Then
$ tau_(<=a) B iso shift(cohsh(a,B),-a) $
so set $cM_a:=cN_a$. Suppose inductively that
$ DR_U (cM_(m-1)) iso tau_(<=m-1) B $
The next truncation triangle is
$
tau_(<=m-1) B
arrow.r.long
tau_(<=m) B
arrow.r.long
shift(cohsh(m,B),-m)
arrow.r.long^(theta_m)
shift(tau_(<=m-1) B,1)
$
By @prop:rh-full-faithfulness, the connecting morphism lifts uniquely to
$ tilde(theta)_m:cN_m->shift(cM_(m-1),1) $
Set
$ cM_m:=shift(cone(tilde(theta)_m),-1) $
Applying $DR_U$ gives the truncation triangle above and hence
$ DR_U (cM_m) iso tau_(<=m) B $
Since $B$ is bounded, the induction terminates and produces
$ cM_U in D_"rh"^b (DX(U)) quad "with" quad DR_U (cM_U) iso B $

The closed stratum is a point, so $DX(Z)=CC$ and $DR_Z$ is the identity. Regard $A$ as an object
$ cM_Z in D_"rh"^b (DX(Z)) quad "with" quad DR_Z (cM_Z) iso A $
Set
$ cN_U:=dint(j) (cM_U) quad cN_Z:=dint(i) (cM_Z) $
By @thm:rh-compatibility,
$ DR_X (cN_U) iso Rpush(j) (B) quad DR_X (cN_Z) iso Rpush(i) (A) $

Under these identifications, @prop:rh-full-faithfulness lifts $delta$ uniquely to
$ tilde(delta):cN_U->shift(cN_Z,1) $
Define
$ cM:=shift(cone(tilde(delta)),-1) $
Since $DR_X$ preserves distinguished triangles,
$ DR_X (cM) iso shift(cone(delta),-1) iso K $

Thus the open and closed lifts, together with the lifted connecting morphism, recover $K$ up to isomorphism.
]
<exmp:rh-two-strata>

Iterating the two-stratum construction over a finite algebraic stratification gives the following generation statement.

#lem(title: "Stratumwise local systems generate the constructible derived category")[
Let $K in Dbc(X^"an")$. After refining an algebraic Whitney stratification, $K$ belongs to the triangulated subcategory generated by objects
$ shift(Rpush(i) (cL), m) $
where $i:S into X$ is the inclusion of a smooth affine locally closed stratum, $cL$ is a finite-rank local system on $S^"an"$, and $m in ZZ$.
]
<lem:rh-constructible-generators>

#proof[
Choose a finite algebraic Whitney stratification adapted to $K$, refined so that the strata and their inclusions have the affine properties in the statement, as in #cite(<HTT2008>, supplement: [proof of Thm. 7.2.2]). We induct on the total number of strata. Let $j:U arrow.r.hook X$ be the union of the open strata and let $i:Z arrow.r.hook X$ be its closed complement. The frontier condition ensures that $Z$ is a closed union of fewer strata. Recollement gives the distinguished triangle $i_* i^! K -> K -> R j_* j^(-1)K -> (i_* i^!K)[1]$.

On each component $S$ of $U$, the cohomology sheaves of $j^(-1)K$ are finite-rank local systems. The canonical truncation triangles therefore build $j^(-1)K$ from shifts of local systems on these components. Applying $R j_*$ expresses $R j_* j^(-1)K$ in terms of the required generators associated with the open strata. By induction, $i^!K$ is generated on $Z$ by the corresponding objects for its strata. Applying $i_*$ gives generators on $X$, since direct images compose and $i_*$ is exact. The displayed triangle then places $K$ in the same triangulated subcategory. The case of an empty closed complement starts the induction.
]
This is an induction using the open–closed recollement of @sect:recollement. The gluing theorem (@thm:gluing-t-structures) uses the same decomposition to glue $t$-structures, whereas the present argument uses it to generate objects of the triangulated category. See @BBD1982[§1.4].


#prop(title: "Every constructible complex is a de Rham complex")[
For every $K in Dbc(X^"an")$ there exists $cM^bullet in D_"rh"^b (DX(X))$ with
$ DR_X (cM^bullet) iso K. $
]
<prop:rh-essential-surjectivity>

#proof[
By @prop:rh-full-faithfulness the essential image of $DR_X$ is a full triangulated subcategory of $Dbc(X^"an")$. By @lem:rh-constructible-generators it is therefore enough to lift one generator $shift(Rpush(i) (cL), m)$.

Let $d = dim_CC S$. Deligne's theorem supplies a regular algebraic integrable connection $cE$ on $S$ whose horizontal local system is $cL$, and by @sec:rh-de-rham
$ DR_S (cE) iso shift(cL, d) $
Set
$ cM^bullet := shift(dint(i) (cE), m-d) $
Regular holonomicity is preserved by this direct image, and @thm:rh-compatibility gives
$ DR_X (cM^bullet) iso shift(Rpush(i) (DR_S (cE)), m-d) iso shift(Rpush(i) (cL), m). $
Thus every generator lies in the essential image, and since that image is triangulated, so does every constructible complex.
]

#thm(title: "Riemann--Hilbert correspondence")[
Let $X$ be a smooth complex algebraic variety. The normalised de Rham functor is an equivalence of triangulated categories
$ DR_X : D_"rh"^b (DX(X)) -> Dbc(X^"an") $
Equivalently, the solution functor gives a contravariant equivalence
$ Sol_X : D_"rh"^b (DX(X)) -> Dbc(X^"an")^"op" $
]
<thm:riemann-hilbert>

#proof[
Full faithfulness is @prop:rh-full-faithfulness and essential surjectivity is @prop:rh-essential-surjectivity. The statement for $Sol_X$ follows from @prop:rh-dr-sol-duality and Verdier biduality on constructible complexes, @thm:verdier-duality.
]

This is @HTT2008[Thm. 7.2.2 and Cor. 7.2.4]. 

#rmrk(title: "Analytic and algebraic forms")[
For a complex manifold $X$, the analytic theorem gives
$ DR_X : D_"rh"^b (DX(X)) -> Dbc(X) $
as an equivalence with the analytically constructible derived category; see @HTT2008[Thm. 7.2.1]. For algebraic $X$, the theorem above uses the smaller category of complexes constructible with respect to a finite algebraic stratification. Deligne's regular-singular correspondence supplies the algebraisation of the local systems on the strata, and @HTT2008[Thm. 4.7.7] shows that algebraic holonomic modules land in this smaller target.
]
<rmrk:rh-analytic-algebraic>

== Finite cellular models of constructible complexes <sec:finite-cellular-models>

The construction below represents an algebraically constructible complex by finite cellular data. It applies in particular to the de Rham and solution complexes of regular holonomic complexes. Its input is the constructible complex, an adapted triangulation, and choices of local cohomology representatives and primitives. A presentation of the differential module alone does not supply these choices.

Recall the Euler module $M_0:=A_1/(A_1 (x partial))$ from @exmp:ordinary-versus-derived-solutions. After analytification, write $z$ for the complex coordinate. Its unshifted solution complex is $F_0^bullet:=Sol_CC (M_0) iso [cO_CC xto(z partial_z) cO_CC]$, with terms in degrees $0$ and $1$. The germ of $1$ in the degree-one term represents the generator of $stalk(cal(H)^1 (F_0^bullet),0)$. On a simply connected punctured sector it becomes a boundary because $z partial_z (log z)=1$. Branches of $log z$ on overlapping sectors differ by constants, and their continuation around the origin produces the jump $2 pi i$. A cellular model records the finite-dimensional complexes on the cells together with the restriction maps containing these transition constants.

Let $F^bullet in Dbc(X^"an")$ be constructible with respect to a finite algebraic stratification. Choose an algebraic compactification $X into overline(X)$, put $Y:=overline(X)^"an"$, and choose a finite simplicial pair $(K,L)$ compatible with the stratification and the boundary such that $Y iso abs(K)$ and $X^"an" iso abs(K)-abs(L)$. To obtain the pair, regard the boundary and the strata as subanalytic subsets of a real analytic ambient space. The compatible triangulation supplied by @KashiwaraSchapira1990[Prop. 8.2.5] is finite because $Y$ is compact. Write $j:X^"an" into Y$ for the open inclusion and put $E^bullet:=lsh(j) (F^bullet)$. Then $E^bullet$ is constructible for the cells of $K$ and has zero stalks on the cells of $L$. If $X^"an"$ is compact, take $Y=X^"an"$ and $L$ empty.
#def(title: "Finite cellular model")[
A *finite cellular model* of $F^bullet$ relative to $(K,L)$ is a bounded cellular complex $B^bullet$ on $K$ with finite-dimensional values, satisfying $B_sigma^bullet=0$ for every $sigma in L$, together with an isomorphism
$ op("Real")_K (B^bullet) iso lsh(j) (F^bullet) $
in the constructible derived category on $Y$.
]
<def:finite-cellular-model>
For a cell $sigma$ of $K$, let $op("st") (sigma)$ be its topological open star as in @sec:cellular-sheaves. If $sigma <= tau$, then $op("st") (tau) subset.eq op("st") (sigma)$. Choose a bounded-below injective resolution $E^bullet -> I^bullet$ and set $A_sigma^bullet:=Gamma (op("st") (sigma),I^bullet)$. Restriction gives cochain maps $r_(sigma,tau) : A_sigma^bullet -> A_tau^bullet$ satisfying $r_(tau,upsilon) compose r_(sigma,tau)=r_(sigma,upsilon)$ and $d_tau compose r_(sigma,tau)=r_(sigma,tau) compose d_sigma$.

For $x in sigma$, evaluation gives $Gamma ("st"(sigma),I^bullet)->stalk(I^bullet,x)$, which is a quasi-isomorphism by @Shepard1985[Lemma 5.2.2]. Exactness of stalks also makes $stalk(E^bullet,x)->stalk(I^bullet,x)$ a quasi-isomorphism. Thus $A_sigma^bullet$ represents the stalk complex of $E^bullet$ on $sigma$, and every $H^q (A_sigma^bullet)$ is finite-dimensional. Shepard's comparison identifies the sheaf complex reconstructed from this open-star diagram with $E^bullet$; see [8, Theorem 5.2.3]. The vector spaces in the complexes $A_sigma^bullet$ need not themselves be finite-dimensional.

#lem(title: "Finite subdiagrams")[
Let $P$ be a finite poset and let $A^bullet$ be a diagram of complexes of $CC$-vector spaces supported in a common finite range of degrees $[a,b]$. Assume that every $H^q (A_sigma^bullet)$ is finite-dimensional. There is a subdiagram $B^bullet subset.eq A^bullet$, finite-dimensional in every degree at every element of $P$, such that each inclusion $B_sigma^bullet->A_sigma^bullet$ is a quasi-isomorphism.
]
<lem:rh-finite-diagram-reduction>

#proof[
For every $sigma$ and $q$, choose cycles representing a basis of $H^q (A_sigma^bullet)$. Let $B^bullet$ initially be their span, closed under the diagram maps. Finiteness of $P$ makes every $B_sigma^q$ finite-dimensional. The chosen vectors and their images are cycles, and compatibility with composition makes $B^bullet$ a subdiagram. The maps $H^q (B_sigma^bullet)->H^q (A_sigma^bullet)$ are surjective.

Proceed downwards through $q=b,b-1,...,a+1$. For every $sigma$, choose cycles $z_(sigma,1),...,z_(sigma,m_sigma)$ representing a basis of $op("ker") (H^q (B_sigma^bullet)->H^q (A_sigma^bullet))$. Each $z_(sigma,i)$ is a boundary in $A_sigma^bullet$, so choose $y_(sigma,i) in A_sigma^(q-1)$ with $d_sigma (y_(sigma,i))=z_(sigma,i)$. Adjoin these elements and all their images under the diagram maps to $B^(q-1)$.

The enlarged spaces form a subcomplex because $d_tau (r_(sigma,tau) (y_(sigma,i)))=r_(sigma,tau) (z_(sigma,i))$, and the right-hand side belongs to $B_tau^q$. This step kills the kernel in degree $q$ and changes no terms in degrees at least $q$. Later steps handle the lower-degree kernels. Surjectivity persists because a cycle representing a nonzero class in $A_sigma^bullet$ cannot become a boundary in its subcomplex.

After the step $q=a+1$, the map on degree-$a$ cohomology is injective: a cycle in $B_sigma^a$ that is a boundary in $A_sigma^bullet$ is the differential of an element of $A_sigma^(a-1)=0$. The resulting maps are isomorphisms on cohomology in every degree. Every step adds finitely many vectors and their images under the maps of $P$.
]

#prop(title: "Finite cellular model")[
With the chosen simplicial pair $(K,L)$, the complex $F^bullet$ admits a finite cellular model in the sense of @def:finite-cellular-model. In particular, two regular holonomic complexes whose de Rham complexes have isomorphic realised cellular models are isomorphic.
]
<prop:rh-cellular-construction>

#proof[
Use the diagram $A_sigma^bullet:=Gamma (U_sigma,I^bullet)$ constructed above. It is bounded below. Since $K$ has finitely many cells and every $A_sigma^bullet$ has bounded cohomology, there is a common upper bound $b$ for their cohomology. Replace each $A_sigma^bullet$ by its good truncation in degrees at most $b$: replace degree $b$ by $op("ker") (d_sigma^b)$ and set the higher degrees to zero. The restriction maps preserve these kernels, so the truncations form a bounded subdiagram, and their inclusions are quasi-isomorphisms at every cell.

Apply the preceding lemma. The inclusions $B_sigma^bullet -> A_sigma^bullet$ are objectwise quasi-isomorphisms, and Shepard's comparison therefore identifies $op("Real")_K (B^bullet)$ with $E^bullet=lsh(j) (F^bullet)$. The construction can be made with $B_sigma^bullet=0$ on $L$: the stalk complexes of $E^bullet$ on $L$ are acyclic, and closure under the maps $r_(sigma,tau)$ introduces no vectors on $L$.

If $F^bullet=DR_X (cM^bullet)$, the final assertion follows from the full faithfulness of @thm:riemann-hilbert.
]

The choices are noncanonical, but the objectwise quasi-isomorphism with the open-star diagram fixes the realised object up to isomorphism in the constructible derived category. If $F^bullet=DR_X (cM^bullet)$, derived full faithfulness determines the isomorphism class of $cM^bullet$ from this realised object. This determination is categorical and does not reconstruct a differential-module presentation.

Since a finite cellular model vanishes on $L$, its total cellular complex computes sections of the extension by zero on $Y$. We write $C_c^bullet (K;B):=C^bullet (K;B)$ to record this compact-support interpretation.

#prop(title: "Compactly supported cohomology from a finite model")[
Let $B^bullet$ be a finite cellular model of $F^bullet$ relative to $(K,L)$. Then
$ C_c^bullet (K;B) iso RGamc (X^"an",F^bullet) $
If $X^"an"$ is compact, the same total complex computes $RGam (X^"an",F^bullet)$.
]
<prop:rh-total-cellular-complex>

#proof[
By @prop:cellular-hypercohomology and @def:finite-cellular-model,
$ C_c^bullet (K;B) iso RGam (Y,op("Real")_K (B^bullet)) iso RGam (Y,lsh(j) (F^bullet)) $
Since $Y$ is compact, the last object is $RGamc (X^"an",F^bullet)$. If $X^"an"$ is compact, take $Y=X^"an"$ and $L$ empty.
]

=== The Euler module

Apply the construction to the unshifted solution complex $F_0^bullet$. Let $Delta$ be a small open disc centred at $0$ and set $Y:=overline(Delta)$, $X:=Delta=op("int") (Y)$ and $L:=partial Y$. Write $j:Delta into Y$ for the open inclusion. Choose a finite triangulation $K$ of $Y$ with central vertex $v$, three boundary vertices, three radial edges $e_0,e_1,e_2$, three boundary edges and three triangular two-cells $t_0,t_1,t_2$. Assign the zero complex to the cells of $L$.

The free resolution of $M_0$ gives $rest(F_0^bullet,Delta) iso [cO_Delta xto(z partial_z) cO_Delta]$ in degrees $0$ and $1$, as in @exmp:ordinary-versus-derived-solutions. The open star of $v$ is $Delta$. Every other retained open star is a simply connected punctured sector. These sets are Stein, so their complexes of holomorphic sections compute the required derived sections.

At the central vertex take $B_v^bullet:=[CC xto(0) CC]$ using the constant functions in both degrees. At every other retained cell $sigma$, choose a branch $ell_sigma$ of $log z$ on $U_sigma$ and take $B_sigma^bullet:=[op("span")_CC {1,ell_sigma} xto(z partial_z) op("span")_CC {1}]$. In the displayed bases its differential is $d_sigma=mat(0,1):CC^2->CC$.

For a face relation between noncentral cells, write $rest(ell_sigma,U_tau)=ell_tau+c_(sigma,tau)$. Restriction is then represented by $r_(sigma,tau)^0=mat(1,c_(sigma,tau);0,1)$ and $r_(sigma,tau)^1=mat(1)$. The maps from the centre are $r_(v,sigma)^0=mat(1;0)$ and $r_(v,sigma)^1=mat(1)$.

#prop(title: "Euler model")[
These complexes and maps form a finite cellular model of $rest(F_0^bullet,Delta)$. The branches may be chosen so that every $c_(e_i,t_j)$ is zero except $c_(e_0,t_2)=-2 pi i$. With the radial edges oriented away from $v$ and the two-cells oriented counterclockwise, Gaussian elimination reduces the total compactly supported cellular complex to $[CC xto(2 pi i) CC]$ with terms in total degrees $1$ and $2$, so the total complex is acyclic.
]
<prop:rh-euler-cellular-model>

#proof[
On $Delta$, the operator sends $sum_(m>=0) a_m z^m mapsto sum_(m>=1) m a_m z^m$. Its kernel consists of constants, and its image consists exactly of the holomorphic functions with zero constant term. Thus the constants in degrees $0$ and $1$ represent bases of the two cohomology groups, so $B_v^bullet$ is a quasi-isomorphic subcomplex.

On a noncentral star $U_sigma$, a holomorphic function $g$ has a preimage under $z partial_z$ because $g (z)/z$ has a holomorphic primitive on the simply connected domain $U_sigma$. The kernel again consists of constants. Since $z partial_z (ell_sigma)=1$, the chosen finite subcomplex has the same kernel and zero cokernel. Its inclusion is therefore a quasi-isomorphism.

The displayed matrices are the restrictions of the chosen holomorphic functions, so they commute with the differentials and satisfy the composition identities. For example, $mat(0,1) mat(1,c_(sigma,tau);0,1)=mat(0,1)$, and the map from the central degree-zero term lands in the kernel of $mat(0,1)$.

Choose the arguments on $t_0,t_1,t_2$ in $(0,2 pi/3)$, $(2 pi/3,4 pi/3)$ and $(4 pi/3,2 pi)$, respectively. Choose the argument on $U_(e_0)$ in $(-2 pi/3,2 pi/3)$, and those on $U_(e_1)$ and $U_(e_2)$ in $(0,4 pi/3)$ and $(2 pi/3,2 pi)$, respectively. All restrictions agree except from $U_(e_0)$ to $U_(t_2)$, where the arguments differ by $-2 pi$. This gives the stated constant.

In every noncentral cell, the internal differential maps the logarithmic basis vector to the constant basis vector by the identity. Gaussian elimination cancels these pairs and the incidence identity maps along a spanning tree of the circular link. The central degree-one class in total degree $1$ and the compactly supported two-cell class in total degree $2$ remain. Their differential is the logarithmic jump $2 pi i$ across the omitted edge, up to the sign fixed by the cell orientations. Its nonzero value makes the total complex acyclic.
]

On the punctured disc, degree-one hypercohomology comes from the monodromy of the degree-zero local system. The cochain $1$ at the centre represents a class in $bb(H)^1 (Delta,F_0^bullet)$. On every simply connected punctured star, its image is the boundary of the chosen logarithm. The transition constants around the puncture sum to $2 pi i$. On $Delta^times:=Delta-{0}$, multiplication by $(d z)/z$ in degree $1$ gives an isomorphism of complexes $[cO xto(z partial_z) cO]->[cO xto(d) Omega^1]$. The class of $1$ is sent to $(d z)/z$, whose integral around a positively oriented circle is $2 pi i$. It therefore gives a nonzero class in $bb(H)^1 (Delta^times,rest(F_0^bullet,Delta^times))$. This period is the final differential in the compactly supported total complex.

#rmrk(title: "Analytic input")[
The Euler calculation gives the required local representatives and primitives explicitly. For a general differential module, finding them is an analytic problem. Constructibility makes the local cohomology finite-dimensional; after the analytic choices, reduction and totalisation are finite linear-algebraic procedures.
]
<rmrk:rh-scope>

For an adapted finite triangulation, @prop:rh-cellular-construction represents every algebraically constructible de Rham complex by finitely many complexes and restriction maps. The transition constants in the Euler example record the gluing of local logarithms, and @prop:rh-total-cellular-complex computes compactly supported cohomology from the resulting finite diagram. It remains to recognise which such complexes correspond to differential modules concentrated in degree $0$; this is the role of the perverse heart.

== The perverse heart <sec:rh-perverse-heart>


For a regular holonomic module $cM$, @thm:holonomic-solutions-perverse and @prop:rh-dr-sol-duality give that $DR_X (cM)$ is perverse. A short exact sequence of regular holonomic modules gives a distinguished triangle whose three de Rham complexes all lie in the perverse heart, and a distinguished triangle with all three vertices in the heart of a $t$-structure is a short exact sequence there. The restriction of $DR_X$ to regular holonomic modules is therefore exact as a functor into $Perv (X^"an")$.

The two-stratum line makes the target heart concrete. By @thm:simple-perverse, with $X=CC$, $U=CC^times$ and $Z={0}$, the simple objects are the skyscraper at $0$ and the intermediate extensions $midext (shift(cL,1))$ of irreducible local systems on $CC^times$. Their differential counterparts are $delta_0$ and, by Deligne, the differential minimal extensions of the corresponding irreducible regular connections. The next proposition identifies the two extension procedures.

#prop(title: "Minimal extension is preserved")[
Let $i:S into X$ be an affine locally closed embedding of a smooth stratum of dimension $d$, let $cE$ be a regular integrable connection on $S$, and let $cL$ be its horizontal local system. Then
$ DR_X (i_(!*)^(Dop) cE) iso ICs(overline(S), cL). $
]
<prop:rh-minimal-extension>

#proof[
Factor $i$ as $S xto(j) overline(S) xto(a) X$ with $j$ open and $a$ closed. For affine $i$ the two differential extensions of @prop:d-minimal-extension-characterization are regular holonomic modules, and $i_(!*)^(Dop) cE$ is the image of their canonical morphism. De Rham is exact on regular holonomic modules, and by @thm:rh-compatibility it carries the upper differential extension to the corresponding derived direct image on sheaves; the lower extension follows from the same statement and duality. Because the differential extensions are modules, their de Rham images lie in the perverse heart, so they are the standard and costandard perverse extensions of $shift(cL,d)$ in the sense of @def:extreme-extensions.

Taking the image of their canonical morphism in the perverse heart gives $push(a, midext (shift(cL,d)))$, which by @def:intermediate-extension and @def:intersection-complex is $ICs(overline(S), cL)$. Equivalently, @thm:intermediate-extension-characterization identifies it as the unique perverse extension with no nonzero subobject and no nonzero quotient supported on the boundary. This is the correspondence recorded in @HTT2008[Rem. 7.2.10]; on the perverse side it is the construction organised by @BBD1982[§1.4 and §4.3].
]


#thm(title: "Abelian Riemann--Hilbert correspondence")[
The de Rham functor restricts to an equivalence of abelian categories
$ DR_X : Mod_"rh" (DX(X)) -> Perv (X^"an"). $
]
<thm:abelian-riemann-hilbert>

#proof[
We first show that de Rham is $t$-exact for the standard $t$-structure on the differential side and the perverse $t$-structure on the sheaf side. A regular holonomic module in degree $0$ is sent to the perverse heart. Every bounded complex $cal(M)^bullet$ is built by its canonical truncation triangles from the layers $cal(H)^q (cal(M)^bullet)[-q]$. Applying de Rham turns these into shifts by $[-q]$ of perverse sheaves. If $cal(M)^bullet$ has no positive cohomology, only $q<=0$ occur; these shifts lie in the nonpositive perverse half, which is closed under extensions. If $cal(M)^bullet$ has no negative cohomology, only $q>=0$ occur; these shifts lie in the nonnegative perverse half, which is likewise closed under extensions. This proves both required inclusions.

Hence $DR_X$ is $t$-exact, and for every $i$ there is a natural isomorphism
$ pH(i) (DR_X (cM^bullet)) iso DR_X (cohsh(i,cM^bullet)) $

Full faithfulness on the hearts follows by restricting @prop:rh-full-faithfulness to objects concentrated in degree $0$.

For essential surjectivity, let $P in Perv (X^"an")$. By @thm:riemann-hilbert there is $cM^bullet in D_"rh"^b (DX(X))$ with $DR_X (cM^bullet) iso P$. For $i eq.not 0$, $t$-exactness gives
$ DR_X (cohsh(i,cM^bullet)) iso pH(i) (P)=0. $
A fully faithful functor detects the zero object: it carries the identity of $cohsh(i,cM^bullet)$ to the identity of the zero object, so that identity vanishes. Hence $cohsh(i,cM^bullet)=0$ for every $i eq.not 0$, the complex $cM^bullet$ is isomorphic to the regular holonomic module $cohsh(0,cM^bullet)$ placed in degree $0$, and $DR_X$ carries that module to $P$. See @HTT2008[Thm. 7.2.5].
]

#rmrk(title: "Perverse objects in a finite model")[
Let $B^bullet$ be a finite cellular model of an algebraically constructible object $F in Dbc(X^"an")$. By the Riemann--Hilbert equivalence there is a regular holonomic complex $cM^bullet$ with $DR_X (cM^bullet) iso F$. The complex $cM^bullet$ is isomorphic to a regular holonomic module concentrated in degree $0$ when $F in Perv (X^"an")$.

For a cell $sigma$ contained in a complex stratum, the stalk of $F$ is represented by $B_sigma^bullet$. After a local subdivision making $x$ a vertex, its costalk is represented by the cone of the restriction
$ C^bullet (op("st") (x);B) -> C^bullet (op("st") (x)-{x};B) $
shifted by $[-1]$. The pointwise bounds of @rmrk:pointwise-perverse-bounds therefore decide by finite linear algebra whether the model corresponds to a regular holonomic module concentrated in degree $0$.
]
<rmrk:rh-heart-finite-model>

The two basic objects on the line summarise the dimension shift. The trivial connection has
$ DR_CC (cO_CC) iso shift(constSh(CC)_CC, 1) $
while the point-supported module satisfies
$ DR_CC (delta_0) iso push(i_0, CC) $
Both $cO_CC$ and $delta_0$ are ordinary regular holonomic modules in degree zero. Their de Rham images occupy different ordinary sheaf degrees because their supports have different dimensions, yet both lie in perverse degree zero. The perverse heart is therefore the degree convention in which the differential module category appears without artificial shifts from one support dimension to another.


The Euler example shows why monodromy on the nonsingular locus is insufficient. On $CC^times$, a regular connection is determined by its local system; after the origin is restored, the constructible complex also records boundary-supported terms and their attaching morphisms. The correspondence sends closed support to closed support, differential minimal extension to perverse intermediate extension, and differential duality to Verdier duality. For an adapted finite triangulation, the cellular model packages this constructible object into finite-dimensional complexes and restriction maps without discarding its derived gluing data.

Holonomicity alone still gives constructible, perversely normalized solution data. An irregular meromorphic connection may also carry Stokes data, which ordinary constructible sheaves do not retain. Regularity is therefore the condition under which the full constructible de Rham complex determines the differential system.

== Further directions
The construction of @sec:finite-cellular-models does not yet provide an intrinsic category of differential systems on a stratified cellulation or an effective procedure for reconstructing differential operators from a finite cellular diagram. One further direction is therefore to define a category $op("CellD") (K,cal(S))$ that records local propagation on strata, extension maps, compatibility relations and monodromy, together with a realisation functor to $D_"rh"^b (DX(X))$. The problem is to determine which additional analytic or algebraic data make such a presentation intrinsic. Such a category would extend the constructible-side diagrams of @sec:finite-cellular-models by the analytic or algebraic data needed to recover differential operators.

A further possible application of such a cellular model appears in the theory of contextuality. Abramsky, Brandenburger, and their collaborators formulate ״contextuality״ as a failure to pass from local data to global data @AbramskyBrandenburger2011. In their setting, a measurement is a question about a particular quantity in a physical system, whose outcome is one of several possible answers, and a context is a collection of measurements that can be performed jointly. A measurement scenario is represented by a finite cover of possible contexts and a sheaf of local assignments, and a model is contextual when the local assignments agree on overlaps but cannot be glued to a global assignment. The same structure also appears in logical paradoxes - for example, in the familiar liar cycle, every local relation between two adjacent statements can be realised, while no assignment of truth values satisfies the entire cycle. This gluing problem can be represented by a finite complex, for example the Čech complex of the context cover, in which a nontrivial cohomology class may witness contextuality. If the cellular model is realised as a constructible complex, the Riemann--Hilbert correspondence relates it to a complex of regular holonomic $cal(D)$-modules. It therefore seems possible to begin with this finite model, translate a finite logical obstruction into a system of differential equations whose solution complex recovers the cellular data, and then study it using monodromy, singularities, and nearby and vanishing cycles.  
