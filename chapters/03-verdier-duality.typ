
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

// ---------------------------------------------------------------------
// Chapter-local notation.
// ---------------------------------------------------------------------
#let semi = math.class("punctuation", ";")   // ";" after a #-interpolation is eaten
#let Shk(X) = $op("Sh")(#X semi k)$
// Macros.typ's cohsh(x,K) does not interpolate its arguments (missing #);
// chapter-local corrected version, same name.
#let dualzc(X) = $omega_(#X,"cell")$
#let VDX(X) = $bb(D)_#X$
#let VDXc(X) = $bb(D)_(#X,"cell")$
// Macros.typ has xto but no xfrom; retained for compatibility with older chapter snippets.
#let xfrom(l) = math.class("relation", $limits(arrow.l.long)^#l$)

// PENDING CROSS-REFERENCE IN CHAPTER 1:
// add <def:total-complex> to the definition of the total complex there.

= Verdier Duality <chap:verdier-duality>

== Motivation <sec:verdier-motivation>

Duality's story begins with a simple observation - a finite-dimensional vector space can be described through its vectors or through the linear tests applied to them. By a linear test we mean a linear functional $ell:V -> k$, which assigns a scalar to every vector. The collection of all such tests is the dual space

$ V^vee := Hom_k(V,k) $

A vector $v in V$, in turn, defines a linear test on the space of tests: it sends each $ell in V^vee$ to $ell(v)$. This gives the canonical evaluation map

$ V -> V^(vee vee), quad v |-> (ell |-> ell(v)) $

which evaluates each functional $ell$ at the vector $v$. Finite-dimensionality makes this map an isomorphism, so the answers to all linear tests determine the original vector. There is generally no canonical identification $V iso V^vee$ since the original space consists of the objects being tested, while the dual space consists of the tests themselves.

Sheaves of vector spaces, as we have seen, organise algebraic data over a geometric space while retaining much of the algebraic structure of their values. We ask whether linear duality can also be made local and sensitive to the geometry. In oter words, for every open subset $U subset.eq X$, we would like to test the information carried by $rest(K,U)$ through its derived sections and organise these tests so that passing to a smaller open subset gives the restriction maps of a sheaf. But if $U subset.eq V$ are open, ordinary derived sections give a restriction map

$ RGam(V,rest(K,V)) -> RGam(U,rest(K,U)) $

Linear duality reverses arrows, so dualising this map would give

$ RHom_k (RGam(U,rest(K,U)),k)
  ->
  RHom_k (RGam(V,rest(K,V)),k) $

which points from the smaller open set to the larger one, opposite to the direction of sheaf restriction.

Compact support resolves this problem. Compactly supported information on a smaller open set can be extended by zero to a larger one. Concretely, a continuous function with compact support inside an open ball vanishes on a neighbourhood of its boundary, so extending it by zero to a larger ball remains continuous. This is the mechanism encoded by extension by zero in @def:extension-by-zero and used in @exmp:real-line-compact-cohomology. Thus, if $U subset.eq V$, $RGamc(U,rest(K,U)) -> RGamc(V,rest(K,V)). $

The derived linear dual $RHom_k (-,k)$ reverses both the maps and the cohomological degrees of a complex. Dualising the preceding maps therefore gives

$ RHom_k (RGamc(V,rest(K,V)),k)
  ->
  RHom_k (RGamc(U,rest(K,U)),k) $

which now points from the larger open set to the smaller one. In this chapter we will organise the test complexes $RHom_k (RGamc(U,rest(K,U)),k) $
as a single derived object on $X$, compatibly with restriction as $U$ varies.

// The use of compact support has an immediate geometric consequence. As we have seen (@exmp:real-line-compact-cohomology), compactly supported information on an open ball must vanish before reaching its boundary, so the calculation retains information about how the local data sit relative to that boundary. Thus compact support also preserves geometric information about local dimension that ordinary cohomology forgets. This sensitivity to dimension also creates a constraint: data supported in different dimensions naturally occur in different cohomological degrees, so a single fixed notion of degree zero cannot simultaneously accommodate every support dimension and duality.
Compact support also retains local dimension. As computed in @exmp:real-line-compact-cohomology, the compactly supported cohomology of a small real $d$-ball is concentrated in degree $d$, although its ordinary cohomology is concentrated in degree $0$. Verdier duality therefore assigns different cohomological shifts to data supported in different dimensions.

A second boundary problem appears when a space is decomposed as
$X = U union Z$, with $U$ open and $Z$ closed. The restrictions of $K$ to $U$ and $Z$ do not determine how the two pieces are attached. We therefore need operations that distinguish extension from $U$ with or without boundary contributions, and that isolate the part supported on $Z$. Verdier duality exchanges the ordinary operations with their support-sensitive counterparts. These open--closed constructions will also be used in the next chapter to describe how constructible complexes pass between strata.


// There is a another boundary issue. We will often understand a space $X$ by separating a closed subset $Z$ from its open complement $U = X - Z$. Knowing $K$ separately on $U$ and on $Z$ does not by itself describe its behaviour near the boundary between them: we must distinguish the information on $U$ that persists towards $Z$, the information that disappears there, and the information supported entirely on $Z$. We will therefore need different ways of transporting information between the open part and the ambient space, and different ways of extracting the contribution supported on the closed part. Verdier duality will systematically exchange the ordinary operations with their support-sensitive counterparts. The same mechanism will later control how constructible data extend between strata of different dimensions.

// This chapter has two connected aims. The first is to construct the local dual object described above and give a usable method for computing it. The second is to develop, for maps between spaces and especially for open--closed decompositions, the smallest collection of transport operations required by the perverse theory of the next chapter, together with the way Verdier duality exchanges them. The full calculus of operations is deferred to the Riemann--Hilbert chapter, where its differential counterpart is also available.

Throughout, $k$ is a field; in the Riemann--Hilbert setting $k = CC$. Spaces are locally compact Hausdorff and countable at infinity. Whenever an exceptional inverse image is used, we impose the corresponding finite-cohomological-dimension hypothesis explicitly. When algebraic constructibility is invoked, the spaces and maps are complex algebraic varieties and algebraic morphisms. Analytic constructibility is used only under the hypotheses stated there. We write $Shk(X)$ for sheaves of $k$-vector spaces and $Dbc(X)$ for the bounded constructible derived category in the relevant setting. Dimension means complex dimension unless real dimension is stated.

== Verdier duality

#ed[We seek an object whose derived sections on every open $U subset.eq X$ are
$RHom_k (RGamc(U,rest(K,U)),k). $
Internal derived Hom is compatible with restriction and converts sheaf-valued Hom into the external derived Hom complex:
$ rest(RsHom_X (K,L),U)
  iso
  RsHom_U (rest(K,U),rest(L,U)) $
$ RGam(U,rest(RsHom_X (K,L),U))
  iso
  RHom_(Shk(U)) (rest(K,U),rest(L,U)) $
(@lem:internal-hom-restriction, @lem:internal-external-derived-hom). It remains to choose an object $L$ for which the latter complex is the $k$-linear dual of compactly supported sections.]

// === The dualizing complex <sec:dualizing-complex>

Let $a_X:X->{*}$ be the structure map. Since
$R a_(X,!)(-) = RGamc(X,-), $
the required coefficient object is obtained from the right adjoint of $R a_(X,!)$. Under the finite-cohomological-dimension hypothesis of @thm:exceptional-inverse-image (stated below), this right adjoint exists:
$ a_X^!:Dp(Vect_k) -> Dp(Shk(X)), quad R a_(X,!) tack.l a_X^! $

#def(title: "Dualizing complex")[
The *dualizing complex* of $X$ is $ dualz(X)^bullet := a_X^! k $
]
<def:dualizing-complex>

For a point, $a_({*})$ is the identity and hence $dualz({*})^bullet iso k$. Thus the zero-dimensional case is the ordinary coefficient object used in linear duality.

#prop(title: "The defining property")[
For every $K in Db(Shk(X))$ there is a natural isomorphism
$ RHom_k (RGamc (X,K),k) iso RHom_(Shk(X)) (K,dualz(X)^bullet) $
]
<prop:dualizing-defining-property>

#proofsketch[
The derived adjunction gives, for every $n$,
$ Hom_(Dp(Shk(X))) (K,a_X^! k[n]) iso Hom_(Dp(Vect_k)) (R a_(X,!) K,k[n]) $
These groups are the degree-$n$ cohomology groups of the two derived Hom complexes. In the standard resolution models for derived Hom, the adjunction maps assemble to the natural quasi-isomorphism
$ RHom_(Shk(X)) (K,a_X^! k) iso RHom_k (R a_(X,!) K,k) $
Substituting $dualz(X)^bullet = a_X^! k$ and $R a_(X,!) K = RGamc (X,K)$ gives the formula.
]


The representing object is compatible with restriction to open subsets.

#prop(title: "Restriction of the dualizing complex")[
For every open embedding $j:U into X$,
$ rest(dualz(X)^bullet,U) iso dualz(U)^bullet $
]
<prop:dualizing-restriction>

#proof()[
  Let $j:U into X$ be open. Extension by zero $j_!$ is exact for an open embedding, as is checked on stalks. For $L in Db(Shk(U))$, the adjunction $j_! tack.l j^(-1)$ therefore gives
$ RHom_(Shk(U)) (L,rest(dualz(X)^bullet,U))
  iso RHom_(Shk(X)) (j_! L,dualz(X)^bullet)
  iso RHom_k (RGamc (U,L),k) $
Thus $rest(dualz(X)^bullet,U)$ has the same representing property as $dualz(U)^bullet$. Uniqueness of representing objects finishes the proof.
]

// === The Verdier dual

The Verdier dual is the internal derived Hom into the dualizing complex.

#def(title: "Verdier dual")[
For $K in Db(Shk(X))$, the *Verdier dual* is
$ VDX(X) (K) := RsHom_X (K,dualz(X)^bullet) $
]
<def:verdier-dual>

It sends $Db(Shk(X))^op$ to $Dp(Shk(X))$.

For a point this becomes ordinary derived linear duality
$ VDX({*}) (V) iso RHom_k (V,k),$ and therfore the point case recovers the opening construction.

By @prop:dualizing-restriction and restriction of internal derived Hom (@lem:internal-hom-restriction),
$rest(VDX(X) (K),U) iso VDX(U) (rest(K,U)) $
and therfore the Verdier dual is therefore local in the sense that it commutes with restriction to open subsets.

#prop(title: "Local tests from supported information")[
For every open $U subset.eq X$ and $K in Db(Shk(X))$,
$ RGam (U,rest(VDX(X) (K),U)) iso RHom_k (RGamc (U,rest(K,U)),k) $
]
<prop:verdier-local-tests>

#proof[
Restriction identifies the left-hand side with
$ RGam (U,RsHom_U (rest(K,U),dualz(U)^bullet)) $
by @lem:internal-hom-restriction and @prop:dualizing-restriction. The internal--external comparison (@lem:internal-external-derived-hom) turns this into $RHom_(Shk(U)) (rest(K,U),dualz(U)^bullet), $
and the defining property @prop:dualizing-defining-property identifies that complex with the dual of $RGamc (U,rest(K,U))$.
]

This is the object sought in the motivation. One first collects the information on $U$ that is compactly supported, then takes all derived linear tests on it, and Verdier duality organises those test complexes compatibly as $U$ varies.

#prop(title: "Global Verdier duality")[
For every $K in Db(Shk(X))$,
$ RGam (X,VDX(X) (K)) iso RHom_k (RGamc (X,K),k). $
Consequently,
$ bb(H)^m (X,VDX(X) (K)) iso (bb(H)_c^(-m) (X,K))^vee. $
]
<prop:global-verdier-duality>

#proof[
Take $U=X$ in @prop:verdier-local-tests. Over a field, linear duality is exact, so $H^m (RHom_k (C,k)) iso H^(-m) (C)^vee$ for a complex $C$; this gives the second formula.
]

== Computing Verdier duals <sec:computing-verdier-duals>

First let us examine the compactly supported cochain complexes on sufficiently small neighbourhoods. Their derived duals determine the local models of $dualz(X)^bullet$; their cohomology gives the stalks described in @thm:stalks-of-dualizing-complex, while the restriction maps, and in several cohomological degrees also the extension data, determine how those local pieces assemble as a derived object. Once $dualz(X)^bullet$ is known, compute
$ VDX(X) (K) = RsHom_X (K,dualz(X)^bullet). $
For a constructible complex the same procedure may be carried out stratum by stratum or, after choosing an adapted cell decomposition, through the derived cellular realization of @sec:cellular-calculations. The local-test formula provides an independent check on the resulting object.



#thm(title: "Stalks of the dualizing complex")[
For every $x in X$ and $m in ZZ$,
$ H^m (dualz(X)^bullet)_x iso colim_(U in.rev x) (H_c^(-m) (U,k))^vee, $
where $U$ runs through open neighbourhoods of $x$ ordered by reverse inclusion.
]
<thm:stalks-of-dualizing-complex>

The theorem tests the defining property against extensions by zero from small neighbourhoods; see @Dimca2004[Thm. 3.2.9(i)] and @Iversen1986[Prop. V.2.4]. It gives a concrete calculation - compute compactly supported cohomology near the point, dualise it, and then analyzing how those local groups vary.

For $X = {*}$, as we previously
$dualz({*})^bullet iso k, quad VDX({*}) (V) iso RHom_k (V,k). $
Nothing geometric has yet been added.

#exmp(title: "The real line revisited")[
Fix $x in RR$ and choose a sufficiently small open interval $I$ around it. In @exmp:real-line-compact-cohomology we computed
$ RGamc (I,constSh(k)_I) iso shift(k,-1), $
so $H_c^q (I,k) = 0$ for $q != 1$ and $H_c^1 (I,k) iso k$. Substituting these groups into the stalk formula gives
$ H^(-1) (dualz(RR)^bullet)_x iso k, quad H^m (dualz(RR)^bullet)_x = 0 " for " m != -1. $
The canonical orientation of $RR$ identifies these one-dimensional local spaces compatibly as $x$ varies, so the surviving cohomology sheaf is constant. Hence
$dualz(RR)^bullet iso shift(constSh(k)_RR,1) $.
The same one-dimensional local class appeared as $H_c^1 (RR;k)$ in @exmp:real-line-compact-cohomology and, through the punctured-neighbourhood comparison, in the derived costalk of @exmp:stalk-derived-costalk-line. Here its dual gives the local generator of $dualz(RR)^bullet$ and accounts for the shift.
]
<exmp:dualizing-real-line>

On a real $d$-manifold, every small coordinate ball has compactly supported cohomology $k$ in degree $d$ and zero in the other degrees. Dimension therefore still produces only one shift. The local generators may nevertheless acquire nontrivial monodromy as they are transported around $X$.

#def(title: "Orientation local system")[
If $X$ is a real $d$-manifold, the *orientation local system* $"or"_X$ is the rank-one local system of local orientations. Equivalently, its stalk at $x$ is
$ ("or"_X)_x := colim_(U in.rev x) (H_c^d (U,k)^vee), $
where $U$ ranges over coordinate balls; for nested balls, the transition maps are obtained by dualising extension by zero on compactly supported cohomology.
]
<def:orientation-local-system>

#prop(title: "Dualizing complex of a manifold")[
Let $X$ be a real $d$-manifold without boundary. Then
$ dualz(X)^bullet iso shift("or"_X,d). $
If $X$ is $k$-orientable,
$ dualz(X)^bullet iso shift(constSh(k)_X,d). $
In particular, for a complex manifold of complex dimension $n$,
$ dualz(X)^bullet iso shift(constSh(k)_X,2n). $
]
<prop:dualizing-complex-of-manifold>

#proof[
A coordinate ball has compactly supported cohomology $k$ in degree $d$ and zero in the other degrees. By @thm:stalks-of-dualizing-complex, the dualizing complex therefore has one cohomology sheaf, in degree $-d$. The transition maps between its local generators are precisely those defining the orientation local system, giving $dualz(X)^bullet iso shift("or"_X,d)$. If the orientation local system is trivial, this becomes the shifted constant sheaf. Complex coordinates provide a canonical real orientation, so a complex $n$-manifold gives the shift by real dimension $2n$.
]

The open Möbius band changes only the gluing. Every small disc still contributes one class in degree $2$, but transport around the core reverses its generator. Over a field of characteristic different from $2$, the orientation local system has monodromy $-1$, and
$ dualz(M)^bullet iso shift("or"_M,2) $
The dimension has not changed; the new datum is the sign acquired when local fundamental classes are transported around a nonorientable loop.
//לא בטוח שזה באמת חשוב פה
#exmp(title: "The complex torus")[
Return to the torus whose derived global sections were computed in
@exmp:cellular-circle-torus-derived. There we obtained $RGam(T^2,constSh(k))
iso
[k arrow.r.long^0 k^2 arrow.r.long^0 k]$ in degrees $0,1,2$.

Choose $omega_1,omega_2 in CC$ linearly independent over $RR$ and set

$
Lambda := ZZ omega_1 + ZZ omega_2,
quad
E := CC \/ Lambda
$

The one-dimensional compact complex torus $E$, with the class of $0$ as origin, is the analytic space underlying an elliptic curve. Its underlying topological space is a torus, so the preceding calculation applies to $constSh(k)_E$. As a complex manifold of dimension $1$, it is a canonically oriented real manifold of dimension $2$. Hence @prop:dualizing-complex-of-manifold gives
$ dualz(E)^bullet iso shift(constSh(k)_E,2) $

Because $E$ is compact, $RGamc (E,-) iso RGam (E,-)$. Applying the defining property of the dualizing complex (@prop:dualizing-defining-property) to the constant sheaf gives
$ RHom_k (RGam (E,constSh(k)_E),k) iso RHom_(Shk(E)) (constSh(k)_E,shift(constSh(k)_E,2)) $
Taking cohomology recovers
$ H^m (E,k) iso H^(2-m) (E,k)^vee $

The earlier calculation gave dimensions $1,2,1$ in degrees $0,1,2$.
Verdier duality explains this - the shift by the real dimension $2$ pairs degrees $m$ and $2-m$. Its local origin is the compactly supported
cohomology class of a small real $2$-ball in degree $2$, while compactness of $E$ identifies ordinary and compactly supported cohomology.
]
<exmp:complex-torus-duality>

Smooth manifolds contribute local compactly supported cohomology in one degree, but a singularity can remove that simplification.

#exmp(title: "A singular point produces several local degrees")[
Let
$ X := lr({(x,y) in CC^2 mid(bar.v) x y = 0}) $
Near the origin, the local conical structure theorem (@thm:local-conical-structure) identifies a sufficiently small neighbourhood with the open cone (@def:open-cone) on the link
$ L = S^1 union.sq S^1 $
Since the link $L$ is compact, the one-point compactification of $C (L)$ is the suspension $Sigma L$. The suspension is obtained by collapsing the two ends of $L times [0,1]$ to two cone points. We write $tilde(H)^bullet$ for reduced cohomology; in positive degrees it agrees with ordinary cohomology, while $tilde(H)^0$ records connected components modulo the constant class. Compactly supported cohomology of the open cone is therefore reduced cohomology of its one-point compactification, so
$ H_c^m (C (L),k) iso tilde(H)^m (Sigma L,k) iso tilde(H)^(m-1) (L,k). $
The link has two connected components and one loop in each component, so
$ tilde(H)^0 (L,k) iso k, quad tilde(H)^1 (L,k) iso k^2 $
Hence
$ H_c^1 (C (L),k) iso k, quad H_c^2 (C (L),k) iso k^2 $
By the stalk formula (@thm:stalks-of-dualizing-complex),
$ H^(-1) (dualz(X)^bullet)_0 iso k, quad H^(-2) (dualz(X)^bullet)_0 iso k^2 $
Away from the origin the space is a smooth complex curve, so only degree $-2$ remains. At the origin an additional local degree $-1$ appears alongside the smooth degree $-2$. No single shifted sheaf can record both groups, so a genuine derived complex is required.
]
<exmp:dualizing-node>


#exmp(title: "The cellular Verdier dual on the interval")[
Let $X=[0,1]$, with vertices $v_0,v_1$ and open edge $e$, oriented from $v_0$ to $v_1$. Write the cellular sheaf of @exmp:cellular-three-stratum-line as
$ A arrow.r^alpha C arrow.l^beta B $
where the coefficient spaces are finite-dimensional over $k$.

By the derived realization of @sec:cellular-calculations, the assignment
$ sigma |-> C_c^bullet (op("st") (sigma);cF)^vee $
forms a bounded cellular complex. Curry's cellular duality identifies its realization with the Verdier dual of $op("Real")_X (cF)$; see @Curry2018[Def. 7.1 and Prop. 7.13]. With the chosen orientation, the three compactly supported complexes are
$ C_c^bullet (op("st") (v_0));cal(F)) = [A arrow.r^(-alpha) C] $
$ C_c^bullet (op("st") (v_1);cal(F)) = [B arrow.r^beta C] $
$ C_c^bullet (op("st") (e);cal(F)) = shift(C,-1) $
The vertex complexes are in degrees $0,1$, and the edge complex is concentrated in degree $1$.

Their linear duals are
$ D_0=[C^vee arrow.r^(-alpha^vee) A^vee], quad
D_1=[C^vee arrow.r^(beta^vee) B^vee], quad
D_e=shift(C^vee,1) $
with the vertex complexes now in degrees $-1,0$.

The cellular maps $D_0->D_e$ and $D_1->D_e$ are the identity on $C^vee$ in degree $-1$ and zero in degree $0$. These maps complete the description of the dual as a complex of cellular sheaves.

For the constant sheaf, $A=B=C=k$ and $alpha=beta=id$. Both vertex complexes are acyclic, while the edge complex is $shift(k,1)$. The resulting realized object is therefore
$VDX(X) (constSh(k)_X) iso lsh(j) (shift(constSh(k)_((0,1)),1)), $
where $j:(0,1) into X$.

The dependence on the open star is essential. If $A=C=k$ but $alpha=0$, the left vertex complex instead has nonzero cohomology in both degrees $-1$ and $0$. Keeping the same vertex stalk while changing its map to the edge changes the Verdier dual at that vertex.
]
<exmp:cellular-verdier-interval>

// The sequence of examples we will add one geometric difficulty at a time. A point has no dimensional shift. The real line introduces local dimension. A nonorientable manifold changes how the local generators glue. A singular point can create several local cohomological degrees. The cellular model then turns the same procedure into finite linear algebra.


The manifold, singular and cellular calculations describe the local mechanism of Verdier duality. We still need to show that these local duals remain constructible, glue across a finite stratification and reconstruct the original complex after dualising twice.

#thm(title: "Verdier biduality")[
Let $X$ be a complex algebraic variety, or a complex analytic space in a constructible setting for which Verdier duality preserves $Dbc(X)$. Then $VDX(X)$ is a contravariant triangulated equivalence on $Dbc(X)$. For every $K in Dbc(X)$, the canonical evaluation morphism
$ K -> VDX(X) (VDX(X) (K)) $
is an isomorphism.
]
<thm:verdier-duality>
#proofsketch[ 
We use Verdier biduality and preservation of constructibility as external theorems; see #cite(<Dimca2004>, supplement: [Thm. 3.3.6 and §4.1]), #cite(<KashiwaraSchapira1990>, supplement: [Prop. 3.4.3]), and #cite(<Iversen1986>, supplement: [§VII.5]). The preceding examples explain the local calculations involved. On a smooth open stratum, Verdier duality combines finite-dimensional linear duality with the dimension shift. At a boundary point, the dual stalk is determined by compactly supported local cohomology, as in @thm:stalks-of-dualizing-complex and @exmp:dualizing-node. These calculations illustrate the theorem, but do not by themselves prove constructibility of the dual or global biduality.
]

== Boundary operations and recollement <sec:costalks>

We now study how sheaves are transported along a map $f:X -> Y$, with particular attention to an open subset and its closed complement. The direct and inverse image functors associated with these inclusions give the adjunctions and distinguished triangles used to construct perverse sheaves. Additional operations will be introduced in @chap:riemann-hilbert alongside their differential-module counterparts.

// How sheaf information is transported along a map $f:X->Y$ and across the boundary between an open subset and its closed complement? A full calculus of operations exists, but for defining perverse sheaves we do not not need all of it. This section develops exactly the relevant operations, while the remaining operations will enter with the Riemann--Hilbert proof, once their differential counterparts will be available.

=== Direct and proper direct image

The ordinary direct image $f_*$ of @def:direct-image collects all sections over inverse images of opens. The proper direct image $f_!$ of @def:proper-direct-image keeps only sections whose support is proper over the target. Both are left exact in the present setting, so their derived versions retain the higher obstruction data.

#def(title: "Derived direct images")[
Let $f:X->Y$ be continuous. The right derived functors of $f_*$ and $f_!$ are denoted $Rpush(f)$ and $Rpushc(f)$. For $K in Dp(Shk(X))$, they may be computed by choosing an injective resolution $K->I^bullet$ and applying the ordinary functors termwise:
$ Rpush(f) (K) iso f_* I^bullet, quad Rpushc(f) (K) iso f_! I^bullet $
]
<def:derived-direct-images>
For $a_X:X -> {*}$, ordinary pushforward is the global-section functor $Gamma(X,-)$, while proper pushforward is the compactly supported section functor $Gamma_c(X,-)$ of the proper push forward (@def:proper-direct-image). Their derived functors satisfy
$ Rpush(a_X) (K) = RGam (X,K), quad Rpushc(a_X) (K) = RGamc (X,K) $
Because the target is a point, the distinction between the two pushforwards is exactly the distinction between ordinary and compactly supported global information.

Let $j:U=bb(R) without {0} arrow.r.hook bb(R)$. Since extension by zero along an open inclusion is exact, $R j_! k_U=j_! k_U$, and its stalk at the origin is zero in every degree. To compute the stalk of $R j_* k_U$, take $V_epsilon=(-epsilon,epsilon)$. The punctured interval $V_epsilon sect U=(-epsilon,0) union (0,epsilon)$ consists of two contractible components, so $H^0(V_epsilon sect U;k) approx k plus.o k$ and $H^q(V_epsilon sect U;k)=0$ for $q>0$. Restriction to smaller punctured intervals preserves the two component values, so passing to the stalk gives $cal(H)^0(R j_* k_U)_0 approx k plus.o k$ and $cal(H)^q(R j_* k_U)_0=0$ for $q != 0$. Thus $(R j_* k_U)_0 approx (k plus.o k)[0]$, whereas $(j_! k_U)_0=0$. The two copies of $k$ record the independent locally constant values on the two sides of the missing point.

=== Inverse and exceptional inverse image <sec:grothendieck-six-operations>

Ordinary inverse image reads information on the source from information on the target. It preserves stalks and is exact for sheaves of vector spaces (@prop:inverse-image-stalks), so the sheaf-level adjunction @prop:inverse-direct-adjunction passes directly to the derived category:
$ f^(-1) tack.l Rpush(f) $
No derived replacement of $f^(-1)$ is needed.

The support-sensitive pushforward $R f_!$ has a different right adjoint. We already met its special case for $a_X$ when constructing the dualizing complex. The general theorem says that the same supported reading exists relative to a map.

#thm(title: "Existence of the exceptional inverse image")[
Let $f:X->Y$ be continuous, with $X$ and $Y$ locally compact Hausdorff and countable at infinity. Assume that there is an integer $N$ such that, for every sheaf $cF$ on $X$ and every $q>N$,
$ cohsh(q,Rpushc(f) (cF)) = 0 $
Then there is a functor
$ ushr(f):Dp(Shk(Y))->Dp(Shk(X)) $
characterised by natural isomorphisms
$ Hom_(Dp(Shk(Y))) (Rpushc(f) (K),L) iso Hom_(Dp(Shk(X))) (K,ushr(f) (L)) $
Thus
$ Rpushc(f) tack.l ushr(f). $
]
<thm:exceptional-inverse-image>

The hypothesis gives a uniform upper bound on the nonzero derived functors of $f_!$ on sheaves. The cited existence theorem uses this finite cohomological dimension to construct the right adjoint on $Dp$; preservation of boundedness alone would not establish its existence. For $f=a_X$, this is the adjoint used in @def:dualizing-complex. We take the existence proof from @Dimca2004[Thm. 3.2.3 and Cor. 3.2.4], @KashiwaraSchapira1990[Thm. 3.1.5], and @Iversen1986[§VII.3].

For a point inclusion, exceptional inverse image is the derived costalk already constructed in the @chap:sheaf-cohomology.

#prop(title: "The point case of exceptional inverse image")[
Let $i_x:{x} into X$. The exceptional inverse image $ushr(i_x) (K)$ is canonically identified with the derived costalk of @def:derived-costalk. Equivalently, for every $V in Dp(Vect_k)$,
$ Hom_(Dp(Shk(X))) (i_(x,*) V,K) iso Hom_(Dp(Vect_k)) (V,ushr(i_x) (K)). $
]
<prop:costalk-exceptional-inverse-image>

#proof[
The inclusion of a point is closed, so proper and ordinary direct image agree: $Rpushc(i_x) = i_(x,*)$. The derived costalk is the right adjoint to this point-supported direct image, while @thm:exceptional-inverse-image characterises $ushr(i_x)$ by the same adjunction. Uniqueness of right adjoints gives the identification.
]

The left-hand side of the displayed adjunction asks for maps into $K$ from an object supported entirely at $x$; the right-hand side says that every such map is encoded by $i_x^! K$. The relative-neighbourhood cone formula (@prop:derived-costalk-cone) computes this same object by comparing a small neighbourhood of $x$ with the neighbourhood after removing $x$.

#ed[On the line at the origin, $i^(-1)$ simply reads the stalk $k$ of the constant sheaf. The exceptional inverse image instead computes the relative local complex comparing a neighbourhood of the origin with the punctured neighbourhood, and the calculation of @exmp:stalk-derived-costalk-line gives
$ ushr(i) (constSh(k)_RR) iso shift(k,-1) $]
The two inverse images therefore answer different local questions: $i^(-1)$ asks what remains visible at the point, while $i^!$ asks what contribution is supported there relative to deleting it.

=== #ed[Dictionary of basic operations] <sec:six-operations-dictionary>

The preceding examples can be compressed into a small dictionary of basic maps.

#prop(title: "Dictionary of basic maps")[
Let $K in Db(Shk(X))$.

+ For $a_X:X->{*}$,
  $ Rpush(a_X) (K) = RGam (X,K), quad Rpushc(a_X) (K) = RGamc (X,K). $
+ For $i_x:{x} into X$,
  $ invimg(i_x,K) = K_x $
  is the stalk and $ushr(i_x) (K)$ is the derived costalk.
+ For an open embedding $j:U into X$,
  $ lsh(j) tack.l j^(-1) tack.l Rpush(j), quad ushr(j) = j^(-1). $
+ For a closed embedding $i:Z into X$,
  $ i^(-1) tack.l i_* tack.l ushr(i), quad Rpushc(i) = Rpush(i) = i_*. $
]
<prop:basic-maps-six-operations>

The first line turns geometry over a point into ordinary versus compactly supported cohomology. The second turns a point inclusion into stalk versus costalk. The last two compare the two ways of crossing an open--closed boundary. #ed[Each row was realised above on the line at the origin: ordinary against compactly supported sections, stalk against costalk, and the two extensions across the puncture.]

#thm(title: "Preservation of algebraic constructibility")[
Let $f:X->Y$ be a morphism of complex algebraic varieties. The functors
$ Rpush(f), quad Rpushc(f), quad invimg(f,-), quad ushr(f) $
preserve bounded complexes with algebraically constructible cohomology sheaves.
]
<thm:six-operations-preserve-constructibility>

This preservation theorem allows the geometric direct- and inverse-image operations introduced above to be performed inside the constructible derived categories. We use it as an external result; see @Dimca2004[§§2.3 and 4.1] and @KashiwaraSchapira1990[§§8.4--8.5].

#ed[Verdier duality interacts with these operations by exchanging ordinary and support-sensitive transport.]

#thm(title: "Verdier duality and geometric operations")[
Let $f:X->Y$ be an algebraic morphism and assume the displayed operations preserve the bounded constructible categories. For $K in Dbc(X)$ and $L in Dbc(Y)$ there are natural isomorphisms
$ VDX(Y) (Rpush(f) (K)) iso Rpushc(f) (VDX(X) (K)), $
and
$ VDX(X) (invimg(f,L)) iso ushr(f) (VDX(Y) (L)). $
Equivalently, using biduality,
$ VDX(Y) (Rpushc(f) (K)) iso Rpush(f) (VDX(X) (K)), $
and
$ VDX(X) (ushr(f) (L)) iso invimg(f,VDX(Y) (L)). $
The same identities hold for analytic maps whenever the corresponding operations preserve $Dbc$.
]
<thm:verdier-exchange>

#ed[The first identity says that dualising after ordinary pushforward agrees with properly supported pushforward of the dual. The second is the relative form of the stalk--costalk exchange; for a point inclusion it specialises to the local exchange displayed in the recollement discussion below. The proof rests on a sheaf-valued relative form of the adjunction $Rpushc(f) tack.l ushr(f)$ together with biduality, and the constructible finiteness needed for the passage to $Dbc$ is part of the external theorem; the formal mechanism is developed with the common calculus in the Riemann--Hilbert chapter. See @Dimca2004[Thm. 3.3.6 and §4.1], @KashiwaraSchapira1990[Prop. 3.4.3], and @Iversen1986[§VII.5].]

=== Recollement <sect:recollement>

A closed subset and its open complement provide the smallest nontrivial example of gluing. Let $i:Z into X$ be closed and let $j:U = X-Z into X$ be the complementary open embedding. We work in a constructible setting in which the six operations in this decomposition preserve $Dbc$; this holds in the algebraic setting of @thm:six-operations-preserve-constructibility, and in the analytic setting whenever the corresponding preservation theorem applies. Assume moreover that $Z$ and $U$ are constructible for a common finite stratification, for example that $Z$ is a closed union of strata. #ed[The line at the origin already showed the local difference between $j_!$ and $R j_*$ and between $i^(-1)$ and $i^!$.] The corresponding global statement is that an object on $X$ can be reconstructed from its open and closed pieces in two dual ways.

#thm(title: "The two open--closed triangles")[
For every $K in Dbc(X)$ there are natural distinguished triangles
$ lsh(j) (j^(-1) K) -> K -> i_* (i^(-1) K) -> shift(lsh(j) (j^(-1) K),1), $
and
$ i_* (ushr(i) (K)) -> K -> Rpush(j) (j^(-1) K) -> shift(i_* (ushr(i) (K)),1). $
]
<thm:recollement>

#proof[
For an ordinary sheaf $F$, the sequence
$ 0 -> j_! j^(-1) F -> F -> i_* i^(-1) F -> 0 $
is exact on stalks: on $U$ it is $0->F_x->F_x->0$, while on $Z$ it is $0->0->F_x->F_x->0$. Applying this degreewise to a representative of $K$ gives the first distinguished triangle. Apply the first triangle to $VDX(X) (K)$ and then apply $VDX(X)$. Biduality @thm:verdier-duality and the exchange identities @thm:verdier-exchange transform the three terms into $i_* i^! K$, $K$ and $R j_* j^(-1) K$, giving the second triangle.
]

The first triangle reconstructs $K$ from its restriction to $U$ and the information ordinarily visible on $Z$. The second reconstructs it from the contribution supported on $Z$ and the open information retained by $R j_*$. Applying cohomology to either triangle produces the corresponding long exact sequence, while the final morphism of the triangle packages the entire family of connecting maps. This is the same passage from exact sequences to distinguished triangles developed in @chap:derived-categories, now applied to the attachment of open and closed geometric pieces.


#prop(title: "Open--closed recollement")[
#ed[Under the constructibility hypothesis above, the six functors
$ i^(-1), i_*, ushr(i), quad lsh(j), j^(-1), Rpush(j) $
preserve the corresponding constructible derived categories, and together with the adjoint triples $i^(-1) tack.l i_* tack.l ushr(i)$ and $lsh(j) tack.l j^(-1) tack.l Rpush(j)$ (@prop:basic-maps-six-operations) and the two triangles of @thm:recollement they constitute a *recollement* of $Dbc(X)$ by $Dbc(Z)$ and $Dbc(U)$. In particular the insertion functors $i_*$, $j_!$ and $R j_*$ are fully faithful, the essential image of $i_*$ consists exactly of the objects killed by $j^(-1)$, and the incompatible readings vanish:
$ i^(-1) j_! = 0, quad j^(-1) i_* = 0, quad i^! R j_* = 0. $]
]
<prop:open-closed-recollement>

#ed[The second statement says that the closed category is exactly the part of $Dbc(X)$ invisible on the open piece. Preservation of constructibility holds in the algebraic setting by @thm:six-operations-preserve-constructibility and is part of the standing hypothesis in the analytic one; the remaining assertions are formal consequences of the adjunctions and the two triangles. For the axiomatic formulation of recollement see @BBD1982[§1.4].]

#exmp(title: "The two reconstructions across the origin")[
Take $X = RR$, $Z = {0}$, $U = RR-{0}$ and $K = constSh(k)_RR$. The object $j_! j^(-1) K$ has zero stalk at the origin, while $R j_* j^(-1) K$ has stalk $k ds k$, one copy from each side. The first triangle restores the missing ordinary stalk $k$. The second uses the derived costalk $shift(k,-1)$ computed in @exmp:stalk-derived-costalk-line to correct the two boundary values retained by $R j_*$. Both triangles reconstruct the same constant sheaf, but they express the attaching data from the two dual local directions.
]
<exmp:recollement-line>

Verdier duality exchanges the two open--closed reconstructions through
$ VDX(X) j_! iso R j_* VDX(U), quad
  VDX(Z) i^(-1) iso i^! VDX(X). $
For a point inclusion $i_x:{x} into X$, the corresponding local identities can be displayed together as

#align(center)[#diagram(
  spacing: 1.5cm,
  node((0,0), $invimg(i_x,VDX(X) (K))$),
  node((0,1), $ushr(i_x) (VDX(X) (K))$),
  node((1,0), $RHom_k (invimg(i_x,K),k)$),
  node((1,1), $RHom_k (ushr(i_x) (K),k)$),
  edge((0,0),(1,1), "->", label: $iso$),
  edge((0,1),(1,0), "->", label: $iso$),
)]

The crossed arrows display the exchange between the two local readings. Ordinary information of the dual is determined by the linear dual of the supported information of $K$, while supported information of the dual is determined by the linear dual of the ordinary information of $K$. The relative-neighbourhood cone formula of @prop:derived-costalk-cone gives a model for the supported term by comparing a neighbourhood of $x$ with the punctured neighbourhood, and this is the local contribution that appears in the second recollement triangle.

A finite stratification allows recollement to be applied inductively. One separates an open stratum from its closed complement, studies the object on each part, and then reconstructs the original object from this data. Repeating this process, which called *dévissage*, reduces questions about constructible complexes on the whole space to corresponding questions on the individual strata and hence very useful to our purposes. 


== Support dimension<sec:standard-insufficient>

Let $E$ be the smooth complex curve of @exmp:complex-torus-duality, and let $i:{p} into E$ be the inclusion of a point. Verdier duality acts on the following two objects by shifts determined by the dimensions of their supports.

#exmp(title: "Different supports require different shifts")[
The curve-supported side was computed in @exmp:complex-torus-duality: $VDX(E) (constSh(k)_E) iso shift(constSh(k)_E,2)$,
so $shift(constSh(k)_E,1)$ is self-dual. The point-supported side requires no shift
$ VDX(E) (i_* k) iso i_* (VDX({p}) (k)) iso i_* k $
The second equality is the point case, $dualz({p})^bullet iso k$, so finite-dimensional duality does not create a dimensional shift. The difference between the two objects comes from the dimensions of their supports.
]
<exmp:duality-breaks-standard-heart>

 The curve-supported object is centred by $[1]$, whereas the point-supported object is centred in degree $0$. Thus there is no single global shift that makes both types of objects self-dual in the same degree. The appropriate degree bounds must instead depend on the dimension of the support and must exchange stalk and costalk conditions under Verdier duality. - as we will see in the next chapter. 
