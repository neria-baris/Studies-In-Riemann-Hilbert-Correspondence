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

= Perverse Sheaves <chap:perverse-sheaves>

== Motivation <sec:perverse-problem>

The calculation of @exmp:duality-breaks-standard-heart shows that Verdier duality does not preserve the standard $t$-structure. Thus, if we want a $t$-structure compatible with Verdier duality, the allowed cohomological degrees must depend on the dimension of the stratum on which an object is supported. As we saw, Verdier duality exchanges stalks and costalks. Since these encode complementary kinds of local information, the desired conditions should likewise come in a dual pair.

In this chapter, $k$ is a field. We fix a finite Whitney stratification $cal(S)$ of $X$ by connected complex analytic strata, and every object is constructible with respect to $cal(S)$. For a stratum $S$, write $i_S:S into X$ for its inclusion. Dimension means complex dimension throughout this chapter.

== Dimension-dependent conditions <sec:support-cosupport>

On the torus $E$, a local system is centred as $shift(cL,1)$, while a skyscraper supported at a point is centred without a shift. More generally, let $S$ be a stratum of complex dimension $d$. We seek a degree bound $p(S)$ for the ordinary local information along $S$:
$ H^m (invimg(i_S,K))=0 " for " m>p(S) $
The example (@exmp:duality-breaks-standard-heart) suggests that $p(S)$ should depend on $d$ and the compatibility with Verdier duality determines it

Since $S$ is a complex manifold of complex dimension $d$, its dualizing complex is $shift(constSh(k)_S,2 d)$ (@prop:dualizing-complex-of-manifold). The stalk--costalk exchange gives
$ ushr(i_S) VDX(X) K iso VDX(S) invimg(i_S,K) $
and therefore
$ H^m (ushr(i_S) VDX(X) K) iso (H^(-m - 2 d) (invimg(i_S,K)))^vee $
If the stalk condition vanishes above $p(S)$, the formula shows that the corresponding costalk condition for the Verdier dual vanishes below
$ -p(S)-2 d. $
For Verdier duality to exchange the two halves of the same degree convention, this lower cutoff must again be $p(S)$. Hence
$p(S)=-p(S)-2 d, $
so
$p(S)=-d. $

Thus $-d$ is the unique stratumwise cutoff fixed by the transformation
$ p |-> -p-2 d $
induced by Verdier duality.

The calculation gives the upper bound on ordinary local information,
$ H^m (invimg(i_S,K))=0 " for " m>-dim S $
Verdier duality forces the complementary lower bound on supported local information:
$ H^m (ushr(i_S) K)=0 " for " #ed($m < -dim S$) $

#def(title: "Perverse support and costalk conditions")[
Define full subcategories of $D_c^b (X; k)$ by
$ pDle(0) (X):= {K bar.v H^m (invimg(i_S,K))=0 " for every " S in cal(S) " and " m > -dim S}, $
$ pDge(0) (X):= {K bar.v H^m (ushr(i_S) K)=0 " for every " S in cal(S) " and " m < -dim S}. $
]
<def:perverse-conditions>

For $n in ZZ$, we use the shifted notation
$ pDle(n) (X):=shift(pDle(0) (X),-n), quad pDge(n) (X):=shift(pDge(0) (X),-n) $

The stratumwise formulation is convenient for the definition. For calculations at a point, the corresponding bounds take a slightly different form because the point costalk includes the real-dimensional shift of the stratum.

#rmrk(title: "Stratum conditions and pointwise bounds")[
The definition is stated for the restriction and exceptional restriction along an entire stratum. If $x in S$, write $i_x:{x} into X$ and let $dim S=d$. The equivalent pointwise bounds are
$ H^m (invimg(i_x,K))=0 " for " m>-d, quad H^m (ushr(i_x) K)=0 " for " m<d. $
The two tests behave differently under this passage:

#table(
  columns: (1.2fr, 1.6fr, 1.6fr),
  inset: 6pt,
  align: left,
  [], [*Along the stratum $S$*], [*At a point $x in S$*],
  [Ordinary local test], [$H^m=0$ for $m>-d$], [$H^m=0$ for $m>-d$],
  [Supported local test], [$H^m=0$ for #ed($m < -d$)], [$H^m=0$ for $m<d$],
)

Only the supported test changes, by the real-dimensional shift $2 d$ of the stratum. #ed[To see the shift, factor the point inclusion as
$ {x} ->^(i_(x,S)) S ->^(i_S) X $
For closed embeddings, ordinary and proper direct image agree, so their right adjoints compose - 
$ ushr(i_x) K iso ushr(i_(x,S)) (ushr(i_S) K). $
Put $M := ushr(i_S) K$. Constructibility makes the cohomology sheaves of $M$ locally constant on $S$. Since $S$ is a complex manifold of real dimension $2 d$ with its canonical orientation, the manifold calculation of @prop:dualizing-complex-of-manifold gives
$ ushr(i_(x,S)) (M) iso shift(invimg(i_(x,S),M),-2 d) $
Consequently,
$ H^m (ushr(i_x) K) iso H^(m - 2 d) (invimg(i_(x,S),ushr(i_S) K)) $
The stratumwise condition makes the right-hand side vanish when $m - 2 d < -d$, or equivalently when $m < d$. This is the pointwise costalk bound in the table.] Geometrically, we work inside the smooth stratum $S$ and choose a sufficiently small ball $B$ around $x$. Its real dimension is $2 d$, and the local cohomology of the pair formed by $B$ and the punctured ball $B-{x}$ is one-dimensional in degree $2 d$. Hence
$ ushr(i_(x,S)) constSh(k)_S iso shift(k,-2 d) $
For a local system $cL$ on $S$, the same calculation is performed fibrewise. After the shift by $d$ it gives
$ invimg(i_(x,S),shift(cL,d)) iso shift(cL_x,d) quad ushr(i_(x,S)) shift(cL,d) iso shift(cL_x,-d) $
Thus the point stalk is concentrated in ordinary degree $-d$, while the point costalk is concentrated in degree $+d$. The normalization by the complex dimension places these two local readings symmetrically around degree zero, and the real-dimensional shift $2 d$ contributed by the ball is divided equally between them.
]
<rmrk:pointwise-perverse-bounds>

#exmp(title: "The torus and a point")[
Let $i:{p} into E$ be the inclusion of a point in the torus. The shifted local system $shift(constSh(k)_E,1)$ and the skyscraper $push(i,V)$ both satisfy the perverse conditions. At $p$,
$ invimg(i,shift(constSh(k)_E,1)) iso shift(k,1), quad ushr(i) shift(constSh(k)_E,1) iso shift(k,-1), $
so the ordinary stalk and costalk degrees are $-1$ and $+1$. For $push(i,V)$ both are $V$ in degree $0$. The dimension-dependent bounds therefore place both objects in perverse degree zero.
]
<exmp:basic-perverse-objects>

The local conditions can also be read as a bound on the dimensions of the supports of the ordinary cohomology sheaves.

#prop(title: "Support formulation and duality")[
For $K in D_c^b (X; k)$,
$ K in pDle(0) (X) <==> dim supp H^m (K)<= -m " for every " m, $
and
$ K in pDge(0) (X) <==> VDX(X) K in pDle(0) (X) <==> dim supp H^m (VDX(X) K)<= -m " for every " m. $
]
<prop:support-formulation>

#proofsketch[
On a stratum $S$, exactness of restriction gives
$ rest(H^m (K),S) iso H^m (invimg(i_S,K)). $
The first perverse condition says that $H^m (K)$ vanishes on every stratum of dimension greater than $-m$. Because the support of a constructible sheaf is a union of closures of strata, this is equivalent to the displayed support bound. The second equivalence follows from the stalk--costalk exchange under Verdier duality (@thm:verdier-duality) and exactness of finite-dimensional linear duality. See @BBD1982[§2.2] and @Dimca2004[Prop. 5.1.16].
]

The support half can be read as a staircase relating ordinary degree to support dimension. For a complex threefold:

#table(
  columns: (1.2fr, 3fr),
  inset: 6pt,
  align: left,
  [*Ordinary degree $m$*], [*Where $H^m (K)$ may be supported*],
  [$-3$], [Anywhere in $X$; support dimension may be $3$],
  [$-2$], [On subsets of complex dimension at most $2$],
  [$-1$], [On curves and points],
  [$0$], [On points],
  [$m>0$], [Nowhere],
)


On a complex curve the two local conditions admit a sheaf-theoretic dictionary.

#prop(title: "The perverse conditions on a curve")[
Let $X$ be a complex curve stratified by a smooth open stratum and finitely many point strata. A constructible complex $K$ satisfies both perverse conditions if and only if

+ $H^m (K)=0$ for $m != -1,0$;
+ $H^0 (K)$ is supported on the point strata;
+ $H^(-1) (K)$ has no nonzero subsheaf supported on the point strata.
]
<prop:curve-dictionary>

#proof()[
Let $j:U arrow.r.hook X$ be the smooth open part and $i:Z arrow.r.hook X$ the finite set of point strata. Suppose first that $K$ satisfies the perverse conditions. On $U$, the two conditions force $j^(-1)K$ to be a local system placed in degree $-1$. The support condition gives $cal(H)^m(K)=0$ for $m>0$ and confines $cal(H)^0(K)$ to $Z$.

Apply $i^(-1)$ to the second recollement triangle to obtain $i^!K -> i^(-1)K -> i^(-1)R j_* j^(-1)K -> (i^!K)[1]$. Since $j^(-1)K$ is concentrated in degree $-1$ and $R j_*$ is a right derived functor of a left-exact functor, the third term has no cohomology below degree $-1$. The long exact sequence therefore gives $H^m(i^!K) tilde.equiv H^m(i^(-1)K)$ for $m<-1$. The point-costalk condition makes the left-hand side zero. Together with the calculation on $U$ and exactness of stalks, this proves $cal(H)^m(K)=0$ for $m<-1$.

Put $cal(F)=cal(H)^(-1)(K)$ and $cal(G)=cal(H)^0(K)$. The canonical truncation triangle is $cal(F)[1] -> K -> cal(G) -> cal(F)[2]$. Exceptional inverse image is the right derived functor of the ordinary left-exact supported-section functor, so $i^!cal(F)$ and $i^!cal(G)$ have no negative cohomology. Applying $i^!$ to this triangle gives $H^(-1)(i^!K) tilde.equiv H^0(i^!cal(F))$. The sheaf $i_*H^0(i^!cal(F))$ is the largest subsheaf of $cal(F)$ supported on $Z$. The point-costalk condition therefore excludes every nonzero such subsheaf.

Conversely, suppose the three stated conditions hold. On $U$, they make $j^(-1)K$ a local system in degree $-1$, so both perverse conditions hold there. At $Z$, the stalk condition follows from the absence of positive cohomology. Applying $i^!$ to the same truncation triangle shows that its cohomology vanishes below degree $-1$, and that its degree-$-1$ cohomology is $H^0(i^!cal(F))$. The third assumption makes this group zero. Thus the costalk condition holds at every point stratum as well.

]


== The perverse $t$-structure <sec:perverse-t-structure>

#ed[To obtain kernels, cokernels and images, the two classes of @def:perverse-conditions must form a $t$-structure. On a single smooth stratum of dimension $d$ they are the standard $t$-structure shifted by $d$; on a stratified space these shifted structures are glued across open--closed decompositions.]

#thm(title: [Gluing a $t$-structure])[
Let $i:Z into X$ be a closed embedding with open complement $j:U into X$. Suppose bounded $t$-structures
$ (cal(T)_Z^(<=0), cal(T)_Z^(>=0)) quad "and" quad (cal(T)_U^(<=0), cal(T)_U^(>=0)) $
are given on $D_c^b (Z; k)$ and $D_c^b (U; k)$. Then the conditions
$ invimg(j, K) in cal(T)_U^(<=0), quad invimg(i, K) in cal(T)_Z^(<=0) $
and
$ invimg(j, K) in cal(T)_U^(>=0), quad ushr(i) K in cal(T)_Z^(>=0) $
define a bounded $t$-structure on $D_c^b (X; k)$.
]
<thm:gluing-t-structures>

#proofsketch[
Only the mechanism of the construction is sketched here. Orthogonality follows from the first open--closed triangle
$ lsh(j) invimg(j, A) -> A -> push(i, invimg(i, A)) ->, $
together with the adjunctions $j_! tack.l j^(-1)$ and $i_* tack.l i^!$ from the open--closed recollement (@prop:open-closed-recollement). For truncations, first truncate the restriction of an object to $U$ and lift the resulting triangle to $X$. The remaining term is supported on $Z$, where it can be truncated using the given $t$-structure on $Z$. The octahedral axiom (@def:triangulated-category) splices the two corrections into a truncation triangle on $X$.

The rest of the proof verifies functoriality of this construction and the remaining $t$-structure axioms after the two truncations are spliced. Those checks use the same adjunction and octahedral diagrams. See @BBD1982[§1.4] and @Dimca2004[Thm. 5.2.4].
]

#thm(title: [The perverse $t$-structure])[
The pair
$(pDle(0) (X), pDge(0) (X)) $
is a bounded $t$-structure on $D_c^b (X; k)$.
]
<thm:perverse-t-structure>

#proof[
#ed[Induct on the number of strata. With a single stratum the perverse conditions are the shifted standard $t$-structure, as observed above. For the inductive step, remove an open stratum $j:U into X$ and let $i:Z into X$ be its closed complement. The perverse conditions (@def:perverse-conditions) split along this decomposition: the upper half is tested by $invimg(j,-)$ and $invimg(i,-)$, the lower half by $invimg(j,-)$ and $ushr(i)$. These are exactly the hypotheses of the gluing theorem (@thm:gluing-t-structures), applied to the $t$-structures already constructed on $U$ and on $Z$ by the induction.]
]

Changing the $t$-structure does not change $D_c^b (X; k)$ or its morphisms. It changes which objects count as degree zero, and with them the meanings of subobject, quotient, kernel, cokernel and short exact sequence. The heart of this new $t$-structure is the category of perverse sheaves.

#def(title: "Perverse sheaf")[
For a fixed adapted stratification $cal(S)$, a *perverse sheaf* on $X$ is an object of the heart
$ Perv_(cal(S)) (X):=pDle(0) (X) sect pDge(0) (X). $

]
<def:perverse-sheaf>
Note that a perverse sheaf can have ordinary cohomology sheaves in several degrees; "degree zero" here refers to the perverse $t$-structure. Also, perversity of a constructible object is independent of the chosen adapted stratification in our allowed class (@rmrk:perverse-common-refinement), so we write $Perv (X)$ when working in $D_c^b (X; k)$.

On a point, $Perv ({*})$ is the category of finite-dimensional $k$-vector spaces. On a smooth connected complex manifold of dimension $d$ with one stratum, the assignment
$cL |-> shift(cL, d) $
identifies finite-rank local systems with perverse sheaves. On a mixed-dimensional stratification, the restriction of a general perverse sheaf to every stratum need not be a single shifted local system. In other words, the heart allows objects supported in different dimensions to be treated in one abelian category and assembled by extensions.


We denote the perverse truncation functors by $ptle(n)$ and $ptge(n)$ and the corresponding cohomology functors by $pH(n)$ (Perverse cohomology uses the dimension-dependent grading defined above). Thus $pH(0) (K)$ is the degree-zero cohomology object of $K$ for the perverse $t$-structure.

#cor(title: "The perverse heart")[
$Perv (X)$ is an abelian category. If a morphism $P -> Q$ in the heart is completed to a triangle
$ P -> Q -> C -> shift(P, 1), $
then
$ ker_(Perv (X)) (P -> Q) iso pH(-1) (C), quad op("coker")_(Perv (X)) (P -> Q) iso pH(0) (C). $
]
<cor:perverse-abelian>

#proof[
The abelian-heart theorem (@thm:heart-abelian) says that the heart of every $t$-structure is abelian. Applying that result to the perverse $t$-structure gives the first statement. The displayed kernel and cokernel formulas are the usual heart construction applied to the cone triangle of $P -> Q$.
]

#cor(title: "Verdier duality preserves the perverse heart")[
Verdier duality restricts to an exact contravariant equivalence
$ VDX(X): Perv (X)^"op" -> Perv (X), $
and biduality remains valid on the heart.
]
<cor:duality-preserves-perv>

#proof[
The support formulation and its dual half (@prop:support-formulation) show that $VDX(X)$ exchanges $pDle(0) (X)$ and $pDge(0) (X)$. Hence it preserves their intersection. Exactness follows because a contravariant functor exchanging the two halves of a $t$-structure reverses short exact sequences in the heart.
]

#rmrk(title: "Middle perversity")[
It is worth noting that perverse sheaves can be defined around different folding points (i.e - dimension-dependent cutoffs), giving different perversity functions. The choice used here is the middle perversity. It is distinguished by the property just proved, as Verdier duality exchanges the two halves of the resulting $t$-structure and therefore preserves its heart. In other words, among perversities, the middle one has unusually good manners under duality. See @Dimca2004[§5.1] and @Goresky2026[§20.5].
]

#rmrk(title: "Refining the stratification")[
A *common refinement* of two stratifications $cal(S)$ and $cal(T)$ is a third stratification $cal(R)$ whose every stratum is contained in a stratum of $cal(S)$ and in a stratum of $cal(T)$. Geometrically, $cal(R)$ cuts the two decompositions into smaller pieces until both are simultaneously respected. In the constructible derived category we already assumed that the allowed finite Whitney stratifications admit such common refinements (@def:constructible-derived-category).

If $K$ is constructible with respect to two adapted stratifications, passing to a common refinement does not change the support dimensions of its cohomology sheaves. The support formulation (@prop:support-formulation) therefore gives the same perverse condition after refinement. However, the statement concerns a fixed constructible object, while a finer stratification may, of course, make additional objects constructible.
]
<rmrk:perverse-common-refinement>

== Extensions across a boundary <sec:perverse-exactness>

#ed[The first use of the new heart is the boundary-extension problem, whose basic phenomenon already appears on a curve.]

#exmp(title: "The two extreme extensions on a punctured curve")[
Let $Delta$ be a small complex disc, let $U=Delta-{0}$, and write
$ j:U into Delta quad i:{0} into Delta $
Let $cL_T$ be a finite-rank local system on $U$ with fibre $V$ and monodromy $T$, and put $P:=shift(cL_T,1)$.

The cellular calculation of @exmp:cellular-link-monodromy gives
$ C_T^bullet:=RGam (U,cL_T) iso [V arrow.r.long^(T - id_V) V] $
with
$ H^0 (C_T^bullet) iso V^T:=ker (T - id_V) quad H^1 (C_T^bullet) iso V_T:=coker (T - id_V) $

Consider the two derived extensions
$P_!:=lsh(j) (P) quad P_*:=Rpush(j) (P) $.
The stalk of $P_*$ at the origin is computed by derived sections on sufficiently small punctured discs, so
$invimg(i,P_*) iso shift(C_T^bullet,1)$.
The incompatible costalk reading vanishes by the open-closed (@prop:open-closed-recollement) 
$ushr(i) (P_*)=0$.

For extension by zero,
$invimg(i,P_!)=0 $.
Applying $invimg(i,-)$ to the second triangle of @thm:recollement gives
$ ushr(i) (P_!) iso shift(invimg(i,P_*),-1) iso C_T^bullet $

#table(
  columns: (0.8fr, 1.6fr, 1.6fr),
  inset: 6pt,
  align: left,
  table.header(
    [*Object*],
    [*Stalk at the origin*],
    [*Costalk at the origin*],
  ),
  [$P_*$],
  [$shift(C_T^bullet,1)$ in degrees $-1$ and $0$],
  [$0$],
  [$P_!$],
  [$0$],
  [$C_T^bullet$ in degrees $0$ and $1$],
)

On $U$, both extensions restrict to $P$, which is concentrated in degree $-1$. At the point stratum, the table gives no positive stalk cohomology and no negative costalk cohomology. The pointwise bounds of @rmrk:pointwise-perverse-bounds therefore show that both $P_!$ and $P_*$ are perverse. This is special to the one-dimensional local model; @exmp:direct-image-not-perverse shows that the conclusion fails already in complex dimension $2$.

When $T=id_V$, put
$ P_0:=shift(constSh(V)_Delta,1) $
Rotating the two open--closed triangles gives short exact sequences in $Perv (Delta)$:
$ 0 -> push(i,V) -> P_! -> P_0 -> 0 $
$ 0 -> P_0 -> P_* -> push(i,V) -> 0 $
Thus the two extreme extensions differ from the middle extension by a boundary subobject on the $j_!$ side and a boundary quotient on the $R j_*$ side.
]
<exmp:two-exact-sequences>

Suppose a perverse sheaf is known on an open union of strata $U$. Extending it to $X$ is not automatic: restriction to $U$ forgets every constituent supported on the closed boundary. The punctured-curve sequences above (@exmp:two-exact-sequences) already show that several perverse extensions can have the same restriction. The problem is to determine which boundary information is forced by the object on $U$ and which information could be added independently.

Let $i:Z into X$ be the inclusion of a closed union of strata, and let $U=X-Z$ with inclusion $j:U into X$. #ed[The dictionary of basic maps] already supplied the two extreme derived extensions, $j_!$ and $R j_*$ (@sec:six-operations-dictionary), while open--closed recollement describes their relation to the boundary (@thm:recollement). The new question is how these extensions sit relative to the perverse heart.

#ed[First, neither extreme derived extension needs to lie in the heart, even for the simplest coefficients.]

#exmp(title: "Why perverse truncation is needed")[
Let $X=CC^2$, $U=X - {0}$, and $P = shift(constSh(k)_U, 2)$. For the inclusion $j:U into X$ and the origin $i_0:{0} into X$, a punctured ball retracts onto $S^3$, hence
$ invimg(i_0, Rpush(j) P) iso shift(RGam (S^3, k), 2) $In @exmp:dualizing-node, disconnectedness of the link produced an additional low degree. Here the link is connected, but its top class in $H^3(S^3;k)$ appears after the shift in #ed[ordinary] degree $1$. #ed[Thus the stalk complex has cohomology in ordinary degrees $-2$ and $1$. The point stratum has complex dimension $0$, so the perverse support condition permits stalk cohomology there only in degrees at most $0$; the class in ordinary degree $1$ therefore places $Rpush(j) P$ outside the perverse heart. Applying $pH(0)$ removes that contribution and leaves the degree-zero extension.]
]
<exmp:direct-image-not-perverse>

From this point on, perverse truncation is the operation that returns a derived extension to the dimension-sensitive degree zero before abelian constructions are applied.

#thm(title: "One-sided perverse exactness")[
For the perverse $t$-structures on $Z$, $X$, and $U$:

+ $j^(-1)=j^!$ and $i_*$ are $t$-exact;
+ $j_!$ and $i^(-1)$ carry the nonpositive half to the nonpositive half;
+ $R j_*$ and $i^!$ carry the nonnegative half to the nonnegative half.
]
<thm:perverse-exactness>

#proofsketch[
The first line follows directly from the gluing description of the perverse $t$-structure (@thm:gluing-t-structures). For $A in pDle(0) (U)$ and $B in pDge(1) (X)$,
$ Hom (lsh(j) A, B) iso Hom (A, invimg(j, B))=0, $
so orthogonality places $lsh(j) A$ in $pDle(0) (X)$. Verdier duality gives the corresponding assertion for $Rpush(j)$. The adjunctions $i^(-1) tack.l i_*$ and $i_* tack.l i^!$ give the two statements for the closed inclusion. See @BBD1982[§1.4.16].
]

The one-sided exactness statements visualised in the following table.

#table(
  columns: (1.4fr, 1.5fr, 3fr),
  inset: 6pt,
  align: left,
  [*Functor*], [*Perverse exactness*], [*Geometric role*],
  [$j^(-1)=j^!$], [$t$-exact], [Restriction back to the open part],
  [$i_*$], [$t$-exact], [Boundary data regarded as an object on $X$],
  [$lsh(j)$], [Right $t$-exact], [Adds no ordinary sections on the boundary],
  [$i^(-1)$], [Right $t$-exact], [Tests the stalk-side boundary contribution],
  [$Rpush(j)$], [Left $t$-exact], [Retains cohomology of punctured neighbourhoods],
  [$ushr(i)$], [Left $t$-exact], [Tests the supported or costalk-side contribution],
)

For $P in Perv (U)$, extension by zero satisfies $lsh(j)P in pDle(0)(X)$, while derived direct image satisfies $Rpush(j)P in pDge(0)(X)$. Either object can still have perverse cohomology away from degree $0$. Its degree-zero part gives an extension that lies in the heart.

#def(title: "The two perverse boundary extensions")[
For $P in Perv (U)$, define
$ j_!^p P:=pH(0) (lsh(j) P), quad j_*^p P:=pH(0) (Rpush(j) P). $
These are called the standard and costandard *perverse extensions*.
]
<def:extreme-extensions>

 The identity of $P$, transported through the adjunctions $j_! tack.l j^(-1) tack.l R j_*$, induces a canonical morphism
$ j_!^p P -> j_*^p P. $
The relation among the four objects is
$ lsh(j) P -> j_!^p P -> j_*^p P -> Rpush(j) P, $
where the two middle terms lie in $Perv(X)$. The left extension may contribute a boundary subobject on the supported side and the right extension may contribute a boundary quotient on the ordinary side.

The desired extension keeps only the boundary information forced by $P$ on $U$. It should introduce neither an independent subobject nor an independent quotient supported on $Z$. Its construction is therefore an image, which is why the abelian heart is needed to begin with. 


#def(title: "Intermediate extension")[
For $P in Perv (U)$, define
$ midext P := im_(Perv (X)) (j_!^p P -> j_*^p P). $
]
<def:intermediate-extension>

The operations $j_!$ and $R j_*$ already exist in the derived category, and $j_!^p$, $j_*^p$ and $midext$ become available after the perverse heart has been chosen. In particular, the definition of $midext$ uses the image of a morphism in the abelian category $Perv(X)$.

#thm(title: "Boundary characterization of the intermediate extension")[
The exact functor $i_*$ identifies $Perv (Z)$ with the full subcategory of $Perv (X)$ consisting of objects $Q$ for which $invimg(j, Q)=0$. Moreover, for $Q in Perv (X)$:

+ $Q$ has no nonzero quotient supported on $Z$ exactly when $pH(0) (invimg(i, Q))=0$;
+ $Q$ has no nonzero subobject supported on $Z$ exactly when $pH(0) (ushr(i) Q)=0$.

Consequently, $midext P$ is, up to unique isomorphism, the unique perverse sheaf $Q$ satisfying

+ $invimg(j, Q) iso P$;
+ $Q$ has no nonzero subobject supported on $Z$;
+ $Q$ has no nonzero quotient supported on $Z$.

Equivalently,
$ invimg(i, Q) in pDle(-1) (Z), quad ushr(i) Q in pDge(1) (Z). $
]
<thm:intermediate-extension-characterization>

#proof[
If $invimg(j, Q)=0$, the open--closed triangles (@thm:recollement) identify $Q$ with $push(i, invimg(i, Q))$ and with $push(i, ushr(i) Q)$. One-sided perverse exactness (@thm:perverse-exactness) then places the corresponding object on $Z$ in its perverse heart. Thus $i_*$ identifies $Perv(Z)$ with the perverse sheaves supported on $Z$.

Since $invimg(i, Q) in pDle(0) (Z)$, adjunction gives, for $R in Perv (Z)$,
$ Hom (Q, push(i, R)) iso Hom (pH(0) (invimg(i, Q)), R). $
A nonzero quotient of $Q$ supported on $Z$ therefore exists when $pH(0) (invimg(i, Q))$ is nonzero. Verdier duality gives the corresponding statement for subobjects and $pH(0) (ushr(i) Q)$.

The perverse direct-image extension $j_*^p P$ has no nonzero subobject supported on $Z$, and the perverse extension by zero $j_!^p P$ has no nonzero quotient supported there. Their image inherits both properties. Conversely, an extension $Q$ with neither kind of boundary constituent receives a morphism from $j_!^p P$ and maps to $j_*^p P$. The cokernel of the first map and the kernel of the second are supported on $Z$, so both vanish. Hence $Q$ is the image of the canonical morphism. The final degree conditions restate the two vanishings in the perverse $t$-structure.
]
In short, the functor $i^(-1)$ detects boundary information that remains ordinarily visible and can produce a quotient. The exceptional inverse image $i^!$ detects contributions supported on the boundary and can produce a subobject. Intermediate extension excludes both independent boundary contributions - and Verdier duality exchanges the two conditions.

#prop(title: "Formal properties of intermediate extension")[
The functor $midext: Perv (U) -> Perv (X)$ is fully faithful and commutes with Verdier duality:
$ VDX(X) (midext P) iso midext (VDX(U) P). $
]
<prop:midext-properties>

#proof[
A morphism between two intermediate extensions that vanishes on $U$ has image supported on $Z$. That image is simultaneously a quotient of the source and a subobject of the target, so the boundary characterization of intermediate extension (@thm:intermediate-extension-characterization) forces it to vanish. This proves faithfulness.

For fullness, let $f:P->Q$ be a morphism in $Perv(U)$, and write $alpha_P:j_!^p P->j_*^p P$ and $alpha_Q:j_!^p Q->j_*^p Q$ for the canonical maps. Functoriality gives the commutative square
#square(
  $j_!^p P$, $j_*^p P$,
  $j_!^p Q$, $j_*^p Q$,
  f: $alpha_P$,
  g: $j_!^p f$,
  h: $j_*^p f$,
  k: $alpha_Q$,
)
and therefore a morphism between the two images. This proves fullness. Verdier duality exchanges $j_!^p$ with $j_*^p$, so it preserves the image of the canonical morphism.
]

The punctured-curve model shows what boundary information survives this image construction.

#ed[On a curve the intermediate extension can moreover be reached by an ordinary truncation of $Rpush(j)$, as the calculation below shows. That formula is a special feature of the one-dimensional dictionary (@prop:curve-dictionary), where only ordinary degrees $-1$ and $0$ occur; in general $midext$ is defined only as the image in the perverse heart.]

#exmp(title: "Intermediate extension on a punctured curve")[
Retain the notation of @exmp:two-exact-sequences. Since $P_!$ and $P_*$ are already perverse,
$ j_!^p P iso P_! quad j_*^p P iso P_* $
The ordinary degree-$0$ cohomology of $P_*$ is supported at the origin and has stalk $V_T$. The boundary characterization of @thm:intermediate-extension-characterization therefore gives
$ midext (P) iso tle(-1) (P_*) $
The truncation removes the degree-$0$ boundary quotient and retains the invariant term:
$ invimg(i,midext (P)) iso shift(V^T,1) $

For the dual local system,
$ ker (T^vee - id_(V^vee)) iso (coker (T - id_V))^vee iso V_T^vee $
Compatibility with Verdier duality from @prop:midext-properties then gives
$ ushr(i) (midext (P)) iso shift(V_T,-1) $
Thus the same map $T-id_V$ controls both boundary readings: its kernel occurs in stalk degree $-1$, while its cokernel occurs in costalk degree $1$.
]
<exmp:curve-intermediate-extension>

The same formula gives three boundary tests - 

#table(
  columns: (1.5fr, 1fr, 1fr, 3fr),
  inset: 6pt,
  align: left,
  [*Monodromy*], [$V^T$], [$V_T$], [*Boundary behaviour of $midext shift(cL_T,1)$*],
  [$T=id_V$], [$V$], [$V$], [The local system extends across the puncture],
  [$T-id_V$ invertible], [$0$], [$0$], [No point stalk or costalk contribution remains],
  [$T=mat(1,1;0,1)$], [$k$], [$k$], [One invariant and one coinvariant class survive],
)

== Intersection complexes and cohomology <sec:intersection-complexes>

The intermediate extension now gives a canonical coefficient object on a singular space. Let $X$ be pure of complex dimension $n$, and let $j:X_"reg" into X$ be its smooth locus. On $X_"reg"$, a local system $cL$ has the natural perverse normalization $shift(cL,n)$. The question is how to extend this generic top-dimensional data across the singular locus without introducing additional subobjects or quotients supported only there.

The boundary characterization of $midext$ gives such an extension. Thus we define the intersection complex by extending $shift(cL,n)$ from the smooth locus using $midext$. Since, as we saw, intermediate extension also commutes with Verdier duality, this construction preserves the duality enjoyed by the normalized local system on the smooth part. 


However, let $X = PP^1 union.sq_p PP^1 $, be two projective lines meeting at one point. Topologically, $X$ is a wedge of two $2$-spheres, so

$ bb(H)^0(X,k) iso k, quad bb(H)^1(X,k)=0, quad bb(H)^2(X,k) iso k^2 $
Thus ordinary cohomology does not have matching dimensions in degrees $0$ and $2$. Hence, we need a different coefficient object.

#def(title: "Intersection complex")[
Let $S$ be a stratum of complex dimension $d$, let $j:S into overline(S)$ be its inclusion, and let $a_S:overline(S) into X$ be the closed embedding. For a finite-rank local system $cL$ on $S$, define
$ ICs(overline(S), cL):= push(a_S, midext (shift(cL, d))). $
]
<def:intersection-complex>

A complex space is *pure $n$-dimensional* when all of its irreducible components have dimension $n$. If $X$ is irreducible and pure $n$-dimensional, with smooth locus $j:X_"reg" into X$, we write
$ IC_X (cL) := midext (shift(cL, n)), quad IC_X := IC_X (constSh(k)_(X_"reg")). $
For a reducible pure-dimensional space, $IC_X$ is the direct sum of the corresponding intersection complexes of its irreducible components.

#exmp(
  title: "The elliptic curve: dualizing and perverse shifts",
  label: <exmp:elliptic-curve-two-shifts>,
)[
Return to the elliptic curve $E=CC \/ Lambda$ from the opening of the chapter. Since $E$ is smooth of complex dimension $1$, its regular locus is all of $E$, and the definition gives
$IC_E iso shift(constSh(k)_E,1). $
#ed[Verdier duality gives]
$VDX(E) (constSh(k)_E) iso shift(constSh(k)_E,2), $
and therefore
$VDX(E) (IC_E) iso IC_E. $
The shift by $2$ comes from the real dimension of the dualizing complex. The shift by $1$ is the complex-dimensional normalization that places the constant local system in the perverse heart.
]

#ed[Let $X$ be a reduced pure complex curve, let $nu:tilde(X) -> X$ be its normalization, and let $j:X_"reg" into X$ be the smooth-locus inclusion. Put
$P := Rpush(nu) shift(constSh(k)_(tilde(X)),1). $
The normalization is finite, so $nu_*$ is exact and $Rpush(nu) = nu_*$. Let $x in X$ and write $r_x := op("card") (nu^(-1) (x))$ for the number of local branches at $x$. For a sufficiently small neighbourhood $B$ of $x$, the inverse image $nu^(-1) (B)$ is a disjoint union of $r_x$ discs. The stalk of $P$ is therefore the direct sum of their constant branch values. Its costalk is computed by the corresponding disjoint union of local pairs $(D,D - {0})$; each pair contributes $k$ in real degree $2$, which appears in ordinary degree $+1$ after the shift by $[1]$. Hence
$ invimg(i_x,P) iso shift(k^(r_x),1), quad ushr(i_x) P iso shift(k^(r_x),-1). $
The restriction to the smooth locus and these pointwise stalk and costalk bounds show that $P$ is perverse. Both displayed complexes have vanishing ordinary cohomology in degree $0$, so the boundary characterization of intermediate extension (@thm:intermediate-extension-characterization) shows that $P$ has no nonzero subobject or quotient supported at a singular point. Since $nu$ is an isomorphism over $X_"reg"$, it follows that
$ IC_X iso Rpush(nu) shift(constSh(k)_(tilde(X)),1). $
This is the one-dimensional normalization formula used in the curve examples below; see @HTT2008[§8.2.2].]

#def(title: "Intersection cohomology")[
For a pure $n$-dimensional space, define
$ I bb(H)^m (X, cL):= bb(H)^(m - n) (X, IC_X (cL)). $
For the constant local system, write $I bb(H)^m (X)$.
]
<def:intersection-cohomology>

The shift $shift(cL,n)$ is the perverse normalization determined by the support and costalk conditions (@def:perverse-conditions). Hypercohomology of the normalized object is shifted by $n$ relative to the usual topological indexing, and the term $m-n$ restores degrees $0$ through $2n$ on a compact $n$-dimensional space.

#prop(title: "Duality of intersection complexes")[
For the fibrewise dual local system $cL^vee$,
$ VDX(X) ICs(overline(S), cL) iso ICs(overline(S), cL^vee). $
In particular, the intersection complex with constant coefficients is Verdier self-dual.
]
<prop:ic-duality>

#proof[
On the smooth stratum, complex orientation gives
$ VDX(S) shift(cL, d) iso shift(cL^vee, d). $
Compatibility of intermediate extension with Verdier duality (@prop:midext-properties) carries this isomorphism across the boundary. Proper pushforward along the closed embedding $a_S$ then gives the displayed formula.
]

Global Verdier duality turns the self-duality of the intersection complex into a pairing between complementary intersection-cohomology degrees.

#thm(title: "Poincaré duality for intersection cohomology")[
Let $X$ be compact, irreducible, and pure of complex dimension $n$. Then
$ I bb(H)^m (X, cL) iso (I bb(H)^(2 n - m) (X, cL^vee))^vee. $
For constant coefficients the same conclusion holds componentwise on a reducible pure-dimensional space.
]
<thm:ic-poincare-duality>

#proof[
Apply global Verdier duality (@prop:global-verdier-duality) to $IC_X(cL)$. Compactness identifies ordinary and compactly supported global sections. Duality of intersection complexes (@prop:ic-duality) identifies the Verdier dual with $IC_X(cL^vee)$. Taking cohomology and translating by the indexing in the definition of intersection cohomology (@def:intersection-cohomology) gives the displayed degrees.
]

For the reducible curve above, the coefficient change can be seen through normalization.

#exmp(title: "Two projective lines meeting at a point")[
For $X = PP^1 union.sq_p PP^1$, the germ at $p$ is the two-branch singularity of @exmp:dualizing-node. The intersection cohomology treats it globally as follows. Let
$nu :PP^1 union.sq PP^1 -> X$ be the normalization map. The constant sheaf on $X$ has one value at $p$, so sections on the two branches must agree there. The normalization has two preimages of $p$, and the intersection complex keeps the corresponding branch data separate - 
$ IC_X iso Rpush(nu) shift(constSh(k)_(PP^1 union.sq PP^1), 1). $
And therefore
$ I bb(H)^0 (X) iso k^2, quad I bb(H)^1 (X)=0, quad I bb(H)^2 (X) iso k^2. $

The space $X$ is connected, so ordinary degree-zero cohomology is $bb(H)^0(X,k) iso k$. The group $I bb(H)^0(X) iso k^2$ retains the two top-dimensional branches supplied by the intersection complex. In particular, $I bb(H)^0$ should not be read as the number of connected components of the underlying topological space.
]
<exmp:two-lines-repaired>

#table(
  columns: (1.8fr, 1fr, 1fr, 1fr),
  inset: 6pt,
  align: center,
  [], [$m=0$], [$m=1$], [$m=2$],
  [$bb(H)^m(X,k)$], [$k$], [$0$], [$k^2$],
  [$I bb(H)^m(X)$], [$k^2$], [$0$], [$k^2$],
)

The reducible node above compared ordinary and intersection cohomology globally. The irreducible nodal curve below has the same two-branch local germ as @exmp:dualizing-node, there the germ will exhibit an intersection-complex factor and a point-supported factor inside one object of the perverse heart.

== Simple perverse sheaves <sec:simple-perverse>

The intersection complex gives a canonical perverse object from an irreducible local system on one stratum. To use these objects as building blocks, we need to know which perverse sheaves are simple and whether arbitrary perverse sheaves can be assembled from finitely many such pieces.

#def(title: "Simple objects and irreducible local systems")[
A nonzero object $P$ of an abelian category is *simple* if its only subobjects are $0$ and $P$. A finite-rank local system is *irreducible* if it has no nonzero proper sub-local system.
]
<def:simple-object>

Irreducibility controls subobjects on the stratum itself. The boundary characterization of intermediate extension (@thm:intermediate-extension-characterization) prevents new subobjects or quotients from appearing only on the complement. Together these two facts identify the simple objects of the perverse heart.

#thm(title: "Simple objects and finite composition")[
Every object $P in Perv (X)$ admits a finite filtration
$ 0=P_0 subset P_1 subset dots subset P_r=P $
whose successive quotients are simple. The simple objects are exactly
$ ICs(overline(S), cL), $
where $S$ is a stratum and $cL$ is an irreducible finite-rank local system on $S$.
]
<thm:simple-perverse>

#proofsketch[
We first prove the part that displays the mechanism. If $P in Perv (U)$ is simple, any nonzero subobject of $midext P$ restricts either to $0$ or to all of $P$. In the first case it is supported on the boundary and vanishes by the boundary characterization of intermediate extension (@thm:intermediate-extension-characterization). In the second case the quotient is supported on the boundary and vanishes for the same reason. Hence intermediate extension preserves simplicity. In particular, $ICs(overline(S),cL)$ is simple whenever $cL$ is irreducible.

Let $P$ be simple and choose a stratum $S$ that is open in $supp P$. Its restriction has the form $shift(cM,dim S)$ for a finite-rank local system $cM$. A proper nonzero sub-local system of $cM$ would produce, by adjunction and image in the perverse heart, a proper nonzero subobject of $P$; thus $cM$ is irreducible. The canonical maps from the two perverse boundary extensions to and from $P$ then force $P$ to be their image, hence
$ P iso ICs(overline(S),cM). $
For finite length, one inducts on the number of strata, taking a finite composition series on an open stratum and applying the induction hypothesis to the closed complement. The detailed induction is given in @BBD1982[Thm. 4.3.1] and @Dimca2004[Thm. 5.2.12].
]

A finite composition series separates two kinds of information. Its factors specify which irreducible local systems occur on which supports, and the successive extension classes in the chosen filtration record how those factors are assembled. The filtration need not split, so the composition factors alone do not determine the perverse sheaf. 

#exmp(title: "A perverse sheaf with two composition factors")[
Let $X$ be an irreducible curve with one ordinary node $p$. Let $nu:tilde(X) -> X$ be the normalization, which replaces $p$ by two points, and let $i:{p} into X$ be the singular-point inclusion. Away from $p$, the object $shift(constSh(k)_X,1)$ restricts to the perverse-normalized constant local system on a smooth curve. It remains to test the point stratum.

Choose a sufficiently small neighbourhood $B$ of the node and put $B^times=B-{p}$. The neighbourhood $B$ is contractible, while $B^times$ has two connected components, each homotopy equivalent to $S^1$. Hence
$ H^0 (B;k)=k, quad H^0 (B^times;k)=k^2, quad H^1 (B^times;k)=k^2, $
and the map $H^0 (B;k)->H^0 (B^times;k)$ is the diagonal inclusion. The long exact sequence of the pair $(B,B^times)$ gives
$ H^1 (B,B^times;k) iso k, quad H^2 (B,B^times;k) iso k^2, $
with no relative cohomology in lower degrees. Thus
$ invimg(i,shift(constSh(k)_X,1)) iso shift(k,1), $
while the costalk, represented by the shifted local pair, has cohomology
$ H^0 (ushr(i) shift(constSh(k)_X,1)) iso k, quad H^1 (ushr(i) shift(constSh(k)_X,1)) iso k^2, $
and vanishes in negative degrees. These are the pointwise perverse bounds (@rmrk:pointwise-perverse-bounds), so $shift(constSh(k)_X,1)$ is perverse.

The normalization has two local values over the node, so there is an exact sequence of ordinary sheaves
$ 0 -> constSh(k)_X -> push(nu,constSh(k)_(tilde(X))) -> push(i,k) -> 0 $
where the first map is diagonal at the node and the quotient measures the difference between the two branch values. After shifting by $1$ this becomes a distinguished triangle
$ shift(constSh(k)_X,1) -> Rpush(nu) shift(constSh(k)_(tilde(X)),1) -> shift(push(i,k),1) $
The middle term is the intersection complex,
$ IC_X iso Rpush(nu) shift(constSh(k)_(tilde(X)),1) $
and $push(i,k)$ is perverse in degree $0$. Taking perverse cohomology gives the short exact sequence
$ 0 -> push(i,k) -> shift(constSh(k)_X,1) -> IC_X -> 0 $

The normalization calculation is therefore read differently in the two hearts:

#table(
  columns: (1.4fr, 4.6fr),
  inset: 6pt,
  align: left,
  [*Heart*], [*Short exact sequence*],
  [Ordinary sheaves], [$0 -> constSh(k)_X -> push(nu,constSh(k)_(tilde(X))) -> push(i,k) -> 0$],
  [Perverse sheaves], [$0 -> push(i,k) -> shift(constSh(k)_X,1) -> IC_X -> 0$],
)

The second row is not obtained by simply shifting the first row as a short exact sequence. One shifts the associated distinguished triangle and then takes cohomology in the perverse heart. The derived object has not changed; the change of heart changes which triangles become short exact sequences and therefore which subobjects and quotients are visible.

The two simple composition factors are therefore the point-supported skyscraper and the intersection complex. The example separates the two issues controlled by the theory: the perverse bounds decide which degrees are allowed, while the abelian heart keeps track of subobjects and extensions among objects satisfying those bounds.
]
<exmp:nodal-curve>

== Toward Riemann--Hilbert <sec:perverse-summary>
The perverse $t$-structure places a local system on a smooth $d$-dimensional stratum in degree zero after the shift $[d]$. Recollement glues these shifted local systems across strata, while intermediate extension removes subobjects and quotients supported only on the boundary. The simple objects of $Perv(X)$ are therefore the intersection complexes $ICs(overline(S),cL)$ attached to irreducible local systems, and arbitrary perverse sheaves are assembled from them by extensions.

Riemann--Hilbert supplies the differential counterparts of these data. Regular connections produce the local systems on smooth strata, Kashiwara's equivalence treats objects supported on closed strata, and the compatibility of the solution functor with the six operations and Verdier duality carries the gluing and extension data between the two categories.
