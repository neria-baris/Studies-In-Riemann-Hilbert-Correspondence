#import "../template/template.typ": *
#import "../template/macros.typ": *

// Shared local corrections and chapter notation (see Thesis.typ).
#let cohsh(n, K) = $cal(H)^(#n) (#K)$
#let vee = $or$
#let gray8(x) = text(8pt, fill: luma(110))[#x]

= Sheaf Cohomology and Constructible Complexes <chap:sheaf-cohomology>

== Motivation

The preceding chapter described a single sheaf and the information it carries on open sets, near points, and across a stratification. The language of complexes developed in @chap:homological-algebra allows us to attach several stages of data to a single topological space and to each of its open subsets, with the differentials describing the relations among these stages. As we shall see, however, the global-section functors are not exact. Moreover, information affected by the removal of a point need not disappear, but may instead occur in higher degrees; in other words, the ordinary costalk functor is not exact either. The tools of @chap:derived-categories allow us to replace these operations with their derived versions and retain the cohomology they produce.

In the preceding chapter, we saw that, for the map from $X$ to a point, direct image gives global sections, while direct image with a support condition gives compactly supported sections. For the inclusion of a point into $X$, the two corresponding inverse-image operations give the stalk and the costalk. We also discussed tensor product and Hom. Therefore we continue studying these operations, now from the perspective of exactness and derived functors.

== Complexes of sheaves <sec:complexes-of-sheaves>


@chap:homological-algebra defined cochain complexes and their morphisms in an arbitrary abelian category. Since $op("Sh") (X;R)$ is abelian, no new algebraic definition is required here. 

A *cohomological complex of sheaves* is a complex in $op("Sh") (X;R)$, written
$ dots.c -> K^(n - 1) arrow.r.long^(d^(n - 1)) K^n arrow.r.long^(d^n) K^(n + 1) -> dots.c $

The $n$-th *cohomology sheaf* of $K$ is
$ cohsh(n,K) := ker(d^n) \/ op("im")(d^(n - 1)) $
where the kernel and image are taken in $op("Sh") (X;R)$, i.e - after sheafification.

#exmp(title: "Support created by a two-term complex")[
On $CC$, put two copies of the holomorphic structure sheaf in degrees $0$ and $1$:
$K_z=[cO_CC arrow.r.long^z cO_CC].
$
Multiplication by $z$ is injective. Away from the origin it is invertible, while at the origin
$stalk(cO_CC,0)\/z stalk(cO_CC,0) iso CC.
$
Therefore
$
cohsh(0,K_z)=0,
quad
cohsh(1,K_z) iso push(i_0,CC).
$
The cohomology is supported where multiplication by $z$ fails to be invertible.
]
<exmp:support-from-z-complex>

Taking stalks term by term gives a complex $K_x^bullet$ of $R$-modules. Exactness of the stalk functor gives the basic comparison between the sheaf complex and these ordinary complexes.

#prop(title: "Cohomology sheaves are computed on stalks")[
For every complex $K$ and every $x in X$,
$ cohsh(n,K)_x iso H^n (K_x^bullet). $
Consequently, a morphism $K -> L$ is a quasi-isomorphism if and only if $K_x^bullet -> L_x^bullet$ is a quasi-isomorphism for every $x in X$.
]
<prop:cohomology-sheaves-stalkwise>

#proof[
Exactness of the stalk functor identifies the stalks of kernels, images, and quotients with the corresponding kernels, images, and quotients of stalks. Hence $cohsh(n,K)_x iso H^n (K_x^bullet)$. A morphism of sheaves is an isomorphism exactly when it is an isomorphism on every stalk, so the same identity gives the stalkwise criterion for quasi-isomorphisms.
]

We write
$ Db (X;R) := Db (op("Sh") (X;R)) $
for the bounded derived category of sheaves. The notation $Dp (X;R)$ will be used when bounded-below complexes are required. Exact functors on sheaves, such as $f^(-1)$, act term by term and preserve quasi-isomorphisms; left- or right-exact functors require the derived constructions of the preceding chapters.

The symbol $cohsh(q,K)$ therefore denotes a sheaf on $X$. The next section applies derived global sections and produces cohomology modules instead.

== Sheaf cohomology

For a sheaf $cF$, the module of global sections is
$globalSect(X,cF) = cF (X). $
If $X$ is locally compact and Hausdorff, the compactly supported global sections form the submodule
$Gamma_c (X,cF) subset.eq globalSect(X,cF). $
The distinction is already visible on the real line. For the constant sheaf,
$ globalSect(RR,constSh(k)) iso k, quad Gamma_c (RR,constSh(k)) = 0. $
A global locally constant section is determined by one scalar. A nonzero such section has support all of $RR$, so none is compactly supported. For a skyscraper $i_(0,*) M$, every global section is supported at one point and therefore
$ globalSect(RR,i_(0,*) M) iso Gamma_c (RR,i_(0,*) M) iso M. $

The next issue is exactness. Return to the exponential sequence of @exmp:exponential-sheaf-epimorphism. The map of sheaves is locally surjective because a circle-valued function has a continuous argument locally. On global sections, the identity map of $S^1$ has no continuous lift to $RR$. Thus global sections do not preserve an epimorphism of sheaves. 
// #text(fill: red)[אמנם? הרי זה לא תלוי, אולי זה יקל על הבהירות דווקא?]

#def(title: "Sheaf cohomology")[
For a sheaf $cF$ regarded as a complex concentrated in degree $0$, define
$ H^n (X,cF) := R^n globalSect(X,cF), quad H_c^n (X,cF) := R^n Gamma_c (X,cF). $
Equivalently,
$ H^n (X,cF) = H^n (RGam (X,cF)), quad H_c^n (X,cF) = H^n (RGamc (X,cF)). $
]
<def:sheaf-cohomology>

In degree $0$ these groups recover the ordinary section functors:
$ H^0 (X,cF) = globalSect(X,cF), quad H_c^0 (X,cF) = Gamma_c (X,cF). $
The higher groups record the failure of exactness.


#exmp(title: "The helix as a cohomology class")[
Return to the sheaf of lifts from the helix. The corresponding short exact sequence of sheaves of abelian groups has the form
$ 0 -> constSh(ZZ) -> C_R^0 -> C_(S^1)^0 -> 0, $
where the middle map sends a real-valued function to its value modulo $ZZ$, viewed as an $S^1$-valued function. Locally every circle-valued function admits a lift, so the final map is an epimorphism of sheaves. Applying global sections produces part of the long exact sequence
$ globalSect(S^1,C_R^0) -> globalSect(S^1,C_(S^1)^0) arrow.r.long^delta H^1 (S^1,constSh(ZZ)). $
The identity map of $S^1$ has no global lift to $RR$, exactly as in the helix calculation. Exactness therefore gives
$delta (id_(S^1)) != 0$. 
This is the obstruction to a global lift. Differences between local lifts define an integer-valued cocycle whose value around the circle is $1$, matching the geometric change of level in the helix.
]
<exmp:exponential-cohomology-obstruction>

A complex of sheaves can carry several cohomology sheaves, so we also need to apply derived sections directly to a complex.

#def(title: "Hypercohomology")[
For $K in Dp(X;R)$, define
$ bb(H)^n (X,K) := H^n (RGam (X,K)), quad bb(H)_c^n (X,K) := H^n (RGamc (X,K)). $
These are the *hypercohomology modules* of $K$.
]
<def:hypercohomology>
$Dp $

The notation separates the cohomology sheaves of $K$ from the cohomology obtained after taking sections. To compute the latter, choose an injective replacement $K -> I_K^bullet$. Then

#figure(
  diagram(
    spacing: 0.75cm,

    node((0, 0), $K^(q - 1)$),
    node((2, 0), $K^q$),
    node((4, 0), $K^(q + 1)$),

    node((0, 1.35), $I_K^(q - 1)$),
    node((2, 1.35), $I_K^q$),
    node((4, 1.35), $I_K^(q + 1)$),

    node((0, 2.7), $globalSect(X,I_K^(q - 1))$),
    node((2, 2.7), $globalSect(X,I_K^q)$),
    node((4, 2.7), $globalSect(X,I_K^(q + 1))$),

    edge((0, 0), (2, 0), "->"),
    edge((2, 0), (4, 0), "->"),

    edge((0, 1.35), (2, 1.35), "->"),
    edge((2, 1.35), (4, 1.35), "->"),

    edge((0, 2.7), (2, 2.7), "->"),
    edge((2, 2.7), (4, 2.7), "->"),

    edge((0, 0), (0, 1.35), "-->", label: $iota^(q-1)$),
    edge((2, 0), (2, 1.35), "-->", label: $iota^q$),
    edge((4, 0), (4, 1.35), "-->", label: $iota^(q+1)$),

    edge((0, 1.35), (0, 2.7), "-->"),
    edge((2, 1.35), (2, 2.7), "-->", label: $globalSect(X,-)$),
    edge((4, 1.35), (4, 2.7), "-->"),
  )
)

Thus
$ RGam (X,K) iso globalSect(X,I_K^bullet), quad bb(H)^n (X,K) = H^n (globalSect(X,I_K^bullet)). $
The derived object $RGam (X,K)$ contains the full complex of global sections. Passing to $bb(H)^n (X,K)$ selects its $n$-th cohomological degree, as the derived functors of @chap:derived-categories are obtained from a derived object by taking cohomology.

#figure(
  diagram(
    spacing: 0.95cm,
    node((0, 0), $K$),
    node((2.0, 0), $I_K^bullet$),
    node((4.3, -0.8), $globalSect(X,I_K^bullet)$),
    node((6.7, -0.8), $bb(H)^n (X,K)$),
    node((4.3, 0.8), $Gamma_c (X,I_K^bullet)$),
    node((6.7, 0.8), $bb(H)_c^n (X,K)$),
    edge((0, 0), (2.0, 0), "-->"),
    edge((2.0, 0), (4.3, -0.8), "=>", label: $globalSect(X,-)$),
    edge((4.3, -0.8), (6.7, -0.8), "=>", label: $H^n$),
    edge((2.0, 0), (4.3, 0.8), "=>", label: $Gamma_c (X,-)$),
    edge((4.3, 0.8), (6.7, 0.8), "=>", label: $H^n$),
  )
)

The definitions above use injective replacements. For a sheaf represented by a finite cellular diagram, derived sections can instead be computed by a finite cochain complex. This gives explicit calculations of both ordinary and compactly supported cohomology.

== Cellular calculations <sec:cellular-calculations>

The interval diagram of @exmp:cellular-three-stratum-line records the local values and the maps between them. To obtain a global complex, we combine those maps with the incidence signs of the cell structure. Choose orientations of the cells. For cells $sigma <= tau$ with $dim tau=dim sigma+1$, let $[sigma:tau]$ denote the coefficient of $sigma$ in the cellular boundary of $tau$. 

#thm(title: "Cellular computation of sheaf cohomology", label: <thm:cellular-sheaf-cohomology>)[
Let $cF_"cell"$ be a cellular sheaf on a finite regular cell complex $X$, and let $cF_"top"$ be its realization under @thm:cellular-realization. After choosing orientations of the cells, set
$ C^p (X;cF_"cell"):=plus.big_(dim sigma=p)cF_"cell" (sigma) $
with differential
$ d^p|_(cF_"cell" (sigma)):=sum_(tau supset sigma,dim tau=p+1)[sigma:tau]rho_(sigma,tau) $
Then $d^(p+1) compose d^p=0$ and
$ C^bullet (X;cF_"cell") iso RGam (abs(X),cF_"top") $
in the derived category of $k$-vector spaces.
]

We use the cellular comparison theorem from @Curry2018[Defs. 4.14--4.16 and §§5--6]; see also Shepard, Ch. 5, especially §5.2.

#exmp(title: "A cellular interval")[
Decompose $[-1,1]$ into vertices $v_-,v_0,v_+$ and oriented edges $e_-,e_+$. For the constant cellular sheaf,
$ C^0 (X;k) = k^3, quad C^1 (X;k) = k^2, $
$ d (a_-,a_0,a_+) = (a_0 - a_-,a_+ - a_0). $
For constant coefficients, this is the same terminal-minus-initial differential computed in @ex:oriented-interval-cochain. The new point is that it now arises from the cellular sheaf diagram of @exmp:cellular-three-stratum-line, and @thm:cellular-sheaf-cohomology identifies the resulting finite complex with derived global sections. Combining the generization maps with these signs turns the comparison of @ex:oriented-interval-cochain into the cellular differential. Hence
$ H^0 (X;k) iso k, quad H^1 (X;k) = 0. $
The kernel consists of triples with one common value; the cokernel vanishes because every pair of edge differences can be realized.
]<exmp:cellular-interval-cohomology>
#prop(title: "Compact support and extension by zero", label: <prop:compact-support-extension-by-zero>)[
Let $j:U arrow.hook X$ be an open embedding. For $K in Db(U;R)$ there is a natural isomorphism
$ RGamc (U,K) iso RGamc (X,j_! K) $
If $X$ is compact, this becomes
$ RGamc (U,K) iso RGam (X,j_! K) $
]

#proof[
Extension by zero identifies compactly supported sections on $U$ with compactly supported sections on $X$. Since $j_!$ is exact by @prop:extension-by-zero-exact, the same identity holds after deriving. If $X$ is compact, every closed support in $X$ is compact.
]

#exmp(title: "Compact support on the real line")[
Consider the case $n = 1$ of @exmp:boundary-difference. Thus $U = (-1,1)$, $X = [-1,1]$, and $j : U arrow.hook X$. Give $X$ the regular cell structure with endpoint vertices $v_-,v_+$ and open edge $e = U$. For $cF := constSh(k)_U$, extension by zero has cellular values $(j_! cF) (v_-) = 0$, $(j_! cF) (v_+) = 0$, and $(j_! cF) (e) = k$. Hence its cellular cochain complex is $C^bullet (X;j_! cF) = [0 arrow.r.long k]$, with the terms in degrees $0$ and $1$.

By @thm:cellular-sheaf-cohomology, $H^0 (X,j_! cF) = 0$ and $H^1 (X,j_! cF) iso k$. By @prop:compact-support-extension-by-zero,
$ RGamc (U,cF) iso RGam (X,j_! cF) iso shift(k,-1) $ Identifying $U$ with $RR$, we obtain $H_c^0 (RR;k) = 0$ and $H_c^1 (RR;k) iso k$.

The same cellular calculation applies to the open ball $B^n$. Choose a finite regular cellulation of its boundary and adjoin the open $n$-cell $B^n$. The extension $j_! constSh(k)_(B^n)$ has value $0$ on every boundary cell and value $k$ on the open $n$-cell. The chosen boundary cellulation therefore contributes only zero terms, and

$ C^q (overline(B^n);j_! constSh(k)_(B^n)) = cases(k quad q = n, 0 quad q != n) $

Consequently, $RGamc (B^n,constSh(k)_(B^n)) iso shift(k,-n)$, and hence

$ H_c^q (B^n;k) iso cases(k quad q = n, 0 quad q != n) $

By contrast, $RGam (B^n,constSh(k)_(B^n)) iso k$, independently of $n$. Ordinary cohomology sees that every ball is contractible; compactly supported cohomology records its dimension in the degree of the surviving class.

For $0 < r < R$, extension by zero along $B_r^n arrow.hook B_R^n$ induces

$ RGamc (B_r^n,constSh(k)_(B_r^n)) -> RGamc (B_R^n,constSh(k)_(B_R^n)). $

With the orientations inherited from $RR^n$, this map identifies the copies of $k$ in degree $n$. See @Curry2018[Def. 4.14 and §§5--6].
]
<exmp:real-line-compact-cohomology>

#exmp(title: "Monodromy as a cellular differential")[
Let $cL_T$ be the local system of @exmp:linear-local-system-circle, with fibre $V$ and monodromy
$T in op("Aut")_k(V) $. Use the regular two-vertex subdivision of @ex:circle-subdivision. There all four generization maps were identities; here three remain identities and the fourth, across the cut where the circuit closes, is $T$. Hence the cellular differential is
$ D_T:V plus.o V -> V plus.o V ,quad D_T (a,b)=(b-a,T a-b) $

Set
$(u,v)=(a,b-a)$.
Then
$D_T(u,v)=(v,(T-id_V)u-v)$.
The target coordinate change
$(x,y) |-> (x+y,x)$
turns this into
$((T-id_V)u,v)$.
Thus the cellular complex is the direct sum of a contractible identity complex and
$[V arrow.r.long^(T-id_V) V]$.
Since the subdivision is regular, @thm:cellular-sheaf-cohomology gives
$
RGam(S^1,cL_T)
iso
[V arrow.r.long^(T-id_V) V].
$
Consequently,
$
H^0(S^1,cL_T)=ker(T-id_V),
quad
H^1(S^1,cL_T)=coker(T-id_V).
$
]
<exmp:cellular-link-monodromy>

#exmp(title: "Circle and torus in the derived category")[
The ordinary cellular cochain complexes of the circle and the torus were computed in @ex:cellular-circle-torus. We now reinterpret those calculations as models for derived global sections.
Taking $T=id_k$ in @exmp:cellular-link-monodromy gives
$RGam(S^1,constSh(k))
iso
[k arrow.r.long^0 k]$,
recovering the circle complex of @ex:cellular-circle-torus.

For the torus, the one-vertex, two-edge, one-face CW structure used in @ex:cellular-circle-torus is not regular, so it does not directly satisfy the hypotheses of @thm:cellular-sheaf-cohomology. Choose a finite regular cellulation $K$ of $T^2$. Its cellular cochain complex represents
$RGam(T^2,constSh(k))$
and has the cohomology computed in @ex:cellular-circle-torus:
$
H^0(T^2;k) iso k,
quad
H^1(T^2;k) iso k^2,
quad
H^2(T^2;k) iso k.
$

Over a field, a bounded complex is quasi-isomorphic to its cohomology with zero differential. Choose splittings
$
Z^n=B^n plus.o H^n$, $
C^n=Z^n plus.o L^n$
so that $L^n -> B^(n+1)$ is an isomorphism. These summands form contractible pairs. Hence
$
RGam(T^2,constSh(k))
iso
[k arrow.r.long^0 k^2 arrow.r.long^0 k]
$
in degrees $0,1,2$.
]
<exmp:cellular-circle-torus-derived>

The same construction applies degreewise to a bounded complex of cellular sheaves. A *bounded cellular complex* is an object $B^bullet in Cx^b (op("Cell") (X;k))$. Equivalently, it assigns a bounded complex $B_sigma^bullet$ to every cell and a cochain map $r_(sigma,tau) : B_sigma^bullet -> B_tau^bullet$ to every face relation. Shepard's derived comparison associates to it a constructible complex $op("Real")_X (B^bullet)$.

For chosen orientations, set $C^(p,q) (X;B):=bds_(dim sigma=p) B_sigma^q$. For $c=(c_sigma)_sigma$ and $dim tau=p+1$, define $(delta c)_tau:=sum_(sigma<tau,dim sigma=p) [sigma:tau] r_(sigma,tau) (c_sigma)$. Put $C^m (X;B):=bds_(p+q=m) C^(p,q) (X;B)$ and let $D:=delta+(-1)^p d_B$ on bidegree $(p,q)$.

#prop(title: "Cellular hypercohomology")[
The operator $D$ satisfies $D^2=0$, and the total complex satisfies
$ C^bullet (X;B) iso RGam (abs(X),op("Real")_X (B^bullet)) $
in the derived category of $k$-vector spaces.
]
<prop:cellular-hypercohomology>

#proof[
The incidence identity gives $delta^2=0$. The maps $r_(sigma,tau)$ are cochain maps, so $delta d_B=d_B delta$. On bidegree $(p,q)$, the mixed terms in $D^2$ have signs $(-1)^p$ and $(-1)^(p+1)$ and therefore cancel. Together with $d_B^2=0$, this proves $D^2=0$. Applying the preceding cellular comparison in every internal degree and totalising gives the stated identification. Boundedness ensures that only finite direct sums occur in each total degree.
]



== Local cohomology and derived costalks

Return to the constant sheaf on $RR$. Its ordinary costalk at $0$ is zero, because a nonzero locally constant section cannot be supported on one point. The previous calculation shows that supported information may still appear after derivation. The correct local comparison uses a neighbourhood together with the same neighbourhood after the point has been removed.

However, its higher right-derived functors do not vanish. For a neighbourhood $U$ of $x$, the derived costalk is computed locally from the restriction map
$ RGam(U,K) -> RGam(U - {x},K) $

#def(title: "Derived costalk")[
For $x in X$, let $i_x : {x} arrow.hook X$ be the inclusion. The *derived costalk* of a bounded-below complex $K$ is
$ R i_x^! K $
]
<def:derived-costalk>
This is the right-derived functor of the ordinary costalk $i_x^!$ from @def:ordinary-costalk.


#prop(title: "Local cone model for the derived costalk")[
Let $U$ be an open neighbourhood of $x$ and put $U^times := U - {x}$. Write $R Gamma_({x}) (U,K)$ for the right-derived complex of sections on $U$ supported at $x$. It fits into a distinguished triangle
$ R Gamma_({x}) (U,K) -> RGam (U,K) -> RGam (U^times,K) -> shift(R Gamma_({x}) (U,K),1). $
As $U$ shrinks to $x$, these supported complexes compute the derived costalk $R i_x^! K$. In the locally conical situations used below, a sufficiently small neighbourhood gives the stable local model, and then
$ R i_x^! K iso shift(Cone (RGam (U,K) -> RGam (U^times,K)),-1). $
]
<prop:derived-costalk-cone>

#proof[
Choose an injective resolution $K -> I^bullet$. For each degree $q$, sections supported at $x$ are the kernel of
$ Gamma (U,I^q) -> Gamma (U^times,I^q). $
Injective sheaves are flabby, so this restriction map is surjective; see @KashiwaraSchapira1990[Ch. II, Prop. 2.4.6(vii)]. We therefore obtain a short exact sequence of complexes
$ 0 -> Gamma_({x}) (U,I^bullet) -> Gamma (U,I^bullet) -> Gamma (U^times,I^bullet) -> 0. $
The associated distinguished triangle gives the first statement. Passing to arbitrarily small neighbourhoods is exactly the local supported-section construction underlying $R i_x^!$. When the local stratified type stabilizes on a sufficiently small neighbourhood, one such $U$ computes the resulting costalk. The underived supported-section functor is defined in @KashiwaraSchapira1990[Ch. II, Def. 2.3.8], and its derived cohomology is developed in @KashiwaraSchapira1990[Ch. II, §2.6].
]

#exmp(title: "Stalk and derived costalk on the real line")[
Let $I = (-epsilon,epsilon)$ and $I^times = I - {0}$. For the constant sheaf,
$ RGam (I,constSh(k)) iso k, quad RGam (I^times,constSh(k)) iso k plus.o k $
in degree $0$. Restriction is the diagonal map
$k -> k plus.o k, quad a |-> (a,a). $
Its kernel is zero and its cokernel is $k$. Hence the cone has one copy of $k$ in degree $0$, and shifting by $-1$ places that copy in degree $1$. Therefore
$R i_0^! constSh(k)_RR iso shift(k,-1). $
The stalk is
$(constSh(k)_RR)_0 iso k $
in degree $0$. The stalk records the local value that persists through the point, and the derived costalk records the relative contribution detected by comparing the neighbourhood with the punctured one. The ordinary costalk vanished as calculated in @exmp:ordinary-stalk-costalk, but the derived costalk does not, since comparing the interval with the punctured interval recovers the missing datum as $shift(k,-1)$.
]
<exmp:stalk-derived-costalk-line>

#exmp(title: "A skyscraper at the point")[
For $K = i_(0,*) M$, the punctured neighbourhood contains no part of the sheaf. Hence
$ R i_0^! K iso M $
in degree $0$. This is the row of @exmp:ordinary-stalk-costalk on which stalk and costalk already agreed and hence deriving makes no changes.
]

Derived sections and derived costalks take sheaf complexes to complexes of $R$-modules. Verdier duality also requires a sheaf-valued complex of local morphisms. Internal derived Hom provides that object, while derived global sections recover the ordinary derived Hom complex.

== Internal derived Hom and Ext <sec:internal-derived-hom-global-ext>
The internal sheaf Hom of @def:internal-sheaf-hom is left exact in its second
variable. Deriving that variable for complexes means combining an injective
replacement with the Hom complex of @def:hom-complex.

Let $K^bullet$ be a bounded complex, let $L in D^(+) (X;R)$, and let
$L -> I_L^bullet$ be a bounded-below injective replacement. Applying internal
Hom degreewise produces the double complex
$ C^(p,q) := sHom_X (K^p,I_L^q). $
Apply the Hom-complex construction of @def:hom-complex with internal sheaf Hom in place of ordinary Hom.

#def(title: "Internal derived Hom")[
Let $K in D^b (X;R)$ and $L in D^(+) (X;R)$. Choose a bounded representative
$K^bullet$ and a bounded-below injective replacement $L -> I_L^bullet$. The
*internal derived Hom* is the object of $D^(+) (X;R)$ represented by
$ RsHom_X (K,L) := sHom_X^bullet (K^bullet,I_L^bullet). $
]
<def:internal-derived-hom>

As in @thm:derived-hom-represents, the construction is independent of the chosen bounded representative and injective replacement. The only additional input is that $sHom_X (-,I)$ is exact for injective $I$. Indeed, for an open inclusion $j colon U arrow.hook X$, exactness of $j_!$ and the adjunction $j_! tack.l j^(-1)$ imply that $rest(I,U)$ is injective, so $sHom_X (-,I) (U)$ is exact.


Take now ordinary sheaves $cF$ and $cG$, placed in degree $0$. The double
complex has a single nonzero row, the totalization collapses to
$ A^bullet := sHom_X (cF,I_cG^bullet)$, $d_A^q (phi) = d_I^q compose phi $ For every open $U subset.eq X$, the sections of $A^bullet$ form the Hom complex (@def:hom-complex)
$ A^bullet (U) = Hom_(op("Sh")(U;R)) (rest(cF,U),rest(I_cG^bullet,U)). $
 The *local Ext sheaves* are its cohomology sheaves,
$ cal(E)"xt"_X^q (cF,cG) := cohsh(q,RsHom_X (cF,cG)) = Ker (d_A^q) \/ im (d_A^(q - 1)). $



#align(center)[
  #diagram(
    spacing: (1.0cm, 1.2cm),

    node((0, 0.5), $underbrace(cal(B)^q, = im d_A^(q-1))$),
    node((1.8, 0.5), $underbrace(cal(Z)^q, = Ker d_A^q)$),
    node((3.6, 0), $sHom_X (cF,I_cG^q)$),
    node((3.6, 1.2), $cal(E)"xt"_X^q (cF,cG)$),

    edge((0, 0.5), (1.8, 0.5), "hook->"),
    edge((1.8, 0.5), (3.6, 0), "hook->"),
    edge((1.8, 0.5), (3.6, 1.2), "->>"),
  )
]

An epimorphism of sheaves need not be surjective on sections over an open set. Thus a section of $cal(E)x t_X^q(cal(F),cal(G))$ lifts locally to a cocycle, but a global lift need not exist. The following lemmas relate internal derived Hom to the derived Hom complex of global morphisms by applying derived sections.

#lem(title: "Restriction of internal derived Hom")[
For every open $U subset.eq X$,
$ rest(RsHom_X (K,L),U) iso RsHom_U (rest(K,U),rest(L,U)). $
]<lem:internal-hom-restriction>

#proof[
Restriction preserves injectives, as noted above, so $rest(I_L^bullet,U)$ is a
bounded-below injective replacement of $rest(L,U)$, and internal Hom restricts
degreewise to the corresponding double complex on $U$. Each total degree
involves finitely many factors, $K^bullet$ being bounded, so totalization
commutes with restriction.
]

#lem(title: "Internal and external derived Hom")[
For every open $U subset.eq X$,
$ RGam (U,rest(RsHom_X (K,L),U)) iso RHom_(op("Sh") (U;R)) (rest(K,U),rest(L,U)). $
In particular,
$ RGam (X,RsHom_X (K,L)) iso RHom_(op("Sh") (X;R)) (K,L). $
]
<lem:internal-external-derived-hom>

#proof[
By @lem:internal-hom-restriction it suffices to argue on $U$. Suppose $I$ is
injective and $cF$ is a sheaf on $U$; we claim $sHom_U (cF,I)$ is flabby. Let
$j colon V arrow.hook U$ be an open inclusion. A morphism $rest(cF,V) ->
rest(I,V)$ corresponds under $j_! tack.l j^(-1)$ to a morphism $j_! rest(cF,V)
-> I$, and the canonical map $j_! rest(cF,V) -> cF$ is monic, so injectivity of
$I$ extends the latter morphism to $cF -> I$. The restriction map from $U$ to
$V$ is thus surjective.

Every total degree of $sHom_U^bullet (rest(K,U),rest(I_L,U))$ is a finite
product of flabby sheaves and so is acyclic for global sections. The complex is
bounded below, since $K^bullet$ is bounded and $I_L^bullet$ is bounded below,
which is what allows derived global sections to be computed term by term. The
identification
$ globalSect(U,sHom_U (cF,cG)) iso Hom_(op("Sh") (U;R)) (cF,cG) $
then matches the result with the external Hom complex. Compare
@KashiwaraSchapira1990[§II.2.6]. // TODO: verify the section number
]

#cor(title: "Ext as hypercohomology of internal derived Hom")[
For ordinary sheaves $cF,cG$ and every $n >= 0$,
$ bb(H)^n (X,RsHom_X (cF,cG)) iso Ext_(op("Sh") (X;R))^n (cF,cG). $
]
<cor:ext-hypercohomology>

#proof[
Apply $H^n$ to the second isomorphism of @lem:internal-external-derived-hom and
use @cor:ext-derived-morphisms.
]

#figure(
  diagram(
    spacing: 1cm,
    node((2, 0), $RsHom_X (cF,cG)$),
    node((0, 1.25), $cal(E)"xt"_X^q  (cF,cG)$),
    node((3, 1.25), $RHom_(op("Sh") (X;R)) (cF,cG)$),
    node((3, 2.5), $Ext_(op("Sh") (X;R))^n  (cF,cG) $),
    edge((2, 0), (0, 1.25), "=>", label: $cal(H)^q$),
    edge((2, 0), (3, 1.01), "=>", label: $RGam (X,-)$),
    edge((3, 1.25), (3, 2.5), "=>", label: $H^n$),
  ),
  caption: [Cohomology sheaves give local Ext on $X$; derived global sections
  give the external Hom complex, whose cohomology gives global Ext.]
)



// #figure(
//   table(
//     columns: (1.5fr, 0.65fr, 1.5fr),
//     align: center + horizon,
//     inset: 7pt,
//     table.header([*Input*], [*Operation*], [*Output*]),
//     $R cal(H)o m_X (cal(F),cal(G))$, $cal(H)^q$, $cal(E)x t_X^ (cal(F),cal(G))$,
//     $R cal(H)o m_X (cal(F),cal(G))$, $R Gamma(X,-)$, $R op("Hom")_(op("Sh")(X;R))(cal(F),cal(G))$,
//     $R op("Hom")_(op("Sh")(X;R)) (cal(F),cal(G))$, $H^n$, $op("Ext")_(op("Sh")(X;R))^n (cal(F),cal(G))$,
//   ),
//   kind: table,
//   caption: [Internal derived Hom produces local Ext sheaves by taking cohomology sheaves. Applying derived global sections first produces the external derived Hom complex, whose cohomology groups are global Ext.],
// )

// #rmrk(title: "Local-to-global Ext")[
// We use the hypercohomology spectral sequence as a black box. For ordinary sheaves $cF,cG$, it has
// $ E_2^(p,q) = H^p (X,cal(E)"xt"_X^q (cF,cG)) => Ext_(op("Sh") (X;R))^(p + q) (cF,cG). $
// Here convergence means that the abutment $Ext^(n)$ has a finite filtration whose associated graded pieces are obtained from the limiting terms $E_infinity^(p,n - p)$. The index $q$ is the internal derived-Hom degree, while $p$ is the sheaf-cohomology degree. No further spectral-sequence machinery is used below; see @weibel[Thm. 5.7.9].
// ]
// <rmrk:local-to-global-ext>

Over a point there is no restriction datum to record, $op("Sh") ({*};R)$ is the
category of $R$-modules, and the construction returns ordinary derived Hom:
$ RsHom_({*}) (V,W) iso RHom_R (V,W). $

The bifunctor $RsHom_X$ is contravariant and triangulated in its first variable, and covariant and triangulated in its second. A distinguished triangle in either variable therefore gives a distinguished triangle of internal derived Homs.

#exmp(title: "Derived morphisms between local systems on the circle")[
Let $cL_T,cL_S$ be the local systems of @exmp:linear-local-system-circle, with fibres $V,W$ and monodromies $T,S$. Their internal Hom has fibre $Hom_k(V,W)$ and monodromy
$A(phi) := S compose phi compose T^(-1) $.

Since $cL_T$ is locally free of finite rank,
$ RsHom_(S^1) (cL_T,cL_S) iso sHom_(S^1) (cL_T,cL_S) $

in degree $0$. Applying @exmp:cellular-link-monodromy gives
$ RHom_(op("Sh") (S^1;k)) (cL_T,cL_S)
iso [Hom_k(V,W) arrow.r.long^(A-id) Hom_k(V,W)] $

And hence,
$Ext^0 iso ker(A-id), quad Ext^1 iso op("coker")(A-id), $
and the higher Ext groups vanish. Degree $0$ consists of the intertwiners satisfying $S compose phi = phi compose T$.
]<exmp:derived-hom-local-systems-circle>

== Constructible complexes <sec:derived-categories-of-sheaves>

Constructibility was defined in the preceding chapter for a single sheaf. A derived object can have several cohomology sheaves, so the same finite geometric control must hold in every degree.


#def(title: "Constructible derived categories")[
Assume that $R$ is Noetherian. An object $K in Db (X;R)$ is *$cal(S)$-constructible* if every cohomology sheaf $cohsh(n,K)$ is $cal(S)$-constructible. We write
$ D_cal(S)^b (X;R) $
for the full subcategory of such objects.

The category $D_c^b (X;R)$ is the full subcategory of objects constructible with respect to some allowed finite Whitney stratification. We assume that any two allowed stratifications admit a common Whitney refinement.
]
<def:constructible-derived-category>

#prop(title: "Stability of constructible complexes")[
For fixed $cal(S)$, $D_cal(S)^b (X;R)$ is a full triangulated subcategory of $Db (X;R)$, stable under canonical truncations. Its standard heart is $op("Sh")_cal(S) (X;R)$. Under the common-refinement assumption, the same statements hold for $D_c^b (X;R)$.
]
<prop:constructible-derived-structure>

#proof[
A distinguished triangle $A -> B -> C -> A[1]$ gives, for every $n$, a short exact sequence $0 -> op("coker")(cal(H)^n(A) -> cal(H)^n(B)) -> cal(H)^n(C) -> ker(cal(H)^(n+1)(A) -> cal(H)^(n+1)(B)) -> 0$. If $A$ and $B$ are constructible, the two outer terms are constructible by the kernel and cokernel statements of @prop:open-closed-constructible, and the middle term is constructible by extension closure. Rotation handles the other choices of two constructible vertices. Thus the subcategory is closed under distinguished triangles and shifts.

For canonical truncations,
$ cohsh(m,tle(n) K) iso cases(cohsh(m,K) & m <= n, 0 & m > n) $
and analogously for $tge(n) K$. Hence both truncation functors preserve constructibility. The heart consists precisely of objects whose only nonzero cohomology sheaf is in degree $0$, and therefore identifies with $op("Sh")_cal(S) (X;R)$.

For objects constructible with respect to different allowed stratifications, pass to a common Whitney refinement and apply the same argument.
]



The notation
$ D^b (op("Sh")_cal(S) (X;R)) quad "and" quad D_cal(S)^b (X;R) $
should not be identified by definition. The first category is derived inside the abelian category of constructible sheaves; the second is the full subcategory of the ambient derived category selected by its cohomology sheaves. Their equivalence, when used, is an additional theorem.

The category $D_c^b (X;R)$ is the derived category used from this point onward. The constructions of this chapter separate sheaf-valued layers, pointwise tests, and global tests:

#figure(
  diagram(
    spacing: 1.30cm,
    node((0, 0), $K$),
    node((2.8, -1.8), $cohsh(q,K)$),
    node((2.8, -0.6), $i_x^(-1) K$),
    node((2.8, 0.6), $R i_x^! K$),
    node((2.8, 1.8), $RGam (X,K)$),
    node((5.5, 1.8), $bb(H)^n (X,K)$),
    node((2.8, 3.0), $RGamc (X,K)$),
    node((5.5, 3.0), $bb(H)_c^n (X,K)$),
    edge((0, 0), (2.8, -1.8), "=>", label: $cal(H)^q$),
    edge((0, 0), (2.8, -0.6), "=>", label: $i_x^(-1)$),
    edge((0, 0), (2.8, 0.6), "=>", label: $R i_x^!$),
    edge((0, 0), (2.8, 1.8), "=>", label: $RGam (X,-)$,label-angle: -30deg),
    edge((2.8, 1.8), (5.5, 1.8), "=>", label: $H^n$),
    edge((0, 0), (2.8, 3.0), "=>", label: $RGamc (X,-)$, label-angle: -45deg),
    edge((2.8, 3.0), (5.5, 3.0), "=>", label: $H^n$)
  )
)
<fig:derived-sheaf-tests>

Constructibility is a condition on the first branch: every $cohsh(q,K)$ must be locally constant of finite rank along the strata. Verdier duality will compare the two pointwise branches after dualization and will relate ordinary global sections to compactly supported sections of the dual complex.