#import "../template/template.typ": *
#import "../template/macros.typ": *

// Shared local corrections and chapter notation (see Thesis.typ).
#let cohsh(n, K) = $cal(H)^(#n) (#K)$
#let vee = $or$
#let gray8(x) = text(8pt, fill: luma(110))[#x]
= Sheaves (and stratification) <chap:sheaves>

== Motivation

A topological space specifies which points occur together in open neighbourhoods, and the inclusions among those neighbourhoods record how local regions fit inside larger ones. Data that live on a space can therefore carry geometric information through their behaviour on open sets, even when their values at individual points look identical.

Continuous functions are the basic example. For every open set $U subset.eq X$, let
$ C_X^0 (U) := {f : U -> RR bar.v f " is continuous"} $
A function on a larger open set determines one on every smaller open subset, and functions defined on an open cover determine one function on the union when they agree on every overlap. The point of sheaf theory is to isolate this pattern from the particular notion of function.

Passing to open sets allows us to study points from two perspectives: what happens as we shrink a neighbourhood of a point to arbitrarily small neighbourhoods, and what happens when we remove the point and compare the neighbourhood with its punctured counterpart. We can collect the information obtained by shrinking around each point and assemble these local pieces into a topological space in its own right. This geometric viewpoint gives a different meaning to information that becomes zero or disappears when the point is removed.

To complete this geometric view of information, we will examine the different ways in which information can be transported between spaces, as well as the ways in which it can be treated within a single space according to its relation to the underlying geometry. Finally, we will develop a useful tool for decomposing complicated geometric spaces into layers on which the information becomes simpler, without losing the ability to describe the original information. Throughout this chapter and the next, $R$ denotes a commutative ring with unit. When constructibility is considered over $R$, Noetherianity will be imposed explicitly. The cellular calculations later in the chapter use a field $k$.

== Basic Definitions <sec:sheaves-basic>

Begin with the weakest possible structure: for every open $U subset.eq X$, choose a set $cF (U)$. At this stage the sets attached to two nested neighbourhoods are unrelated. 

#def(title: "Section")[
Let $cF$ assign a set $cF (U)$ to every open subset $U subset.eq X$. An element $s in cF (U)$ is called a *section of $cF$ over $U$*. A section over $X$ is a *global section*.
]
<def:section>

To make these local descriptions coherent, data on a region must determine data on every smaller region. For $V subset.eq U$, we therefore require a restriction map from $cF (U)$ to $cF (V)$, and successive restrictions must agree with direct restriction.

#def(title: "Presheaf of sets")[
A *presheaf of sets* $cF$ on $X$ assigns a set $cF (U)$ to every open $U subset.eq X$ and, for every inclusion $V subset.eq U$, a restriction map
$ rho_V^U : cF (U) -> cF (V) $
such that
$ rho_U^U = id_(cF (U)), quad rho_W^V compose rho_V^U = rho_W^U $
whenever $W subset.eq V subset.eq U$.
]
<def:presheaf>

The two identities say that restriction is itself coherent. Categorically, they say that the assignment is a contravariant functor
$ cF : "Op" (X)^"op" -> "Set". $
For a section $s in cF (U)$, we write $rest(s,V)$ for its image in $cF (V)$.

Restrictions alone still allow incompatible local descriptions. Suppose that $U = union.big_i U_i$ and sections $s_i in cF (U_i)$ have been chosen. Two separate requirements are needed. First, a global section is determined by its restrictions, so two sections on $U$ that agree on every $U_i$ must be equal. Second, whenever the $s_i$ agree on every overlap $U_i inter U_j$, they should arise from one section on $U$.

#def(title: "Sheaf of sets")[
A presheaf $cF$ of sets on $X$ is a *sheaf* if every open cover $U = union.big_i U_i$ satisfies the following two conditions.

*Locality.* If $s,t in cF (U)$ and
$ rest(s,U_i) = rest(t,U_i) $
for every $i$, then $s = t$.

*Gluing.* If sections $s_i in cF (U_i)$ satisfy
$ rest(s_i,U_i inter U_j) = rest(s_j,U_i inter U_j) $
for every $i,j$, then there is a section $s in cF (U)$ with
$ rest(s,U_i) = s_i $
for every $i$.

By locality, the glued section is unique.
]
<def:sheaf>

For $C_X^0$, locality is immediate because two functions that agree on a cover agree at every point. Gluing is also immediate: compatible functions on the $U_i$ define a pointwise function on their union, and continuity can be checked locally. Thus $C_X^0$ is a sheaf of $RR$-algebras. The same argument gives the sheaf
$ C_X^infinity (U) := {f : U -> RR bar.v f " is smooth"} $
on a smooth manifold and
$ cO_X (U) := {f : U -> CC bar.v f " is holomorphic"} $
on a complex manifold.

The two parts of the sheaf axiom are logically independent. The constant-presheaf example below satisfies locality but can fail gluing. Conversely, let $X = RR$, put $cA (X) = {a,b}$, and put $cA (U) = {bullet}$ for every proper open subset $U subset.eq X$ with $U != X$, with the only possible restriction maps. Compatible local sections always have at least one global lift, but a cover of $RR$ by proper open sets cannot distinguish $a$ from $b$. Thus gluing exists while locality fails. This artificial example (as examples often are) isolates why both clauses are required.

#def(title: "Constant presheaf and constant sheaf")[
Fix an $R$-module $M$. Define the *constant presheaf* $cM_"pre"$ by
$ cM_"pre" (U) := cases(M & U != emptyset, 0 & U = emptyset) $
with identity restrictions between nonempty open sets and the unique zero map to the empty set.

The corresponding *constant sheaf* $constSh(M)$ is defined by
$ constSh(M) (U) := {f : U -> M bar.v f " is locally constant"} $
where $M$ has the discrete topology. The later sheafification construction will show that this sheaf is the canonical sheaf associated with $cM_"pre"$.
]
<def:constant-sheaf>

The difference appears as soon as an open set is disconnected. If $U = U_1 union.sq U_2$ with both pieces nonempty, then $cM_"pre" (U) = M$: one element must supply the value on both components. In the constant sheaf, the two components can carry independent values, so
$constSh(M) (U) iso M plus.o M. $
More generally, when $U$ is locally connected,
$ constSh(M) (U) iso product_(C in pi_0 (U)) M $
Thus the constant presheaf already has coherent restrictions, and it satisfies locality, but it fails the gluing requirement on a disconnected cover when different values are chosen on different components. On connected open sets the two constructions agree. Thus the term "constant sheaf" is some-what misleading, even abusive.

The elementwise definitions are the form used throughout the chapter. They also have a categorical formulation that will matter later, because our sections will usually form modules rather than bare sets.

#def(title: "Category-valued presheaves and sheaves")[
Let $cal(C)$ be a category. A *$cal(C)$-valued presheaf* on $X$ is a contravariant functor
$ cF : "Op" (X)^"op" -> cal(C) $
If $cal(C)$ has the products and equalizers required by an open cover $U = union.big_i U_i$, the presheaf is a *$cal(C)$-valued sheaf* when the canonical morphism
$ cF (U) -> product_i cF (U_i) $
identifies $cF (U)$ with the equalizer of
the two restriction morphisms
$ r_1,r_2 : product_i cF (U_i) -> product_(i,j) cF (U_i inter U_j) $
obtained from the two inclusions of each overlap into $U_i$ and $U_j$. For $cal(C) = "Set"$ or $cal(C) = R"-Mod"$, this is equivalent to the locality and gluing conditions above.
]
<def:category-valued-sheaf>

When $cal(C) = R"-Mod"$, the elements of $cF (U)$ are again called sections, and all restriction maps are $R$-linear.

Kashiwara--Schapira give the presheaf definition in @KashiwaraSchapira1990[Ch. II, Def. 2.1.1], the terminology of sections in @KashiwaraSchapira1990[Ch. II, Terminology 2.1.2], and the ordinary sheaf axiom in @KashiwaraSchapira1990[Ch. II, Def. 2.2.1].

The covering map
$ p : RR -> S^1, quad p (t) = e^(2 pi i t) $
provides the first example in which local sections exist everywhere while global compatibility fails. Over every sufficiently small open arc $U subset.eq S^1$ there is a continuous lift
$ s : U -> RR, quad p compose s = id_U $
If $s$ is one lift, then $s + n$ is another for every locally constant integer-valued function $n$ on $U$.

There is no continuous lift on the whole circle. If $s : S^1 -> RR$ were such a lift and $gamma (u) = e^(2 pi i u)$, then $a (u) := s (gamma (u))$ would satisfy $a (u) - u in ZZ$. This is a continuous integer-valued function and hence constant, so $a (1) - a (0) = 1$. Since $gamma (0) = gamma (1)$, the same function $s$ would give $a (0) = a (1)$.

Define
$ cP (U) := {s : U -> RR bar.v s " continuous with " p compose s = id_U}. $
Restriction makes $cP$ a sheaf of sets. The equality $cP (S^1) = emptyset$ is compatible with the sheaf axiom: local lifts exist, while a family of local lifts on a cover need not agree on every overlap. The sheaf condition says that a compatible family glues once compatibility has actually been achieved.

#def(title: "Morphisms of sheaves")[
Let $cF$ and $cG$ be presheaves of sets or $R$-modules. A *morphism* $phi : cF -> cG$ is a family of maps
$ phi_U : cF (U) -> cG (U) $
compatible with passage to smaller open sets. A morphism of sheaves is a morphism of their underlying presheaves. For sheaves of $R$-modules, every $phi_U$ is $R$-linear.
]
<def:sheaf-morphism>

We write
$ op("Sh") (X;R) $
for the category of sheaves of $R$-modules on $X$. From this point onward this is the default coefficient category unless a set-valued example is explicitly named.

#def(title: "Skyscraper sheaf")[
Fix $x in X$ and an $R$-module $M$. The *skyscraper sheaf* at $x$ is
$ (i_(x,*) M) (U) = cases(M & "if " x in U, 0 & "if " x in.not U) $
where $i_x : {x} -> X$ is the inclusion.
]
<def:skyscraper-sheaf>

=== Stalks, support, and costalks

So far, a sheaf has assigned information to open subsets of $X$, not directly to points. To recover what the sheaf says near a point $x$, we should forget every feature that disappears after shrinking the neighbourhood of $x$.

Consider $C_RR^0$ near $0$. Let
$ f (t) = 0, quad g (t) = cases(0 & abs(t) < 1, abs(t) - 1 & abs(t) >= 1), quad h (t) = t $
The global sections $f$ and $g$ are different, but they become identical after restriction to $(-1,1)$. The function $h$ has the same value as $f$ at the point $0$, while it disagrees with $f$ on every neighbourhood of $0$. The local object attached to $0$ should therefore identify $f$ with $g$ and distinguish $h$ from both.

#def(title: "Stalk")[
Let $cF$ be a presheaf of sets or $R$-modules, let $x in X$, and let $cal(N)_x$ denote the set of open neighbourhoods of $x$. Consider pairs $(U,s)$ with $U in cal(N)_x$ and $s in cF (U)$. Declare
$(U,s) tilde (V,t) $
if there is an open neighbourhood $W$ satisfying
$x in W subset.eq U inter V $
and
$rest(s,W) = rest(t,W). $
The *stalk* of $cF$ at $x$, written $stalk(cF,x)$, is the quotient
$ cF_x := ( union.sq.big_(U in cal(N)_x) cF (U) ) \/ tilde $
For an $R$-module-valued presheaf, addition and scalar multiplication are defined after restricting representatives to a common neighbourhood.
]
<def:stalk>

#def(title: "Germ")[
If $s in cF (U)$ and $x in U$, the equivalence class of $(U,s)$ in $cF_x$ is the *germ* of $s$ at $x$, written $s_x$.
]
<def:germ>

#prop(title: "Equality of germs")[
For $s in cF (U)$ and $t in cF (V)$ with $x in U inter V$,
$ s_x = t_x <==> rest(s,W) = rest(t,W) " for some open " W " with " x in W subset.eq U inter V $
]
<prop:germ-equality>

This gives the intended answer in the example:
$ f_0 = g_0, quad h (0) = f (0) = 0, quad h_0 != f_0. $
The first equality forgets behaviour away from $0$. The last inequality shows why the stalk is richer than evaluation at a point: it retains behaviour on arbitrarily small neighbourhoods.

The same object has a categorical description. The neighbourhoods of $x$ form a directed system under restriction.

#prop(title: "Stalk as a filtered colimit")[
There is a natural isomorphism
$ cF_x iso op("colim")_(x in U) cF (U) $
where $U$ runs through the open neighbourhoods of $x$ and the transition maps are restrictions.
]
<prop:stalk-explicit>

#proof[
Every section $s in cF (U)$ determines its germ $s_x$, and these maps are compatible with restriction. Conversely, two sections have the same image in the quotient of @def:stalk exactly when they become equal after restriction to some smaller neighbourhood. The quotient therefore satisfies the universal property of the filtered colimit.
]

Kashiwara--Schapira use the filtered-colimit description in @KashiwaraSchapira1990[Ch. II, Eq. (2.1.3)] and call the image of a section its germ immediately afterward. Goresky gives the same construction in @Goresky2026[§1.2]. The concrete quotient in @def:stalk is the elementwise realization of that colimit.

The construction is also functorial. A morphism of sheaves sends representatives to representatives and respects the equivalence relation.

#def(title: "Stalk functor")[
For a fixed point $x in X$, a morphism $phi : cF -> cG$ induces
$phi_x : cF_x -> cG_x, quad s_x |-> (phi_U (s))_x. $
The assignments
$cF |-> cF_x, quad phi |-> phi_x $
define the *stalk functor*
$ i_x^(-1) : op("Sh") (X;R) -> R"-Mod", quad i_x^(-1) cF := cF_x $
]
<def:stalk-functor>

Once the abelian structure of $op("Sh") (X;R)$ has been established below, this will imply that the stalk functor is exact.

#def(title: "Support of a section and of a sheaf")[
Let $cF$ be a sheaf of $R$-modules on $X$, let $U subset.eq X$ be open, and let $s in cF (U)$. The *support of $s$ in $U$* is
$ op("supp") (s) := {x in U : s_x != 0} $
It is closed in $U$. The section has *compact support* if $op("supp") (s)$ is compact.

The *closed support* of $cF$ is
$ op("supp") (cF) := overline({x in X : cF_x != 0})^X $
]
<def:support>

The function $h (t) = t$ has $h (0) = 0$, while $0 in op("supp") (h)$ because $h_0 != 0$. The tent function
$ b (t) = cases(1 - abs(t) & abs(t) <= 1, 0 & abs(t) > 1) $
has support $[-1,1]$ and therefore compact support. The function $e^(-t^2)$ tends rapidly to zero, yet it never vanishes, so its support is all of $RR$ and is not compact.

The constant sheaf and the skyscraper sheaf separate another local question. Both have nonzero stalk at $0$. A nonzero section of $constSh(k)_RR$ on a connected neighbourhood of $0$ remains nonzero on a smaller interval, so it cannot be supported only at $0$. A section of the skyscraper $i_(0,*) M$ is supported there by definition. The stalk sees that both sheaves have local data at the point; it does not by itself distinguish data passing through the point from data concentrated there. 

This motivates a second pointwise construction. For the next definition and the adjunction below, assume that ${x}$ is closed. This holds in the Hausdorff spaces used later and ensures that $U - {x}$ is open whenever $U$ is an open neighbourhood of $x$.

#def(title: "Ordinary costalk")[
Define
$ Gamma_({x}) (U,cF) := {s in cF (U) : op("supp") (s) subset.eq {x}} $
Using the stalk's  equivalent relation (@def:stalk) the *ordinary costalk* of $cF$ at $x$ is
$ i_x^! cF := (union.sq.big_(U in cal(N)_x) Gamma_({x}) (U,cF)) \/ tilde $
For a sheaf of $R$-modules, addition and scalar multiplication are defined after restricting representatives to a common neighbourhood.
]
<def:ordinary-costalk>

 Equivalently,
$ i_x^! cF iso op("colim")_(U in cal(N)_x) Gamma_({x}) (U,cF) $

// The assignment $[(U,s)] |-> s_x $
// defines a natural monomorphism $i_x^! cF arrow.hook cF_x$. Its image consists precisely of the germs that admit a representative supported in ${x}$.

The inclusions $Gamma_({x}) (U,cF) arrow.hook cF (U) $ are compatible with restriction as $U$ shrinks, and therefore induce a natural map $i_x^! cF -> cF_x $ This map forgets the support condition. The stalk retains every germ visible after shrinking around $x$, while the ordinary costalk retains those germs that can be represented by sections supported at $x$. After these constructions are derived, we will see that in some cases we can exchange the corresponding two local tests.

#prop(title: "Stalk, skyscraper, and costalk")[
For every $x in X$, the stalk functor and the ordinary costalk are the left and right adjoints of the skyscraper functor:
$ i_x^(-1) tack.l i_(x,*) tack.l i_x^! $
Equivalently,
$ Hom_R (cF_x,M) iso Hom_(op("Sh") (X;R)) (cF,i_(x,*) M), $
$ Hom_(op("Sh") (X;R)) (i_(x,*) M,cF) iso Hom_R (M,i_x^! cF) $

]
<prop:point-adjunctions>

The second adjunction requires ${x}$ to be closed.
#proof[
A morphism $cF -> i_(x,*) M$ is determined on neighbourhoods of $x$. Compatibility with restriction gives a compatible family of maps $cF (U) -> M$, hence a unique map from the colimit $cF_x$ to $M$.

For the right adjunction, a morphism $i_(x,*) M -> cF$ sends every $m in M$ to compatible sections that vanish on open sets avoiding $x$. Their germs at $x$ are therefore represented by sections supported at $x$, giving a map $M -> i_x^! cF$.

Conversely, let a supported germ be represented by $s in cF (W)$ with $op("supp") (s) subset.eq {x}$, and let $U$ be any neighbourhood of $x$. On $U inter W$ use $rest(s,U inter W)$. On $U - {x}$ use the zero section. These two sections agree on $(U inter W) - {x}$: every germ there is zero, so the locality axiom forces the restriction itself to vanish. The sheaf axiom therefore glues them uniquely to a section on $U$. Changing the representative of the germ gives the same glued section after shrinking once more. In this way every supported germ determines compatible sections on all neighbourhoods of $x$. Applying the construction elementwise to a homomorphism $M -> i_x^! cF$ gives a sheaf morphism $i_(x,*) M -> cF$. The two constructions are natural and inverse.
]

For the supported-section construction attached to a closed subset, see @KashiwaraSchapira1990[Ch. II, §2.3, Def. 2.3.8 and Prop. 2.3.9]. The point case above is all that is needed at this stage.

#exmp(title: "Stalk and costalk in elementary cases")[

At $0 in RR$:

+ For $C_RR^0$, the stalk consists of germs of continuous functions, while $i_0^! C_RR^0 = 0$ because a continuous function supported at one point must vanish.
+ For $constSh(k)_RR$, the stalk is $k$ and the ordinary costalk is $0$. A locally constant section is visible near $0$, while no nonzero locally constant section can be supported only at $0$.
+ For the skyscraper $i_(0,*) M$, both the stalk and the ordinary costalk are $M$.
+ For $cF = constSh(k)_RR plus.o i_(0,*) M$, $ cF_0 iso k plus.o M, quad i_0^! cF iso M $
 
In these examples the map $i_0^! cF -> cF_0$ is $0 -> k$ for the constant sheaf and $M -> M$ for the skyscraper. ]
<exmp:ordinary-stalk-costalk>

=== Étale spaces and local systems

Stalks can be assembled into a topological space over $X$. In this presentation, sections of a sheaf become continuous sections of a local homeomorphism.

#def(title: "Étale space over a topological space")[
An *étale space over $X$* is a local homeomorphism $pi : E -> X$. A morphism is a continuous map over $X$. The resulting category is denoted $"Ét" (X)$.
]
<def:etale-space-over-x>

#def(title: "Étale space of a presheaf")[
For a presheaf $cF$ of sets, define
$ "Et" (cF) := union.sq.big_(x in X) stalk(cF,x) $
with projection $pi (s_x) = x$. For $U subset.eq X$ open and $s in cF (U)$, put
$[U,s] := {s_x : x in U} $.
These subsets form a basis for the *germ topology* on $"Et" (cF)$.
]
<def:etale-space>

#prop(title: "The germ topology is étale")[
The projection $pi : "Et" (cF) -> X$ is a local homeomorphism.
]

#proof[
If $r_x in [U,s] inter [V,t]$, then $s_x = t_x$. By @prop:germ-equality, the two sections agree on a smaller neighbourhood $W$ of $x$, and $[W,rest(s,W)]$ lies in the intersection. Hence the sets $[U,s]$ form a basis. The map
$ pi|_([U,s]) : [U,s] -> U $
is a homeomorphism with inverse $x |-> s_x$.
]

#def(title: "Geometric section")[
For $pi : E -> X$, a *section over $U$* is a continuous map $sigma : U -> E$ satisfying $pi compose sigma = id_U$. We write $Gamma (U,E)$ for the set of such sections.
]
<def:geometric-section>

Every $s in cF (U)$ gives a section $x |-> s_x$ of $"Et" (cF)$. For a sheaf this accounts for every geometric section.

#prop(title: "A sheaf is recovered from its germs")[
If $cF$ is a sheaf of sets, the germ map
$cF (U) -> Gamma (U,"Et" (cF)), quad s |-> (x |-> s_x) $
is a bijection for every open $U$.
]
<prop:sheaf-recovered-from-germs>

#proof[
Injectivity is the locality axiom. A continuous section of the étale space is locally contained in basic opens $[U_i,s_i]$ and is therefore locally represented by sections $s_i$. Their germs agree on overlaps, so after refinement the sections agree and glue uniquely.
]

#thm(title: "Étale space and sheaf equivalence")[
Taking the étale space and taking continuous sections define an equivalence of categories
$ op("Sh") (X;"Set") equiv "Ét" (X) $
]
<thm:etale-sheaf-equivalence>
//  

#proof[

Both constructions are functorial. By @prop:sheaf-recovered-from-germs, for every sheaf $cF$ there are natural bijections $cF (U) iso Gamma (U,"Et" (cF)) $ for every open $U$, hence a natural isomorphism
$cF iso Gamma (-,"Et" (cF)).$

Conversely, for an étale space $pi : E -> X$, evaluation defines
$ epsilon_E : "Et" (Gamma (-,E)) -> E, quad sigma_x |-> sigma (x) $ Every $e in E$ has a neighbourhood on which $pi$ is a homeomorphism, whose inverse gives the unique germ of a local section mapped to $e$. On such a neighbourhood, $epsilon_E$ is a homeomorphism. Thus $epsilon_E$ is a natural isomorphism of étale spaces.
]
This equivalence returns us to the motivate idea, of continuous functions, that opened the chapter. 

The statement is set-valued.  For the helix sheaf $cP$, the equivalence recovers the original covering $p : RR -> S^1$: a point $t in RR$ determines the germ of the unique local inverse of $p$ through $t$. For a sheaf $cF$ of $R$-modules Addition and scalar multiplication are defined locally by representatives
$s_x + t_x := (s + t)_x, quad r s_x := (r s)_x $.

#def(title: "Local system")[
A sheaf $cL$ of $R$-modules is a *local system* if every point has an open neighbourhood $U$ such that
$ rest(cL,U) iso rest(constSh(M),U) $
for some $R$-module $M$. It has *finite type* if the local fibres are finitely generated.
]
<def:local-system>

The étale space of $constSh(M)$ is $X times M_"disc"$. More generally, the étale space of a local system is a covering whose fibres carry compatible $R$-module structures.

#def(title: "Parallel transport and monodromy")[
Let $q : Y -> X$ be a covering map and $gamma : [0,1] -> X$ a path. For every $y in q^(-1) (gamma (0))$, there is a unique lift $eta$ of $gamma$ beginning at $y$. Its endpoint defines a bijection
$ T_gamma : q^(-1) (gamma (0)) -> q^(-1) (gamma (1)) $
For a loop based at $x_0$, these maps give the *monodromy representation*
$ rho_q : pi_1 (X,x_0) -> op("Bij") (q^(-1) (x_0)) $
For a local system of $R$-modules, the image lies in
$op("Aut")_R (stalk(cL,x_0)). $
]
<def:monodromy>

For the helix, the positive loop around $S^1$ sends $n in p^(-1) (1) = ZZ$ to $n + 1$. This is the monodromy of the sheaf of lifts $cP$. It is a permutation of the fibre, not an automorphism of the additive group with a chosen zero.


#exmp(title: "A linear local system on the circle")[
Let $V$ be an $R$-module, with discrete topology, and let $T in op("Aut")_R (V)$. Form
$ E_T := (RR times V)\/tilde  $
where
$(t + 1,v) tilde (t,T v), $
and project $[t,v]$ to $e^(2 pi i t) in S^1$. Over a sufficiently short arc, choosing one lift of the angular coordinate identifies the inverse image with $U times V$. The locally constant sections therefore form a local system $cL_T$ with fibre $V$.

Follow $[0,v]$ once around the positive generator of $pi_1 (S^1)$. The lifted path is $t |-> [t,v]$, and at its endpoint
$[1,v] = [0,T v]. $
The constant-coefficient cellular calculation for the same circle appears in the homological-algebra appendix, in @ex:cellular-circle-torus. The present construction adds the return map $T$: after one circuit, the fibre is identified with itself through $T$ rather than through the identity. Thus the fibre over one point does not determine the local system; its monodromy also records how the local data are glued around the circle. For $V = k$ and $T (v) = lambda v$ with $lambda in k^times$, this gives a rank-one local system whose monodromy is multiplication by $lambda$. See @Goresky2026[§1.7(d)].
]
<exmp:linear-local-system-circle>

#exmp(title: "Riemann surface of the logarithm")[
Begin with a germ of $log$ at $1 in CC^times$ and continue it along paths. One counterclockwise turn around the origin adds $2 pi i$. The corresponding connected component of the étale space of $cO$ is the universal cover
$exp : CC -> CC^times. $
Analytic continuation is path lifting in this étale space.
Over $1$, the fibre is $exp^(-1) (1) = 2 pi i ZZ $, and a positive loop acts by the translation $w |-> w + 2 pi i$. As for the helix, this is a permutation of the fibre rather than the linear monodromy of @exmp:linear-local-system-circle.

]<exmp:logarithm-helix>

=== Sheafification and exactness

We now return to presheaves of $R$-modules. Their étale spaces are the étale spaces of the underlying set-valued presheaves, equipped with the fibrewise module operations described above. A presheaf may have suitable germs but fail to glue. Sheafification replaces it by the sheaf of continuous sections of this étale space.

#def(title: "Sheafification")[
The *sheafification* of a presheaf $cF$ is
$ shf(cF) (U) := Gamma (U,"Et" (cF)) $
The natural map $theta : cF -> shf(cF)$ sends a section to its germs.
]
<def:sheafification>

#prop(title: "Sheafification preserves stalks")[
For every $x in X$, the unit induces a natural isomorphism
$ stalk(cF,x) iso stalk(shf(cF),x) $
]

#proof[
A germ of a continuous section of $"Et" (cF)$ is locally represented by a section of $cF$, and its value at $x$ is the corresponding germ in $stalk(cF,x)$. The two constructions are inverse.
]

#thm(title: "Universal property of sheafification")[
For every sheaf $cG$, composition with $theta$ induces a natural isomorphism
$ Hom_(op("Sh") (X;R)) (shf(cF),cG) iso Hom_(op("PSh") (X;R)) (cF,cG) $
Equivalently, sheafification is left adjoint to the inclusion of sheaves into presheaves.
]
<thm:sheafification-adjunction>

#proof[
A section of $shf(cF)$ is locally represented by sections of $cF$. Applying a morphism $cF -> cG$ to these representatives gives compatible local sections of $cG$, which glue uniquely. This produces the required factorization, and local representability gives uniqueness.
]

The constant presheaf $cM_"pre"$ sheafifies to $constSh(M)$. Likewise, the presheaf of bounded continuous functions sheafifies to the sheaf of all continuous functions: boundedness is local near each point but need not be preserved by an infinite gluing.

Let $phi : cF -> cG$ be a morphism of sheaves. The kernel presheaf is already a sheaf. The image and cokernel presheaves need not satisfy gluing, so their sheaf-theoretic versions are obtained by sheafification.

#prop(title: "The category of sheaves is abelian")[
The category $op("Sh") (X;R)$ is abelian. Kernels are computed sectionwise; images and cokernels are the sheafifications of the corresponding presheaves.
]
<prop:sheaves-abelian>

#proof[
The presheaf category is abelian because its kernels and cokernels are computed open set by open set in $R$-modules. Sheafification supplies cokernels in the full subcategory of sheaves. On every stalk, the canonical map from coimage to image is the ordinary module isomorphism. Since sheafification preserves stalks, the comparison is an isomorphism of sheaves.
]

#prop(title: "Stalkwise criterion")[
A morphism of sheaves is a monomorphism, epimorphism, or isomorphism if and only if every stalk map has the corresponding property. A sequence of sheaves is exact if and only if it is exact on every stalk.
]
<prop:stalkwise-exactness>

#proof[
Stalks are filtered colimits of $R$-modules and are therefore exact. Conversely, a sheaf with zero stalk at every point is zero: every section is locally zero and hence zero by locality. Apply this observation to kernels and cokernels.
]

#prop(title: "Sheaves have enough injectives")[
The abelian category $op("Sh") (X;R)$ has enough injective objects.
]
<prop:sheaves-enough-injectives>

#proof[
For each $x in X$, choose an embedding $cF_x arrow.hook I_x$ into an injective $R$-module. The stalk functor is exact and left adjoint to the skyscraper functor, so $i_(x,*) I_x$ is injective. Products of injective objects are injective, hence $product_(x in X) i_(x,*) I_x$ is injective. The chosen embeddings define a morphism
$cF -> product_(x in X) i_(x,*) I_x$. For every $x$, the composition of its stalk map with the projection to $I_x$ is the chosen embedding $cF_x arrow.hook I_x$. The morphism is therefore a monomorphism by @prop:stalkwise-exactness.
]

The constructions of @sec:injective-model and @sec:derived-functors therefore apply to sheaves.

#exmp(title: "The exponential sequence")[
Let $C_R^0$ be the additive sheaf of continuous real-valued functions on $S^1$, and let $C_(S^1)^0$ be the sheaf of continuous circle-valued functions under pointwise multiplication. Exponentiation gives an exact sequence of sheaves of abelian groups
$ 0 -> constSh(ZZ) -> C_R^0 arrow.r.long^(t |-> e^(2 pi i t)) C_(S^1)^0 -> 0 $
The final map is an epimorphism because every circle-valued function has a continuous argument locally. It is not surjective on global sections: $id_(S^1)$ has no global lift. The obstruction is the one already visible in @exmp:logarithm-helix: a local
branch exists everywhere, and one circuit changes it.
Thus an epimorphism of sheaves need not be surjective after applying global sections.
]
<exmp:exponential-sheaf-epimorphism>

== Basic sheaf operations

The point inclusion has already given two familiar transport constructions: taking a stalk and forming a skyscraper sheaf. Both are special cases of operations attached to an arbitrary continuous map. We define those general operations first. Proper direct image is introduced separately because the support of a section can matter when data are moved between spaces.

=== Direct and inverse image

#def(title: "Direct image")[
For a sheaf $cF$ on $X$, its *direct image* is the sheaf on $Y$ defined by
$ push(f,cF) (V) := cF (f^(-1) (V)) $
for every open $V subset.eq Y$.
]
<def:direct-image>

The sheaf axiom is inherited from $cF$ because inverse images preserve unions and intersections.

For the map $a_X : X -> {*}$ sending every point to the unique point,
$ (a_(X,*) cF) ({*}) = cF (X) $
Under the identification of sheaves on a point with $R$-modules, this says
$ a_(X,*) cF = globalSect(X,cF) $
Similarly, direct image along $i_x : {x} -> X$ gives the skyscraper sheaf.

Inverse image is most transparent in the étale description. Let $pi : "Et" (cG) -> Y$ be the étale space of a sheaf $cG$. Form the pullback
$ E_f := X times_Y "Et" (cG) $
with its projection to $X$.

#def(title: "Inverse image")[
The *inverse image* $invimg(f,cG)$ is the sheaf of continuous sections of the pullback étale space $E_f -> X$.
]
<def:inverse-image>

Equivalently, it is the sheafification of the presheaf
$ U |-> op("colim")_(f (U) subset.eq V) cG (V), $
where $V$ ranges over the open subsets of $Y$ containing $f (U)$. The set $f (U)$ need not be open.

#prop(title: "Inverse image pulls back stalks")[
For every $x in X$ there is a natural isomorphism
$stalk(invimg(f,cG),x) iso stalk(cG,f (x)). $
Consequently, $f^(-1)$ is exact.
]
<prop:inverse-image-stalks>

#proof[
The fibre of $E_f -> X$ over $x$ is the fibre of $"Et" (cG) -> Y$ over $f (x)$, which is $cG_(f (x))$. The stalk of the sheaf of sections of an étale space is its fibre. Exactness follows from the stalkwise criterion.
]

For an inclusion $j : A arrow.hook X$, $j^(-1) cF$ is the restriction of $cF$ to $A$. For the point inclusion $i_x : {x} -> X$, inverse image recovers the stalk functor introduced in @def:stalk-functor:
$ i_x^(-1) cF iso cF_x $

If $cL$ is a local system on $S^1$, then $p^(-1) cL$ is constant on $RR$. Choose an isomorphism $p^(-1) cL iso constSh(V)$. The deck transformation $tau (t) = t+1$ acts on $V$ by the monodromy operator of $cL$. The pullback is constant, while the descent action retains the twisting on the circle.

#prop(title: "Inverse and direct image are adjoint")[
There is a natural isomorphism
$ Hom_(op("Sh") (X;R)) (f^(-1) cG,cF) iso Hom_(op("Sh") (Y;R)) (cG,f_* cF) $
Hence $f^(-1) tack.l f_*$. For $f = i_x$, this is the first adjunction of @prop:point-adjunctions. Since $f_*$ is a right adjoint, it is left exact.
]
<prop:inverse-direct-adjunction>

#proof[
Using the colimit description of inverse image, a morphism $f^(-1) cG -> cF$ is equivalent to compatible maps
$ cG (V) -> cF (f^(-1) (V)) = (f_* cF) (V) $
for the open subsets $V subset.eq Y$. These are exactly the components of a morphism $cG -> f_* cF$.
]

=== Proper direct image

Assume in this subsection that the spaces are locally compact and Hausdorff.

#def(title: "Proper map")[
A continuous map $g : Z -> Y$ is *proper* if $g^(-1) (K)$ is compact for every compact subset $K subset.eq Y$.
]
<def:proper-map>

#def(title: "Proper direct image")[
For a sheaf $cF$ on $X$, define
$ (f_! cF) (V) := {s in cF (f^(-1) (V)) : f|_(op("supp") (s)) : op("supp") (s) -> V " is proper"} $
Equivalently, $s$ belongs to $(f_! cF) (V)$ when
$ op("supp") (s) inter f^(-1) (K) $
is compact for every compact $K subset.eq V$.
]
<def:proper-direct-image>

These assignments form a sheaf on $Y$, and the resulting functor $f_!$ is left exact. For the map to a point,
$ Gamma_c (X,cF) := a_(X,!) cF $
is the module of global sections with compact support.

#def(title: "Extension by zero")[
Let $j : U arrow.hook X$ be an open embedding and let $cF$ be a sheaf on $U$. Then
$ (j_! cF) (V) := {s in cF (V inter U) : overline(op("supp") (s))^V subset.eq U} $
This sheaf is the *extension by zero* of $cF$ from $U$ to $X$.
]
<def:extension-by-zero>

#prop(title: "Extension by zero is exact")[
For an open embedding $j : U arrow.hook X$, the functor
$ j_! : op("Sh") (U;R) -> op("Sh") (X;R) $
is exact. Its stalks are
$ (j_! cF)_x iso cases(cF_x & x in U, 0 & x in X - U) $
]
<prop:extension-by-zero-exact>

#proof[
If $x in U$, choose a neighbourhood contained in $U$; on such neighbourhoods extension by zero agrees with $cF$, so $(j_! cF)_x iso cF_x$. If $x in X - U$, every germ allowed by the support condition vanishes after shrinking around $x$, so the stalk is zero. A short exact sequence is therefore carried to a sequence that is exact at every stalk, and @prop:stalkwise-exactness gives exactness of $j_!$.
]

#exmp(title: "Extension by zero at the boundary")[
Let $j : U := (-1,1) arrow.hook X := [-1,1]$, let $K := [-1\/2,1\/2]$, and choose $W := (-3\/4,3\/4)$. Since the compact Hausdorff space $X$ is normal, Urysohn's lemma gives a continuous function $f : X -> [0,1]$ that equals $1$ on $K$ and vanishes on $X - W$. Thus $rest(f,U)$ has support contained in $overline(W)^X subset.eq U$ and defines a section of $j_! C_U^0$. In the étale-space description, its germ map agrees with the zero section near the endpoints, so extension by zero is continuous.

The function $g (t) := 1-t^2$ extends continuously to $X$ by zero, but $op("supp") (g) = U$, so it does not define a section of $j_! C_U^0$. Similarly, for $cF := constSh(RR)_U$, a nonzero constant section near $1$ defines a nonzero germ in $(j_* cF)_1$, while its support reaches the boundary and hence $(j_! cF)_1 = 0$. Since $X$ is compact, $globalSect(X,j_! cF) iso Gamma_c (U,cF)$.
]
<exmp:boundary-difference>

Let $j : U := B^n arrow.hook X := overline(B^n)$ be the inclusion of the open unit ball in the closed unit ball. Given a compact subset $K subset.eq U$, choose an open set $W$ such that $K subset.eq W subset.eq overline(W)^X subset.eq U$. By Urysohn's lemma, there is a continuous function $f : X -> [0,1]$ that equals $1$ on $K$ and vanishes on $X - W$. Thus $rest(f,U)$ has support contained in $overline(W)^X$ and defines a section of $j_! C_U^0$. Thus $rest(f,U)$ has support contained in $overline(W)^X$ and defines a section of $j_! C_U^0$. By @prop:sheaf-recovered-from-germs, every section $s in cF (U)$ of a sheaf is represented by the continuous map $x |-> s_x$ from $U$ to $"Et" (cF)$. The function $rest(f,U)$ is therefore a concrete instance of this:  because its support stays inside $U$, its germ map agrees locally with the zero section near $X - U$ and extends continuously to $X$ by following the zero section outside $U$.

The function $g (x_1,...,x_n) := 1 - sum_(i=1)^n x_i^2$ extends continuously to $X$ by assigning the value $0$ on the boundary. However, $op("supp") (g) = U$, so its germ map disagrees with the zero section on every neighbourhood of a boundary point and cannot be extended there by the zero section. Hence $g$ does not define a section of $j_! C_U^0$.

Similarly, if $cF := constSh(R)_U$ and $p$ is a boundary point, then $(j_* cF)_p iso R$, whereas $(j_! cF)_p = 0$. Since $X$ is compact, $globalSect(X,j_! cF) iso Gamma_c (U,cF)$.


For a point inclusion $i_x:{x}->X$, proper and ordinary direct image agree:
$
i_(x,!)=i_(x,*).
$
This is the skyscraper functor, whose right adjoint is the costalk $i_x^!$ of @def:ordinary-costalk. Thus $i_x^(-1)$ reads the stalk at $x$, whereas $i_x^!$ reads information supported at $x$.

=== Tensor product and internal Hom

Let $cF,cG$ be sheaves of $R$-modules on $X$.

#def(title: "Tensor product")[
The tensor product is
$ cF times.o_R cG := shf(U |-> cF (U) times.o_R cG (U)) $
Its stalks satisfy
$ (cF times.o_R cG)_x iso cF_x times.o_R cG_x $
]
<def:sheaf-tensor>

#def(title: "Internal sheaf Hom")[
The internal Hom is the sheaf
$ sHom_X (cF,cG) (U) := Hom_(op("Sh") (U;R)) (rest(cF,U),rest(cG,U)) $
]
<def:internal-sheaf-hom>

If $U subset.eq V$, restricting a morphism over $V$ gives a map $ sHom_X (cF,cG) (V) -> sHom_X (cF,cG) (U) $ 
Compatible morphisms glue, so these modules and restriction maps already form a sheaf. Taking the largest open set gives $ globalSect(X,sHom_X (cF,cG)) iso Hom_(op("Sh") (X;R)) (cF,cG) $ Thus $sHom_X (cF,cG)$ retains the morphisms available on each open subset together with their restrictions, while the ordinary Hom module is its value on the whole space. 

There is a natural map $ sHom_X (cF,cG)_x -> Hom_R (cF_x,cG_x) $
which need not be an isomorphism for arbitrary sheaves. A morphism of stalks need not extend to a morphism on a neighbourhood.

If $cL_T$ and $cL_S$ are local systems on $S^1$ with fibres $V,W$ and monodromies $T,S$, then their tensor product has fibre $V times.o_R W$ and monodromy $T times.o S$. Their internal Hom has fibre $Hom_R (V,W)$ and monodromy
$ phi |-> S compose phi compose T^(-1) $

Consequently, $ globalSect(S^1,sHom_(S^1) (cL_T,cL_S)) iso {phi in Hom_R (V,W) : S compose phi = phi compose T} $ 
#prop(title: "Tensor and Hom adjunction")[
There is a natural isomorphism
$ Hom (cF times.o_R cG,cH) iso Hom (cF,sHom_X (cG,cH)) $
Thus $(- times.o_R cG) tack.l sHom_X (cG,-)$.
]
<prop:tensor-hom-adjunction>

#proof[
The universal property of tensor product identifies a morphism from the tensor presheaf to $cH$ with a compatible family of bilinear maps, equivalently with a morphism $cF -> sHom_X (cG,cH)$. The universal property of sheafification gives the stated bijection.
]

The same constructions apply on a ringed space $(X,cO_X)$ with tensor product and internal Hom taken over $cO_X$. This is the coefficient setting used later for $cD$-modules.


== Stratification and constructibility <sec:stratifications>

We now assume that $X$ is a complex algebraic or analytic variety embedded in a smooth manifold $M$. As we saw, sheaves themselves are defined on an arbitrary topological space. However, on a singular space, different points may have different local geometry. If we want to describe a sheaf by finitely many kinds of local behaviour, we must first divide the space into areas on which the geometry is locally uniform. In this sense, we want each piece to recover a familiar feature of a connected smooth manifold, in which there is no distinguished point from the differential-topological point of view. This is what the following theorem proves.

#thm(title: "Homogeneity of a connected smooth manifold")[
Let $M$ be a connected smooth manifold. For any $p,q in M$, there is a diffeomorphism
$ phi:M->M $
such that $phi(p)=q$.
]
<thm:diffeomorphism-transitivity>

#proof[
Choose a smooth path from $p$ to $q$ and cover its image by finitely many coordinate balls. Inside each ball, a compactly supported vector field can be chosen whose local flow moves one prescribed point to the next and is the identity outside that ball. Composing the resulting diffeomorphisms sends $p$ to $q$.
]

The theorem concerns the geometry of the manifold. However, a sheaf may vary even on a connected smooth manifold. The stratification will specify the pieces on which constructibility separately requires local constancy.

This homogeneity fails at a singularity, as the origin stubbornly refuses to look like a point on one of the arms.  In the cross $x y=0$, for example, the origin cannot play the same geometric role as a point on one of the open arms. This suggests decomposing a singular space into smooth pieces. Smoothness of the pieces alone, however, is too weak. We must also prevent pieces from accumulating arbitrarily and specify consistently which pieces occur in the boundary of which others.

Recall that a family of subsets is *locally finite* if every point has a neighbourhood meeting only finitely many members of the family. A subset is *locally closed* if it is open in its closure, equivalently if it is the intersection of an open and a closed subset.

#def(title: "Smooth stratification")[
A *smooth stratification* of $X$ is a locally finite decomposition
$ X=union.sq.big_(S in cal(S)) S $
into pairwise disjoint, connected, locally closed smooth submanifolds of $M$, called *strata*, such that the following frontier condition holds:
if
$S inter overline(T) != emptyset, $
then
$S subset.eq overline(T) $

Here the closure is taken in $X$. If $S subset.eq overline(T)$ and $S != T$, we write $S<T$ and require
$ dim S < dim T $
]
<def:smooth-stratification>

Connectedness is only a convenient normalization: if a smooth piece has several connected components, we regard those components as separate strata. The frontier condition is more substantial. It says that incidence cannot change while one moves inside a stratum. If one point of $S$ occurs in the boundary of $T$, then every point of $S$ has the same incidence relation with $T$.

For the real cross, the origin is therefore a zero-dimensional stratum and the four open rays are four one-dimensional strata. Each ray has the origin in its closure.

#figure(
  image("figures/stratification-cross-frontier.png", width: 65%),
  caption: [The cross $x y = 0$ and its frontier relation. Each open ray has the origin in its closure.]
)

The frontier condition controls which strata approach one another. It still says almost nothing about how one stratum approaches another. This distinction becomes important as soon as the transverse geometry changes while we move along a lower-dimensional stratum.

Consider the real algebraic surface
$ X={ (x,y,z) in RR^3 : x^2+z^3-y^2 z^2=0 } $
Its singular locus is the $y$-axis ${x=z=0}$. If we fix a point with coordinate $y=t$ and cut transversely to that axis, the resulting plane curve is
$ x^2+z^3-t^2 z^2=0 $
For $t != 0$ and $z$ sufficiently close to zero, the equation may be written
$x=plus.minus z sqrt(t^2-z)$
so the slice consists of two smooth branches meeting at the origin. At $t=0$, the slice becomes
$x^2+z^3=0$
which is a cusp. Thus the singular axis is itself smooth and satisfies the elementary frontier picture, while its transverse geometry changes at the origin. If a stratum is supposed to be a region on which the local geometry is uniform, the origin cannot remain in the same stratum as the rest of the singular axis.



We therefore need a condition on the manner of approach between incident smooth strata. Whitney condition $(B)$ supplies exactly this control.

Let $S<T$ and let $y in S$. Tangent spaces $T_x T$ for different points $x$ live in different tangent spaces of the ambient manifold, so they cannot literally be compared without making an identification. Choose a smooth coordinate chart around $y$. Inside this chart the tangent spaces may be regarded as subspaces of one fixed Euclidean space, and convergence is then convergence in the appropriate Grassmannian. The condition below is independent of the chosen chart.

#def(title: "Whitney condition (B)")[
Let $S<T$ be incident strata and let $y in S$. Consider sequences
$x_i in T$, $y_i in S $
with $x_i != y_i$ and
$x_i -> y$, $y_i -> y. $

Suppose that, in local coordinates around $y$,

- the tangent spaces $T_(x_i)T$ converge in the Grassmannian to a subspace $tau$, and
- the secant lines through $x_i$ and $y_i$ converge in projective space to a line $ell$.

The pair $(S,T)$ satisfies *Whitney condition $(B)$ at $y$* if every such pair of convergent sequences satisfies
$ell subset.eq tau. $

It satisfies Whitney condition $(B)$ if this holds at every $y in S$.
]
<def:whitney-b>

The secant line records the direction from the lower stratum toward the nearby point of the higher stratum. The limiting tangent space records the directions that remain tangent to the higher stratum as the two points approach one another. The inclusion
$ell subset.eq tau $
requires these two limiting descriptions to be compatible, an actual limiting direction of approach cannot disappear from the limiting tangent geometry.

For the surface above, suppose that the whole singular axis is one stratum $S$, and let $T$ be the adjacent smooth stratum. Choose $t_i>0$ with $t_i -> 0$ and set
$ a_i=(0,t_i,t_i^2) in T, quad b_i=(0,t_i,0) in S $
The secant lines through $a_i$ and $b_i$ are the $z$-axis. For
$ f(x,y,z)=x^2+z^3-y^2 z^2 $
we have
$ nabla f(a_i)=(0,-2t_i^5,t_i^4) $
Hence the normal directions converge to the $z$-axis, so the tangent planes $T_(a_i)T$ converge to the $x y$-plane. The limiting secant line is not contained in this limiting tangent plane. Thus the pair $(S,T)$ fails Whitney condition $(B)$ at the origin, and the origin must be separated from the rest of the singular axis.

#figure(
  image("figures/whitney-cusp-condition-b.png", width: 100%),
  caption: [The Whitney cusp. Normal slices change at the origin. Whitney condition $(B)$ compares limiting tangent spaces with limiting secant lines; failure requires a refinement of the lower stratum.]
)

#def(title: "Whitney stratification")[
A *Whitney stratification* of $X$ is a smooth stratification for which every incident pair
$S<T $
satisfies Whitney condition $(B)$.
]
<def:whitney-stratification>
In the complex setting used later, we take the strata to be complex analytic submanifolds and apply Whitney condition $(B)$ to their underlying real manifolds. Thus a stratum of complex dimension $d$ has real dimension $2d$.

Complex algebraic varieties admit finite Whitney stratifications. Complex analytic spaces admit locally finite Whitney stratifications; for a noncompact analytic space, finiteness is an additional hypothesis. From this point onward we work with a fixed finite Whitney stratification.

Whitney $(B)$ is a differential-geometric condition, whereas the later sheaf theory needs a topological conclusion: as one moves inside a stratum, the local stratified topology should remain unchanged. The passage between these two statements is supplied by the isotopy and control-data theorems for Whitney stratifications. To state the local model they produce, we first isolate the geometry transverse to a stratum.

=== Cones, slices, and links

Suppose for a moment that all transverse information around a point could be recovered from the set of directions leaving that point. Restoring only a radial coordinate would then reconstruct the whole transverse neighbourhood. The appropriate construction is a cone.

#def(title: "Open cone")[
Let $L$ be a compact topological space. Its *open cone* is
$ c^degree L := (L times [0,1))\/(L times {0}), $
where all points of $L times {0}$ are identified to a single point $v$, called the *vertex*. Away from the vertex there is a canonical identification
$ c^degree L-{v} iso L times (0,1) $

By convention, $c^degree emptyset $ is a single point.
]
<def:open-cone>
If $L$ is stratified, then $c^degree L$ carries the cone stratification: its strata are the vertex ${v}$ and the subsets
$ A times (0,1) $
where $A$ ranges over the strata of $L$. We give $V times c^degree L$ the product stratification. A homeomorphism of stratified spaces is *stratified* if it carries every stratum onto a stratum.

A point away from the vertex consists of a direction in $L$ together with a positive radial coordinate. Moving the radial coordinate to zero forgets the direction and approaches the vertex. The cone on one point is a half-line, $c^degree S^0$ is a line, and $c^degree S^(m-1) $
is homeomorphic to $RR^m$. The cone on four points is the local model of the four-armed cross.

#figure(
  image("figures/open-cone-construction.png", width: 65%),
  caption: [The open cone is obtained by collapsing $L times {0}$ in $L times [0,1)$ to one vertex.]
)

We now need to extract the set $L$ of transverse directions from a stratified space. If $p$ belongs to an $i$-dimensional stratum $S$, a small ambient sphere around $p$ is unsuitable: it contains directions tangent to $S$ as well as directions normal to it. We first remove the tangent directions by taking a normal slice.

#def(title: "Normal slice and link")[
Let $p in S$, where $S$ is a stratum of a stratified subset $X subset.eq M$. A *normal slice to $S$ at $p$* is a smooth submanifold $N subset.eq M$ through $p$ such that
$T_p M = T_p S plus.o T_p N$

For the link construction, choose such a slice $N$ sufficiently small and transverse to every stratum that it meets near $p$. Choose a Riemannian metric on $N$ and $epsilon>0$ sufficiently small so that the corresponding sphere
$bb(S)_epsilon(p) subset.eq N$
is transverse to every stratum of $X inter N$. The *link associated with $N$ and $epsilon$* is
$L_(p,N,epsilon):=X inter N inter bb(S)_epsilon(p)$
Its strata are the connected components of the intersections
$T inter N inter bb(S)_epsilon(p)$
where $T$ ranges over the strata of $X$.
]
<def:normal-slice-link>

The normal slice removes motion along $S$. Intersecting it with a small sphere also removes the radial coordinate, leaving the directional part of the transverse geometry. The notation $L_(p,N,epsilon)$ still records the choices of slice, metric, and radius. The local conical theorem below shows that, once these choices are sufficiently small and transverse, its stratified homeomorphism type depends only on the point and its stratum.


#figure(
  image("figures/normal-slice-link-local-model.png", width: 65%),
  caption: [A normal slice removes the tangent directions to $S$. The resulting link gives the transverse conical factor in the local product model.]
)

We can now state the topological consequence for which the Whitney condition was introduced.

#thm(title: "Local conical structure")[
Let $X$ be a complex algebraic or analytic space equipped with a Whitney stratification, and let $p$ lie in a stratum $S$ of real dimension $i$. For all sufficiently small transverse choices in @def:normal-slice-link, the stratified homeomorphism type of $L_(p,N,epsilon)$ is independent of the slice $N$, the metric, and the radius $epsilon$. We denote this type by $L_p$.

After shrinking around $p$, there are neighbourhoods $V subset.eq S$ and $U subset.eq X$ of $p$, with $V$ diffeomorphic to an open ball in $RR^i$, and a stratified homeomorphism
$U iso V times c^degree L_p$
which identifies
$S inter U$
with
$V times {v}$
]
<thm:local-conical-structure>

At a point of a top-dimensional smooth stratum, the normal slice meets $X$ only at $p$, so $L_p=emptyset$ and the conical factor is a point. The local model therefore reduces to the smooth neighbourhood $V$. At the origin of the real cross, the link consists of four points, and its open cone recovers the four local arms.

We use this theorem as a black box; see @Goresky2026[§8]. Its role is worth separating from its hypotheses. Whitney $(B)$ controls limiting tangent geometry. The isotopy and control-data theory converts that differential control into local topological triviality. The resulting conical model is what we will actually use later.

The factor $V$ in
$V times c^degree L_p$
describes motion along the stratum, while the link and the radial coordinate describe the transverse geometry. If $T>S$, then each local component of $T inter U$ corresponds to
$V times A times (0,1)$
for a stratum $A$ of $L_p$. A single stratum $T$ may contribute more than one stratum of the link. Approaching $S$ means sending the radial coordinate to zero.


#figure(
  table(
    columns: (1.1fr, 3fr),
    align: left,
    inset: 6pt,
    table.header(
      [*Geometric input*],
      [*Local consequence*],
    ),
    [Smooth strata],
    [Each stratum is a smooth manifold.],
    [Frontier condition],
    [The incident strata are constant along a stratum.],
    [Whitney condition $(B)$],
    [Every limiting secant direction lies in the corresponding limiting tangent space.],
    [Local conical structure],
    [A neighbourhood of $p in S$ has the stratified form $V times c^degree L_p $],
  ),
  caption: [The geometric conditions and their local consequences.]
)
<fig:stratification-control>

// There is one final qualification. Local constancy does not provide a preferred global identification of the transverse models over the whole stratum. As $p$ moves in a small contractible part of $S$, the links may be identified. Transporting such an identification around a loop in $S$ can return with a nontrivial stratified automorphism of the link, and hence can act nontrivially on invariants such as its cohomology. We refer to this possible twisting as *link monodromy*.
// לבדוק שזה משמש בהמשך.
The local conical theorem says that the stratified geometry is locally constant as one moves inside $S$. It imposes no condition on a sheaf. Constructibility adds such a condition by requiring the restriction to each stratum to be a finite-rank local system. This restriction may have monodromy around loops in the stratum even when the transverse links have no twisting. Variation within a stratum is governed by local-system transport, while variation across strata is recorded by the attachment data between their restrictions.

=== Constructible sheaves <sec:constructible-sheaves>

The conical model separates variation along a stratum from variation across strata. Constructibility requires local constancy in the first direction and finite algebraic data.

#def(title: "Constructible sheaf")[
Let $(X,cal(S))$ be a finite Whitney-stratified space and let $R$ be Noetherian. A sheaf $cF in op("Sh") (X;R)$ is *$cal(S)$-constructible* if $rest(cF,S)$ is a local system of finitely generated $R$-modules for every stratum $S in cal(S)$.
]
<def:constructible-sheaf>

If $R = k$ is a field, finite generation means finite-dimensional stalks.

// #def(title: "Serre subcategory")[
// A full subcategory of an abelian category is a *Serre subcategory* if it is closed under subobjects, quotients, and extensions.
// ]
// <def:serre-subcategory>

#prop(title: "Constructible sheaves form an abelian subcategory")[
For a fixed finite Whitney stratification $cal(S)$ and a Noetherian coefficient ring $R$ #footnote[A ring $R$ is *Noetherian* if every ideal of $R$ is finitely generated; equivalently, every ascending chain of ideals eventually stabilizes.], the category $op("Sh")_(cal(S))(X;R)$ is a full abelian subcategory of $op("Sh")(X;R)$, and its inclusion is exact. It is also closed under extensions in $op("Sh")(X;R)$.
]
<prop:constructible-sheaves-serre>



#proof[
Restriction to a stratum is exact. Given a morphism between two constructible sheaves, work on a sufficiently small connected open subset of a stratum on which both restrictions are constant. The morphism is then represented by a homomorphism of finitely generated $R$-modules. Its kernel and cokernel are constant sheaves associated with the corresponding module kernel and cokernel, which are finitely generated because $R$ is Noetherian. Thus kernels and cokernels computed in the ambient sheaf category remain constructible.

For extension closure, consider an exact sequence $0 -> cal(F) -> cal(E) -> cal(G) -> 0$ with constructible end terms. Restrict to a stratum and choose a point $x$ and a neighbourhood on which the end terms are constant. The stalk $cal(E)_x$ is finitely generated, hence finitely presented over $R$. Representatives of a finite set of generators, followed by shrinking to enforce their finitely many relations, define a morphism from the constant sheaf with fibre $cal(E)_x$ to $cal(E)$ near $x$. After shrinking again, this morphism commutes with the maps from the constant sheaf with fibre $cal(F)_x$ and to the constant sheaf with fibre $cal(G)_x$. Finite generation makes it enough to check these equalities on finitely many generators. Comparing the resulting short exact sequences on stalks shows that the middle morphism is an isomorphism. Hence $cal(E)$ is locally constant on the stratum and has finitely generated stalks. This proves extension closure, and since finite direct sums, kernels, and cokernels remain in the full subcategory and are computed in the ambient abelian category, the subcategory is abelian and its inclusion is exact.
]
For a constructible sheaf $cF$, the nonzero-stalk locus is the union of the strata on which its restriction is nonzero. With the closed-support convention of @def:support, this gives $op("supp")(cF)=union.big_(rest(cF,S) != 0) overline(S)$, where $S$ ranges over $cal(S)$ and closures are taken in $X$. Since the stratification is finite, this union of closures equals the closure of the nonzero-stalk locus. The frontier condition ensures that taking these closures adds only lower-dimensional strata, so the support dimension is the largest dimension of a stratum on which $cF$ is nonzero. We set $dim op("supp")(0)=-oo$.

#prop(title: "Open and closed embeddings preserve constructibility")[
Let $i : Z -> X$ be a closed union of strata and $j : U = X - Z -> X$ the complementary open union. With the induced stratifications, the exact functors
$ j^(-1), quad j_!, quad i^(-1), quad i_* $
preserve constructible sheaves.
]
<prop:open-closed-constructible>

#proof[
The assertion is checked on each stratum. Restriction retains the same local systems, extension by zero inserts the zero local system on the complementary strata, and closed pushforward changes only the ambient support.
]

For the stratification
$ RR = (-infinity,0) union.sq {0} union.sq (0,infinity) $
a constructible sheaf is described by three finitely generated modules and two generization maps 
$V_- <--V_0-->V_+ $.

For $U = RR - {0}$,

+ $j_! constSh(R)_U$ has $V_0 = 0$ and $V_- = V_+ = R$;
+ $j_* constSh(R)_U$ has $V_0 = R plus.o R$, with the two projections as generization maps;
+ $i_* V$ has $V_0 = V$ and $V_- = V_+ = 0$.

Constructibility preserves the singular boundary data while restricting it to finitely many local systems and maps. A cellular model makes this description computational.

== Cellular sheaves <sec:cellular-sheaves>

The three-stratum description of the real line above is already a finite diagram, and now we  isolate the setting in which such a diagram represents a sheaf. Let $X$ be a finite regular cell complex, meaning that the closure of each cell is a closed ball and its boundary is a union of lower-dimensional cells. We take coefficients in a field $k$.

#def(title: "Cellular sheaf")[
Let $P_X$ be the face poset of $X$, with $sigma <= tau$ when $sigma subset.eq overline(tau)$. A *cellular sheaf* is a covariant functor $cF : P_X -> k"-Vect"$ whose values are finite-dimensional. Thus it assigns a vector space $cF (sigma)$ to every cell and a map $rho_(sigma,tau) : cF (sigma) -> cF (tau)$ to every face relation, compatibly with identities and composition. We write $op("Cell") (X;k)$ for the category of these diagrams.
]
<def:cellular-sheaf>

For $sigma in P_X$, write $P_(>= sigma):={tau in P_X : sigma <= tau}$ and let $op("st") (sigma) subset.eq abs(X)$ be the union of the corresponding open cells. If $sigma <= tau$, then $op("st") (tau) subset.eq op("st") (sigma)$. Restriction from $op("st") (sigma)$ to $op("st") (tau)$ therefore has the same direction as the cellular map $cF (sigma) -> cF (tau)$. This accounts for the covariance in @def:cellular-sheaf.

#thm(title: "Cellular realization of cell-constructible sheaves")[
Let $X$ be a finite regular cell complex. Sheaves of $k$-vector spaces on $abs(X)$ that are constructible with respect to the stratification by open cells and have finite-dimensional stalks are equivalent to finite-dimensional cellular sheaves on the face poset $P_X$. Under this equivalence, the vector space attached to a cell $sigma$ is identified with the stalk on the open cell, and the face maps encode the corresponding generization maps.
]
<thm:cellular-realization>
We denote the topological sheaf corresponding to $cF$ by $op("Real")_X (cF)$. The derived form of this realization will be introduced in @sec:cellular-calculations after complexes of sheaves are available.

We keep the two categories notationally distinct and use @thm:cellular-realization when passing between them. See @Curry2018[Rem. 4.9 and §6] for the cell-poset description and @Shepard1985[Ch. 5, especially §5.2], for the derived comparison.

The theorem applies to the stratification by open cells. A sheaf constructible for a Whitney stratification enters this framework only after choosing an adapted finite regular cell decomposition, when one is available.


#exmp(title: "A cellular interval as a finite diagram")[
Let $X = [0,1]$ have vertices $v_0,v_1$ and one open edge $e$. Its face poset has the two relations $v_0 <= e$, $v_1 <= e$.
A cellular sheaf is therefore the finite diagram
$ V_0 arrow.r.long^(rho_0) V_e arrow.l.long^(rho_1) V_1 $
Under @thm:cellular-realization, the three vector spaces are the stalk values of $op("Real")_X (cF)$ on the open cells. The maps carry germs from the endpoints into the edge, where they can be compared. For the constant sheaf all three spaces are $k$ and both maps are the identity.

For constant coefficients this recovers the interval of @ex:oriented-interval-cochain. There the endpoint values already belonged to one coefficient space. A cellular sheaf allows different spaces at the endpoints and compares them after applying the generization maps. Section @sec:cellular-calculations adds the incidence signs and turns this diagram into a cochain complex.
]
<exmp:cellular-three-stratum-line>

Let $Delta$ be a small complex disc and set $Delta^* = Delta - {0}$. The decomposition $Delta = Delta^* union.sq {0}$ is a Whitney stratification. Its open stratum is not an open cell, and a local system on $Delta^*$ with fibre $V$ may have nontrivial monodromy $T$. A cellular model therefore requires an adapted decomposition into contractible cells whose incidence diagram contains a cycle around the origin. In @sec:cellular-calculations, the corresponding cellular complex reduces to $[V arrow.r.long^(T - id_V) V]$.



