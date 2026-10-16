#import "../template/template.typ": *
#import "../template/macros.typ": *

#let cohsh(n, K) = $cal(H)^(#n) (#K)$        // shared macro drops its arguments
#let sSol = math.op($cal(S)o l$)             // undecorated solution sheaf, as in chapters 05-06
#let Dual = math.op("Dual")                  // differential duality functor
#let Theta(X) = $Θ_#X$                       // bare `Theta` is undefined in this Typst version

= Differential Equations and Their Solution <chap:solution-narrative>

At the introduction we described how local solutions restrict and glue, continuation around a deleted singular point may change a branch, and restoring the point asks what information must be kept there. This chapter translates (formally) that picture into the sheaf language developed above.

We move between two descriptions of the same differential problem. On the analytic side, solutions form sheaves and derived complexes of sheaves. On the algebraic side, equations become modules over a sheaf of differential operators. Whenever the relation between the two descriptions follows directly from the definitions, we prove it here, but the full identification will come from the Riemann--Hilbert correspondence of the next chapter.

Throughout this chapter, the equation side is algebraic on a smooth complex algebraic variety $X$, while holomorphic solutions live on the associated analytic manifold $X^"an"$. The analytification step connecting these settings is made explicit below.

== Local solution data <sec:local-solution-spaces>

Let $Y'=A (z)Y$ be a linear system on an open set $U subset.eq CC$. Its local solution sheaf is defined as follows.




#def(title: "The local solution sheaf of a linear system", label: <def:local-solution-sheaf>)[
For an open subset $W subset.eq U$, set
$ sSol_A (W):=lr({Y in cO_U (W)^r mid(bar.v) Y'=A Y}) $
where $cO_U (W)^r$ consists of holomorphic maps $W->CC^r$. Restriction is componentwise. We write $sSol$ for the ordinary solution sheaf and $Sol$ for the derived solution functor introduced later.
]

Solutions agreeing on overlaps glue componentwise to a holomorphic map. The equation holds locally, so it also holds for the glued map; hence $sSol_A$ is a sheaf. At an ordinary point, where $A$ is holomorphic, the initial-value theorem gives the stronger local-system property.



#thm(title: "Nonsingular linear systems produce local systems", label: <thm:linear-system-local-system>)[
If $A:U->op("Mat")_r (CC)$ is holomorphic, then the local solution sheaf $sSol_A$ (@def:local-solution-sheaf) is a local system (@def:local-system) of rank $r$. Here the rank means the complex dimension of a fibre, or equivalently of any stalk. For every $z_(0) in U$, evaluation at $z_(0)$ identifies its stalk with $CC^r$.
]

#proof[
Fix $z_(0) in U$. For every $v in CC^r$, local existence and uniqueness give a unique solution $Y_v$ near $z_(0)$ with $Y_v (z_(0))=v$. Hence evaluation identifies the stalk with $CC^r$.

Choose the solutions $Y_1,...,Y_r$ whose initial values are the standard basis of $CC^r$, and put them into the columns of a matrix $Phi=(Y_1|...|Y_r)$. Then $Phi (z_(0))=I_r$. After shrinking the neighbourhood, $det Phi$ remains nonzero. Every local solution can therefore be written uniquely as
$ Y=Phi c $
for a holomorphic vector-valued function $c$. The equation forces this coefficient vector to be constant. Indeed, $c=Phi^(-1)Y$, and differentiating gives
$ c'=(Phi^(-1)Y)'=-Phi^(-1)Phi'Phi^(-1)Y+Phi^(-1)Y'=0 $
because $Phi'=A Phi$ and $Y'=A Y$. Thus $c in CC^r$ is constant. On this neighbourhood the solution sheaf is isomorphic to the constant sheaf with fibre $CC^r$, so it is a local system of rank $r$.
]

If $U$ is connected, continuation along paths gives the monodromy representation
$ rho:pi_1(U,z_(0))->op("GL")((sSol_A)_(z_(0))) $
Evaluation at $z_(0)$ identifies global solutions with the vectors fixed by every monodromy operator.


#exmp(title: "The Euler equation and monodromy", label: <exmp:euler-monodromy>)[
For
$ z u' (z)=alpha u (z) $
on $CC^times$, choose a branch $"Log"_W z$ on a simply connected open set $W$. The local solutions are
$ u (z)=c e^(alpha "Log"_W z) $
After one counterclockwise circuit around the origin, $"Log" z$ changes by $2 pi i$, so the solution is multiplied by
$ lambda:=e^(2 pi i alpha). $
Thus the solution sheaf is a rank-one local system $cL_lambda$ with monodromy $lambda$. Monodromy, it seems, has a poor memory for integers, as it remembers $alpha$ only modulo $ZZ$, since replacing $alpha$ by $alpha+m$ with $m in ZZ$ leaves $e^(2 pi i alpha)$ unchanged. 
]

For a local system $cL_T$ on $CC^times$ with fibre $V$ and monodromy $T$, the cellular calculation (@exmp:cellular-link-monodromy) gives
$ RGam(CC^times,cL_T) iso [V arrow.r.long^(T-id_V) V]$
in degrees $0$ and $1$. Thus
$ H^0(CC^times,cL_T) iso ker(T-id_V), quad H^1(CC^times,cL_T) iso V / ((T-id_V)V) $
The kernel consists of single-valued global solutions. A class in $H^1$ is represented by a cellular $1$-cochain $b in V$; it vanishes exactly when $b=(T-id_V)v$ for some $v in V$, so that $b$ can be removed by a cellular coboundary. For the Euler local system, both groups vanish when $lambda eq.not 1$ and both are $CC$ when $lambda=1$.

To compare extensions of these local systems across the origin, we now encode the equations as differential modules.

== Differential modules <sec:weyl-modules>

Differentiating a system can produce relations that are absent from its
displayed equations. Consider a holomorphic function $u (x,y)$ satisfying
$ partial_x u=0, quad partial_y u=x u $
Differentiate the first equation with respect to $y$ -
$ partial_y partial_x u=0 $
Differentiate the second with respect to $x$ and use $partial_x u=0$ - 
$ partial_x partial_y u=partial_x (x u)=u+x partial_x u=u. $
Holomorphic functions have commuting mixed partial derivatives, so
$ partial_x partial_y u=partial_y partial_x u $
Comparing the two calculations gives $u=0$.


On the algebraic affine line we write the coordinate as $x$. After analytification it becomes the same complex coordinate that was written $z$ on the solution side.

Multiplication by the coordinate $x$ and differentiation $partial$ act on $CC[x]$. The product rule gives
$ partial (x f)-x partial (f)=f $
for every polynomial $f$. Thus, as operators,
$ partial x-x partial=1 $
For operators $P,Q$, their *commutator* is $[P,Q]:=P Q-Q P$. The relation
$ [partial,x]=1 $
shows that multiplication and differentiation generate a noncommutative algebra.

#def(title: "The Weyl algebra", label: <def:weyl-algebra>)[
The *first Weyl algebra* is the associative $CC$-algebra
$ A_1:=(CC<x,partial>)/(partial x-x partial-1) $
Here $CC<x,partial>$ is the free associative algebra on the two generators, and the denominator denotes the two-sided ideal generated by the displayed relation.
The *$n$-th Weyl algebra* is the tensor product over $CC$ of $n$ copies of $A_1$, one for each pair $(x_i,partial_i)$. Equivalently, it is generated by
$ x_1,...,x_n,partial_1,...,partial_n $
with relations
$ [partial_i,x_j]=delta_(i j), quad [x_i,x_j]=0, quad [partial_i,partial_j]=0 $
It acts on the polynomial ring $CC[x_1,...,x_n]$ by multiplication and ordinary differentiation.
]

An element of $A_n$ is a polynomial-coefficient differential operator. For example,
$ P=x^2 partial^2+(x+1)partial-3 $
acts on a function $f$ by
$ P (f)=x^2 f''+(x+1)f'-3f $
Every element of $A_n$ has a unique ordered expression
$ P=sum_(alpha,beta)c_(alpha,beta)x^alpha partial^beta $

The ordered monomials form a basis, so the displayed commutator relations introduce no further linear relations. The Weyl algebra is left and right Noetherian; see @HTT2008[Prop. 1.4.6].



For an equation $P u=0$, take the cyclic left module
$ M_P:=A_n / (A_n P) $
Its generator $[1]$ represents the unknown, and $P[1]=0$ is the relation. Since $A_n P$ is a left ideal, every differential consequence $Q P[1]=0$ also holds in the quotient (including the ones we lacked the patience to write down).

For $s$ unknowns, use a free module with basis $e_1,...,e_s$. A relation
$ r_j=sum_(ell=1)^s P_(j ell)e_ell $
represents the equation $sum_(ell=1)^s P_(j ell)u_ell=0$. The system is presented by
$ M:=A_n^s/(A_n r_1+...+A_n r_m) $
Replacing the generators of this relation submodule leaves the quotient unchanged. In particular, the Euler equation gives
$ M_alpha:=A_1 / (A_1 (x partial-alpha)) $
Mapping the quotient into a left $A_n$-module $B$ recovers the solutions with values in $B$.

#prop(title: "Solutions as module morphisms", label: <prop:solutions-as-module-morphisms>)[
Let $B$ be a left $A_n$-module. Evaluation at the cyclic generator $[1]$, the class of $1 in A_n$, gives a natural isomorphism
$ Hom_(A_n) (M_P,B) iso lr({b in B mid(bar.v) P b=0}). $
For a finitely presented system $M$, the space $Hom_(A_n) (M,B)$ is the space of tuples in $B$ satisfying all its relations.
]

#proof[
An $A_n$-linear morphism $phi:M_P->B$ is determined by $b:=phi ([1])$. Since $P [1]=0$, one must have $P b=0$. Conversely, if $P b=0$, then
$ Q [1] mapsto Q b $
defines a well-defined $A_n$-linear morphism. The same argument applied to a free presentation gives the statement for several unknowns and relations.
]

For the Euler module $M_alpha$, a nonzero polynomial solution exists exactly when $alpha$ is a nonnegative integer; a nonzero rational solution exists exactly when $alpha in ZZ$. On a simply connected open subset of $CC^times$, a holomorphic branch of $z^alpha$ exists for every $alpha$. The solution space therefore depends on the target $A_n$-module $B$.

The compatibility calculation that opened this section now becomes algebraic. Put
$ I:=A_2 partial_x+A_2 (partial_y-x) $
The commutator calculation
$ [partial_x,partial_y-x]=-1 $
shows that $1 in I$. Hence $I=A_2$ and $A_2 \/ I=0$. The quotient already contains the differential consequence $u=0$ that was obtained earlier by differentiating and comparing the two displayed equations.

=== Differential operators on a smooth variety

// The Weyl algebra gives the coordinate model on affine space. On a general smooth variety there need not be global coordinates or global operators $partial_i$, so the construction has to be phrased intrinsically and locally. Regular functions still act by multiplication, vector fields still act by differentiation, and the Leibniz rule relates the two. Because these data restrict to smaller opens and agree on overlaps, they assemble into a sheaf of rings.

// Only a small amount of algebraic geometry is needed below. The affine space $bb(A)^n$ over $CC$ is $CC^n$ equipped with its algebraic functions. Zariski-closed subsets are cut out by polynomial equations, and their complements are the Zariski-open subsets. The punctured affine line $bb(A)^1-{0}$ will be the basic example.

// #ed[#def(title: "Regular functions and the structure sheaf", label: <def:regular-functions-structure-sheaf>)[
// On affine space $bb(A)^n$, a global regular function is a polynomial. On a general algebraic variety $X$, a function is *regular* on an open set when locally it can be written as a quotient of polynomials whose denominator does not vanish there. These functions form the *structure sheaf* $cO_X$.
// ]

// #def(title: "Smooth algebraic variety", label: <def:smooth-algebraic-variety>)[
// A complex algebraic variety $X$ is *smooth* at $x$ when $dim_CC T_x X=dim_x X$, and it is smooth when this holds at every point. For the varieties used here, this is equivalent to regularity of the local rings. Smoothness ensures that the tangent and cotangent spaces below assemble into vector bundles.
// ]]

// A tangent vector should be thought of literally as a derivative at a point. If $x in X$, a tangent vector $v in T_(x) X$ is a $CC$-linear rule that assigns to every germ of a regular function $f$ at $x$ a number $v (f) in CC$ and satisfies the Leibniz rule
// $ v (f g)=f (x)v (g)+g (x)v (f). $
// On $bb(A)^n$, a vector $v=(v_1,...,v_n)$ acts by the directional derivative
// $ v (f)=sum_i v_i partial_i f (x). $
// Thus $T_(x) X$ is the space of derivative directions at $x$, and smoothness ensures that these spaces have locally constant dimension.

// An *algebraic vector field* on an open set $U$ is a regular choice of tangent vector $v_x in T_(x) X$ for every $x in U$. Equivalently, it is a derivation
// $ v:cO_X (U)->cO_X (U) $
// satisfying $v (f g)=f v (g)+g v (f)$. The sheaf of algebraic vector fields is denoted $Theta(X)$. From here on, $v$ and $w$ denote vector fields and the letters $xi_i$ are reserved for cotangent fibre coordinates.

// Dually, a regular function $f$ determines at each point the covector $d f_x (v):=v (f)$, and the sheaf $Omeg(X)^1$ of *algebraic one-forms* is locally generated by $d x_1,...,d x_n$ with regular-function coefficients. One-forms are all that the connections below require; the cotangent bundle itself is introduced in @sec:characteristic-varieties, at the point where it becomes geometric.

// The Weyl algebra is the coordinate model on affine space. On a smooth algebraic variety $X$, regular functions form the structure sheaf $cO_X$, and algebraic vector fields form the sheaf $Theta(X)$ of $CC$-linear derivations of $cO_X$.

// At a point $x in X$, a tangent vector is a derivation on germs of regular functions:
// $ v (f g)=f (x)v (g)+g (x)v (f). $
// An algebraic vector field on an open set $U$ is a derivation
// $ v:cO_X (U)->cO_X (U) $
// satisfying $v (f g)=f v (g)+g v (f). $
// The sheaf $Omeg(X)^1$ of algebraic one-forms is dual to $Theta(X)$ and is locally generated by $d x_1,...,d x_n$. We reserve $v,w$ for vector fields and $xi_i$ for cotangent fibre coordinates.

On a smooth algebraic variety $X$, the structure sheaf $cO_X$ consists of regular functions, locally expressible on affine charts as quotients of polynomial functions with nonvanishing denominator. The sheaf $Theta(X)$ consists of the $CC$-linear derivations of $cO_X$.

At a point $x$, a tangent vector is a $CC$-linear map
$v:cO_(X,x)->CC $
satisfying
$ v (f g)=f (x)v (g)+g (x)v (f) $
The sheaf $Omeg(X)^1$ of algebraic one-forms is the $cO_X$-dual of $Theta(X)$. A regular function $f$ determines the one-form $d f$ by
$ (d f)(v)=v (f) $
Locally, $Omeg(X)^1$ has a basis $d x_1,...,d x_n$. We use $v,w$ for vector fields and $xi_i$ for cotangent fibre coordinates.

#def(title: "The sheaf of differential operators and its modules", label: <def:algebraic-d-sheaf-module>)[
Let $X$ be a smooth complex algebraic variety. The sheaf $DX(X)$ is the subsheaf of $End_CC (cO_X)$ generated locally by multiplication by regular functions and by algebraic vector fields.

Equivalently,
$F_(-1) DX(X)=0$, $F_0 DX(X)=cO_X $
and, for $m>=1$, $F_m DX(X)$ consists of the local $CC$-linear endomorphisms $P$ of $cO_X$ satisfying
$[P,f] in F_(m-1) DX(X) $
for every local regular function $f$, viewed as a multiplication operator.

A left $DX(X)$-module is *coherent* if it is locally finitely presented over this sheaf of rings. 
]
Concretely, this means that locally the differential system can be described by finitely many generators and finitely many generating relations.

We abbreviate $DX(X)$ to $Dop$ when $X$ is clear. The relation
$[v,f]=v(f) $
is the local form of the Weyl relation. On $bb(A)^n$, the global differential operators form $A_n$.

For a regular function $f$, put $X_f=lr({x in X mid(bar.v) f(x) eq.not 0})$. The localization
$ cM_f:=cO_X[f^(-1)] otO cM $
is a sheaf on $X$ whose restriction to $X_f$ is $rest(cM,X_f)$; the vector-field action extends by the quotient rule. On the punctured affine line, $x$ is invertible, so the Euler relation becomes
$ partial u=(alpha/x)u $

The nonsingular differential modules considered here are those whose underlying $cO_X$-modules are locally free of finite rank. Thus every point has an open neighbourhood $U$ on which
$rest(cE,U) iso cO_U^r $.

A connection differentiates sections of a vector bundle along vector fields. Its Leibniz rule extends the product rule for scalar functions.

A connection on a locally free $cO_X$-module $cE$ is a $CC$-linear morphism of sheaves
$ nabla:cE->Omeg(X)^1 otO cE $
satisfying
$ nabla (f e)=d f otO e+f nabla (e) $
for local sections $f$ of $cO_X$ and $e$ of $cE$. Evaluating the one-form part on a vector field $v$ gives the covariant derivative $nabla_v$. The connection is *integrable* or *flat* when
$[nabla_v,nabla_w]=nabla_([v,w]) $.

A local section $s$ is called *horizontal* when
$nabla (s)=0. $
Equivalently, $nabla_v s=0$ for every local vector field $v$. On a line, for the rank-one connection
$ nabla (u)=d u-a (z) u d z, $
the horizontal condition is exactly
$ u'=a (z)u. $
Thus the familiar solutions of a nonsingular first-order equation are horizontal sections of the corresponding connection. After analytification, flatness is what makes horizontal transport compatible in several directions and locally produces a constant finite-dimensional space of horizontal sections.

#prop(title: "Flat connections as nonsingular differential modules", label: <prop:connections-as-d-modules>)[
For a locally free finite-rank $cO_X$-module $cE$, giving a left $DX(X)$-module structure extending its $cO_X$-module structure is equivalent to giving an integrable connection on $cE$.
]

#proof[
A $DX(X)$-action lets every vector field $v$ act on $cE$. The relation $[v,f]=v (f)$ gives the Leibniz rule, and the commutator relation among vector fields gives
$ [nabla_v,nabla_w]=nabla_([v,w]). $
Conversely, an integrable connection gives actions of regular functions and vector fields satisfying exactly these relations. Since $DX(X)$ is generated locally by functions and vector fields, the actions extend uniquely to all differential operators.
]

Thus integrable connections are precisely $DX(X)$-modules whose underlying $cO_X$-modules are locally free of finite rank; see @HTT2008[Lemma 1.2.1]. After analytification, their horizontal sections form local systems.

The variance is visible in a rank-one calculation. On $X=bb(A)^1$, let $a in CC[x]$ and consider
$ cM=DX(X)/(DX(X)(partial-a)) $
with generator $e=[1]$. Since $partial e=a e$, the action on a section $f e$ is
$ partial (f e)=(f'+a f)e $
Thus $f e$ is horizontal exactly when
$f'=-a f $.

A $DX(X)$-linear morphism $phi:cM->cO_X$ is determined by $u:=phi (e)$, and
$ u'=partial phi (e)=phi (partial e)=a u $
Hence a morphism from $cM$ to $cO_X$ satisfies the dual equation $u'=a u$. After analytification, these morphisms form the local system of horizontal sections of the dual connection..

== Derived solution <sec:derived-solution-transition>

The ordinary solution functor is not exact in the module variable. The following equations have the same ordinary solution sheaf but different derived solution complexes.

#exmp(title: "The same ordinary solutions, different derived data", label: <exmp:ordinary-versus-derived-solutions>)[
Consider the equations $u'=0$ and $z u'=0$ on $CC$, and write $i_0:{0} into CC$ for the inclusion of the origin. For the first, $u$ is locally constant. For the second, $z u'=0$ implies $u'=0$ away from $0$, and holomorphicity forces the same constant value across the origin. Thus
$ ker (partial:cO_CC->cO_CC) iso ker (z partial:cO_CC->cO_CC) iso constSh(CC)_CC $
The ordinary solution sheaf does not distinguish the equations.

The difference appears in the corresponding inhomogeneous equation. Put the source in degree $0$ and the target in degree $1$:
$ K_partial:=[cO_CC xto(partial) cO_CC], quad K_(z partial):=[cO_CC xto(z partial) cO_CC] $
Every holomorphic germ has a local antiderivative, so
$ cohsh(0,K_partial)=constSh(CC)_CC, quad cohsh(1,K_partial)=0 $
For the second complex, write
$ u (z)=sum_(n>=0) a_n z^n $
Then
$ z u' (z)=sum_(n>=1) n a_n z^n $
whose image consists exactly of germs with zero constant term. The cokernel at $0$ is therefore one-dimensional, while away from $0$ multiplication by $z$ is invertible and the cokernel vanishes. Hence
$ cohsh(0,K_(z partial))=constSh(CC)_CC, quad cohsh(1,K_(z partial))=push(i_0,CC) $

The extra skyscraper is the obstruction to solving $z u'=f$ when $f$ has a nonzero constant term. For $alpha=0$, the Euler equation has trivial monodromy on $CC^times$ but point-supported first solution cohomology after extension across the origin.
]

The module formalism explains why the two-term complexes in @exmp:ordinary-versus-derived-solutions arise canonically. Write
$ M_partial:=A_1/(A_1 partial), quad M_0:=A_1/(A_1 x partial) $
For $P=partial$ or $P=x partial$, the cyclic module $M_P$ has a free resolution
$ 0->A_1 xto(R_P) A_1->M_P->0 $
We use the fact that $A_1$ has no zero divisors, so right multiplication by a nonzero $P$ is injective; compare @HTT2008[§1.1 and Appendix D]. Here $R_P (Q):=Q P$. This is a morphism of left $A_1$-modules because
$ R_P (a Q)=(a Q)P=a (Q P)=a R_P (Q) $
and its image is the left ideal $A_1 P$. Applying $Hom_(A_1) (-,B)$ reverses the arrow and gives $[B xto(P) B]$.

For the sheaf complexes above, pass instead to the analytic sheaf of differential operators on $CC$. The corresponding resolution is
$ 0->DX(CC) xto(R_P) DX(CC)->DX(CC)/(DX(CC)P)->0 $
where $DX(CC)$ now denotes the analytic sheaf of holomorphic differential operators. Applying sheaf $sHom_(DX(CC)) (-,cO_CC)$ gives $[cO_CC xto(P) cO_CC] $
with terms in degrees $0$ and $1$. Derived sheaf Hom makes the result independent of the chosen resolution. The next subsection formalizes the passage from algebraic modules to analytic differential modules.



=== Analytification and the solution complex

Let
$rho:X^"an"->X $
be the analytification map. Regular functions and algebraic vector fields act on holomorphic functions, giving a morphism
$ invimg(rho,DX(X)) -> DX(X^"an"). $
For an algebraic differential module $cM$, define
$ cM^"an":=DX(X^"an") times.o_(invimg(rho,DX(X))) invimg(rho,cM) $
The sheaf $DX(X^"an")$ is faithfully flat over $invimg(rho,DX(X))$, so analytification is exact; see @HTT2008[§4.7].

Analytification permits holomorphic coefficients but does not take solutions. For example, $partial-1$ is an algebraic operator, whereas its solution $exp (x)$ lies in $cO_(X^"an")$ rather than $cO_X$.


#def(title: "The holomorphic solution complex", label: <def:solution-complex>)[
For an algebraic $DX(X)$-module $cM$, the ordinary holomorphic solution sheaf is
$ sSol (cM):=sHom_(DX(X^"an")) (cM^"an",cO_(X^"an")) $
For $cM^bullet in Db(Mod(DX(X)))$, its *solution complex* is
$ Sol_X (cM^bullet):=RsHom_(DX(X^"an")) ((cM^bullet)^"an",cO_(X^"an")) $
]

Here $sSol$ denotes the ordinary solution sheaf, while $Sol_X$ is its derived extension to bounded complexes. The subscript $X$ records the algebraic variety, and the resulting complex is a complex of sheaves on $X^"an"$. The notation $RsHom_(DX(X^"an"))$ denotes internal derived Hom over the sheaf of analytic differential operators; its Hom-complex and totalization are formed by the same procedure as in @def:internal-derived-hom. The analytic and algebraic definitions are given in @HTT2008[§4.2 and §4.7].

The output is a sheaf, or a derived complex of sheaves, of $CC$-vector spaces. In general it is not an $cO_(X^"an")$-module. If $u'=0$ and $f$ is holomorphic, then
$ (f u)'=f' u $
which need not vanish. The product rule promptly vetoes arbitrary holomorphic scalars.

The construction is contravariant. A morphism $a:cM^bullet->cN^bullet$ in $Db(Mod(DX(X)))$ gives, by precomposition,
$ Sol_X (cN^bullet)->Sol_X (cM^bullet) $
This reversal is already visible in $Hom (-,cO)$ and is the derived version of the dual-horizontal-section calculation above. If $cM$ is concentrated in degree $0$, then $cohsh(0,Sol_X (cM)) iso sSol (cM)$. The sheaves $cohsh(i,Sol_X (cM))$ for $i>0$ are the sheaves $cal(E)"xt"^i_(DX(X^"an")) (cM^"an",cO_(X^"an"))$, the derived corrections of that ordinary sheaf. The skyscraper found for $x partial$ is the first such contribution, in degree $1$: it measures a local failure of exactness of the ordinary solution functor, and the Ext is taken over the ring of holomorphic differential operators, not over $cO_(X^"an")$ or over the constant sheaf.

Because $Sol_X$ is contravariant and, for an integrable connection, returns the horizontal sections of the dual connection, we formulate Riemann--Hilbert using the covariant de Rham complex.

#def(title: "The normalized de Rham complex", label: <def:de-rham-complex>)[
Let $n=dim_CC X$ and let $cM$ be a left $DX(X)$-module. After analytification, local holomorphic coordinates $x_1,...,x_n$ give the complex
$ cM^"an" -> Omeg(X^"an")^1 times.o_(cO_(X^"an")) cM^"an" -> dots -> Omeg(X^"an")^n times.o_(cO_(X^"an")) cM^"an", $
with $cM^"an"$ in degree $0$ and differential
$ d (omega times.o m)=d omega times.o m+sum_(i=1)^n d x_i and omega times.o partial_i m. $
The *normalized de Rham complex* $DR_X (cM)$ is this complex shifted by $[n]$. For a bounded complex of differential modules, one totalizes the resulting double complex.
]
For an integrable connection $cE$, the holomorphic Poincaré lemma gives $ DR_X (cE) iso shift(cL,n), $
where $cL$ is its local system of horizontal sections.

For a nonsingular algebraic system $Y'=A Y$, let $cM_A$ be the differential module generated by $e_1,...,e_r$ with relations
$partial e_i=sum_j A_(i j)e_j $
Evaluation at the generators and the holomorphic Poincaré lemma give
$ cohsh(0,Sol_X(cM_A)) iso sSol_A quad cohsh(i,Sol_X(cM_A))=0 " for " i>0 $
Thus $Sol_X(cM_A)$ recovers the ordinary solution sheaf. At singular points higher solution cohomology may occur, as in @exmp:ordinary-versus-derived-solutions.

The functor $Sol_X$ is contravariant and $DR_X$ is covariant. Their relation through differential and Verdier duality is stated in @prop:rh-dr-sol-duality; see @HTT2008[Prop. 4.2.1 and §7.1]. To ensure that these complexes vary along finitely many strata, we now impose a condition on the characteristic geometry of the module.

== Characteristic geometry<sec:characteristic-varieties>

Passing to the associated graded algebra turns the order filtration into commutative data on the cotangent bundle.

#def(title: "Cotangent space and cotangent bundle", label: <def:cotangent-bundle>)[
For $x in X$, the *cotangent space* is the linear dual
$ T_(x)^* X:=Hom_CC (T_(x) X,CC). $
Its elements are *covectors*: they measure tangent vectors rather than provide derivative directions themselves. The fibre of $Omeg(X)^1$ at $x$ is $T_(x)^* X$, and the *cotangent bundle* $T^* X$ is the vector bundle whose fibre over $x$ is $T_(x)^* X$. In local coordinates a point of $T^* X$ is written
$ (x_1,...,x_n;xi_1,...,xi_n), $
meaning the covector $sum_i xi_i d x_i$ over the base point $(x_1,...,x_n)$.
]

Return now to affine space. An operator of order at most $m$ has the form
$ P=sum_(|beta|<=m) a_beta (x) partial^beta, $
which is the coordinate description of the filtration $F_m DX(X)$ introduced in @def:algebraic-d-sheaf-module, so that
$ F_0 A_n subset.eq F_1 A_n subset.eq F_2 A_n subset.eq ... . $
Set
$ grF A_n:=bds_(m>=0) F_m A_n/F_(m-1) A_n $
This algebra records each differential order modulo lower-order terms. Denote the degree-one class of $partial_i$ by $xi_i$. Since commutators lower differential order, these classes commute, and
$ grF A_n iso CC[x_1,...,x_n,xi_1,...,xi_n] $
This is the coordinate ring of $T^*bb(A)^n$, where $xi_i$ is the fibre coordinate dual to $d x_i$. Thus
$ partial_i mapsto xi_i $
turns the highest-order part of an operator into a polynomial function on the cotangent bundle. For example,
$ P=x^2 partial^2+(x+1)partial-3 $
has order $2$ and principal symbol
$ sigma_2(P)=x^2 xi^2 $
Only the order-two part contributes to the principal symbol.

The coordinate-free form is
$ grF DX(X) iso "Sym"_(cO_X) (Theta(X)) iso push(pi,cO_(T^* X)), $
where $pi:T^* X->X$. The symmetric algebra appears because, after lower-order commutators have been discarded, the degree-one symbols of vector fields commute. An order-$m$ operator therefore determines a degree-$m$ polynomial along each cotangent fibre, its *principal symbol*.

For a coherent $DX(X)$-module $cM$, a *good filtration* is locally of the form
$ F_p cM=sum_j F_(p-a_j) DX(X) m_j $
for finitely many local generators $m_j$ and integers $a_j$. Equivalently, $grF cM$ is coherent over $grF DX(X)$. Every coherent $DX(X)$-module admits such a filtration locally. The graded module therefore determines a coherent sheaf on $T^* X$. Although the graded module depends on the chosen good filtration, its support does not; these are @HTT2008[Thms. 2.1.3 and 2.2.1].

#def(title: "Characteristic variety", label: <def:characteristic-variety>)[
The *characteristic variety* of a coherent $DX(X)$-module $cM$ is
$ Char (cM):=supp (grF cM) subset.eq T^* X, $
where $F$ is any good filtration. It is a closed conic subset and is independent of the chosen good filtration.
]

The projection of $Char (cM)$ to $X$ is the ordinary support of $cM$, but the cotangent fibres contain more information. Recall that an actual derivative direction is a tangent vector $v in T_(x) X$. A covector $xi in T_(x)^* X$ instead tests such directions. If a hypersurface is locally given by $phi=0$, the covector $d phi_x$ vanishes on tangent vectors that stay inside the hypersurface and therefore measures the normal direction across it. For a scalar operator $P$ of order $m$, the hypersurface is characteristic at $x$ when
$ sigma_m (P) (x,d phi_x)=0. $
Informally, the leading part of the equation then fails to control propagation across that hypersurface.For example, on $CC^2$ consider
$ partial_x u=0. $
The principal symbol is $xi_x$. Across the hypersurface $x=c$, take $phi=x-c$. Then $d phi=d x$ and
$ sigma (partial_x) (d x)=1, $
so the hypersurface is non-characteristic. Indeed, prescribing a function of $y$ on $x=c$ determines the nearby solution uniquely: the equation says to keep that value constant as $x$ varies. Across $y=c$, however, $d phi=d y$ and
$ sigma (partial_x) (d y)=0. $
The equation imposes no condition on how the solution varies with $y$, so data on that hypersurface do not control a unique nearby solution. The Cauchy--Kowalevski--Kashiwara theorem generalizes this local calculation.

#exmp(title: "Propagation, point support, and the Euler singularity", label: <exmp:three-characteristic-varieties>)[
On $bb(A)^n$, the polynomial module
$ CC[x_1,...,x_n] iso A_n / (A_n partial_1+...+A_n partial_n) $
has
$Char (CC[x_1,...,x_n])=V (xi_1,...,xi_n) $
the zero section of $T^* bb(A)^n$. It represents nonsingular propagation across the base.

For $delta_0:=A_1 /( A_1 x) $
one has $Char (delta_0)=V (x)=T_(0)^* bb(A)^1, $
the full cotangent fibre over the origin. The notation recalls the Dirac delta - the relation $x delta_0=0$ is compatible with the nonzero derivatives $partial^k delta_0$. Its characteristic variety records precisely these normal cotangent directions.

For the Euler module
$ M_alpha=A_1 / (A_1 (x partial-alpha)) $
the principal symbol is $x xi$, so
$ Char (M_alpha)=V (x xi)=V (xi) union V (x) $
Away from $0$ only the zero section remains, while the extra cotangent fibre appears over the singular point. The exponent $alpha$ is lower-order data and is therefore invisible to the characteristic variety.

This missing parameter reappears in the solution data. After restriction to $CC^times$, @exmp:euler-monodromy gives the monodromy
$ exp (2 pi i alpha) $
For example, $M_0$ and $M_(1/2)$ have the same characteristic variety, while their solution local systems have monodromies $1$ and $-1$. The characteristic variety records the possible singular directions and suggests the relevant stratification. The full differential module retains the local system and its monodromy along the smooth stratum.

In particular, compare $M_partial$ with $M_0$. The first has only the zero section, while the second has an additional cotangent fibre over $0$. The additional cotangent fibre of $M_0$ corresponds to the skyscraper $push(i_0,CC)$ in degree $1$ of the derived solution calculation.
]

The appearance of conormal directions links this algebraic geometry to the stratified language of the preceding chapters. For a smooth stratum $S subset.eq X$, its conormal bundle is
$ T_S^* X:=lr({(x,xi) in T^* X mid(bar.v) x in S, quad rest(xi,T_x S)=0}). $
Thus a conormal covector vanishes on every tangent direction that stays inside the stratum and detects only transverse directions. If $S$ has complex dimension $d$ inside an $n$-dimensional smooth variety, then each conormal fibre has dimension $n-d$, so
$ dim T_S^* X=d+(n-d)=n $
Hence conormal bundles have dimension $n$, the minimum permitted by Bernstein's inequality. Their base directions lie along the stratum, while their cotangent fibres record transverse directions.


#prop(title: "Characteristic varieties in exact sequences", label: <prop:characteristic-exact-sequence>)[
For a short exact sequence of coherent $DX(X)$-modules
$ 0->cM'->cM->cM''->0, $
one has
$ Char (cM)=Char (cM') union Char (cM''). $
]

#proof[
Locally choose a good filtration on $cM$, give $cM'$ the induced filtration and $cM''$ the quotient filtration, and choose them so that the filtered sequence is strict. The associated graded sequence is then exact over the commutative ring $grF DX(X)$. The support of the middle graded module is the union of the supports of the other two, giving the stated formula. This is the argument behind @HTT2008[Thm. 2.2.1].
]

The cotangent bundle of an $n$-dimensional smooth variety has dimension $2n$, and
$Char(DX(X))=T^*X $
Bernstein's inequality gives the lower bound for the characteristic variety of a nonzero coherent module.

#thm(title: "Bernstein inequality", label: <thm:bernstein-inequality>)[
If $cM$ is a nonzero coherent $DX(X)$-module on a smooth variety of complex dimension $n$, then
$ dim Char (cM)>=n. $
]

The bound follows from the involutivity of characteristic varieties; see @HTT2008[Cor. 2.3.2].

#def(title: "Holonomic module", label: <def:holonomic-d-module>)[
A coherent $DX(X)$-module $cM$ is *holonomic* if $cM=0$ or
$ dim Char (cM)=dim_CC X. $
]

Finite-dimensionality cannot serve as a finiteness condition even for modules over $A_1$. Suppose that $V$ were a nonzero finite-dimensional $A_1$-module. The trace of a commutator vanishes, so
$ op("tr") ([partial,x])=0 $
The Weyl relation $[partial,x]=1$ identifies this commutator with $id_V$. Hence
$ 0=op("tr") ([partial,x])=op("tr") (id_V)=dim V>0 $
which is impossible. Thus every nonzero $A_1$-module is infinite-dimensional over $CC$. Holonomicity measures geometric size through the characteristic variety. The modules $CC[x_1,...,x_n]$ and $delta_0$ are infinite-dimensional vector spaces whose characteristic varieties have the minimal possible dimension $n$. Two separate steps take us from this dimension count to conormal geometry. Involutivity together with the minimal dimension makes $Char (cM)$ a conic Lagrangian subvariety of $T^* X$; the classification of such subvarieties then writes it as a finite union of closures of conormal bundles of smooth locally closed subvarieties. Only the second step produces the strata. Consequently one can choose a Whitney stratification $cal(S)$ such that
$ Char (cM) subset.eq union_(S in cal(S)) overline(T_S^* X). $
The stratification is not extra structure carried by $cM$; it is a geometric decomposition chosen so that the system has a uniform local type along each piece. Tangent directions to a stratum are then non-characteristic, while the characteristic directions are confined to the transverse conormal geometry. This is the geometric input behind constructibility; see @HTT2008[Thm. 2.3.1 and §4.6].

#prop(title: "Holonomic modules form a finite-length abelian category", label: <prop:holonomic-finite-length>)[
Submodules, quotients, and extensions of holonomic $DX(X)$-modules are holonomic. Moreover, every holonomic module has finite length.
]

#proof[
The characteristic-variety formula for a short exact sequence (@prop:characteristic-exact-sequence) identifies the characteristic variety of the middle term with the union of those of the two ends. If the middle term is holonomic, every nonzero submodule and quotient has characteristic dimension at most $n$ and, by Bernstein's inequality, at least $n$; hence both are holonomic. The converse for extensions follows from the same union formula.

Finite length follows from the additivity of characteristic cycles in short exact sequences, which bounds the length of any chain of submodules. We take it from @HTT2008[Prop. 3.1.2 and Thm. 2.2.3].
]
#def(title: "Coherent and holonomic derived categories", label: <def:holonomic-derived-categories>)[
Write $Mod_"hol" (DX(X))$ for the full subcategory of $Mod(DX(X))$ consisting of holonomic modules. Set
$ Dbcoh(DX(X)):=lr({cM^bullet in Db(Mod(DX(X))) mid(bar.v) cohsh(j,cM^bullet) " is coherent for every " j}) $
and
$ Dbhol(DX(X)):=lr({cM^bullet in Dbcoh(DX(X)) mid(bar.v) cohsh(j,cM^bullet) in Mod_"hol" (DX(X)) " for every " j}) $
]
Choose a Whitney stratification adapted to $Char (cM)$. The Cauchy--Kowalevski--Kashiwara theorem gives local constancy of solution cohomology along its strata, while characteristic-dimension estimates give the support and costalk bounds of the middle-perverse $t$-structure. These external results imply the following theorem.


#thm(title: "Holonomic systems have perverse solution complexes", label: <thm:holonomic-solutions-perverse>)[
Let $X$ be a smooth complex variety of dimension $n$ and let $cM$ be a holonomic $DX(X)$-module. After analytification, both $Sol_X (cM)$ and $DR_X (cM)$ have constructible cohomology. Moreover,
$ shift(Sol_X (cM),n) quad "and" quad DR_X (cM) $
are perverse sheaves.
]

The analytic statement is @HTT2008[Thms. 4.6.3 and 4.6.6]. For an algebraic holonomic module, algebraic constructibility of the analytified solution complex is @HTT2008[§4.7]. The normalising shift is by the complex dimension $n$, so a local system on a smooth complex $n$-fold occurs as $shift(cL,n)$ in perverse degree zero.


// #rmrk(title: "The sheaf-side cotangent invariant")[
// The constructible stratification appearing here can be taken to be the one determined by $Char (cM)$. The sheaf-theoretic counterpart of the characteristic variety is the microsupport $SS (K)$, which records the cotangent directions across which the local cohomology of $K$ can change; a local system has microsupport the zero section, while a point-supported sheaf has the whole cotangent fibre. For a coherent analytic differential module the two invariants agree,
// $ Char (cN)=SS (RsHom_(DX(X^"an")) (cN,cO_(X^"an"))), $
// so the characteristic directions of $cM$ are exactly the singular propagation directions of $Sol_X (cM)$. We use this only as an interpretation; see @KashiwaraSchapira1990[Thm. 11.3.3] and @HTT2008[Thm. 4.4.5].
// ]

Holonomicity gives constructible perverse solution complexes. Recovering the differential module from its solution complex requires the regularity condition introduced below.

== Extension and operations <sec:solution-singularities-extension>

Let
$ j:Delta^*:=Delta-{0} into Delta. $
For a local system $cL_T$ on $Delta^*$, the calculations of @exmp:curve-intermediate-extension give distinct lower, upper, and intermediate extensions across $0$. After the perverse shift, the intermediate extension
$ midext (shift(cL_T,1)) $
is the unique extension with no nonzero subobject or quotient supported at the puncture; see @def:intermediate-extension and @BBD1982[§2.1].

This ambiguity already occurs in the Euler family. The equations
$ z u'=0 quad "and" quad z u'=-u $
have solution local systems generated by $1$ and $z^(-1)$ on $CC^times$. Multiplication by $z$ identifies these local systems, but only the first generator extends holomorphically across $0$. The common local system therefore does not determine the singular extension.

More generally, restriction to an open stratum forgets complexes supported on its boundary. A perverse sheaf contains both its shifted local system on a dense smooth stratum and the extension data attaching boundary-supported subquotients to it. The intermediate extension is the case with no independent boundary contribution.

The Euler modules exhibit the same ambiguity algebraically. On $U=bb(A)^1-{0}$, the modules $M_partial$ and $M_0$ become isomorphic because $x$ is invertible there. Both restrict to the trivial connection and therefore have the same trivial solution local system. On the whole affine line they are different. The inclusion of left ideals $A_1 (x partial) subset.eq A_1 partial$ gives a surjection
$ M_0->M_partial. $
Its kernel is
$ (A_1 partial) /( A_1 x partial) iso A_1 / (A_1 x)=delta_0, $
where the isomorphism sends the class of $Q$ to the class of $Q partial$; injectivity again uses that $A_1$ has no zero divisors. Hence
$ 0->delta_0->M_0->M_partial->0. $
Thus $M_0$ contains an independent submodule supported at the origin, even though its restriction to $U$ is the same nonsingular system as $M_partial$.
=== Operations for differential modules <sec:localization-algebraic-d-modules>
The proof of Riemann--Hilbert uses differential inverse image, direct image, duality, and external products. We describe their geometric effect and take their transfer-bimodule constructions from @HTT2008[§§1.3--1.5]. 

The easiest operation is change of variables. Suppose a scalar equation on a $z$-space is pulled back along $z=f (w)$. If $v (w):=u (f (w))$, the chain rule rewrites derivatives with respect to $z$ in terms of derivatives with respect to $w$. For the Euler equation and $z=w^m$,
$ z (d u)/(d z)=alpha u $
becomes
$ w ( d v)/(d w)=m alpha v. $
This is the elementary model for the differential inverse image $dpull(f)$. For a general morphism $f:X->Y$, the derived construction performs the same change of variables simultaneously on functions, vector fields, and relations.

For an embedding, inverse image must also account for derivatives normal to the subvariety. If an equation in coordinates $(x,y)$ contains $partial_y u$, then setting $y=0$ does not determine what happens to the normal derivative. The non-characteristic condition ensures that the equation controls these normal directions.

For $f:X->Y$, the direct image $dint(f)$ accounts for derivatives tangent to the fibres and retains the cohomology produced by eliminating them. For $a:bb(A)^1->{*}$, and up to the normalizing shift, the direct image of $cO_(bb(A)^1) iso M_partial$ is computed by
$ [CC[x] xto(partial) CC[x]]. $
The derivative is surjective on $CC[x]$ and has kernel $CC$, so this complex has one nonzero cohomology group. On $U=bb(A)^1-{0}$ the corresponding complex is
$ [CC[x,x^(-1)] xto(partial) CC[x,x^(-1)]]. $
Its kernel is again $CC$, but its cokernel is one-dimensional, generated by the class of $x^(-1)$. This residue class agrees with the sheaf-side group $H^1 (CC^times,cL_T) iso coker (T-id_V)$ for trivial monodromy. Its occurrence in a second degree requires the direct image to be derived.

Note that these are not the pullback and pushforward of the underlying sheaves. Transfer bimodules adjust the source and target differential-operator actions before the derived operation is taken; see @HTT2008[§§1.3--1.5].


In one variable, differential duality is modelled by the formal-adjoint rules
$ partial^*=-partial, quad x^*=x. $
For
$cM=A_1 \/( A_1 (partial-a)), $
the adjoint relation gives
$A_1 \/ (A_1 (partial+a)). $
Its generator satisfies $partial e'=-a e'$, so a section $f e'$ is horizontal precisely when $f'=a f$, the solution equation of the original module. For a general differential module, duality is defined by derived $Hom$ and the canonical bundle rather than by applying formal adjoints to a chosen presentation.


Write
$ omega_X:=Omeg(X)^n, quad n=dim_CC X, $
for the sheaf of top forms. Derived $sHom$ into $DX(X)$ produces a right differential module, and tensoring with $omega_X^(-1)$ converts it back to a left one.

#def(title: "Differential duality", label: <def:dmodule-duality>)[
For $cM^bullet in Dbcoh(DX(X))$ set
$ Dual_(cal(D),X) (cM^bullet):=shift(RsHom_(DX(X)) (cM^bullet,DX(X)) times.o_(cO_X) omega_X^(-1),n). $
]

The shift by $n$ is the dimension normalisation compatible with the normalised de Rham complex.

#thm(title: "Differential duality on holonomic complexes", label: <thm:dmodule-duality-holonomic>)[
For every $cM^bullet in Dbcoh(DX(X))$, the biduality morphism
$ cM^bullet -> Dual_(cal(D),X) (Dual_(cal(D),X) (cM^bullet)) $
is an isomorphism. Differential duality preserves $Dbhol(DX(X))$. If $cM in Mod_"hol" (DX(X))$, then $Dual_(cal(D),X) (cM)$ is concentrated in degree $0$, and differential duality restricts to an exact contravariant equivalence between $Mod_"hol" (DX(X))$ and its opposite category.
]

Biduality on coherent complexes is @HTT2008[Prop. 2.6.5]. The assertions for holonomic modules and holonomic complexes are @HTT2008[Cor. 2.6.8(iv) and Prop. 3.2.1]. See @HTT2008[Def. 2.6.1] for the definition of differential duality.


Finally, if $cM$ is a system in variables on $X$ and $cN$ a system in independent variables on $Y$, their external product $cM ⊠ cN$ is the system on $X times Y$ in which both sets of equations hold independently. For example, the equations
$ (partial_x-lambda)u=0, quad (partial_y-mu)u=0 $
have solutions $u (x,y)=c exp (lambda x+mu y)$. This simple product construction will later let us compare two systems at the same point by restricting from $X times X$ to the diagonal.

We do not develop a separate six-functor formalism for differential modules. The models above explain the operations that are actually used later; the Riemann--Hilbert chapter will state their precise compatibility with the six operations already constructed for sheaves.

===  Closed and open extensions

The first singular case is a closed embedding. A differential module supported on the smaller variety still contains normal derivatives. The point module introduced above is the smallest example:
$ delta_0=A_1 / A_1 x $
Let $e$ denote the class of $1$. Then $x e=0$. Commuting $x$ past successive powers of $partial$ gives
$ x partial^m e=-m partial^(m-1) e $
for every $m>=1$. If $partial^m e=0$ for some $m$ then multiplication by $x$ gives $partial^(m-1)e=0$. Repeating the argument would give $e=0$, contradicting the choice of the cyclic generator. Thus every $partial^m e$ is nonzero, and the relation $x e=0$ forces an infinite tower of derivatives normal to the point.

Concretely, if $i_0:{0} into bb(A)^1$ then the one-dimensional differential module $CC$ on the point has direct image
$ dint(i_0) (CC) iso delta_0 $
The commutator determines the entire normal derivative tower from the single generator $e$. Kashiwara's equivalence says that this ambient module still contains exactly the information of a differential module intrinsic to the closed subvariety.

#thm(title: "Kashiwara equivalence for a closed embedding", label: <thm:kashiwara-equivalence-closed-embedding>)[
Let $i:Z into X$ be a closed embedding of smooth complex varieties. The direct-image functor for differential modules induces an equivalence between coherent left $DX(Z)$-modules and coherent left $DX(X)$-modules whose set-theoretic support is contained in $Z$. The equivalence restricts to holonomic modules.
]

See @HTT2008[Thm. 1.6.1].


The general open case has the same boundary question. Let $j:bb(A)^1-{0} into bb(A)^1$ and take the trivial connection $cE=cO_(bb(A)^1-{0})$. The upper differential extension is the localization
$ dint(j) (cE) iso cO_(bb(A)^1)[x^(-1)] $
with the usual derivative action. It allows algebraic sections on the punctured line to have poles at the missing point. The regular module
$ cO_(bb(A)^1) iso M_partial $
sits inside this localization and is the minimal extension of the trivial connection: it extends the same generic system without adding an independent point-supported submodule or quotient. The module $M_0$ above is another extension of the same generic connection, but its exact sequence with $delta_0$ shows precisely why it is not minimal.

In general, for an affine locally closed embedding $j:U into X$ there are two holonomic extensions. The upper one is the direct image $dint(j) (cE)$. The lower one is obtained from it by conjugating with differential duality,
$ j_!^(Dop) cE:=Dual_(cal(D),X) (dint(j) (Dual_(cal(D),U) (cE))) $
and there is a canonical morphism from the lower extension to the upper one; see @HTT2008[§3.2]. The two are the differential-module counterparts of $lsh(j)$ and $Rpush(j)$, and their roles parallel the two extremal sheaf extensions. The upper extension has no nonzero *submodule* supported entirely on the boundary, although it may have a boundary-supported quotient; the lower extension has no nonzero *quotient* supported entirely on the boundary, although it may have a boundary-supported submodule. Differential-module duality exchanges these two behaviours. The minimal extension is the common part selected by the canonical map: its image has neither kind of independent boundary contribution.

// The affine hypothesis ensures that, for holonomic modules, both derived extensions are concentrated in degree zero, so the canonical morphism lives in the abelian category of holonomic modules and has an ordinary image; this is the observation opening @HTT2008[§3.4], which uses the holonomicity statement @HTT2008[Thm. 3.2.3] and the canonical morphism @HTT2008[Thm. 3.2.16]. We continue to treat the transfer-bimodule construction of the two extremal functors as a black box; what matters here is this boundary behaviour and the resulting image.

#prop(title: "Minimal extension: characterization", label: <prop:d-minimal-extension-characterization>)[
Let $j:U into X$ be an affine locally closed embedding of smooth varieties and let $cE$ be a finite-rank integrable connection on $U$. There is a holonomic extension, denoted $j_(!*)^(Dop) cE$, such that
+ $rest(j_(!*)^(Dop) cE,U) iso cE$;
+ it has no nonzero submodule supported on $overline(U)-U$;
+ it has no nonzero quotient supported on $overline(U)-U$.
These conditions characterize the extension uniquely.
]

#proof[
Define $j_(!*)^(Dop) cE$ as the image of the canonical morphism $j_!^(Dop) cE -> dint(j) (cE)$. The symbol $j_(!*)^(Dop)$ is ours, chosen to run parallel to $midext$ on the sheaf side; @HTT2008[Def. 3.4.1] writes this module as $cal(L) (U,cE)$. Because $j$ is affine, both extremal extensions are concentrated in degree $0$ and may therefore be regarded as holonomic modules; this is the observation opening @HTT2008[§3.4]. The canonical morphism between them is supplied by @HTT2008[Theorem 3.2.16]. The adjunctions for these direct images show that a module supported on $overline(U)-U$ has no nonzero morphism into the upper extension and receives no nonzero morphism from the lower extension. Hence the image has neither a boundary-supported submodule nor a boundary-supported quotient.

Conversely, let $cN$ be another extension with these two vanishing properties. Adjunction gives maps $j_!^(Dop) cE -> cN$ and $cN -> dint(j) (cE)$ whose composite is the canonical map. The kernel of the second map is supported on the boundary and is therefore zero. The first map consequently factors through $j_(!*)^(Dop) cE$. The resulting morphism to $cN$ restricts to the identity on $U$; its kernel and cokernel are supported on the boundary and therefore vanish. Thus the extension is unique. This is the construction of @HTT2008[Def. 3.4.1]; the simple case and its classification are @HTT2008[Thm. 3.4.2].
]

Both $midext$ and $j_(!*)^(Dop)$ are characterized by the absence of nonzero boundary-supported subobjects and quotients in their respective abelian categories. 
=== Dévissage by support <sec:holonomic-devissage>

Every holonomic module has finite length, so arguments preserved by short exact sequences reduce to simple holonomic modules. By @HTT2008[Theorem 3.4.2], every simple holonomic module is a minimal extension
$ j_(!*)^(Dop) cE $
of a simple integrable connection $cE$ on a smooth affine locally closed subvariety $j:U into X$.

More generally, let $cM$ be holonomic with irreducible support $Y$. After replacing $Y$ by a smooth affine dense subset $U$, the generic part of $cM$ is an integrable connection $cE$; this is the generic-connection step of @HTT2008[Proposition 3.1.6], applied on the smooth support through Kashiwara's equivalence. Adjunction gives morphisms
$ j_!^(Dop) cE->cM->dint(j) (cE) $
whose composite is the canonical morphism from the lower extension to the upper extension. Its image is $j_(!*)^(Dop) cE$, so the minimal extension occurs as a subquotient of $cM$. The kernels and cokernels of these morphisms restrict to zero on $U$ and are therefore supported on the lower-dimensional boundary $Y-U$. Stratifying that boundary and applying Kashiwara's equivalence gives induction on the dimension of the support.

For a bounded holonomic complex, canonical truncation triangles first reduce the argument to its cohomology modules. Finite length and the support reduction above then give the algebraic dévissage used in the next chapter. Neither the composition series nor the stratification is canonical, and no direct-sum decomposition is asserted.

== Regularity<sec:regularity-and-rh-class>

Holonomicity bounds the singular cotangent directions of a differential module, whereas regularity controls the growth of its solutions near those singularities. On a punctured curve this is a local growth condition; for a nonproper algebraic variety it must also hold at the boundary of a compactification.


A *meromorphic* function near a puncture is holomorphic away from the puncture and may have a pole at the puncture. A meromorphic connection is a connection whose coefficient matrix is meromorphic in this sense. A change of basis
$ Y=G (z) V, quad G (z) in op("GL")_r, $
with $G$ meromorphic and invertible is called a *meromorphic gauge transformation*: it changes the matrix used to write the system without changing the underlying meromorphic connection.

On a punctured curve, *moderate growth* means, roughly, polynomial growth in the inverse distance to the puncture: on every sufficiently small sector one asks for constants $C>0$ and $N>=0$ such that a local branch satisfies
$ abs (u (z))<=C abs (z)^(-N) $
near $0$. A meromorphic connection is regular singular when its local multivalued solutions have this controlled growth. Equivalently, after a meromorphic change of basis, its system can be written
$ v' (z)=A (z)/z v (z) $
with $A (z)$ holomorphic at the puncture; see @HTT2008[Thm. 5.1.4 and §5.1.2].

Why is such a condition necessary? On a punctured disc, the function $exp (1/z)$ is holomorphic and nonvanishing, so the change of basis $u=exp (1/z)v$ is a legitimate holomorphic gauge transformation on $Delta^*$. It analytically identifies a rank-one exponential connection there with the trivial connection, and both therefore have the same trivial local system on the punctured disc. But this change of basis is not meromorphic across $0$: $exp (1/z)$ has an essential singularity. Along the positive real direction it grows faster than every power of $1/abs (z)$, so it violates the moderate-growth bound, while in other sectors it may decay rapidly. Thus the holomorphic gauge transformation that erases the distinction on $Delta^*$ is not an allowable meromorphic extension through the singular point. Ordinary local-system data do not retain this sectorial behaviour. The missing information is the beginning of Stokes data; the classical constructible-sheaf target is not designed to retain it. Compare @HTT2008[Example 5.1.24].


For a nonproper algebraic variety, regularity is also imposed at the boundary of a smooth compactification. Regard $bb(P)^1$ as $bb(A)^1$ with the additional point $infinity$, and put $w=1/x$ near that point. The equation
$ u'=u $
becomes
$ (d)/(d w) u=-u/w^2 $
The second-order pole at $w=0$ makes the connection irregular at infinity, although it has no singularity on $bb(A)^1$; see @HTT2008[§5.3 and Ch. 6].



Deligne's regular-singular Riemann--Hilbert theorem gives an equivalence
$ "regular algebraic integrable connections on " X arrow.l.r.long "finite-rank local systems on " X^"an" $
This supplies the smooth-stratum case of the correspondence. @chap:riemann-hilbert treats extensions and derived gluing across lower-dimensional strata; see @HTT2008[Thm. 5.3.8 and Cor. 5.3.10].

#def(title: "Regular holonomic module categories", label: <def:regular-holonomic-categories>)[
A holonomic $DX(X)$-module is *regular* if every simple composition factor is the minimal extension of a regular integrable connection on a smooth locally closed subvariety whose inclusion is affine; see @HTT2008[Def. 6.1.1].

Write $Mod_"rh" (DX(X))$ for the full subcategory of $Mod_"hol" (DX(X))$ consisting of regular holonomic modules, and set
$ Dbrh(DX(X)):=lr({cM^bullet in Dbhol(DX(X)) mid(bar.v) cohsh(j,cM^bullet) in Mod_"rh" (DX(X)) " for every " j}) $
]

The differential direct- and inverse-image functors introduced above preserve regular holonomic complexes; see @HTT2008[Theorem 6.1.5(ii)].

#cor(title: "Differential duality preserves regularity", label: <cor:dmodule-duality-regular>)[
Differential duality preserves $Dbrh(DX(X))$ and restricts to an exact contravariant equivalence between $Mod_"rh" (DX(X))$ and its opposite category.
]

This is @HTT2008[Theorem 6.1.5(i)], together with @thm:dmodule-duality-holonomic.

The category $Dbrh(DX(X))$ is the source of the algebraic Riemann--Hilbert correspondence; see @HTT2008[Theorem 7.2.2]. In the next chapter we identify its de Rham complexes with algebraically constructible complexes on $X^"an"$, and finally (hooray!) prove the theorem.

