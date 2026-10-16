#import "../template/template.typ": *
#import "../template/macros.typ": *

#heading(level: 1, numbering: none, outlined: true)[Introduction] <chap:introduction>

This work is an introduction to the Riemann–Hilbert correspondence, with an emphasis on clarity and on understanding each of the ideas needed to reach it.
But before we plunge into the thick of it, we shall begin with the simplest case that illustrates the phenomenon the Riemann--Hilbert correspondence seeks to capture - our beloved linear algebra. For vector spaces $V,W$ and a linear map $T: V -> W$
the equation$T(v)=w$ for $w in W$, asks us to find a vector $v in V$ that is mapped to $w$. If $w=0$, the set of solutions is the kernel $ker T$, and in general a solution exists when $w$ lies in the image of $T$. If $v_0$ is one solution, then all solutions are of the form $v_0+ker T.$
The kernel thus describes the freedom of choice among solutions, while the quotient space $W \/(im T)$ describes a complementary phenomenon. The class of $w$ in this space vanishes precisely when $w$ lies in the image of $T$, that is, precisely when the equation has a solution. A nonzero class indicates that there is no $v$ for which $T(v)=w$, and in this sense one may say that it ‘measures’ the obstruction to solving the equation.

An almost immediate observation is that the same problem can be described in two ways. One may give the map $T$ itself, for example by means of a matrix, and one may instead give, for every $w in W$, the set of solutions ${v in V bar.v T(v)=w} $

The family of solution sets for all $w in W$ determines $T$ completely: the pair $(v,w)$ belongs to the graph of $T$ precisely when $v$ is a solution of the equation $T(v)=w$. The homogeneous solution space is only the fibre over $0$; it describes the kernel, but does not determine how $T$ acts outside it. For this reason, the “solution side” will not refer below merely to the homogeneous solution space, but to its full structure: how solutions are determined by local data, how they vary and continue, and which obstructions may prevent them from existing.

A linear differential equation is a linear problem of the same kind, except that the unknown is a function and the linear map includes differentiation. An ordinary linear differential equation of order $m$ is an equation of the form

$
a_m(z) u^((m))(z)+dots+a_1(z)u'(z)+a_0(z)u(z)=f(z),
$

where the functions $a_0,...,a_m$ are given and the unknown is $u$. The operator

$
a_m(z) dif^m/(dif z^m)
+dots+
a_1(z) dif/(dif z)
+a_0(z)
$

is a linear map between suitable spaces of functions, and so the equation may be written briefly as $P u=f$. As before, the homogeneous solutions are the elements of $ker P$, and the inability to solve $P u=f$ is expressed by the fact that $f$ does not lie in the image of $P$.

A linear system of ordinary differential equations is a system of the form

$
Y'(z)=A(z)Y(z)+b(z),
$

where $Y(z)$ is a vector of unknown functions, $A(z)$ is a given matrix and $b(z)$ is a given vector. The system is called homogeneous when $b=0$. Every higher-order linear scalar equation can be written as such a system by means of the state vector

$
Y=(u,u',...,u^((m-1)))
$

The passage from one equation to a system therefore makes it possible to formulate the problem by means of linear algebra that varies from point to point.

Near an ordinary point, the existence-and-uniqueness theorem states that every initial value $Y(z_0)=v$ determines a unique solution. The equation therefore determines linear transition maps that carry initial values from point to point, and may in turn be recovered from their infinitesimal behaviour. In this sense, the passage from an equation to its solutions is a direct development of the linear-algebraic picture: a single linear map is replaced by a linear rule that varies along the space, and the action of a matrix is replaced by the transport of vectors between points.

Here, however, phenomena appear that do not occur in linear algebra, which acts on fixed and complete spaces (in the sense that they are not fragmented). First, the solutions are local in a genuine sense. Let $U$ be a domain on which $A$ is holomorphic, and write

$
op("Sol")(U)=
{Y: U -> CC^n bar.v Y'=A Y}
$

for the solution space of the homogeneous system on $U$. If $U' subset.eq U$, the restriction of a solution from $U$ to $U'$ is again a solution: the values of the function are already defined on the smaller domain, and differentiation commutes with restriction. In the opposite direction, new values must be found outside $U'$, and this may be impossible if enlarging the domain reaches a singular point of the equation. For example, the equation with polynomial coefficients

$
(1-z)u'-u=0
$

has, on a small neighbourhood of $0$, the solution$u(z)=1/(1-z).
$

This solution does not continue to a holomorphic function on a neighbourhood containing $1$, where the coefficient of the derivative vanishes. If such an extension existed, it could of course be restricted back to the original solution; the problem is that the extension need not exist. Restriction is therefore automatic, whereas extension is not.

Solutions that agree on overlaps glue to a unique solution on their union, because holomorphicity and the equation $Y'=A Y$ are both local conditions. Restriction and gluing are therefore not artificial additions to the equation, but a translation of the fact that a differential equation is checked point by point. A single space of global solutions does not retain this information, and so the solutions must be recorded on every local domain. As we shall see in @chap:sheaves, the structure that organizes such local information is called a sheaf.

Existence and uniqueness also allow a local solution to be continued along a path by repeatedly solving on overlapping discs; uniqueness makes the successive solutions agree on the overlaps. Continuation along a path is thus not a new global operation, but a finite repetition of solving local problems and gluing their results.

Second, a local solution may change when it is continued along a path. Even if every small neighbourhood has the same number of linearly independent solutions, continuation around a closed path may return a different linear combination of the solutions with which we began. This is the phenomenon of monodromy, which we shall discuss at length below. It is not visible in the solution space at a single point, but only when one remembers how the solution spaces at different points are identified along paths. On a domain without singularities one obtains in this way a sheaf that looks locally like a constant vector space, but may twist globally. Such a sheaf is called a local system.

It is now clear why the kernel of the operator as an abstract vector space is insufficient. Near every ordinary point, a system of size $n$ produces an $n$-dimensional solution space. If we retained only the dimension or the isomorphism type of this space, almost all systems of size $n$ would look identical. The information that distinguishes them lies instead in the way the solutions are transported and continued along the space.

Here an additional condition appears that does not occur in one variable: progress in different directions must be consistent. Computing the solution first in one direction and then in another should agree, as one would expect, with computing it in the reverse order. When this compatibility condition holds, the system again describes linear transport along paths. In one variable there are no different directions to compare, and so this difficulty does not appear.

So far we have assumed that the system is nonsingular. If the matrix $A(z)$ is not defined at a certain point, or if the leading coefficient of a higher-order equation vanishes, a singularity may appear—a neighbourhood containing the problematic point in which the function behaves unusually. One may still solve the equation outside the singular set and continue solutions there along paths, but the information on the nonsingular domain does not necessarily determine what happens on the removed set. Two systems may produce the same local system away from the singularity, and nevertheless behave differently when one tries to continue them through it.

One example displays both phenomena at once. On a punctured disc around the origin, consider the equation

$
u'=lambda/z u
$

On a small simply connected domain that does not contain the origin, one may choose a branch of $log z$, and then every solution is of the form

$
u(z)=c exp(lambda log z)
$

When the solution is continued once around the origin, the value of $log z$ changes by $2 pi i$, and therefore the solution is multiplied by $e^(2 pi i lambda)$. In every small disc the solution space is still one-dimensional, but the circuit remembers an additional linear datum that is not visible inside a single disc, and this is how continuation of local solutions produces monodromy.

Even when $lambda$ is an integer and the monodromy is trivial, restoring the origin remains a separate problem. For $lambda=0$ the solutions are constant and therefore continue holomorphically to the origin. For $lambda=-1$ the solutions are $c/z$: on the punctured disc they form a one-dimensional local system isomorphic to that of the constant solutions, but no nonzero solution continues holomorphically to $0$. Hence the solutions away from the singularity, even together with their monodromy, do not determine by themselves what is retained when the point is restored. One must also include information about what is allowed to occur at the point itself and about the way this information is connected to the surrounding solutions.

The problem is not limited to isolated points. In a singular space, or in a system whose singularities extend along subspaces, different points may have different local geometry. We therefore divide the space into finitely many smooth pieces, called strata, so that along each stratum the local type remains uniform. The information is constructible when on every stratum it varies as a finite-dimensional local system and changes occur only in passing between strata. Monodromy may still occur along loops within a stratum; the requirement is only that no new local type appears at every point. We shall treat this notion at the end of @chap:sheaves.

A constructible object may also contain information supported on lower-dimensional strata and maps connecting it to the surrounding local systems. These are precisely the data that were missing when the origin was restored to the punctured disc.

Suppose the space is divided into an open part $U$, on which the system is nonsingular, and a closed part $Z$, on which the singularities are concentrated. The same local system on $U$ may be extended to the whole space in different ways, distinguished by the information supported on $Z$ and by the way it is connected to the surrounding solutions. This creates the need for operations that restrict information, extend it across the boundary, or extract the contribution supported on the closed part. The intermediate extension selects an extension that does not artificially add a subobject or quotient object supported only on the boundary. These operations will be developed in @chap:verdier-duality, and the intermediate extension will return in @chap:perverse-sheaves.

Even the sheaf of homogeneous solutions still does not retain all the necessary information. Consider on the complex line the two equations

$
u'=0,
quad
z u'=0.
$

They have the same homogeneous holomorphic solutions—the constant functions. The behaviour of the inhomogeneous equations, however, is different. Every holomorphic function $f$ has a local antiderivative, and therefore the equation $u'=f$ is locally solvable. By contrast, the equation

$
z u'=f
$

has no holomorphic solution near the origin when $f(0)!=0$. The homogeneous solution space does not distinguish the operators, but the obstruction to solving them distinguishes them immediately.

This is again the distinction from linear algebra between a kernel and the failure to lie in the image. To retain both together, one does not keep a single solution space, but records the operator as an arrow

$
cO arrow.r.long^P cO
$

and retains both its kernel and the quotient of the space on the right by its image. In a system of several equations, relations among the equations may also appear, followed by relations among those relations. The information thus arranges itself into a chain of linear maps. Complexes and homological algebra are the language that makes it possible to treat such a chain as a single object. The derived category makes it possible to compare different presentations of the same system without erasing the solutions, obstructions and relations that appear in the different degrees.

The algebraic foundations of this construction will be given in @chap:homological-algebra and @chap:derived-categories, and its sheaf-theoretic version will be developed in @chap:sheaf-cohomology. We shall return to it in @chap:solution-narrative for the solution complex of a differential system.

The passage to complexes is also important for understanding duality. In linear algebra, passage to the dual space reverses maps and exchanges kernels with appropriate quotient spaces. When the information is spread over a space, one must also distinguish between information visible near a point and information supported around it, and between arbitrary sections and sections with restricted support. Verdier duality extends linear duality while retaining location, support and local topology. It will be developed in @chap:verdier-duality.

Duality and constructibility also create a problem of degrees. On a smooth stratum of complex dimension $d$, a local system occupies its natural position after a shift by $d$, whereas information supported at a point requires no shift. The solution is to fold, or recenter, the scale of degrees according to the dimension of the stratum. The middle choice is arranged so that Verdier duality preserves the resulting degree zero. Its objects are called perverse sheaves: constructible complexes whose degrees have been adapted to the dimensions of the strata on which their information lies. They are also apparently not perverse, but that is a matter of personal taste. We shall discuss them in @chap:perverse-sheaves.

On the equation side too, a passage to a more intrinsic presentation is required. A list of operators is not an internal description of a system, since one may replace an equation by a combination of other equations, add an equation that follows from the existing ones, or differentiate a relation and obtain a new relation. All these differential consequences must be included in the system from the outset. To achieve this, the list of equations is replaced by a module over the algebra of differential operators. This is a $cal(D)$-module. It retains the unknowns, the equations and all the relations that follow from them without depending on a particular list of generators. @chap:solution-narrative will construct $cal(D)$-modules from systems of equations, and in the same context introduce the derived solution complexes.

Not every $cal(D)$-module produces finite and controlled information on the solution side. Holonomicity is the finiteness condition that ensures that its solutions, obstructions and singular information form a constructible complex. Regularity further excludes irregular singularities, near which solutions may grow or decay differently in different sectors around the same point. For regular holonomic systems, monodromy, contributions supported on the singular strata and the maps connecting them to the smooth information constitute a complete description. These conditions will be developed in @chap:solution-narrative.

We can now state the idea of the Riemann--Hilbert correspondence. On one side lies the system of equations, organized as a module of differential operators and including all its differential consequences and relations. On the other lies the solution data organized according to its position in the space: local systems on the smooth strata, monodromy along loops, contributions supported on the singular strata, local obstructions to solving, and the gluing maps between all the parts. For regular holonomic systems, the two descriptions determine one another.

The equivalence between the two descriptions, and the compatibility of the structures and operations built along the way, will be proved in @chap:riemann-hilbert.

The route to this correspondence determines the structure of the text. Sheaf theory carries this language to spaces and records local solutions, gluing and continuation. Constructibility imposes finite geometric control, while the operations developed in @chap:verdier-duality describe restriction, extension, support and duality. Perverse sheaves (@chap:perverse-sheaves) organize information carried by strata of different dimensions. Finally, $cal(D)$-modules, holonomicity and regularity provide the equation side on which the correspondence is defined. To make this introduction as accessible and clear as possible, I have also included two substantial appendices containing the necessary background in homological algebra (@chap:homological-algebra) and derived categories (@chap:derived-categories), so that readers unfamiliar with these subjects can follow the material without requiring prior knowledge of them. The examples woven through these appendices form the basis for those that appear later in the thesis. The appendices may therefore be regarded as Chapters $-2$ and $-1$ of the thesis, if the Introduction is taken to be Chapter $0$. They are best read together as a single unit.


// This route will be illustrated by a small family of examples that recur throughout the text. The two-term map $V -> W$ will isolate the difference between solutions and obstructions. The interval and the circle will gradually add gluing and global topology. The circle and the punctured disc will display monodromy and continuation around a singularity. The torus and the elliptic curve will be used to examine cohomology, duality and dimension shifts. A singular point, a crossing and a node will show why branches, information supported on the singularity and extension data must be retained separately. Finally, explicit differential equations will return these geometric phenomena to the operator side.

When an adapted finite cell decomposition is available, a constructible complex can be represented by finite-dimensional data on the cells and computed by linear algebra. Sections @sec:cellular-sheaves and @sec:cellular-calculations develop this description, and @sec:finite-cellular-models applies it to constructible de Rham and solution complexes.

