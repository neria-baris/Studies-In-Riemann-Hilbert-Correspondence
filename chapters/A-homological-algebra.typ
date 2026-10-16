
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

//make sure that I defined homology and cohomology as functors.

= Basic Homological Algebra (Briefly) <chap:homological-algebra> 
== Motivation <sec:homological-algebra-introduction> 
This chapter is a fast and motivating tour through (some of) the main stops of homological algebra. The basic idea of homological algebra is to distil from the theory of $R$-modules the categorical structure that allows us to discuss kernels, images, quotients, and the relations between them without relying on elements. This allows us to recognise phenomena from module theory, such as the First Isomorphism Theorem, in other mathematical settings that satisfy the conditions required for this interface to apply. The same distillation also allows us to pass from a single map to a sequence of consecutive maps, to examine what happens when the image of one map does not exhaust the kernel of the next, and to identify the nature of this failure. This chapter is fundamentally introductory, we generally have refrained from giving full proofs and have preferred, whenever possible, to explain matters relatively concretely using $R$-modules. The standard references for the material of this chapter are @Weibel1994 and @rotman; for the purely categorical background we follow @awodey and @borceux. I also relied extensively on Yuhang Wei's notes, both as a guide to these references and as a source from which I learned much of the material. The notes are based on and substantially expand Kobi Kremnitzer's Oxford C2.2 Homological Algebra lectures; see @KremnitzerWei2023.

Let us start with the setup of a group, a subgroup, and its quotient. Take the group of integers $ZZ$ and its subgroup of even integers, represented by the multiplication-by-$2$ map from $ZZ$ to $ZZ$. The quotient is $ZZ\/2ZZ$. We can display the three groups and the two maps as $ 0 -> ZZ ->^(dot 2) ZZ -> ZZ\/2ZZ -> 0 $ The zero on the left records that multiplication by $2$ has kernel $0$. The map $ZZ->ZZ\/2ZZ$ is onto, while its kernel is the subgroup $2ZZ$, exactly the image of the preceding multiplication-by-$2$ map. Thus the sequence records in one diagram the subgroup $2ZZ subset.eq ZZ$ and the quotient $ZZ\/2ZZ$ obtained from it.

Now tensor the sequence with $ZZ\/2ZZ$. Each copy of $ZZ$ becomes $ZZ\/2ZZ$, and multiplication by $2$ becomes the zero map because $2=0$ in $ZZ\/2ZZ$. The resulting sequence begins $ 0 -> ZZ\/2ZZ ->^(0) ZZ\/2ZZ $ Before tensoring, the first map had kernel $0$; afterwards its kernel is the whole module $ZZ\/2ZZ$ and it is no longer injective, so tensoring has created elements in the kernel that did not come from the kernel of the original map. The rest of the chapter develops a systematic way to describe and record this kind of failure.

This example allows us to survey the main stages of our journey. First, we need a language in which to discuss kernels, cokernels, and images. Second, we need to discuss consecutive maps and describe what happens when a functor applied to them fails to preserve all their properties. In particular, we need a way to measure maps for which not everything that goes out is what came in: “leaks” and excesses. This will lead us to distinguish between different kinds of objects—those on which the functors behave properly—and to develop a strategy that uses them to measure these gaps precisely and degree by degree, ultimately producing “derived functors”. We conclude the chapter with two explicit examples of such functors, which will be used below.


Throughout this chapter, $R$ denotes a ring (with $1$, not necessarily commutative), $RMod$ the category of left $R$-modules, and $ModR$ the category of right $R$-modules. When $R$ is a field $k$ these are vector spaces; when $R = ZZ$ they are abelian groups, so $ZMod = Ab$.

// Let us make the problem concrete before introducing the general language. Consider the maps $ZZ xto(dot 2) ZZ -> ZZ\/2ZZ$. The first sends an integer $n$ to $2n$, so its image is the subgroup of even integers. The second remembers only the parity of an integer: even integers go to $0$, odd integers to $1$.

// Now perform the coefficient reduction modulo $2$ that will reappear later in the chapter as tensor. Each copy of $ZZ$ becomes $ZZ\/2ZZ$. Multiplication by $2$ then becomes the zero map, while the second map becomes the identity: $ ZZ\/2ZZ xto(dot 0) ZZ\/2ZZ xto(id) ZZ\/2ZZ $

// Before the reduction, multiplication by $2$ sent only $0$ to $0$. Afterwards, every element is sent to $0$. The operation has therefore changed the way the first group sits inside the second and has lost information that was visible in the original map. The purpose of the chapter is to develop a language that can locate such losses and, eventually, measure them. We will return to this calculation at the end of the chapter.

// Let us make this abstract discussion concrete using an example. Start with the fundamental setup of a group, a subgroup, and their quotient. Take the group of integers $ZZ$, and its subgroup of even integers (represented by the "multiply by 2" map from $ZZ$ to $ZZ$). The quotient is simply $ZZ\/2$. We can display this diagrammatically as $ 0 -> ZZ ->^(dot 2) ZZ -> ZZ\/2 -> 0 $ where the zeros at the ends indicate that the first map is one-to-one (hence its kernel is $0$) and the second map covers the entire quotient group (hence $ZZ\/2$ is its kernel and the image is $0$).

// Tensoring everything with $ZZ\/2$, which reduces our groups modulo 2, transforms our diagram into

// $ 0 -> ZZ\/2 ->^(dot 2) ZZ\/2 -> ZZ\/2 -> 0 $

//  The map that previously sent $n$ to $2n$ now sends every element
// to zero, because $2=0$ modulo $2$:
// $ZZ\/2ZZ xto(0) ZZ\/2ZZ$. Now, both elements of $ZZ\/2ZZ$ are sent to zero. The operation has therefore changed an inclusion into a map that loses all of its input.

// This is the phenomenon that will organize the chapter. We shall develop a language for describing when algebraic constructions preserve relations between modules, and for measuring the information that appears when they do not. At the end of the chapter we will return to this calculation and identify the group that measures the failure explicitly.




== Abelian Categories <sec:abelian-categories>
Which categorical structure retains the kernel, quotient and exact-sequence arguments familiar from modules?
#def(title: "Abelian Category")[
   An *abelian category*  is a category $cA$ such that:
  #enum(
    numbering: n => [(A#n)],
    spacing: 0.6em,
    [each $Hom_cA (X, Y)$ is an abelian group and composition is bilinear (_we can add and
     subtract parallel maps_);],
    [there is a zero object, and any two objects have a biproduct $X ds Y$ that is
     simultaneously their product and coproduct (_finite direct sums exist_);],
    [every morphism has a kernel and a cokernel (_we can solve $f(x) = 0$ and pass to
     quotients_);],
    [the canonical map $ coim (f) := Coker (ker f) -> Ker (coker f) =: im (f) $ is an
     isomorphism for every $f$ (_the first isomorphism theorem holds_).],
  )
  
]
A category satisfying only the first axiom is called an Ab-*enriched category*; a category that also satisfies the second axiom is called an *additive category*.

The non-trivial axiom is the fourth. In short, in any setting with kernels and cokernels a map $f colon X -> Y$ has two a priori different "images": the coimage $Coker (ker f)$, a quotient of $X$, and the image $Ker (coker f)$, a subobject of $Y$. In $RMod$ these are $X\/Ker f$ and ${f(x)} subset.eq Y$, and the comparison map between them is exactly the isomorphism $X\/Ker f iso im f$ of the First Isomorphism Theorem. So (A4) is nothing more than an arrow-only version of that theorem.

In other words, in an abelian category every morphism factors canonically as an epimorphism onto its image followed by a monomorphism, $X ->> im (f) into Y$.

The following theorem guarantees that, in some cases, we can understand this abstract definition in terms of $R$-Mod.
#thm(title: "Freyd-Mitchell Embedding Theorem")[
   Every small abelian category $cA$ admits an exact, fully faithful functor $cA -> RMod$ into the modules over some ring $R$, embedding $cA$ as a full subcategory.
]
A proof is given in @Weibel1994[p. 25].

Modules therefore provide a concrete model for the constructions below, in finite diagram arguments.

The relevant structure-preserving functors are the following:
#def(title: "Additive Functor")[
   A functor $F colon cC -> cD$ is an
   *additive functor* if each induced map $Hom(X, Y) -> Hom(F X, F Y)$ is a group homomorphism, such that $ F(f + g) = F(f) + F(g) $ and $F(0) = 0$.
]

// It is important to note that in an abelian category a finite product and the corresponding finite coproduct coincide: Since we could take every pair $(x,y) in X times Y$, split it into two different coordinates — $(x,0),(0,y)$ and by addition restore the original pair. Our additive functor preserves this simple operation.
In an $Ab$-enriched category with a zero object, every finite product or finite coproduct, when it exists, has the canonical structure of a biproduct. In particular, every abelian category has finite biproducts, written $X ds Y$. As shown in @borceux[Proposition 1.2.4] Additive functors preserve finite biproducts. 


== Exact Sequences <sec:exact-sequences>

The First Isomorphism Theorem gives the model to keep in mind. For $R$-modules, a map records both a submodule through its image and a quotient through its kernel. Exact sequences isolate the point at which these two descriptions meet.

#def(title: "Exact Sequence")[
A sequence $A ->(f) B ->(g) C$ is *exact at $B$* if $im f=Ker g$.
]

In $RMod$, this has a direct meaning: the elements of $B$ killed by $g$ are exactly those that arrive from $A$. Thus $g compose f=0$, and if $g (b)=0$, then $b=f (a)$ for some $a in A$.

#def(title: "Short Exact Sequence")[
A sequence $0 -> A ->(i) B ->(q) C -> 0$ is a *short exact sequence* if it is exact at $A$, $B$, and $C$.
]

For modules, this is precisely the familiar submodule--quotient situation. The map $i$ identifies $A$ with the submodule $i (A) subset.eq B$, exactness gives $i (A)=Ker q$, and $q$ is surjective. The First Isomorphism Theorem therefore gives $C iso B\/i (A)$. The sequence from the introduction, $0 -> ZZ xto(dot 2) ZZ -> ZZ\/2ZZ -> 0$, records the inclusion $2ZZ subset.eq ZZ$ together with the corresponding quotient.

There is still a question about how the two end modules are assembled inside $B$. The simplest case is when they separate completely.

#def(title: "Split short exact sequence")[
A short exact sequence $0 -> A xto(i) B xto(q) C -> 0$ is *split* if $B iso A ds C$ compatibly with $i$ and $q$.
]

A splitting can be recognized without first constructing the direct-sum isomorphism. A *retraction* is a map $r colon B -> A$ with $r compose i=id_A$; a *section* is a map $s colon C -> B$ with $q compose s=id_C$. In module language, a section chooses one representative in $B$ for every class in the quotient $C$, and does so $R$-linearly.

#lem(title: "Splitting Lemma")[
For a short exact sequence $0 -> A xto(i) B xto(q) C -> 0$, the following are equivalent:
#enum(
  [the sequence is split;],
  [there is a retraction $r colon B -> A$ with $r compose i=id_A$;],
  [there is a section $s colon C -> B$ with $q compose s=id_C$.]
)
]
<lem:splitting-lemma>

#proof[
Suppose a section $s$ is given. For every $b in B$, the difference $b-s (q (b))$ lies in $Ker q=i (A)$, so there is a unique $a in A$ with $b=i (a)+s (q (b))$. This decomposition is unique, and therefore $(a,c) |-> i (a)+s (c)$ gives an isomorphism $A ds C iso B$. A split sequence clearly supplies both a section and a retraction, and the argument from a retraction is dual. See @splitting-lemma-doc and @rotman[Corollary 2.24].
]


#exmp(title: "A nonsplit extension")[
Consider the short exact sequence
$0 -> ZZ\/2ZZ
  xto(iota) ZZ\/4ZZ
  xto(pi) ZZ\/2ZZ
  -> 0,
$
where $iota([a])=[2a]$ and $pi([b])=[b] mod 2$.

The sequence does not split. Indeed, a section
$s:ZZ\/2ZZ -> ZZ\/4ZZ$
would have to send $[1]$ to an element mapping to $[1]$ modulo $2$ and annihilated by multiplication by $2$, which does not exist.

Thus the two end modules do not determine the middle module: the split extension has middle term
$(ZZ\/2ZZ) plus.o (ZZ\/2ZZ)$,
whereas this extension has middle term $ZZ\/4ZZ$.
]
<ex:nonsplit-z4-extension>



We now ask what happens to a short exact sequence when an algebraic functor is applied to it.

== Exact Functors <sec:exact-functors>

Split sequences cause no difficulty: an additive functor preserves finite biproducts, so it carries $B iso A ds C$ to $F (B) iso F (A) ds F (C)$. The interesting case is therefore a general short exact sequence $0 -> A xto(i) B xto(q) C -> 0$.

For $Hom_R (M,-)$, the kernel part survives. A map $M->B$ whose composite with $q$ is zero takes its values in $Ker q=i (A)$ and therefore factors through $A$. What may fail is the final surjectivity: a map $M->C$ need not admit a *lift* $M->B$.

For $Hom_R (-,M)$, the arrows reverse. A map $B->M$ that vanishes on $i (A)$ depends only on the coset in $B\/i (A) iso C$, so it factors through $C$. What may fail is that a map $A->M$ need not extend to $B$.

Tensor product behaves in the opposite direction. Since $C iso B\/i (A)$, tensoring preserves the quotient and gives an exact sequence $A times.o_R N -> B times.o_R N -> C times.o_R N -> 0$. The map at the left need not remain injective.

#def(title: "Exact functor")[
An additive functor $F$ is *right exact* if $A -> B -> C -> 0$ exact implies $F (A) -> F (B) -> F (C) -> 0$ exact. It is *left exact* if $0 -> A -> B -> C$ exact implies $0 -> F (A) -> F (B) -> F (C)$ exact. It is *exact* if it is both.
]

#lem(title: "One-sided exactness of Hom and tensor product")[
For every object $M$ of an abelian category, $Hom (M,-)$ is left exact and $Hom (-,M)$ is contravariantly left exact. If $N$ is a left $R$-module, $- times.o_R N colon ModR -> Ab$ is right exact; dually, if $M$ is a right $R$-module, $M times.o_R - colon RMod -> Ab$ is right exact.
]
<lem:exactness-of-homensor>

There is a structural reason for the opposite behaviour of tensor product and $Hom$. For this paragraph, suppose that $R$ is commutative. A homomorphism $F colon M times.o_R N -> P$ can be read by fixing $m in M$: it gives the homomorphism $n |-> F (m times.o n)$ from $N$ to $P$. Conversely, a map $G colon M -> Hom_R (N,P)$ defines $F (m times.o n):=G (m) (n)$. Thus $Hom_R (M times.o_R N,P) iso Hom_R (M,Hom_R (N,P))$.

#def(title: "Adjoint functors")[
Functors $F colon cC -> cD$ and $G colon cD -> cC$ are *adjoint*, written $F tack.l G$, if there are natural isomorphisms $Hom_cD (F (A),B) iso Hom_cC (A,G (B))$.
]
<def:adjoint-functors>

The tensor--Hom correspondence is therefore an adjunction in the sense of the preceding definition: $ - times.o_R N tack.l Hom_R (N,-) $ In module language, a homomorphism $M times.o_R N -> P$ is equivalent to a homomorphism $M -> Hom_R (N,P)$, obtained by fixing the first input. #footnote[This adjunction is the commutative-ring form. For a noncommutative ring the same construction requires explicit right-, left-, and bimodule hypotheses, so we will not use the unqualified formula in that setting.]

This adjunction explains the one-sided exactness established above. Left adjoints preserve cokernels, while right adjoints preserve kernels. Hence tensor product preserves the quotient $B\/i (A)$, whereas $Hom_R (N,-)$ preserves the kernel of $B -> C$. The opening sequence shows that the opposite halves need not be preserved. See @KremnitzerWei2023 for the module-theoretic presentation and @awodey[Chapter 9] for the categorical preservation properties of adjoints.

Return to $0 -> ZZ xto(dot 2) ZZ -> ZZ\/2ZZ -> 0$. Applying $Hom_ZZ (ZZ\/2ZZ,-)$ fails at the final term because $id_(ZZ\/2ZZ)$ has no lift to $ZZ$. Tensoring with $ZZ\/2ZZ$ turns multiplication by $2$ into the zero map and creates a new kernel.

// #lem(title: "One-sided exactness of Hom and tensor product")[
// For every object $M$ of an abelian category, $Hom(M,-)$ is left exact and $Hom(-,M)$ is contravariantly left exact. If $N$ is a left $R$-module, the functor $- times.o_R N colon ModR->Ab$ is right exact; dually, if $M$ is a right $R$-module, $M times.o_R - colon RMod->Ab$ is right exact.
// ]
// <lem:exactness-of-homensor>

// Both halves, together with the standard counterexamples showing that neither can be improved, are treated in @rotman[Chapter 2].

// For $Hom_R (M,-)$, the preserved part of exactness has a direct interpretation. Given an exact sequence
// $
// 0 -> A -> B -> C,
// $
// a morphism $M -> B$ whose composite with $B -> C$ is zero factors uniquely through $A = ker(B -> C)$. Hence
// $
// 0 -> Hom_R (M,A) -> Hom_R (M,B) -> Hom_R (M,C)
// $
// is exact. What may fail is surjectivity at the right: a morphism $M -> C$ need not lift through the epimorphism $B -> C$.

// Contravariantly, applying $Hom_R (-,M)$ to
// $
// A -> B -> C -> 0
// $
// reverses the arrows and gives an exact sequence
// $
// 0 -> Hom_R (C,M) -> Hom_R (B,M) -> Hom_R (A,M).
// $
// Here the possible failure is again at the final term: a morphism $A -> M$ need not extend to $B$.

// Tensor product has the opposite one-sided behaviour. If
// $
// A -> B -> C -> 0
// $
// is exact, then
// $
// A times.o_R N -> B times.o_R N -> C times.o_R N -> 0
// $
// is exact. Thus tensor product preserves quotients and cokernels, but it may fail to preserve the injection at the left of a short exact sequence.

// Conceptually, these directions are forced by adjunction. Tensor product is a left adjoint and therefore preserves colimits, in particular cokernels. The relevant Hom functors are right adjoints and therefore preserve limits, in particular kernels - — see @awodey[Chapter 9] for the general statement, and @rotman[Proposition 2.57] for the associativity isomorphism underlying the tensor–Hom adjunction in the module case. This explains which half of exactness is preserved, but not why the other half must be preserved as well—and in general it is not.
// //rephrase it

// The opening sequence already displays this failure. Applying $Hom_ZZ(ZZ\/2,-)$ to
// $ 0 -> ZZ arrow.r.long^2 ZZ -> ZZ\/2ZZ -> 0 $
// gives
// $ 0 -> 0 -> 0 -> ZZ\/2ZZ $
// which is not exact at the final term: the identity map of $ZZ\/2ZZ$ does not lift to a map $ZZ\/2ZZ -> ZZ$.
// We already saw (@sec:homological-algebra-introduction - check) that
// tensoring the same sequence with $ZZ\/2ZZ$ breaks exactness, since the first map is not injective. Thus Hom fails by losing lifts on the right, while tensor product fails by creating a kernel on the left.

// The half-exactness above is not a coincidence; it flows from the 
// adjunction of $Hom(N,-)$ and $(- times.o N)$ [ref]. Because left adjoints preserve colimits and right adjoints preserve limits, the tensor preserves quotient (hence, right exact) while the $Hom$ perserves kernels and submodules (hence, left-exact). Their exactness defect is pre-ordained by their place in the adjunction.

== Chain Complexes and Homology <sec:chain-complexes-homology>
We ended the last section with a problem - while short exact sequences appear to be a crucial part in the grammar \/ interface that abelian categories describe, our very useful functors break it. However, consecutive maps still compose to zero, and hence, instead of $ im d_(n+1) = Ker d_n$, we get $im d_(n+1) subset.eq Ker d_n$; some information is killed without coming from the incoming map.

Before we can construct a new exact sequence that incorporates this defect, we first need to formally measure the failure of exactness. An obvious solution, which fits well the cokernel-kernel attributes of Abelian categories, is to simply use the quotient $Ker d_n \/ im d_(n+1)$, to which we will give a fancy name.


#def(title: "Chain Complex")[
  A *chain complex* $C_bullet$ in an abelian category $cA$ is a family of objects
  ${C_n}_(n in ZZ)$ with morphisms (*differentials*) $d_n colon C_n -> C_(n-1)$ such that 
  consecutive differentials compose to zero:
  $
    d_(n-1) compose d_n = 0, wide "written" wide d^2 = 0 .
  $
  The *$n$-cycles* are $Z_n = Ker d_n$;
   the *$n$-boundaries* are $B_n = im d_(n+1)$. The
  condition $d^2 = 0$ says exactly $B_n subset.eq Z_n$. 
]
This lays the foundations to our measurment tool:
#def(title: "Homology")[
  The *$n$-th homology* is the quotient
  $ H_n (C) = Z_n \/ B_n = (Ker d_n) / (im d_(n+1))$
]

At degree $n$, the two differentials determine $B_n subset.eq Z_n subset.eq C_n$, and homology takes the quotient of the cycles by the boundaries.


#align(center)[
  #diagram(
    spacing: (1.0cm, 1.2cm),

    node((0, 0.5), $underbrace(B_n, = im d_(n+1))$),
    node((2, 0.5), $underbrace(Z_n, = Ker d_n)$),
    node((4, 0), $C_n$),
    node((4, 1.2), $H_n (C)$),

    edge((0, 0.5), (2, 0.5), "hook->"),
    edge((2, 0.5), (4, 0), "hook->"),
    edge((2, 0.5), (4, 1.2), "->>"),
  )

]


Two cycles determine the same class in $H_n (C)$ exactly when their difference lies in $B_n$. Consequently, $H_n (C)=0$ precisely when the complex is exact at $C_n$. This gives the measurement of the difference between an incoming image and the following kernel.

Homology arose in topology from the same construction. For an oriented simplicial complex, let $C_n$ be the free abelian group generated by its oriented $n$-simplices. The differential sends a simplex to the alternating sum of its faces. For an oriented triangle, $d_2 [v_0,v_1,v_2]=[v_1,v_2]-[v_0,v_2]+[v_0,v_1]$, while $d_1 [v_i,v_j]=v_j-v_i$. Applying $d_1$ once more gives $(v_2-v_1)-(v_2-v_0)+(v_1-v_0)=0$. Each vertex occurs twice with opposite signs, which gives the geometric model for $d^2=0$. The construction of simplicial and singular homology is developed in @hatcher[Chapter 2].

In this setting, an $n$-cycle is a chain with zero boundary, while an $n$-boundary already occurs as the boundary of a chain one degree higher. The quotient $Z_n\/B_n$ therefore retains the classes of cycles that remain after boundaries have been identified with zero.

#exmp(title: "The multiplication-by-two map as a differential")[
  A cellular calculation for $RR P^2$ gives the chain complex $0 -> ZZ xto(dot 2) ZZ xto(0) ZZ -> 0$, with the three copies of $ZZ$ in degrees $2$, $1$, and $0$; See @hatcher[Chapter 2].

  At degree $1$, we have $Z_1=Ker(0)=ZZ$ and $B_1=im(dot 2)=2ZZ$. Hence $H_1 (RR P^2;ZZ)=ZZ\/2ZZ$.

  The multiplication by $2$ map from the opening example has now appeared as a differential. If this complex is tensored with $ZZ\/2ZZ$, that differential becomes zero, exactly as in the opening calculation.
]



#def(title: "Chain Map")[
  A *chain map* $f colon C_bullet -> D_bullet$ between two chain complexes is a family of morphisms 
  $f_n colon C_n -> D_n$ that commute with the differentials. That is, for every $n$:
  $
    d^D_n compose f_n = f_(n-1) compose d^C_n quad ("or simply" d f = f d) .
  $
  
]

  Visually, this means the following ladder diagram commutes:
  
    #diagram(
      spacing: (2.2cm, 1.5cm),
      node((0, 0), $dots.c$), node((1, 0), $C_(n+1)$), node((2, 0), $C_n$), node((3, 0), $C_(n-1)$), node((4, 0), $dots.c$),
      node((0, 1), $dots.c$), node((1, 1), $D_(n+1)$), node((2, 1), $D_n$), node((3, 1), $D_(n-1)$), node((4, 1), $dots.c$),
      
      edge((0, 0), (1, 0), "->"),
      edge((1, 0), (2, 0), "->", label: $d^C_(n+1)$),
      edge((2, 0), (3, 0), "->", label: $d^C_n$),
      edge((3, 0), (4, 0), "->"),
      
      edge((0, 1), (1, 1), "->"),
      edge((1, 1), (2, 1), "->", label: $d^D_(n+1)$),
      edge((2, 1), (3, 1), "->", label: $d^D_n$),
      edge((3, 1), (4, 1), "->"),
      
      edge((1, 0), (1, 1), "->", label: $f_(n+1)$, label-side: right),
      edge((2, 0), (2, 1), "->", label: $f_n$, label-side: right),
      edge((3, 0), (3, 1), "->", label: $f_(n-1)$, label-side: right),
    )

These objects and chain maps form the category $C (cA)$, which is abelian whenever $cA$ is abelian; see @rotman[Proposition 5.100].
 
Because a chain map respects the differentials, it carries cycles to cycles and boundaries to boundaries. Consequently, every chain map $f colon C_bullet -> D_bullet$ induces a morphism $H_n (f) colon H_n (C) -> H_n (D)$. Identities and compositions are preserved, so for every $n$ the construction $C_bullet |-> H_n (C)$ defines a functor from the category of chain complexes to $cA$.

#def(title: "chain homotopic")[
  Chain maps $f, g colon C_bullet -> D_bullet$ are *chain homotopic*, written $f tilde.eq g$, if
  there exist maps $s_n colon C_n -> D_(n+1)$ with
  $
    f - g = d compose s + s compose d .
  $
] 

Chain homotopy is an equivalence relation on the chain maps $C_bullet -> D_bullet$, and it is compatible with composition; see @Weibel1994[Section 1.4]. Thus, quotienting the morphisms in $C(cA)$ by chain homotopy produces the homotopy category $K(cA)$, which we will construct later, in @sec:homotopy-category.

The importance of this notion is that homology cannot distinguish between chain-homotopic maps.
//
#lem(title: "Chain homotopy and homology")[
  If $f, g colon C_bullet -> D_bullet$ are chain homotopic, then they induce the same map on homology:
  $
    H_n (f) = H_n (g)
  $
  for every $n in ZZ$.
]

#proof[
If $c$ is a cycle, then $(f-g)(c)=d(s(c))$ is a boundary. Hence $f$ and $g$ determine the same class on every homology object.  See @Weibel1994[Lemma 1.4.5]
]

=== Cochain complexes and cohomology <sec:cohomology>

The cohomological convention reverses the grading of a chain complex. A *cochain complex* $A^bullet$ is a family of objects with differentials $d_A^n colon A^n -> A^(n+1)$ satisfying $d_A^(n+1) compose d_A^n=0$. Write $B^n:=im d_A^(n-1)$ and $Z^n:=Ker d_A^n$. Then $B^n subset.eq Z^n subset.eq A^n$, and the *$n$-th cohomology* object is $H^n (A^bullet):=Z^n\/B^n=Ker d_A^n\/im d_A^(n-1)$. Thus cohomology measures the failure of the complex to be exact at $A^n$.

When a cochain complex has only two nonzero terms in degrees $0$ and $1$, we abbreviate $0 -> A xto(d) B -> 0$ by $[A xto(d) B]$. If the terms occur in different degrees, we state their placement explicitly.

A morphism of cochain complexes $f colon A^bullet -> B^bullet$ is a family $f^n colon A^n -> B^n$ satisfying $d_B^n compose f^n=f^(n+1) compose d_A^n$. It induces morphisms $H^n (f) colon H^n (A^bullet) -> H^n (B^bullet)$, so each $H^n$ is a functor from cochain complexes to $cA$. Two cochain maps $f,g colon A^bullet -> B^bullet$ are *cochain-homotopic* if there are morphisms $h^n colon A^n -> B^(n-1)$ such that $f-g=d_B compose h+h compose d_A$. Cochain-homotopic maps induce the same morphism on cohomology, by the same calculation as for chain homotopy.

For complexes of vector spaces, cochains have a concrete interpretation as linear tests on chains. A cocycle is a test that vanishes on boundaries, while two cocycles differing by a coboundary define the same cohomology class. The standard construction from singular cochains is described in @hatcher[Chapter 3]. The smallest cellular example already shows how the cochain differential is formed.

#exmp(title: "The oriented interval and the cochain differential", label: <ex:oriented-interval-cochain>)[
Let an interval have vertices $v_0,v_1$ and one edge $e$ oriented from $v_0$ to $v_1$. Over a field $k$, its cellular chain groups are $C_1=k e$ and $C_0=k v_0 ds k v_1$, with boundary $d_1 (e)=v_1-v_0$. Applying $Hom_k (-,k)$ gives $C^0:=Hom_k (C_0,k)$ and $C^1:=Hom_k (C_1,k)$, with $d^0 (phi):=phi compose d_1$. If $phi (v_0)=a_0$ and $phi (v_1)=a_1$, then $d^0 (a_0,a_1)=a_1-a_0$. The cochain differential therefore reads the terminal value minus the initial value.
$ C_1 = k e -->^(d_0) c_0=k v_0 ds k v_1 $
$ C^1=Hom_k (C_1,k) <--^(d_0) C^0=Hom_k (C_0,k) $
]

#exmp(title: "Cellular cohomology of the circle and the torus")[
Let $k$ be a field. Give $S^1$ its standard cell decomposition with one vertex $v$ and one edge $e$, whose two endpoints are attached to $v$. The terminal-minus-initial calculation of @ex:oriented-interval-cochain becomes $a-a=0$ after the endpoints are identified. Hence the cellular cochain complex is
$0 -> k arrow.r.long^0 k -> 0$
in degrees $0$ and $1$, and
$
H^0(S^1;k) iso k,
quad
H^1(S^1;k) iso k.
$

Thus $H^0(S^1; k) tilde.equiv k$ reflects connectedness, while $H^1(S^1; k) tilde.equiv k$ gives one independent degree-one cohomology class.

Give the torus $T^2$ its standard cell decomposition with one vertex, two edges $a,b$, and one two-cell. Its cellular cochain complex is $0 -> k arrow.r.long^0 k^2 arrow.r.long^0 k -> 0$ in degrees $0,1,2$. Both differentials vanish: the edges begin and end at the same vertex, and the boundary word $a b a^(-1) b^(-1)$ contains each edge with opposite signs. Hence $H^0 (T^2;k) iso k$, $H^1 (T^2;k) iso k^2$, and $H^2 (T^2;k) iso k$.

]<ex:cellular-circle-torus>


=== Double complexes and Hom complexes <sec:total-hom-complexes>
The examples above have one cohomological index. A second index appears when a construction depends simultaneously on two complexes. 

#def(title: "Total complex")[
A *first-quadrant double cochain complex* is a family $C^(p,q)$, indexed by $p,q >= 0$, with differentials $d_h:C^(p,q) -> C^(p+1,q)$ and $d_v:C^(p,q) -> C^(p,q+1)$ satisfying $d_h^2=0$, $d_v^2=0$, and $d_h compose d_v=d_v compose d_h$. Its *total complex* is defined by $Tot^n (C):=bds_(p+q=n) C^(p,q)$, with $d_"Tot" (x):=d_h (x)+(-1)^p d_v (x)$ for $x in C^(p,q)$.
]
//TODO: יותר מדי אינסופי כרגע, לא?
#align(center)[
  #diagram(
    spacing: (1.7cm, 1.2cm),

    node((0, 0), $C^(0,2)$),
    node((1, 0), $C^(1,2)$),
    node((2, 0), $C^(2,2)$),
    node((3, 0), $dots.c$),
    node((0,-1), $dots.v$),

    node((0, 1), $C^(0,1)$),
    node((1, 1), $C^(1,1)$),
    node((2, 1), $C^(2,1)$),
    node((3, 1), $dots.c$),
    node((1,-1), $dots.v$),

    node((0, 2), $C^(0,0)$),
    node((1, 2), $C^(1,0)$),
    node((2, 2), $C^(2,0)$),
    node((3, 2), $dots.c$),
    node((2,-1), $dots.v$),

    edge((0, 0), (1, 0), "->"),
    edge((1, 0), (2, 0), "->"),
    edge((2, 0), (3, 0), "->"),
    edge((0,0),(0,-1),"->"),
    edge((1,0),(1,-1),"->"),
    edge((2,0),(2,-1),"->"),

    edge((0, 1), (1, 1), "->"),
    edge((1, 1), (2, 1), "->"),
    edge((2, 1), (3, 1), "->"),

    edge((0, 2), (1, 2), "->"),
    edge((1, 2), (2, 2), "->"),
    edge((2, 2), (3, 2), "->"),

    edge((0, 2), (0, 1), "->"),
    edge((1, 2), (1, 1), "->"),
    edge((2, 2), (2, 1), "->"),

    edge((0, 1), (0, 0), "->"),
    edge((1, 1), (1, 0), "->"),
    edge((2, 1), (2, 0), "->"),
  )
]

The horizontal differential moves one column to the right and the vertical differential moves one row upward. The terms with $p+q=n$ lie on one diagonal of this grid, and $Tot^n (C)$ collects exactly that diagonal.

#prop(title: "The total differential squares to zero")[
The differential of the total complex (@def:total-complex) satisfies $d_"Tot" compose d_"Tot"=0$.
]

#proof[
For $x in C^(p,q)$, $d_"Tot"^2 (x)=d_h^2 (x)+(-1)^p d_h d_v (x)+(-1)^(p+1) d_v d_h (x)+d_v^2 (x)=0$. The first and last terms vanish because the rows and columns are complexes, while the middle terms cancel because the two differentials commute.
]


#def(title: "Hom complex")[
For cochain complexes $K^bullet,L^bullet$ in an abelian category $cA$, define
$Hom_cA^n (K^bullet,L^bullet):=product_p Hom_cA (K^p,L^(p+n)).$
For a homogeneous family $phi=(phi^p)_p$ of degree $n$, set
$d (phi)^p:=d_L^(p+n) compose phi^p-(-1)^n phi^(p+1) compose d_K^p.$
]

The two terms are the two routes from $K^p$ to $L^(p+n+1)$.

#figure(
  diagram(
    spacing: 1.8cm,
    node((0, 0), $K^p$), node((2, 0), $K^(p+1)$),
    node((0, 1.2), $L^(p+n)$), node((2, 1.2), $L^(p+n+1)$),
    edge((0, 0), (2, 0), "->", label: $d_K^p$), edge((0, 1.2), (2, 1.2), "->", label: $d_L^(p+n)$),
    edge((0, 0), (0, 1.2), "->", label: $phi^p$, label-side: right), edge((2, 0), (2, 1.2), "->", label: $phi^(p+1)$),
  )
)


When the first argument is an object $A$ concentrated in degree $0$, the definition reduces to $Hom_cA^bullet (A,L^bullet)$, whose degree-$q$ term is $Hom_cA (A,L^q)$ and whose differential sends $phi$ to $d_L^q compose phi$. This is the form used below to compute Ext. 

#def(title: "Acyclic complexes and quasi-isomorphisms", label: none)[
A chain or cochain complex is *acyclic* if all its homology or cohomology objects vanish.

A morphism of chain or cochain complexes is a *quasi-isomorphism* if it induces isomorphisms on all homology or cohomology objects.
]<def:quasi-isomorphism>

A quasi-isomorphism means that, from the point of view of homology, $C_bullet$ and $D_bullet$ share the same information. This provides our strategy - we will replace difficult objects with quasi-isomorphic complexes made entirely of "good" objects.


#exmp(title: "Subdivision changes the complex but not its cohomology")[
Give $S^1$ a cellular decomposition with two vertices and two edges. As we saw, its cellular cochain complex is $C_"reg"^bullet=[k^2 arrow.r.long^D k^2]$, where $D(a,b)=(b-a,a-b)$. The kernel of $D$ is the diagonal copy of $k$ and its image is
${(x,-x):x in k},
$
so its cokernel is one-dimensional. Therefore
$
H^0(C_"reg"^bullet) iso k,
quad
H^1(C_"reg"^bullet) iso k.
$

Let
$C_"min"^bullet=[k arrow.r.long^0 k]$
be the minimal complex of @ex:cellular-circle-torus. Define
$ p^0(a,b)=a, quad p^1(x,y)=x+y 
$
Since
$p^1(D(a,b))=(b-a)+(a-b)=0,
$
the maps define a morphism of complexes
$p:C_"reg"^bullet -> C_"min"^bullet.
$
It induces an isomorphism from the diagonal kernel to $k$ in degree $0$ and an isomorphism
$k^2\/im(D) -> k
$
in degree $1$. Hence $p$ is a quasi-isomorphism.


However, the two complexes are not isomorphic because their terms have different dimensions.
]<ex:circle-subdivision>
Quasi-isomorphisms determine when a morphism preserves all homology objects. But how does the homology of a third complex depend on the homology of two others in a short exact sequence?

#def(title: "long exact sequence")[
  A *long exact sequence* (LES) is an exact sequence, infinite in one or both directions:
  $ dots.c -> X_(n+1) -> X_n -> X_(n-1) -> dots.c$
  meaning it is exact at every interior term.
]
Vanishing or explicit knowledge of neighbouring terms determines an unknown term, like in equations. The Snake Lemma constructs the connecting morphisms that join the separate degrees.
//  which we explain here using the concepts that the classic proof hides. 

#lem(title: "Snake Lemma")[
  Given a commutative diagram with exact rows in an abelian category:
  
    #diagram(
      spacing: (1.9cm, 1.5cm),
      node((1, 0), $A$), node((2, 0), $B$), node((3, 0), $C$), node((4, 0), $0$),
      node((0, 1), $0$), node((1, 1), $A'$), node((2, 1), $B'$), node((3, 1), $C'$),
      edge((1, 0), (2, 0), "->", label: $i$),
      edge((2, 0), (3, 0), "->", label: $p$),
      edge((3, 0), (4, 0), "->"),
      edge((0, 1), (1, 1), "->"),
      edge((1, 1), (2, 1), "->", label: $i'$, label-side: right),
      edge((2, 1), (3, 1), "->", label: $p'$, label-side: right),
      edge((1, 0), (1, 1), "->", label: $f$, label-side: right),
      edge((2, 0), (2, 1), "->", label: $g$, label-side: right),
      edge((3, 0), (3, 1), "->", label: $h$, label-side: right),
    )
  
  there is an exact sequence:
  $
    Ker f -> Ker g -> Ker h xto(partial) Coker f -> Coker g -> Coker h ,
  $
  where $partial$ is the *connecting homomorphism*.
]
#rmrk()[
  The differential $d$ is an internal operator within a single chain complex ($C_n ->^(d_(n)) C_(n-1)$). The map $partial$ is an external bridge between the homologies of two completely different complexes ($H_n (C) ->^(partial_(n)) H_(n-1)(A)$).
]

We recall the construction of $partial$. Let $c in Ker h$. Choose $b in B$ with $p(b)=c$. Commutativity gives
$p'(g(b))=h(p(b))=h(c)=0,$
so exactness of the lower row produces a unique $a' in A'$ such that $i'(a')=g(b)$. If $b$ is replaced by another lift $b+i(a)$, then $a'$ is replaced by $a'+f(a)$. Hence the class of $a'$ in $Coker f$ is independent of the chosen lift. Define
$partial(c):=[a'] in Coker f.$ 
The same argument verifies that the construction is compatible with representatives and is natural in morphisms of diagrams; see @snake-lemma-doc.

// Instead of a mechanical element chase, here is what $partial$ actually measures by breaking down the diagram. The top row $A xto(i) B xto(p) C -> 0$ represents a module $B$ projecting onto a quotient $C$. Exactness at $B$ means that anything in $B$ that gets crushed to zero in the quotient comes exactly from the image of $A$. 

// An element $c in Ker h$ is a solution to $h(x) = 0$ in the quotient module $C$. Because $c$ lives in a quotient, we want to see what happens when we lift it back to the "upstairs" system (the full module $B$) to solve the equation there.

// To track this without getting lost, we align this algebraic goal precisely with the visual layout of the diagram:
// - **Horizontal movement (Left/Right):** Moves between the "internal" source ($A$), the full module ($B$), and its quotient ($C$).
// - **Vertical movement (Top/Bottom):** Translates elements from the source system (the top row) to the target system (the bottom row); The maps $f, g, h$ are exactly these vertical translations.

// #align(center)[
//   #diagram(
//     spacing: (2cm, 1.5cm),
//     node((0, 0), $B$), node((1, 0), $C$),
//     node((0, 1), $B'$), node((1, 1), $C'$),
//     edge((0, 0), (1, 0), "->", label: $p$),
//     edge((0, 1), (1, 1), "->", label: $p'$),
//     edge((0, 0), (0, 1), "->", label: $g$, label-side: right),
//     edge((1, 0), (1, 1), "->", label: $h$, label-side: right),
//   )
// ]
// We start with $c in Ker h$. Because $C$ is a quotient of $B$, we move left to pick a representative $b in B$ such that $p(b) = c$. 
// Now we translate this $b$ **down** to the target system via $g$, getting a term $g(b) in B'$ which may be non-zero, acting as the exact obstruction to $b$ being in $ker(g)$. While $g(b)$ may be non-zero, the commutativity of the square guarantees that pushing it rightward yields $p'(g(b)) = h(p(b)) = h(c) = 0$.

// #align(center)[
//   #diagram(
//     spacing: (2cm, 1.5cm),
//     node((0, 0), $A'$), node((1, 0), $B'$), node((2, 0), $C'$),
//     edge((0, 0), (1, 0), "->", label: $i'$),
//     edge((1, 0), (2, 0), "->", label: $p'$),
//   )
// ]
// We are now in the bottom row. We have an element $g(b) in B'$ that vanishes when moved to the right ($C'$). But exactness tells us that anything vanishing on the right must come from the left. 
// So, there is a unique element $a' in A'$ such that $i'(a') = g(b)$. This $a'$ is the *obstruction* in $A'$ that explains exactly why our representative $b$ didn't cleanly map to zero under $g$.

// #align(center)[
//   #diagram(
//     spacing: (2cm, 1.5cm),
//     node((0, 0), $A$), node((1, 0), $B$),
//     node((0, 1), $A'$), node((1, 1), $B'$),
//     edge((0, 0), (1, 0), "->", label: $i$),
//     edge((0, 1), (1, 1), "->", label: $i'$),
//     edge((0, 0), (0, 1), "->", label: $f$, label-side: right),
//     edge((1, 0), (1, 1), "->", label: $g$, label-side: right),
//   )
// ]
// But $b$ was just an arbitrary choice of representative. We could have picked a different lift by moving further left into $A$. Since $im i = Ker p$, any other lift looks like $b + i(a)$ for some $a in A$. 
// If we use this new lift, we must move it down. By the left square's commutativity, our resulting obstruction in $A'$ shifts by exactly $f(a)$. The ambiguity in our obstruction is precisely the image of $f$ coming from the top-left. Therefore, the obstruction lives naturally and unambiguously in the quotient $A' \/ im f = Coker f$. 

// The connecting map $partial$ simply formalises this journey: start at $C$, lift left, push down, pull left, and mod out by the top-left.

By repeatedly applying the Snake Lemma degree-by-degree to a short exact sequence of chain complexes, we get the following theorem/

#thm(title: "Long Exact Sequence in Homology")[
  A short exact sequence of chain complexes $0 -> A_bullet -> B_bullet -> C_bullet -> 0$ induces a natural long exact sequence in homology:
  $
    dots.c -> H_n (A) -> H_n (B) -> H_n (C) xto(partial) H_(n-1) (A) -> H_(n-1) (B) -> dots.c
  $
]
The construction of the connecting morphism and the proof of naturality are given in @rotman[Theorem 6.13].

The connecting map $partial$ lowers the degree by one. If a cycle in $C_n$ fails to lift to a cycle in $B_n$ (i.e - have no source in the pre-image) its appears as a homology class in $H_(n-1)(A)$. 

Exactness lets us determine unknown terms from the adjacent maps. For example, $0 -> H_n -> 0$ implies $H_n = 0$, while $0 -> A -> H_n -> 0$ implies $H_n iso A$.

== Projective and Injective Objects<sec:projective-injective-objects>

As we just learned, SES's are the natural grammar of modules (and hence of abelian categories), but not every functor respects them. For left/right-exact functors, the missing exactness can be related to lifting through surjections or extending across injections. For instance, an element of $Hom(P,Z)$ is a morphism $f colon P -> Z$. If $h colon Y -> Z$ is surjective, saying that $f$ lies in the image of $Hom(P,Y) -> Hom(P,Z)$ means that there is some $g colon P -> Y$ such that $f = h compose g$. In simple terms, every map to the quotient can be lifted to its source.

This lifting property motivates the following definition and our strategy - to replace objects by "good enough" objects for which the relevant functor behaves better.

#def(title: "Projective Object")[
  In an abelian category $cA$, an object $P$ is *projective* if $Hom_cA (P, -)$ is exact.
]
Dually,
#def(title: "Injective Object")[
  $I$ is *injective* if the contravariant functor $Hom_cA (-, I)$ is exact.
]


Those definitions unpack into:
#prop(title: "Lifting and extension")[
  The following are equivalent characterisations.
  - $P$ is projective $arrow.l.r.double$ for every epimorphism $h colon Y onto Z$ and every
    $f colon P -> Z$, there exists (not necessarily unique) $g colon P -> Y$ with
    $f = h compose g$. This is the *lifting property*:
  
      #diagram(
        spacing: (2.6cm, 1.5cm),
        node((1, 0), $P$),
        node((0, 1), $Y$),
        node((1, 1), $Z$),
        edge((1, 0), (1, 1), "->", label: $f$),
        edge((1, 0), (0, 1), "-->", label: $exists thin g$, label-side: left),
        edge((0, 1), (1, 1), "->>", label: $h$),
      )
    
  - $I$ is injective $arrow.l.r.double$ for every monomorphism $h colon X into Y$ and every
    $f colon X -> I$, there exists $g colon Y -> I$ with $f = g compose h$. This is the
    *extension property*:

      #diagram(
        spacing: (2.2cm, 1.5cm),
        node((0, 0), $0$),
        node((1, 0), $X$),
        node((2, 0), $Y$),
        node((1, 1), $I$),
        edge((0, 0), (1, 0), "->"),
        edge((1, 0), (2, 0), "hook->", label: $h$),
        edge((1, 0), (1, 1), "->", label: $f$, label-side: right),
        edge((2, 0), (1, 1), "-->", label: $exists thin g$),
      )
    
  Moreover $P$ is projective $arrow.l.r.double$ every short exact sequence
  $0 -> A -> B -> P -> 0$ splits; dually every $0 -> I -> A -> B -> 0$ splits.
  ]


What these objects are, module-theoretically?
//Name the theroam
#thm[
  In $RMod$:
  #enum(
    numbering: "(1)",
    [*Free modules are projective*, and more precisely $P$ is projective
     $arrow.l.r.double$ $P$ is a direct summand of a free module.],
    [Consequently $RMod$ *has enough projectives*: every module $M$ admits an epimorphism $F onto M$ from a free (hence projective) module.],
  )
]
The classification of projective modules as the direct summands of free modules, and the consequences drawn below, are treated in @rotman[Chapter 3].

_Why free means projective._ Let $F$ be free on a basis ${x_i}$, let $h:Y ->> Z$ be an epimorphism, and let $f:F->Z$. For each basis element $x_i$, surjectivity of $h$ allows us to choose $y_i in Y$ with $h(y_i)=f(x_i) $. Since $F$ is free, the assignment $x_i |-> y_i$ extends uniquely to an $R$-linear map $g:F->Y$. On every basis element, $ (h compose g)(x_i)=h(y_i)=f(x_i), $ and hence $h compose g=f$ on all of $F$. Thus $F$ has the lifting property and is projective.

_Why projective implies a summand of a free module._ Every module $P$ is a quotient of some free module $F$. This means there exists a short exact sequence $0 -> Ker(h) -> F xto(h) P -> 0$. Because $P$ is projective, this sequence must split by the Splitting Lemma (@lem:splitting-lemma). A split exact sequence implies $F iso P ds Ker(h)$, hence $P$ is a direct summand of $F$.

_Why $RMod$ has enough projectives._  Since every $R$-module $M$ can be generated by some set of elements, it is canonically a quotient of the free module generated by that set.

#exmp[
  Over a field, every module (vector space) is free, hence projective; and dually also injective. 
  
  Over $ZZ$, the projective modules are exactly the free abelian groups;
  e.g. $ZZ$ is projective but $ZZ\/2$ is not (there is no lift of $id colon ZZ\/2 -> ZZ\/2$ along $ZZ onto ZZ\/2$, since $ZZ$ has no element of order $2$).
]

Injectives are subtler, but again explicit in module land.
#thm(title: "Baer's Criterion")[
  A module $M$ over $R$ is injective if and only if every $R$-module homomorphism from an ideal $I subset.eq R$ into $M$ extends to a homomorphism from $R$ into $M$. 
]

The non-trivial direction, is proved in @rotman[Theorem 3.30].

When $R$ is a Principal Ideal Domain (PID), this algebraic condition simplifies: $M$ is injective if and only if $M$ is divisible; this is @rotman[Corollary 3.35]. Furthermore, $RMod$ has enough injectives, see @Weibel1994[Proposition 2.3.10].



=== Resolutions <sec:resolutions>

A projective resolution replaces an arbitrary object by a sequence of projective objects without changing its degree-zero homology. In a module category we may choose the projectives to be free, which gives the construction a concrete interpretation in terms of generators and successive relations.

#def(title: "Projective Resolution")[
  A *projective resolution* of an object $A$ is an exact sequence:
  $
    dots.c -> P_2 xto(d_2) P_1 xto(d_1) P_0 xto(epsilon) A -> 0
  $
  where every $P_n$ is a projective object.
]
///the same definitions and thms apply on the other direction. 

When the resolution is chosen to be free, $P_0$ has a basis of generators mapping onto $A$. The kernel of $P_0 -> A$ consists of the relations among these generators. Choose generators for this kernel and let them form a basis of $P_1$; the map $P_1 -> P_0$ sends each basis vector to the relation it represents. Its kernel consists of relations among those relations, and the same construction produces $P_2$ and the subsequent terms.

// - $P_0$ provides the generators of $A$. (We map a massive free module onto $A$).
// - The map $P_0 -> A$ has a kernel, which represents the relations between the generators. 
// - $P_1$ provides the generators for these relations.
// - $P_2$ provides the relations between the relations, and so on.

// #text(fill: red)[אולי לצייר את זה, עם K]


Because the sequence is exact, the complex $P_bullet = (dots -> P_2 -> P_1 -> P_0 -> 0)$ has zero homology everywhere except at degree 0, where $H_0 (P) = P_0 \/ im d_1 iso A$. In the language of @sec:chain-complexes-homology, the complex $P_bullet$ is quasi-isomorphic to $A$. 

In order to be able to succeed in the process, the category required to fullfile one condition:

#def(title: "Enough Projectives / Injectives")[
  An abelian category has *enough projectives* if every object $M$ is a quotient of a projective object (i.e., there exists an epimorphism $P onto M$ with $P$ projective).

  Dually, it has *enough injectives* if every object can be embedded into an injective object (a monomorphism $M into I$).
]


A resolution requires making arbitrary choices. There are infinitely many ways to choose generators ($P_0$), and infinitely many ways to map relations ($P_1$). If we use these resolutions to compute invariants, won't our answers depend on our arbitrary choices?

The Fundamental Lemma of Homological Algebra guarantees that they do not.

#thm(title: "The Comparison Theorem")[
  Let $P_bullet -> A$ be a projective resolution of $A$, and let $Q_bullet -> B$ be *any* resolution of $B$ (exact sequence). Then, any morphism $f colon A -> B$ can be lifted to a chain map $f_bullet colon P_bullet -> Q_bullet$ between the resolutions:
  
  #align(center)[
    #diagram(
      spacing: (2cm, 1.5cm),
      node((0,0), $dots.c$), node((1,0), $P_1$), node((2,0), $P_0$), node((3,0), $A$), node((4,0), $0$),
      node((0,1), $dots.c$), node((1,1), $Q_1$), node((2,1), $Q_0$), node((3,1), $B$), node((4,1), $0$),
      
      edge((1,0), (2,0), "->", label: $d_1$),
      edge((2,0), (3,0), "->", label: $epsilon_A$),
      edge((3,0), (4,0), "->"),
      edge((0,0), (1,0), "->"),
      
      edge((1,1), (2,1), "->", label: $d'_1$),
      edge((2,1), (3,1), "->", label: $epsilon_B$),
      edge((3,1), (4,1), "->"),
      edge((0,1), (1,1), "->"),
      
      edge((3,0), (3,1), "->", label: $f$),
      edge((2,0), (2,1), "-->", label: $f_0$),
      edge((1,0), (1,1), "-->", label: $f_1$),
    )
  ]
  Furthermore, any two such lifts $f_bullet, g_bullet$ are *chain homotopic* ($f_bullet tilde.eq g_bullet$).
]
This is @Weibel1994[Comparison Theorem 2.26]; an equivalent formulation, with the inductive construction of the lift written out degree by degree, is @rotman[Theorem 6.16].


If we take $A = B$ and $f = id_A$, the Comparison Theorem tells us that any two projective resolutions of $A$ are chain equivalent.  
If $P_bullet->A$ and $Q_bullet->A$ are projective resolutions, the Comparison Theorem applied to $id_A$ produces chain maps $ P_bullet -> Q_bullet quad "and" quad Q_bullet -> P_bullet $ lifting the identity of $A$. Their composites also lift $id_A$, so uniqueness up to chain homotopy implies that the composites are homotopic to the corresponding identity maps. Hence $P_bullet$ and $Q_bullet$ are chain-homotopy equivalent and we can pick any projective resolution we want.


Dually, we have
#def(title: "Injective Resolution")[
   An *injective resolution* of an object $A$ is an exact sequence:
$
  0 -> A xto(eta) I^0 xto(d^0) I^1 xto(d^1) I^2 -> dots.c
$
where every $I^n$ is an injective object. 
  
]
The theorems regarding existence and uniqueness up to chain homotopy apply symmetrically to injective resolutions @Weibel1994[Section 2.3].



== Derived Functors <sec:classical-derived-functors>

We now combine these ingredients to define derived functors. Starting with a left\/right exact functor $F$, we choose a nice projective or injective resolution, apply $F$, and take homology.

The resulting functors measure the failure of $F$ to be exact. For a short exact sequence, they fit together through connecting morphisms to form a Long Exact Sequence. This is the basic construction of derived functors; its axiomatic formulation in terms of $delta$-functors is developed in @Weibel1994[Section 2.1].

 
=== The Construction of Derived Functors<sec:the-construction-of-derived-functors>

Suppose $F colon cA -> cB$ is a right-exact additive functor (such as $- times.o M$, @def:exact-functor), and the category $cA$ has enough projectives (@def:enough-projectives-injectives). We want to measure its defect on an object $A$. We construct the left derived functors of $F$ in four explicit steps; the same recipe, spelled out step by step, appears in @rotman[p. 344]:

*Step 1: Resolve.* Construct a projective resolution for $A$:
$
  dots.c -> P_2 xto(d_2) P_1 xto(d_1) P_0 xto(epsilon) A -> 0
$

*Step 2: Remove the augmentation.* Replace $A$ by $0$, obtaining
$
P_bullet colon dots.c -> P_2 xto(d_2) P_1 xto(d_1) P_0 -> 0.
$
Then $H_0(P_bullet) iso A$ and $H_n(P_bullet)=0$ for $n>0$. The object $A$ is no longer a term of this complex. The augmentation $epsilon: P_0 -> A$ extends to a chain map $epsilon: P^bullet -> A[0]$, which is a quasi-isomorphism. Thus $P^bullet$ is a projective replacement of $A[0]$.

#diagram(
spacing: (2.0cm, 1.5cm),
node((0, 0), $dots.c$), node((1, 0), $P_2$), node((2, 0), $P_1$), node((3, 0), $P_0$), node((4, 0), $0$),
node((0, 1), $dots.c$), node((1, 1), $0$), node((2, 1), $0$), node((3, 1), $A$), node((4, 1), $0$),

edge((0, 0), (1, 0), "->"),
edge((1, 0), (2, 0), "->", label: $d_2$),
edge((2, 0), (3, 0), "->", label: $d_1$),
edge((3, 0), (4, 0), "->"),

edge((0, 1), (1, 1), "->"),
edge((1, 1), (2, 1), "->"),
edge((2, 1), (3, 1), "->"),
edge((3, 1), (4, 1), "->"),

edge((1, 0), (1, 1), "->", label: $0$, label-side: right),
edge((2, 0), (2, 1), "->", label: $0$, label-side: right),
edge((3, 0), (3, 1), "->", label: $epsilon$, label-side: right),
edge((4, 0), (4, 1), "->", label: $0$, label-side: right),
)


*Step 3: Apply the Functor.* Apply the additive functor $F$ to the truncated complex:
$
  dots.c -> F(P_2) xto(F(d_2)) F(P_1) xto(F(d_1)) F(P_0) -> 0
$
Because $F$ is only right-exact, applying it to $P_bullet$ generally disrupts the exactness at higher degrees. 

*Step 4: Compute Homology.* To quantify the deviation from exactness, we take the homology of this new complex. 


#def(title: "Classical Left Derived Functor")[
Let $F colon cA -> cB$ be right exact and additive, and suppose that $cA$ has enough projectives. For $A in cA$, choose a projective resolution $P_bullet -> A$. Define
$ L_n F(A):=H_n (F(P_bullet)) $
]
and, dually - 
#def(title: "Classical Right Derived Functor")[
Let $F colon cA -> cB$ be left exact and additive, and suppose that $cA$ has enough injectives. For $A in cA$, choose an injective resolution $A->I^bullet$. Define
$ R^n F(A):=H^n (F(I^bullet)) $
]<def:classical-right-derived-functors>

#align(center)[
  #diagram(
    spacing: (1.65cm, 1.0cm),

    node((0, 1), $A$),
    node((1.7, 1), $I^bullet$),
    node((3.7, 1), $F(I^bullet)$),

    node((5.8, 0), $R^0 F(A)$),
    node((5.8, 1), $R^1 F(A)$),
    node((5.8, 2), $R^2 F(A)$),
    node((5.8, 2.5), $dots.v$),

    edge((0, 1), (1.7, 1), "-->", label: $"resolve"$),
    edge((1.7, 1), (3.7, 1), "-->", label: $"apply " F$),

    edge((3.7, 1), (5.8, 0), "-->", label: $H^0$),
    edge((3.7, 1), (5.8, 1), "-->", label: $H^1$),
    edge((3.7, 1), (5.8, 2), "-->", label: $H^2$),
  )
]

By the Comparison Theorem (@thm:the-comparison-theorem), any two projective resolutions of $A$ are chain homotopy equivalent. Since $F$ is an additive functor, it preserves chain homotopies. Chain homotopic complexes yield isomorphic homology groups. Therefore, $L_n F(A)$ is independent of the chosen projective resolution.

The construction for left-exact covariant functors uses injective resolutions and cohomological grading. In particular, $Hom_R (M,-)$ is covariant in its second variable, so applying it does not reverse the arrows.

The Comparison Theorem (@thm:the-comparison-theorem) gives independence of the chosen injective resolution up to canonical isomorphism; see also @Weibel1994[Section 2.5].

To get a Long Exact Sequence after applying $F$, we need a short exact sequence of resolutions
$ 0 -> P_A^bullet -> P_B^bullet -> P_C^bullet -> 0 $
Unfortanatley, resolving $A$, $B$, and $C$ separately does not guarantee this. The Horseshoe Lemma constructs compatible resolutions for which the sequence is exact.

#lem(title: "The Horseshoe Lemma")[
  Given a short exact sequence $0 -> A -> B -> C -> 0$ and projective resolutions $P_bullet^A$ for $A$ and $P_bullet^C$ for $C$, there exists a projective resolution $P_bullet^B$ for $B$ such that the sequence of complexes:
  $
    0 -> P_bullet^A -> P_bullet^B -> P_bullet^C -> 0
  $
  is exact. Furthermore, because $P_n^C$ is projective for every $n$, this sequence of complexes splits at every degree: $P_n^B iso P_n^A plus.o P_n^C$.
]


#align(center)[
  #diagram(
    spacing: (0.5cm, 0.55cm),

    node((1, 0), $dots.v$),
    node((2, 0), $dots.v$),
    node((3, 0), $dots.v$),

    node((0, 1), $0$),
    node((1, 1), $P_2^A$),
    node((2, 1), $P_2^B$),
    node((3, 1), $P_2^C$),
    node((4, 1), $0$),

    node((0, 2), $0$),
    node((1, 2), $P_1^A$),
    node((2, 2), $P_1^B$),
    node((3, 2), $P_1^C$),
    node((4, 2), $0$),

    node((0, 3), $0$),
    node((1, 3), $P_0^A$),
    node((2, 3), $P_0^B$),
    node((3, 3), $P_0^C$),
    node((4, 3), $0$),

    node((0, 4), $0$),
    node((1, 4), $A$),
    node((2, 4), $B$),
    node((3, 4), $C$),
    node((4, 4), $0$),

    node((1, 5), $0$),
    node((2, 5), $0$),
    node((3, 5), $0$),

    edge((1, 0), (1, 1), "->"),
    edge((2, 0), (2, 1), "->"),
    edge((3, 0), (3, 1), "->"),

    edge((0, 1), (1, 1), "->"),
    edge((1, 1), (2, 1), "->"),
    edge((2, 1), (3, 1), "->"),
    edge((3, 1), (4, 1), "->"),

    edge((0, 2), (1, 2), "->"),
    edge((1, 2), (2, 2), "->"),
    edge((2, 2), (3, 2), "->"),
    edge((3, 2), (4, 2), "->"),

    edge((0, 3), (1, 3), "->"),
    edge((1, 3), (2, 3), "->"),
    edge((2, 3), (3, 3), "->"),
    edge((3, 3), (4, 3), "->"),

    edge((0, 4), (1, 4), "->"),
    edge((1, 4), (2, 4), "->"),
    edge((2, 4), (3, 4), "->"),
    edge((3, 4), (4, 4), "->"),

    edge((1, 1), (1, 2), "->"),
    edge((2, 1), (2, 2), "->"),
    edge((3, 1), (3, 2), "->"),

    edge((1, 2), (1, 3), "->"),
    edge((2, 2), (2, 3), "->"),
    edge((3, 2), (3, 3), "->"),

    edge((1, 3), (1, 4), "->"),
    edge((2, 3), (2, 4), "->"),
    edge((3, 3), (3, 4), "->"),

    edge((1, 4), (1, 5), "->"),
    edge((2, 4), (2, 5), "->"),
    edge((3, 4), (3, 5), "->"),
  )
]

Each column is a projective resolution, and each horizontal row is short exact. Since $P_n^C$ is projective, the rows in the resolution split degree by degree. An additive functor $F$ preserves these split sequences, giving a short exact sequence of complexes $0 -> F(P_bullet^A) -> F(P_bullet^B) -> F(P_bullet^C) -> 0$. We apply the Snake Lemma (@lem:snake-lemma) to this sequence of complexes to construct the Long Exact Sequence (@def:long-exact-sequence). The resulting morphisms connects the homology groups of the three complexes into
$ dots.c -> H_n(F(P_bullet^A)) -> H_n(F(P_bullet^B)) -> H_n(F(P_bullet^C)) xto(partial) H_(n-1)(F(P_bullet^A)) -> dots.c $.
By definition these homology groups are the derived functors $L_n F(A)$, $L_n F(B)$, and $L_n F(C)$, which gives the long exact sequence of derived functors below. The construction of the resolution grid is @Weibel1994[Horseshoe Lemma 2.2.8].

#thm(title: "Long Exact Sequence of Left Derived Functors")[
  A short exact sequence $0 -> A -> B -> C -> 0$ induces a natural long exact sequence of derived functors:
  $
    dots.c -> L_2 F(C) xto(partial) L_1 F(A) -> L_1 F(B) -> L_1 F(C) \
    xto(partial) F(A) -> F(B) -> F(C) -> 0
  $
]
And, of course, a dual version exist almost verbatim.
This, together with the universality statement below, is @Weibel1994[Theorem 2.4.6 and Theorem 2.4.7].

Notice the termination of the sequence: $ F(A) -> F(B) -> F(C) -> 0 $ The map $F(A) -> F(B)$ remains non-injective.

== $Tor$, $Ext$<sec:tor-ext>
Tensor product and $Hom$ provide the two basic examples of the derived-functor construction. The derived functors $Ext$ and $Tor$ formally measure their failures of exactness. Both are treated at length in @Weibel1994[Chapter 3] and @rotman[Chapter 7].

Using the recepie from @sec:the-construction-of-derived-functors, we construct the follows.
#def(title: "The Tor Functor")[
Let $A in ModR$ and $B in RMod$. For a projective resolution $P_bullet -> A$, define
$ Tor_n^R (A,B):=H_n (P_bullet times.o_R B) $
]
See @Weibel1994[Section 3.1] for the basic computations, and @Weibel1994[Theorem 2.7.2] for the fact that the two variables may be resolved interchangeably.


The name $Tor$ originates from torsion. Apply the definition to the projective resolution
$0 -> ZZ xto(dot 2) ZZ -> ZZ\/2ZZ -> 0.
$
After deleting the augmentation and tensoring the resulting resolution complex with $ZZ\/2ZZ$, one obtains
$0 -> ZZ\/2ZZ xto(0) ZZ\/2ZZ -> 0.
$
Consequently,
$Tor_1^ZZ (ZZ\/2ZZ,ZZ\/2ZZ)
=Ker(0)
iso ZZ\/2ZZ.
$
This is the kernel created in @sec:homological-algebra-introduction when multiplication by $2$ became zero.



For a fixed left $R$-module $A$, the functor $Hom_R (A,-)$ is left exact, so its right derived functors measure the failure of the final lifting map in a short exact sequence to remain surjective.

#def(title: "The Ext Functor")[
  For a fixed $R$-module $A$, define $Ext_R^n (A,-):=R^n (Hom_R (A,-))$.
]

To compute $Ext_R^n (A,B)$, choose an injective resolution $ 0 -> B -> I^0 xto(d_I^0) I^1 xto(d_I^1) I^2 -> dots.c $ Applying $Hom_R (A,-)$ term by term gives the cochain complex $ Hom_R (A,I^0) xto(d_H^0) Hom_R (A,I^1) xto(d_H^1) Hom_R (A,I^2) -> dots.c $, where $d_H^q (phi):=d_I^q compose phi$.

At degree $n$, the two differentials determine $B_H^n subset.eq Z_H^n subset.eq Hom_R (A,I^n)$, and cohomology takes the quotient of the cocycles by the coboundaries.

#align(center)[
  #diagram(
    spacing: (1.0cm, 1.2cm),

    node((0, 0.5), $underbrace(B_H^n, = im d_H^(n-1))$),
    node((2, 0.5), $underbrace(Z_H^n, = Ker d_H^n)$),
    node((4, 0), $Hom_R (A,I^n)$),
    node((4, 1.2), $Ext_R^n (A,B)$),

    edge((0, 0.5), (2, 0.5), "hook->"),
    edge((2, 0.5), (4, 0), "hook->"),
    edge((2, 0.5), (4, 1.2), "->>"),
  )
]


Hence $Ext_R^n (A,B)=Z_H^n\/B_H^n=H^n (Hom_R^bullet (A,I^bullet))$. This is the cohomology construction of @sec:cohomology applied to the Hom complex introduced in @sec:total-hom-complexes. Agreement with the computation obtained from a projective resolution of the first variable is proved in @Weibel1994[Theorem 2.7.6, p. 63].

// The functor $Hom_R (A,-)$ is left exact. Its right derived functors therefore measure the failure of the final lifting map to be surjective. Choose an injective resolution $0 -> B -> I^0 xto(d_I^0) I^1 xto(d_I^1) I^2 -> dots.c$. Regard $A$ as a complex concentrated in degree $0$. The Hom complex (@def:hom-complex) gives $Hom_R^bullet (A,I^bullet)$, with differential $d_H^q (phi):=d_I^q compose phi$.


// #def(title: "The Ext Functor")[
// The $n$-th *Ext* functor is $ Ext_R^n (A,B):=R^n (Hom_R (A,-)) $ $ (B)=H^n (Hom_R^bullet (A,I^bullet))=Ker (d_H^n)\/im (d_H^(n-1)) $
// ]

// Thus $Ext_R^n (A,B)$ is ordinary cohomology of a Hom complex. Agreement with the construction obtained from a projective resolution of the first variable is proved in @Weibel1994[Theorem 2.7.6, p. 63].

// #align(center)[
//   $ B xto("resolve") I^bullet xto(Hom_R (A,-)) Hom_R^bullet (A,I^bullet) xto(H^n) Ext_R^n (A,B) $
// ]

The name $Ext$ stands for *extensions*. A short exact sequence
$0 -> B xto(i) E xto(q) A -> 0$ is called an extension of $A$ by $B$.Two such extensions are equivalent if there is an isomorphism between their middle terms that makes the diagram of short exact sequences commute and induces the identity maps on $A$ and $B$. The group
$Ext_R^1 (A,B)
$
classifies equivalence classes of extensions of $A$ by $B$.

The Splitting Lemma (@lem:splitting-lemma) identifies the distinguished class among them.  An extension represents zero precisely when it splits, equivalently when $q$ has a section or $i$ has a retraction. In that case
$E iso B plus.o A
$
compatibly with the two structure maps. See @Weibel1994[Section 3.4] and @rotman[Lemma 7.29].

The projective-resolution calculation is particularly simple for cyclic groups.
#exmp(title: "Extensions of a cyclic group")[
Let $n>=1$ and let $B$ be an abelian group. The projective resolution
$0 -> ZZ xto(dot n) ZZ -> ZZ\/n ZZ -> 0
$
gives, after applying $Hom_ZZ(-,B)$,
$0 -> B xto(dot n) B -> 0.
$
Therefore
$
Ext_ZZ^0(ZZ\/n ZZ,B)
iso Ker(n : B -> B),
quad
Ext_ZZ^1(ZZ\/n ZZ,B)
iso B\/ n B.
$

For $n=2$ and $B=ZZ\/2ZZ$, multiplication by $2$ is zero, so
$
Ext_ZZ^1(ZZ\/2ZZ,ZZ\/2ZZ)
iso ZZ\/2ZZ.
$
The zero class is represented by
$
0 -> ZZ\/2ZZ
-> (ZZ\/2ZZ) plus.o (ZZ\/2ZZ)
-> ZZ\/2ZZ
-> 0,
$
whereas the nonzero class is represented by the extension of @ex:nonsplit-z4-extension:
$
0 -> ZZ\/2ZZ
-> ZZ\/4ZZ
-> ZZ\/2ZZ
-> 0.
$
]
<ex:cyclic-extension-ext>

The preceding interpretation also recovers the projective splitting criterion of @prop:lifting-and-extension. An $R$-module $A$ is projective precisely when every extension $0 -> B -> E -> A -> 0$
splits, for every $R$-module $B$. I.e, $A$ is projective iff $Ext_R^1(A,B)=0$ for every $B$.


