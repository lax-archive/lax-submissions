This submission formalizes the core of the sparsity theory of nowhere
dense graph classes, following the lecture notes *Sparsity* of Michał
Pilipczuk and Sebastian Siebertz. Its spine is the chain the notes build:
nowhere dense classes are uniformly quasi-wide; the shallow minors of
their members have subpolynomial edge density; an edge-density bound on
shallow topological minors bounds admissibility; admissibility bounds the
strong coloring number; the strong coloring number bounds the weak
coloring number; and, composing the last four, nowhere dense classes have
subpolynomial weak coloring numbers. Weak coloring numbers control how
many distinct traces vertex neighborhoods leave on a set of vertices, and
the submission ends with that consequence: nowhere dense classes have
almost linear neighborhood complexity.

The concept surface has fifteen review units, eight definitions and seven
theorems. The definitions: graph classes over the canonical finite vertex
types $\mathrm{Fin}\ n$; depth-$r$ minors via shallow-minor models, and
nowhere denseness; the edge density of shallow minors, per graph as
$|E(H)| \le d\,|V(H)|$ and per class as $|E(H)| \le c\,m^{1+\varepsilon}$;
depth-$r$ topological minors — an injective choice of principal vertices
joined by internally disjoint walks of length at most $2r+1$ — with their
density bound; the generalized coloring numbers $\mathrm{wcol}_r$ and
$\mathrm{scol}_r$ as minima over vertex orderings of the largest weak
respectively strong $r$-reachability count, with the subpolynomial bound
predicate $m^{o(1)}$; $r$-admissibility, via families of short paths from
a vertex to smaller vertices that are disjoint apart from their common
start; uniform quasi-wideness, the existence for each radius of a bounded
separator after whose deletion every large vertex set contains a large
distance-$r$ independent subset; and neighborhood complexity, the number
of distinct traces $N(v) \cap A$ that the vertices of a graph leave on a
vertex set $A$, with the class-level predicate $|A|^{1+o(1)}$. The
theorems: nowhere dense classes are uniformly quasi-wide (Lemma 3.4 of
Chapter 4 of the notes) and have subpolynomial shallow-minor density
(Theorem 3.1 of Chapter 1); a depth-$r$ topological edge-density bound $d$
gives $\mathrm{adm}_{r+1} \le 1 + 6(r+1)d^3$ (Lemma 3.2 of Chapter 2);
$\mathrm{scol}_r \le 1 + (\mathrm{adm}_r - 1)^r$ (Lemma 2.5);
$\mathrm{wcol}_r \le 1 + r\,(\mathrm{scol}_r - 1)^r$ (Lemma 2.6); nowhere
dense classes have subpolynomial weak coloring numbers, uniformly over
subgraphs of members (Theorem 3.4 of Chapter 2); and nowhere dense classes
have almost linear neighborhood complexity. All parameters are infima of
explicit sets of naturals, and the two links of the coloring-number chain
are separate theorems, each citable on its own.

The proofs port the development accompanying the lecture notes: a
Ramsey-theoretic extraction of distance-independent sets for
quasi-wideness, a Chernoff-based densification argument for the density
theorem, and the tree-counting and path-routing arguments for the
coloring-number chain. The proof network is laid out on the archive rather
than folded into single derivations: the weak-coloring-number theorem is a
glue proof composing the four theorem concepts before it; the
neighborhood-complexity theorem assumes that statement and contributes the
radius-1 trace counting, the VC-dimension bound from $K_{t,t}$-freeness,
the localization to a polynomially small witness set, and the exponent
rescaling; and the quasi-wideness proof assumes the two Ramsey statements
of the submission *Finite Ramsey Theorems for Pairs and Tuples*.

Except for the neighborhood-complexity theorem, all material is from the
lecture notes *Sparsity* of Michał Pilipczuk and Sebastian Siebertz,
taught at the University of Warsaw; the numbering above follows the
2019/20 edition of the course, whose 2017/18 predecessor carries the same
statements under sequential numbering. The neighborhood-complexity bound
is due to Eickmeyer, Giannopoulou, Kreutzer, Kwon, Pilipczuk, Rabinovich
and Siebertz; the radius-1 derivation from the weak coloring numbers
formalized here follows Corollary 6b of Dreier, Mählmann, McCarty,
Pilipczuk and Toruńczyk.
