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

The concept surface has fifteen review units. Eight definitions: graph
classes over the finite vertex types $\mathrm{Fin}\ n$; shallow minors
and nowhere denseness; the edge density of shallow minors; shallow
topological minors with their density bound; the generalized coloring
numbers $\mathrm{wcol}_r$ and $\mathrm{scol}_r$; $r$-admissibility;
uniform quasi-wideness; and neighborhood complexity, the number of
distinct traces $N(v) \cap A$ on a vertex set $A$. Seven theorems: nowhere
dense classes are uniformly quasi-wide (Lemma 3.4 of Chapter 4 of the
notes) and have subpolynomial shallow-minor density (Theorem 3.1 of
Chapter 1); a depth-$r$ topological edge-density bound $d$ gives
$\mathrm{adm}_{r+1} \le 1 + 6(r+1)d^3$ (Lemma 3.2 of Chapter 2);
$\mathrm{scol}_r \le 1 + (\mathrm{adm}_r - 1)^r$ (Lemma 2.5);
$\mathrm{wcol}_r \le 1 + r\,(\mathrm{scol}_r - 1)^r$ (Lemma 2.6); nowhere
dense classes have subpolynomial weak coloring numbers (Theorem 3.4 of
Chapter 2); and nowhere dense classes have almost linear neighborhood
complexity. All parameters are infima of explicit sets of naturals.

The proofs port the development accompanying the lecture notes. The proof
network is laid out on the archive rather than folded into single
derivations: the weak-coloring-number theorem is a glue proof composing
the four theorem concepts before it, the neighborhood-complexity theorem
assumes that statement and adds the radius-1 trace counting, and the
quasi-wideness proof assumes the two Ramsey statements of the submission
*Finite Ramsey Theorems for Pairs and Tuples*.

Except for the neighborhood-complexity theorem, all material is from the
lecture notes *Sparsity* of Michał Pilipczuk and Sebastian Siebertz,
taught at the University of Warsaw; the numbering above follows the
2019/20 edition of the course, whose 2017/18 predecessor carries the same
statements under sequential numbering. The neighborhood-complexity bound
is due to Eickmeyer, Giannopoulou, Kreutzer, Kwon, Pilipczuk, Rabinovich
and Siebertz; the radius-1 derivation from the weak coloring numbers
formalized here follows Corollary 6b of Dreier, Mählmann, McCarty,
Pilipczuk and Toruńczyk.
