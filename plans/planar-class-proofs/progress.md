# Direct proofs for planar graph classes

Status: six former theorem gaps and series-parallel planarity closed; three `opn` statements still open.
Updated 2026-09-28. Submission: [lax-303502](https://laxarchive.org/lax-303502/).

The user's order is to finish unproved entries labeled `theorem`, then work on
entries labeled `opn`. Keep updating the same replaceable draft after each
completed original statement. Do not register it while it is being extended.

The canonical Lax68 source is `f179bc81671b353be657432784d7dee68486b0bd`,
folder `planar-graph-classes-v4-33`, in `lax-archive/lax-submissions`.
The initial search-engine result was stale; the live website and refreshed
archive database agree on this source. In particular, grids and triangles
already have unconditional proofs. Do not recreate the older wheel/Halin
statements that were absent from the current registered record.

## Completed

The new submission contains unconditional proofs of star outerplanarity,
star planarity, finite-tree outerplanarity, and series-parallel planarity.
The tree proof also closes
finite-tree planarity and path outerplanarity/planarity through the existing
Lax68 proof network. There are 20 original entries labeled `theorem`; all are
in the least fixed point of the combined proof network. None of the four new
annotated proofs has a statement assumption. Full local `lax build --replay`
passed; the only warnings concern Lean-generated structure helper lemmas.

Publication boundaries:

- `8d83502`: star outerplanarity, independently accepted by Lax.
- `14fd9be`: star planarity, independently accepted by Lax.
- `ece79f7`: finite-tree outerplanarity, independently accepted by Lax.

The original statements and definitions have not been modified. The new
concept package is empty and the proof package requires the exact registered
Lax68 concept package.

## Human-readable construction used

First checked Diestel's [Section 1.5](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch1.pdf):
a nontrivial finite tree has a leaf, and deleting it preserves being a tree.
[Chapter 4](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch4.pdf)
provides the drawing framework; Exercise 23 states the outerplanarity
characterization without a worked proof.
Then checked Pach and Törőcsik's [Layout of rooted trees, Algorithm 1, printed
page 2](https://www.cs.princeton.edu/techreports/1992/369.pdf), which embeds
rooted trees recursively into point sets with the prescribed root on the hull.

The implemented specialization uses rational unit-circle coordinates
`p(t) = ((1-t²)/(1+t²), 2t/(1+t²))`. After drawing the tree without a leaf,
insert the leaf's parameter in the first gap after its neighbour. For the
new chord with parameters `a < b`, the affine functional
`(1-ab)x + (a+b)y - (1+ab)` evaluates at `p(t)` to
`-2(t-a)(t-b)/(1+t²)`. It vanishes on the chord and is negative at every
other old vertex, and therefore along every disjoint old edge. The circle's
tangent functional excludes a third vertex on an edge. These are explicit
algebraic proofs, not assumptions of a geometric picture.

## `opn` statements and sources

1. **Series-parallel planarity — proved.** Searched the available Diestel Chapters 4
   and 12 and the book website; no explicit two-terminal straight-line
   construction was located there. Courcelle and Engelfriet,
   [Graph Structure and Monadic Second-Order Logic, Section 1.2.2, printed
   page 33](https://www.labri.fr/perso/courcell/Book/TheBook.pdf), give an
   induction preserving both terminals on the outer face. The direct
   straight-line realization is now formalized: see the construction below.
2. **Kuratowski in straight-line form.** Diestel Chapter 4, Theorem 4.4.6,
   supplies the forbidden-subdivision proof; Exercise 15 supplies the
   straightening route. The missing Lean development includes drawing/face
   topology, the three-connected contraction argument and the straightening
   bridge. No verified proof of the original statement has been produced.
3. **Wagner.** The same theorem and Lemma 4.4.2 give the minor/subdivision
   route. The graph-model conversions and the geometric theorem are not
   formalized here. This remains open, not a corollary of an assumed axiom.
4. **Outerplanar excluded minors.** Diestel Exercise 23 states it. The worked
   [McGill MATH350 assignment 5 solution, problem 1](https://www.math.mcgill.ca/snorin/math350f2015/MATH350F15HW5Solutions.pdf)
   uses the cone graph and the planar forbidden-minor theorem. Formalizing
   this route requires both the cone/minor equivalence and a bridge from an
   outer-face drawing to Lax68's circular straight-line certificate. Merely
   citing the still-open planar characterization would not close this gap.

The pinned mathlib tree and the current Lax database were searched for
existing geometric planarity results. No reusable proof of these four
original statements was located. Isabelle's
[Planarity Certificates](https://isa-afp.org/entries/Planarity_Certificates.html)
uses combinatorial maps and a Kuratowski implication; it does not directly
supply the required geometric Lean theorem.

## Series-parallel construction

The exact original `Lax68.SeriesParallelPlanar.seriesParallel_planar` now has
an unconditional proof in `Lax303502Proofs/SeriesParallel.lean`. The existing
source statements and all dependencies are unchanged. The new reference
[Graph Representations (Lax683916)](https://laxarchive.org/lax-683916/index.html)
was inspected: it supplies representation equivalences, not drawing theorems.
The current `SimpleGraph` representation fits the induction directly, so no
conversion or extra dependency was necessary.

`PlaneCells.lean` treats an edge or a supported singleton vertex as a cell.
Its intersection certificate says intersecting cells share an endpoint. It
therefore supplies injectivity, vertex/edge avoidance and independent-edge
disjointness uniformly, and has a generic gluing lemma.

`TerminalGeometry.lean` keeps terminals at `(0,0)` and `(1,0)`, every supported
vertex in `0 ≤ y ≤ min(x,1-x)`, and every nonterminal vertex at height at least
`h > 0`, with `h ≤ 1`. A checked separation lemma says that if a segment enters
the thinner triangle `y ≤ (h/2)x`, `y ≤ (h/2)(1-x)`, each nonterminal endpoint
has zero coefficient. This handles shared terminal edges as well as cells
meeting at either terminal.

`SeriesParallelDrawing.lean` realizes the inductive constructors. Series uses
`L(x,y)=(x/2,(y+x)/4)` and `R(x,y)=((1+x)/2,(y+1-x)/4)`, with the middle vertex
at `(1/2,1/4)`. The half-strips meet only on their terminal boundary, and the
new height bound is `min(hG,hH)/4`. Parallel scales the second drawing's
vertical coordinate by `hG/2`; the new bound is `min(hG,(hG/2)*hH)`.
No finite extrema are needed. The terminal support facts also show why
isolated vertices outside an intermediate component do not enter the drawing
certificate; the final full-support condition yields the original theorem.

Validation: the pinned Lean build and full `lax build --replay` pass.
The extracted proof has the exact original conclusion and `assumptions: []`.
`#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`.
The new package retains only the support lemmas used by the construction;
the additional finite-support results remain in the earlier scratch file.
There are no `sorry`, new axioms, or uses of any open characterization theorem.
