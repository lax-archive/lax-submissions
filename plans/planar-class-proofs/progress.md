# Direct proofs for planar graph classes

Status: five unconditional proofs; Wagner formalized with Kuratowski as its sole statement assumption. Kuratowski remains the independent gap.
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
star planarity, finite-tree outerplanarity, series-parallel planarity, and the
finite outerplanar excluded-minor characterization.
The tree proof also closes
finite-tree planarity and path outerplanarity/planarity through the existing
Lax68 proof network. There are 20 original entries labeled `theorem`; all are
in the least fixed point of the combined proof network. None of the first five
annotated proofs has a statement assumption. The sixth, Wagner, has exactly
the original Kuratowski statement as its assumption. Full local `lax build --replay`
passed; warnings concern Lean-generated structure helper lemmas and the
intentional reusable `outerplanar_minor` corollary.

Publication boundaries:

- `8d83502`: star outerplanarity, independently accepted by Lax.
- `14fd9be`: star planarity, independently accepted by Lax.
- `ece79f7`: finite-tree outerplanarity, independently accepted by Lax.
- `1b94bdd`: series-parallel planarity, independently accepted by Lax.
- `dd76469`: outerplanar excluded minors, independently accepted by Lax.
- `6130776`: Wagner conditional on Kuratowski, independently accepted by Lax,
  with its minor/subdivision bridge proved unconditionally.
- Current checkpoint: unconditional contraction and drawing-stability
  infrastructure for Kuratowski; no additional original statement discharged.

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
   straightening route. The three-connected contraction argument is now
   formalized. Drawing/face topology, the geometric induction step and the
   full original characterization remain unfinished.
3. **Wagner — conditional proof complete.** Theorem 4.4.6 and Lemma 4.4.2
   give the route. The minor/subdivision conversions are now proved in full,
   and Wagner follows using the original Kuratowski characterization as the
   sole statement assumption, as explicitly authorized by the user.
   Wagner is not yet unconditional; Kuratowski must still be discharged.
4. **Outerplanar excluded minors — proved.** Diestel Exercise 23 states it. The worked
   [McGill MATH350 assignment 5 solution, problem 1](https://www.math.mcgill.ca/snorin/math350f2015/MATH350F15HW5Solutions.pdf)
   uses the cone graph and the planar forbidden-minor theorem. Formalizing
   this route requires both the cone/minor equivalence and a bridge from an
   outer-face drawing to Lax68's circular straight-line certificate. Merely
   citing the still-open planar characterization would not close this gap.
   The direct longest-cycle proof below avoids that bridge.

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


## Outerplanar excluded-minor characterization

The exact `Lax68.OuterplanarExcludedMinors.outerplanar_iff_excludedMinors` now
has a direct proof in `Lax303502Proofs/OuterplanarExcludedMinors.lean`.
The user explicitly permits dependencies on the other open statements, but
none was needed for outerplanarity. The later Wagner proof below now reduces
that entry to Kuratowski.

First checked Diestel, Chapter 4, Exercise 23: it states the characterization
without a worked solution. Chartrand and Harary's *Planar Permutation Graphs*
(1967), Theorem 1, gives a forbidden-subdivision argument through Kuratowski.
The direct construction used here is Madeleine Leander,
[*On the bunkbed conjecture* (2009), Theorem 14, printed page 37](https://kurser.math.su.se/pluginfile.php/16103/mod_folder/content/0/2009/2009_07_report.pdf).
That discussion moves from connected to 2-connected graphs without supplying
the block reduction; our finite induction explicitly handles disconnected
graphs and cut vertices, and only then applies the cycle argument.

`CircleNormalization` rotates and rescales an arbitrary finite circle drawing
away from the omitted point of the rational parametrization. `CircularOrder`
proves the equivalence between intersecting chords and alternating endpoints.
`CircularMinors` transports a circular order through connected disjoint minor
branch sets and excludes circular drawings of the two forbidden graphs.

For the converse, `MinorConstructions` constructs the actual connected branch
sets for a cycle with nonconsecutive outside attachments and for alternating
chords. `OuterConnectivity` constructs outside components, attachment paths,
and partitions at disconnections. `LongestCycle` proves that a longest cycle
is spanning in a graph without a cut vertex or a K2,3 minor. `CycleDrawing`
uses the absence of K4 minors to put the spanning cycle on a circle.
`CircularGluing` joins the smaller drawings in separate arcs, rotating their
orders to put a shared cut vertex at parameter zero. The final finite
induction includes empty, singleton, and acyclic graphs.

The original concepts and dependency pins are unchanged. Local Lean checking
passes for the exact original theorem. Full `lax build --replay` passed in
27 seconds, with five extracted proofs and no statement assumptions for any
of them. `#print axioms` for the original equivalence and each direction
lists only `propext`, `Classical.choice`, and `Quot.sound`. The 13 archive
warnings are 12 automatically generated structure lemmas plus the intentional
standalone corollary `outerplanar_minor`, retained as a reusable result.
The archive independently rebuilt and accepted this commit.


## Wagner via the unconditional obstruction bridge

The user explicitly authorized dependencies on the other open statements.
The new `Lax303502Proofs.planar_iff_excludedMinors` concludes the exact original
Wagner statement with only
`Lax68.KuratowskiPlanarity.planar_iff_kuratowskiFree` as a statement assumption.
There is no reverse conditional proof that would create a dependency cycle.

Human source: Diestel, *Graph Theory*, sixth edition, Chapter 4, Lemma 4.4.2
(printed page 107), and Chapter 1, Proposition 1.7.3 (printed page 21).
These sources were read before implementation; no alternative source was
needed. The implementation follows their branch-tree argument with explicit
paths, avoiding a separate minimal-tree classification.

`PathFans` constructs the tripod for three terminals by stopping a path at
its first contact with another path. `FourFans` attaches the fourth terminal
at its first contact with that tripod. Contact at the center gives four
arms; other contact gives disjoint connected sets with two attachments each
and an edge between them. Repeated terminals and zero-length arms are
included. `MinorRouting` chooses consistent inter-branch edges and combines
local fans into the exact `TopologicalMinorModel` of Lax68.

`K5Split` checks the six branch sets of the resulting K3,3 model, using two
parts of the split branch set and the four other original branch sets.
`KuratowskiMinorBridge` converts K3,3 minors into subdivisions.
`TopologicalToMinor` contracts each routed path towards its lesser endpoint
and retains its final edge. `KuratowskiObstructions` combines the cases into
`excludedMinors_iff_kuratowskiFree`; this bridge works for arbitrary vertex
types and uses only the three background axioms.

Local Lean compilation passes. `#print axioms` confirms the bridge is
unconditional and the Wagner proof has exactly the stated Kuratowski
assumption. Full local `lax build --replay` passes in 24 seconds and extracts
six proofs with exactly those assumptions. The 22 warnings concern 21
automatically generated structure lemmas and the intentional standalone
`outerplanar_minor` corollary. The archive independently rebuilt and accepted
commit `6130776` (workflow run `36427264264`). The remaining foundational proof is the original
finite Kuratowski characterization including the straight-line drawing step.

## Kuratowski checkpoint: contraction and drawing stability

Human proof first: Diestel, [Chapter 3, Lemma 3.2.4, printed page 68](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch3.pdf),
gives the minimal-component proof of a three-connected edge contraction.
[Chapter 4, Lemma 4.4.3, printed pages 108–109](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch4.pdf)
uses it in the Kuratowski induction. Kaiser's
[lecture notes, pages 3–5](https://home.zcu.cz/~kaisert/vpdm/3_v3.pdf)
were subsequently consulted for the convex straight-line version of the
vertex expansion. That geometric step has not yet been formalized.

`CutComponents` proves the attachment properties of components after
deleting a separator. `ContractibleEdge` implements Diestel's argument:
choose a smallest component behind a separator consisting of an edge and
one further vertex; a second failed contraction would give a strictly
smaller such component.

`GraphQuotients` transports connectivity through vertex identifications
and composes the exact Lax68 branch-set minor models. `EdgeContraction`
identifies the ends of an edge, supplies the concrete minor model, and
proves preservation of connectivity after deleting at most two vertices.
The unconditional minor/subdivision bridge then proves preservation of
Kuratowski-freeness. `ThreeConnectedContraction` combines these results with
the exact vertex-count decrease. Its endpoint supplies a smaller
three-connected Kuratowski-free graph whenever the original has at least
five vertices, without any open statement assumption.

`SmallPlanar` draws the complete graph on four vertices at `(0,0)`, `(3,0)`,
`(0,3)`, and `(1,1)`, and pulls that drawing back to any graph with at most
four vertices. `DrawingStability` includes isolated vertices as singleton
cells. It proves that intersecting segments form a closed condition on
their endpoints, using compactness of the two interpolation parameters.
A finite intersection of the complementary open conditions then shows
that sufficiently small perturbations preserve the original drawing
certificate.

All seven modules pass their narrow Lean builds, and the full
`lax build planar-class-proofs --replay` passes. Axiom audits of the contraction,
four-vertex planarity, and drawing-stability endpoints list only `propext`,
`Classical.choice`, and `Quot.sound`. No new annotated original proof is claimed: the submission still has five unconditional original
proofs and Wagner conditional on Kuratowski. Remaining work includes the
geometric vertex expansion and face structure, reduction to the
three-connected case, and the geometric obstruction direction. The user
requested that this checkpoint be pushed and work stop afterward.
