# Direct proofs for planar graph classes

Status: five unconditional proofs; Wagner formalized with Kuratowski as its sole statement assumption. The K3,3 subdivision and minor obstructions are now proved independently. The K5 obstruction and the converse Kuratowski implication remain open.
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
- `6130776`: Wagner conditional on Kuratowski, with its minor/subdivision
  bridge proved unconditionally; this is the current archive draft source.

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

## Polygonal subdivision geometry

`Polygonal.subdivisionDrawing` constructs a polygonal drawing of every
topological minor of a graph supplied with a straight-line drawing. A linear
order on the minor's vertex type selects an orientation for each edge; no
finiteness hypothesis is needed for this construction. The source is Diestel,
Chapter 4, Sections 4.1–4.2: polygonal arcs and plane graphs. This is only
the geometric subdivision step. It does not supply the planar separation
theorems, nonplanarity of the two forbidden graphs, or straightening.

`EdgeGeometry` proves that incident drawn edges intersect only at their
common endpoint, then handles arbitrary distinct edges. It also proves
injectivity of straight segments and of concatenated paths whose images meet
only at their joint. `PolygonalWalks` realizes a graph walk continuously,
identifies its range with its segment trace, and proves that nontrivial graph
paths give injective polygonal arcs. The terminal edge is parametrized without
a constant waiting interval. The trace is a finite union of segments.

`SubdivisionGeometry` proves that distinct model routes share only common
branch endpoints and have no edge in common. It selects consistent reversed
routes and packages the construction as `PolygonalDrawing`: distinct vertex
positions, injective continuous arcs, finite segment images, equal images
for opposite orientations, exclusion of other vertices, and intersections
only at common endpoints. All original concept files remain unchanged.

Lean compilation succeeds. `#print axioms` for `subdivisionDrawing`,
`injective_walkPath`, and `subdivision_trace_intersection` lists only
`propext`, `Classical.choice`, and `Quot.sound`. These helpers are intentionally
retained for the pending Kuratowski proof, although none is yet used by an
annotated archive theorem. They do not discharge a seventh original statement.

At this milestone, the next mathematical work was planar separation and
exclusion of polygonal drawings of K5 and K3,3. The K3,3 case is now completed
below. The converse still needs the
forbidden-subdivision construction and straightening step. Do not infer the
original straight-line theorem merely from this polygonal realization.

Proof-network check before the next submission: keep the original concept
files and six annotated conclusions unchanged; check that the new geometric
helpers use only background axioms and that no reverse dependency from
Kuratowski to Wagner has been introduced. Inspect the generated proof
assumption lists after full kernel replay. Publish the next draft after a
completed original statement, as in the standing workflow above.

Validation completed: full `lax build --replay` passes in 68 seconds. It
extracts the same six proofs: five have no statement assumptions, and Wagner
has only the original Kuratowski assumption. There are 50 unused-helper
warnings, comprising the previous 22 and 28 from the intentionally retained
polygonal development (including generated structure lemmas). No new axiom,
placeholder proof, concept, or circular statement dependency was introduced.
This is a local development milestone; the archive draft remains at
`6130776` until another original statement is completed.

## The utility-graph obstruction

`Polygonal.not_topologicalMinor_k33_of_planar` now proves, with the exact Lax68
definitions, that a graph admitting a straight-line drawing contains no
subdivision of K3,3. `Polygonal.not_minor_k33_of_planar` combines this with the
previous degree-three minor/subdivision bridge. Both statements hold without
a finite-vertex hypothesis. This completes the K3,3 part of the forward
implications of both original characterization statements, not either whole
equivalence.

A renewed source search found Álvaro Begué's
[Jordan–Schönflies development](https://github.com/alonamaloh/schoenflies-lean),
commit `05a43d29cde026618777db3d4e4316204ccca237`. Its theorem
`Graph.IsArcK33.elim` excludes nine plane arcs realizing the utility graph.
The 47-module import closure of `Schoenflies.Graph.K33Land` is included under
`Lax303502Proofs/Topology`, with its Apache 2.0 notices and attribution retained.
See `planar-class-proofs/THIRD_PARTY.md` for provenance and port changes.
This includes the polygonal Jordan and crosscut separation proofs; the general
Jordan–Schönflies theorem is not needed or imported. The pinned mathlib itself
still has no Jordan curve theorem.

All ported declarations live under `Lax303502Proofs`. The port makes the few
implicit parameters explicit and repairs namespace and API differences.
`GraphBase` supplies reducible aliases for mathlib's multigraph type and
deletion operations so that the source's graph predicates remain locally
namespaced. No source theorem is replaced by an axiom.

`K33Nonplanar` maps the product plane continuously and injectively into
`EuclideanSpace ℝ (Fin 2)`, extends each path's parametrization to the real
line, and verifies the exact nine-arc incidence conditions. The previous
`subdivisionDrawing` construction provides those arcs from a topological
minor model. The final type and `#print axioms` have been checked: the imported
obstruction and both Lax68 corollaries use only `propext`, `Classical.choice`,
and `Quot.sound`.

The annotated Wagner proof now uses these independent obstruction results
for its K3,3 cases. Consequently the polygonal subdivision bridge and the
necessary separation lemmas are dependencies of an existing archive proof,
not merely unused prospective helpers. Wagner still has the same single
statement assumption, the original Kuratowski characterization, for the K5
case and the converse. The imported source module boundaries are retained
for provenance; unrelated helper lemmas within that closure may still produce
intentional unused-helper warnings.

Next: the K5 obstruction is still needed to finish the forward Kuratowski
implication. A possible route with the now available crosscut machinery is
the five-cycle and its five diagonals: alternating diagonals must lie on
opposite sides, which would two-color an odd cycle. The converse still needs
the construction of a planar drawing from the absence of both subdivisions,
including straightening. Do not add a reverse Wagner/Kuratowski assumption
cycle. No seventh original archive statement has yet been completed.

Validation: full `lax build --replay` of the integrated proof passes in
3m06s, including 2m12s of kernel replay. The six annotated conclusions and
their assumption lists are unchanged: five unconditional, and Wagner with
only the original Kuratowski assumption. The two new obstruction lemmas have
only the three background axioms. Replacing two autogenerated aliases with
explicit lemmas removes the imported docstring/frontmatter warnings. The
remaining 593 warnings are unused helpers, including generated structure
lemmas and auxiliary results retained with the upstream module closure.
This checkpoint is local; the archive draft has not been resubmitted.

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

## Main-branch submission requested

The user explicitly requested pushing the combined checkpoint to main and
resubmitting the existing draft. This includes the independent K3,3 obstruction
and the contraction and drawing-stability infrastructure. Earlier publication
boundaries above describe historical checkpoints. The full characterization
is still unfinished.

## Local vertex splitting (2026-09-29)

Following the user's request to keep the groundwork simple, `VertexSplit`
isolates the geometric operation from the missing face theory. Human sources
were checked first: Diestel, Chapter 4, Lemma 4.4.3 and Exercise 19, and
Kaiser's Lecture 3, page 4 (links above). The stronger convex-drawing induction
remains the intended route to avoid a separate straightening theorem.

Write `p` for the contracted placement on the original vertex set, so
`p x = p y = o`. `SplitDirection` requires, for every disjoint pair of
incident cells `xa` and `yb`, a linear functional `f` with
`f(p a-o) ≤ 0`, `f(p b-o) ≥ 0`, and `f(w) > 0`. The functionals may differ
between edge pairs. Singleton cells are included, so injectivity and
vertex-on-edge avoidance are covered by the same argument.

The new placement keeps every vertex except `y` fixed and sets
`p_t y = o + t*w`. For incident cells, applying `f` to a hypothetical
intersection forces it to be the stationary endpoint `b`; the contracted
drawing excludes that endpoint from the other cell. For all other cell
pairs, the old segments are disjoint, and the finite openness argument in
`DrawingStability` supplies a common positive bound on `t`.

`vertex_split_small` proves that every sufficiently small positive `t`
gives `SeparatedPlacement G p_t`; `planar_of_vertex_split` produces the
exact original `Lax68.Planar.IsPlanar G` certificate. Neither result assumes
an open archive statement. The local lemma does **not** yet establish the
existence of `SplitDirection` from the combinatorial neighbour-order
condition, or preserve the convex-face invariant. Those remain the next
connections required by the intended induction; no new original
Kuratowski/Wagner conclusion is claimed.

A concrete check in `plans/planar-class-proofs/VertexSplitExample.lean`
splits the explicit `K₄` drawing into a wheel on five vertices, using
`w = (1,2)` and the two coordinate functionals. It includes a shared
neighbour and cases with equality on a separating line. Running
`lake env lean ../../plans/planar-class-proofs/VertexSplitExample.lean`
from the proof package succeeds. Axiom audits for the general lemma,
its planarity corollary, and the example list only `propext`,
`Classical.choice`, and `Quot.sound`.

Full `lax build planar-class-proofs --replay` passes in 1m01s, including
51 seconds of kernel replay. The six original proof conclusions and their
assumptions are unchanged. The helper warnings are intentional at this
intermediate boundary; Kuratowski remains open.


## Cyclic sectors and convex boundary preservation (2026-09-29)

The next geometric step follows Diestel, Chapter 4, Lemma 4.4.3 and
Exercise 19, with the convex expansion described by Kaiser, Lecture 3,
page 4. These sources were read before formalization. The details below
supply the signed-area argument omitted from the lecture notes.

`CyclicVertexSplit` proves the incident-cell certificate from two
consecutive blocks of rays. Angles are unwrapped over a full turn, and
nonnegative radii include singleton cells. A block of width at most π
lies in the intersection of the two closed half-planes through its
boundary rays. The complementary block lies outside the open sector,
so one of those two linear functionals separates each retained neighbour
from the moved star. Shared boundary rays and semicircles are allowed.
At least one of the two blocks spans at most π; swapping the blocks
negates a valid displacement.

Convexity imposes an additional direction choice. Write the four bordering
angles as `l ≤ a < b ≤ r < l+2π`, with the moved block between `a` and `b`.
When both transition gaps are less than π, choose the displacement angle
between `max(a,r-π)` and `min(b,l+π)`. The hypotheses make this interval
nonempty. If the left gap exceeds π, choose between `l+π` and `a`; if the
right gap exceeds π, choose between `b` and `r-π`. In the latter cases an
enlarged sector still separates the stars. `exists_convex_split_direction`
proves the splitting certificate and all four corner signs in these three
cases. Strict convexity excludes transition gaps equal to π.

`ConvexVertexSplit` defines the usual strict supporting-edge certificate:
every other polygon vertex lies strictly to the left of each oriented
boundary edge. The half-plane inequalities hold on the actual convex hull.
The corner lemmas prove that checking a line against the two neighbours
of a convex polygon corner suffices for all other vertices. This connects
the four ray signs above to the collapsed triangle tests.

For a triangle with vertices drawn from the split placement, its signed
area is exactly `A + t*B`. There is no quadratic term because only one
vertex moves. Positive old areas remain positive for sufficiently small
`t`; zero old areas become positive when `B > 0`. In particular, a triangle
`x,y,z` collapsed at `x=y` has coefficient `cross(w,p(z)-p(x))`.
`vertex_split_convex_small` gives one positive bound for both the exact
straight-line drawing certificate and every supplied polygon boundary.

The boundary lists and angular order are still inputs. These lemmas do
not prove that the lists enumerate the faces, extract the order from a
two-connected drawing, or prove the forbidden alternating-neighbour
configurations. Those connections, the three-connected reduction, and
the independent K5 obstruction still belong to the unfinished Kuratowski
proof. No original statement or dependency pin was changed.


Validation: the narrow module builds and the full
`lax build planar-class-proofs --replay` pass. The expanded wheel example
checks all five boundary lists under one common displacement bound. A
separate outer-boundary example opens a triangle into a convex quadrilateral;
its reversed displacement is proved to fail the boundary certificate.
Run the examples with
`lake env lean ../../plans/planar-class-proofs/VertexSplitExample.lean`
from the proof package. Axiom audits of the angular direction choice,
convex-hull support, corner propagation, combined split, and examples list
only `propext`, `Classical.choice`, and `Quot.sound`.
The original proof count remains five unconditional conclusions and Wagner
conditional on Kuratowski. The new helper warnings are intentional until
the remaining facial-data construction and induction use these endpoints.
