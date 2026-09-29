This submission gives direct geometric proofs that every finite tree is
outerplanar, that every finite star is outerplanar and planar, and that every
two-terminal series-parallel graph is planar. It also proves that a finite
graph is outerplanar if and only if it has neither a $K_4$ nor a $K_{2,3}$
minor. The tree and star drawings place vertices on the unit circle using a rational parametrization.

For trees, induction removes a leaf and then inserts it beside its neighbour
in a gap between the existing circle parameters. An affine functional for
the new chord separates it from all edges with disjoint endpoints. A tangent
functional rules out vertices inside edges. The star proof is also given
separately: all its edges share the centre.

For series-parallel graphs, an induction keeps the terminals at the ends of
a horizontal segment and the other vertices in the triangle above it, with
a positive height bound. Explicit affine maps join drawings in series.
Vertical compression separates parallel components. The proof checks all
vertex and edge intersections, including a terminal edge shared by both
components, and requires no excluded-minor or straightening theorem.

For the outerplanar characterization, induction splits disconnected graphs
and graphs with a cut vertex into smaller pieces. Acyclic connected pieces
use the tree construction. In the remaining case, a longest cycle contains
every vertex: an outside component would either extend the cycle or
produce a $K_{2,3}$ minor. A pair of alternating chords would produce a $K_4$
minor, so the cycle order gives the required circle drawing. Conversely,
connected minor branch sets preserve circular noncrossing order, and neither
forbidden graph admits such an order. This follows the direct cycle argument
in Leander's *On the bunkbed conjecture*, Theorem 14, with explicit proofs of
the decompositions, minor witnesses, and geometric steps.

These five proofs discharge the original statements in [Planar Graph Classes
(Lax68)](https://laxarchive.org/lax-68/index.html), without changing its
definitions or assuming any open characterization theorem.

The submission also formalizes Diestel's equivalence between containing a
$K_5$ or $K_{3,3}$ minor and containing a subdivision of one of those graphs.
Three-terminal branch sets are replaced by tripod paths. Four-terminal
branch sets either give a four-arm fan or split into two connected pieces
that expose a $K_{3,3}$ minor. This combinatorial bridge is unconditional.
It yields the exact original Wagner characterization using Kuratowski's
straight-line characterization as its sole statement assumption. Each proof
is added to the archive after kernel validation.

Together with the existing Lax68 proofs, finite-tree outerplanarity also
settles finite-tree planarity and path outerplanarity and planarity. Thus all
Lax68 statements labeled as theorems are proved in the combined proof
network. Series-parallel planarity and the outerplanar excluded-minor
characterization close two statements labeled `opn` unconditionally.
Wagner's theorem now has a checked proof conditional on Kuratowski's theorem.
Kuratowski's straight-line characterization, which includes the straightening
step, remains unproved; discharging it will also remove Wagner's remaining
dependency.

The $K_{3,3}$ obstruction is now proved independently: a graph with a
crossing-free straight-line drawing contains neither a subdivision nor a
minor of $K_{3,3}$. Subdivision routes become injective polygonal arcs.
Begué's polygonal separation argument excludes the resulting nine-arc
configuration; its Lean proofs and dependencies are included with attribution.
The $K_5$ obstruction and the converse implication of Kuratowski's theorem
remain to be proved.

As groundwork for Kuratowski, this checkpoint also proves Diestel's
three-connected edge-contraction lemma (Lemma 3.2.4), constructs the
contracted graph and its minor model, and proves preservation of
Kuratowski-freeness. It gives an explicit straight-line drawing for every
graph with at most four vertices and proves that sufficiently small
perturbations preserve a finite straight-line drawing. These are auxiliary
results; the geometric induction step and the full Kuratowski
characterization remain unfinished.

A local vertex-splitting lemma now reverses a contraction under explicit
half-plane conditions. It moves only one vertex and proves that every
sufficiently small positive displacement yields a straight-line drawing.
Deriving those conditions from the facial neighbour order, and preserving
the convex-face invariant, remain separate obligations.
