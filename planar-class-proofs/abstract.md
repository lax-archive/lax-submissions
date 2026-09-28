This submission gives direct geometric proofs that every finite tree is
outerplanar, that every finite star is outerplanar and planar, and that every
two-terminal series-parallel graph is planar. The tree and star drawings
place vertices on the unit circle using a rational parametrization.

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

The proofs discharge the original statements in [Planar Graph Classes
(Lax68)](https://laxarchive.org/lax-68/index.html), without changing its
definitions or assuming any open characterization theorem. Each proof is
added to the archive after kernel validation.

Together with the existing Lax68 proofs, finite-tree outerplanarity also
settles finite-tree planarity and path outerplanarity and planarity. Thus all
Lax68 statements labeled as theorems are proved in the combined proof
network, and series-parallel planarity closes the first statement labeled
`opn`. Three such statements remain open: Kuratowski's theorem, Wagner's
theorem, and the excluded-minor characterization of outerplanarity.
