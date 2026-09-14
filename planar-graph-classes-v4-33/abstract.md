This submission collects definitions of planar graph classes: planar,
outerplanar, maximal outerplanar, grids and walls, triangles, stars, ladders,
Halin graphs, wheels, series-parallel graphs, trees, and paths, together with
triangulations of planar graphs.

The supporting concepts are straight-line graph drawings, graph minors via
connected branch sets, and topological minors via internally disjoint paths.
Planarity is expressed by the existence of a crossing-free straight-line
drawing in the real plane.

Graph-class definitions contain no theorem statements. Elementary
relationships are stated in separate theorem concepts. Each definition concept now
includes a short illustration image.
Proofs are supplied for elementary relationships and preservation of
acyclicity under minors; the remaining gaps are explicitly open statements.
The geometric planarity claims for trees and stars are restricted to finite
graphs. The accompanying visual guide illustrates the defining shapes.

Kuratowski’s subdivision characterization, Wagner’s excluded-minor
characterization, and the excluded-minor characterization of outerplanarity
are stated for finite graphs. These are open statements; this submission does
not supply their proofs.

The supplied proofs include that stars and paths are trees and that minors
of acyclic graphs are acyclic. The latter excludes `K₄` and `K₂,₃` from
trees, proving tree outerplanarity conditional on the open excluded-minor
characterization. The existing tree, star, and path consequences use this
same chain. Wall planarity follows from grid planarity by restricting a drawing. Ladder
planarity has alternative proofs through grids, outerplanarity, and
series-parallel graphs, each conditional on the corresponding open statements.
The remaining open formalization problems are grid planarity, ladder outerplanarity
and series-parallel construction, series-parallel planarity,
triangle maximal outerplanarity, and the wheel-to-Halin construction,
as well as Kuratowski's, Wagner's, and the outerplanar characterization theorems. These
are known mathematical results whose Lean proofs are not supplied here.
