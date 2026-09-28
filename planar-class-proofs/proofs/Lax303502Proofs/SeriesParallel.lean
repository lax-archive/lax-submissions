import Lax303502Proofs.SeriesParallelDrawing

set_option autoImplicit false

namespace Lax303502Proofs

/--
---
conclusion: Lax68.SeriesParallelPlanar.seriesParallel_planar
---
Every two-terminal series-parallel graph with full support has a straight-line
planar drawing.

# Proof strategy

Strengthen the induction on the two-terminal construction. Place the terminals
at `(0,0)` and `(1,0)`, all vertices in `0 ≤ y ≤ min(x,1-x)`, and all other
vertices above a positive height. Keep a certificate that intersecting edges
or singleton vertices have a common endpoint.

For series composition use the affine maps
`(x,y) ↦ (x/2,(y+x)/4)` and `(x,y) ↦ ((1+x)/2,(y+1-x)/4)`.
The drawings occupy opposite half-strips, with the shared terminal at
`(1/2,1/4)`. For parallel composition, multiply the second drawing's heights
by half the first drawing's positive height bound. Its segments then lie
below every non-baseline segment of the first drawing, except at a shared
terminal. A baseline edge present in both components is handled explicitly.
The new positive bounds are respectively one quarter of the minimum old bound,
and the minimum of the first and scaled second bound.

Finally the full-support hypothesis upgrades the supported certificate to
the exact `StraightLineDrawing` required by the original statement. This
proof uses neither an excluded-minor theorem nor a straightening theorem.

# Attribution

First checked Diestel, *Graph Theory*, sixth edition, Chapters 4 and 12;
the consulted material did not give the direct two-terminal construction.
Courcelle and Engelfriet, *Graph Structure and Monadic Second-Order Logic,
a Language Theoretic Approach*, April 2011 preprint, Section 1.2.2,
printed page 33, give the induction with both terminals on the external face.
The explicit affine maps, height invariant and separation inequalities above
are the straight-line realization formalized in this submission.
-/
theorem seriesParallel_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.SeriesParallel.IsSeriesParallel G → Lax68.Planar.IsPlanar G := by
  rintro ⟨s,t,h,hs⟩
  obtain ⟨D⟩ := SP.twoTerminal_drawing h
  exact ⟨SP.clean_drawing D.clean hs⟩

end Lax303502Proofs
