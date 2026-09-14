import Lax68

set_option autoImplicit false

namespace Lax68Proofs

open SimpleGraph Lax68.GraphMinors

/-- Disjoint nonempty branch sets provide distinct representatives, so a
minor cannot have more vertices than the original finite graph. -/
private theorem minor_card_le {V W : Type*} [Finite V]
    {G : SimpleGraph V} {H : SimpleGraph W} (h : IsMinor H G) :
    Nat.card W ≤ Nat.card V := by
  classical
  obtain ⟨M⟩ := h
  let representative (w : W) : M.branchSet w := Classical.choice (M.connected w).nonempty
  apply Nat.card_le_card_of_injective (fun w => (representative w).val)
  intro a b hab
  change (representative a).val = (representative b).val at hab
  by_contra hne
  exact Set.disjoint_left.mp (M.disjoint hne)
    (hab ▸ (representative a).property) (representative b).property

/--
---
conclusion: Lax68.TriangleMaximalOuterplanar.triangle_maximalOuterplanar
---
A triangle is isomorphic to `K₃`. Its three vertices rule out `K₄` and `K₂,₃`
as minors, since minor branch sets are disjoint and nonempty. The excluded-minor
characterization, which remains open, gives outerplanarity. Completeness
makes it maximal: no further edge can be added on the same vertices.
-/
theorem triangle_maximalOuterplanar {V : Type*} {G : SimpleGraph V}
    (hG : Lax68.Triangles.IsTriangle G) :
    Lax68.MaximalOuterplanar.IsMaximalOuterplanar G := by
  obtain ⟨e⟩ := hG
  let : Finite V := Finite.of_injective e e.injective
  have card : Nat.card V = 3 := by simpa using Nat.card_congr e.toEquiv
  have complete : G = ⊤ := by
    apply eq_top_iff_forall_ne_adj.mpr
    intro a b hab
    exact e.map_adj_iff.mp (e.injective.ne hab)
  refine ⟨?_, ?_⟩
  · apply (Lax68.OuterplanarExcludedMinors.outerplanar_iff_excludedMinors
      (G := G) inferInstance).mpr
    constructor
    · intro h
      have bound := minor_card_le h
      simp [card] at bound
    · intro h
      have bound := minor_card_le h
      simp [card] at bound
  · intro H h
    simp [complete] at h

end Lax68Proofs
