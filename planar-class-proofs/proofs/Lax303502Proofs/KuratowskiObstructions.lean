import Lax303502Proofs.K5Split

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.GraphMinors Lax68.GraphTopologicalMinors

/-- A `K₅` minor either has four-arm fans in all five branch sets or splits
one branch set to give a `K₃,₃` minor. -/
theorem k5_minor_topological_obstruction {V : Type*} {G : SimpleGraph V}
    (hM : IsMinor K5 G) : IsTopologicalMinor K5 G ∨ IsTopologicalMinor K33 G := by
  classical
  obtain ⟨M⟩ := hM
  let P := minorPorts M
  by_cases hfan : ∀ a, Nonempty (PathFan (G.induce (M.branchSet a)) (P.terminal a))
  · exact Or.inl ⟨minor_topological_of_fans M P (fun a => Classical.choice (hfan a))⟩
  · push Not at hfan
    obtain ⟨a,ha⟩ := hfan
    let e := k5NeighborEquiv a
    rcases connected_four_fan_or_split (M.connected a).preconnected (P.terminal a ∘ e) with h | h
    · obtain ⟨F⟩ := h
      have hF : Nonempty (PathFan (G.induce (M.branchSet a)) (P.terminal a)) := by
        simpa only [Function.comp_def,Equiv.apply_symm_apply] using
          (show Nonempty (PathFan (G.induce (M.branchSet a)) ((P.terminal a ∘ e) ∘ e.symm)) from
            ⟨F.reindex e.symm.toEmbedding⟩)
      exact (ha.false (Classical.choice hF)).elim
    · obtain ⟨S⟩ := h
      exact Or.inr (k33_minor_topological ⟨k5_split_minor M P a S⟩)

/-- Diestel, Lemma 4.4.2: the ordinary and topological forbidden pairs agree.
This combinatorial statement does not use either planarity characterization. -/
theorem excludedMinors_iff_kuratowskiFree {V : Type*} {G : SimpleGraph V} :
    Lax68.Planar.IsPlanarByExcludedMinors G ↔ IsKuratowskiFree G := by
  classical
  let e := Fintype.equivFin (Fin 3 ⊕ Fin 3)
  let : LinearOrder (Fin 3 ⊕ Fin 3) := LinearOrder.lift' e e.injective
  constructor
  · intro h
    constructor
    · rintro ⟨M⟩
      exact h.1 ⟨topological_to_minor M⟩
    · rintro ⟨M⟩
      exact h.2 ⟨topological_to_minor M⟩
  · intro h
    constructor
    · intro hM
      rcases k5_minor_topological_obstruction hM with hK | hK
      · exact h.1 hK
      · exact h.2 hK
    · intro hM
      exact h.2 (k33_minor_topological hM)

end Lax303502Proofs
