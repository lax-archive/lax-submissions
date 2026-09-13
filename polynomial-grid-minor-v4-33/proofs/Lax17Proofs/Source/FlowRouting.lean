import Lax17Proofs.Source.FlowDegree
import Lax17Proofs.Source.FlowIntegrality

namespace Lax17Proofs

universe u v w

/-!
# Routing disjoint paths from bounded-congestion path flows

This file proves the part of the Chekuri--Chuzhoy boosting argument that turns
a bounded edge-congestion unit path flow into many node-disjoint paths in a
bounded-degree graph.  The existence of the initial fractional flow is kept as
an explicit hypothesis; no max-flow/min-cut postulate is used here.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T : Finset V}

namespace OrientedPathFlow

/-- In maximum degree `Δ`, a unit path flow with edge congestion
`alphaDen / alphaNum` contains every number `k` of node-disjoint paths whose
cardinality is bounded by the scaled value
`3 * alphaNum * |S| / (10 * Δ * alphaDen)`.

The proof scales the unit flow by `3 * alphaNum / (10 * Δ * alphaDen)`.  The
degree estimate from `FlowDegree` bounds the resulting vertex congestion by
one, and `FlowIntegrality` extracts the disjoint paths. -/
theorem hasDisjointSTPaths_of_unit_edgeCongestedFlow
    {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hflow :
      ∃ F : OrientedPathFlow G S T,
        F.IsUnitFlow ∧
          F.EdgeCongestionAtMost (scaledCongestion alphaNum alphaDen))
    (hk : 10 * Δ * alphaDen * k ≤ 3 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k := by
  classical
  rcases hflow with ⟨F, hunit, hedge⟩
  have hDelta_pos : 0 < Δ := by omega
  have halphaDen_pos : 0 < alphaDen := halpha_pos.trans_le halpha_le
  let c : ℚ := (3 * (alphaNum : ℚ)) / (10 * (Δ : ℚ) * (alphaDen : ℚ))
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hη_nonneg : 0 ≤ scaledCongestion alphaNum alphaDen := by
    dsimp [scaledCongestion]
    positivity
  let F' := F.scale c hc_nonneg
  have hsource_le : ∀ v : V, F.sourceLoad v ≤ 1 :=
    F.sourceLoad_le_one_of_sourceLoadExactlyOne hunit.1
  have htarget_le : ∀ v : V, F.targetLoad v ≤ 1 :=
    F.targetLoad_le_one_of_targetLoadExactlyOne hunit.2
  have hvertex_base :
      F.VertexCongestionAtMost
        (2 + (Δ : ℚ) * scaledCongestion alphaNum alphaDen) := by
    intro v
    exact F.vertexLoad_le_two_add_maxDegree_mul_of_edgeCongestion
      hdegree hη_nonneg hedge (hsource_le v) (htarget_le v)
  have hscale_capacity :
      c * (2 + (Δ : ℚ) * scaledCongestion alphaNum alphaDen) ≤ 1 := by
    have hαq_pos : (0 : ℚ) < alphaNum := by exact_mod_cast halpha_pos
    have hβq_pos : (0 : ℚ) < alphaDen := by exact_mod_cast halphaDen_pos
    have hΔq_pos : (0 : ℚ) < Δ := by exact_mod_cast hDelta_pos
    have hα_le_β : (alphaNum : ℚ) ≤ alphaDen := by exact_mod_cast halpha_le
    have hΔ_ge_three : (3 : ℚ) ≤ Δ := by exact_mod_cast hDelta
    dsimp [c, scaledCongestion]
    field_simp [hαq_pos.ne', hβq_pos.ne', hΔq_pos.ne']
    nlinarith
  have hvertex_scaled : F'.VertexCongestionAtMost 1 := by
    intro v
    have hv :=
      F.scale_vertexCongestionAtMost (c := c) hc_nonneg hvertex_base v
    dsimp [F'] at hv ⊢
    exact hv.trans hscale_capacity
  have hvalue_base : F.value = S.card :=
    F.value_eq_card_source_of_sourceLoadExactlyOne hunit.1
  have hvalue_scaled : (k : ℚ) ≤ F'.value := by
    have hden_pos : (0 : ℚ) < 10 * (Δ : ℚ) * (alphaDen : ℚ) := by
      positivity
    have hkQ : (10 * Δ * alphaDen * k : ℚ) ≤
        (3 * alphaNum * S.card : ℚ) := by
      exact_mod_cast hk
    dsimp [F']
    rw [F.scale_value, hvalue_base]
    dsimp [c]
    field_simp [hden_pos.ne']
    norm_num at hkQ ⊢
    nlinarith
  exact FlowIntegrality.unitVertexCapacityFlow_hasDisjointSTPaths
    (G := G) (S := S) (T := T) (k := k)
    ⟨F', hvalue_scaled, hvertex_scaled⟩

/-- Sharpened routing theorem for disjoint terminal sides.

When `S` and `T` are disjoint, endpoint load contributes at most one unit at a
vertex, and every internal occurrence is charged to two incident edges.  This
is the constant used in the nonconstructive proof of Chekuri--Chuzhoy Theorem
2.14. -/
theorem hasDisjointSTPaths_of_unit_edgeCongestedFlow_disjoint
    {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hdisj : Disjoint S T)
    (hflow :
      ∃ F : OrientedPathFlow G S T,
        F.IsUnitFlow ∧
          F.EdgeCongestionAtMost (scaledCongestion alphaNum alphaDen))
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k := by
  classical
  rcases hflow with ⟨F, hunit, hedge⟩
  have hDelta_pos : 0 < Δ := by omega
  have halphaDen_pos : 0 < alphaDen := halpha_pos.trans_le halpha_le
  let c : ℚ := (6 * (alphaNum : ℚ)) / (5 * (Δ : ℚ) * (alphaDen : ℚ))
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hη_nonneg : 0 ≤ scaledCongestion alphaNum alphaDen := by
    dsimp [scaledCongestion]
    positivity
  let F' := F.scale c hc_nonneg
  have hvertex_base :
      F.VertexCongestionAtMost
        (1 + ((Δ : ℚ) * scaledCongestion alphaNum alphaDen) / 2) := by
    intro v
    exact F.vertexLoad_le_one_add_half_maxDegree_mul_of_edgeCongestion
      hdegree hη_nonneg hedge hunit hdisj v
  have hscale_capacity :
      c * (1 + ((Δ : ℚ) * scaledCongestion alphaNum alphaDen) / 2) ≤ 1 := by
    have hαq_pos : (0 : ℚ) < alphaNum := by exact_mod_cast halpha_pos
    have hβq_pos : (0 : ℚ) < alphaDen := by exact_mod_cast halphaDen_pos
    have hΔq_pos : (0 : ℚ) < Δ := by exact_mod_cast hDelta_pos
    have hα_le_β : (alphaNum : ℚ) ≤ alphaDen := by exact_mod_cast halpha_le
    have hΔ_ge_three : (3 : ℚ) ≤ Δ := by exact_mod_cast hDelta
    dsimp [c, scaledCongestion]
    field_simp [hαq_pos.ne', hβq_pos.ne', hΔq_pos.ne']
    nlinarith
  have hvertex_scaled : F'.VertexCongestionAtMost 1 := by
    intro v
    have hv :=
      F.scale_vertexCongestionAtMost (c := c) hc_nonneg hvertex_base v
    dsimp [F'] at hv ⊢
    exact hv.trans hscale_capacity
  have hvalue_base : F.value = S.card :=
    F.value_eq_card_source_of_sourceLoadExactlyOne hunit.1
  have hvalue_scaled : (k : ℚ) ≤ F'.value := by
    have hden_pos : (0 : ℚ) < 5 * (Δ : ℚ) * (alphaDen : ℚ) := by
      positivity
    have hkQ : (5 * Δ * alphaDen * k : ℚ) ≤
        (6 * alphaNum * S.card : ℚ) := by
      exact_mod_cast hk
    dsimp [F']
    rw [F.scale_value, hvalue_base]
    dsimp [c]
    field_simp [hden_pos.ne']
    norm_num at hkQ ⊢
    nlinarith
  exact FlowIntegrality.unitVertexCapacityFlow_hasDisjointSTPaths
    (G := G) (S := S) (T := T) (k := k)
    ⟨F', hvalue_scaled, hvertex_scaled⟩

end OrientedPathFlow

end SimpleGraph

end Lax17Proofs
