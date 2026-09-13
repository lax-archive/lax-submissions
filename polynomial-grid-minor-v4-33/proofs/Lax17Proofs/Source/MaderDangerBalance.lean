import Lax17Proofs.Source.MaderSurplus

namespace Lax17Proofs

universe u v w

/-!
# Center-incidence balance for dangerous sets

This module records the complementary-cut bookkeeping used in the dangerous-set
argument for Mader splitting.  Counts are taken in the named multigraph, so
parallel edges retain their multiplicity.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The number of named edge copies joining the center `s` to `X`. -/
noncomputable def centerIncidentCount (H : FiniteEdgeIndexedGraph W)
    (s : W) (X : Finset W) : Nat :=
  (H.edgesBetween {s} X).card

/-- The center incidences into `X` and its complement in `univ.erase s`
partition all named edge copies incident with `s`. -/
theorem centerIncidentCount_add_compl (H : FiniteEdgeIndexedGraph W)
    (s : W) (X : Finset W) :
    H.centerIncidentCount s X +
        H.centerIncidentCount s ((Finset.univ.erase s) \ X) =
      H.degree s := by
  classical
  let Y := (Finset.univ.erase s) \ X
  have hdisjoint :
      Disjoint (H.edgesBetween {s} X) (H.edgesBetween {s} Y) := by
    rw [Finset.disjoint_left]
    intro e heX heY
    rw [H.mem_edgesBetween] at heX heY
    simp only [Finset.mem_singleton] at heX heY
    rcases heX with heX | heX <;> rcases heY with heY | heY
    · exact (Finset.mem_sdiff.mp heY.2).2 heX.2
    · exact H.end_ne e (heX.1.trans heY.1.symm)
    · exact H.end_ne e (heY.1.trans heX.1.symm)
    · exact (Finset.mem_sdiff.mp heY.2).2 heX.2
  have hunion :
      H.edgesBetween {s} X ∪ H.edgesBetween {s} Y = H.incidentEdges s := by
    ext e
    rw [Finset.mem_union, H.mem_edgesBetween, H.mem_edgesBetween,
      H.mem_incidentEdges]
    simp only [Finset.mem_singleton]
    constructor
    · rintro (h | h) <;> rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
      · exact Or.inl h.1
      · exact Or.inr h.1
    · intro h
      rcases h with hleft | hright
      · have hright_ne : H.right e ≠ s := by
          intro hright
          exact H.end_ne e (hleft.trans hright.symm)
        by_cases hrightX : H.right e ∈ X
        · exact Or.inl (Or.inl ⟨hleft, hrightX⟩)
        · exact Or.inr (Or.inl ⟨hleft, by simp [Y, hright_ne, hrightX]⟩)
      · have hleft_ne : H.left e ≠ s := by
          intro hleft
          exact H.end_ne e (hleft.trans hright.symm)
        by_cases hleftX : H.left e ∈ X
        · exact Or.inl (Or.inr ⟨hright, hleftX⟩)
        · exact Or.inr (Or.inr ⟨hright, by simp [Y, hleft_ne, hleftX]⟩)
  rw [centerIncidentCount, centerIncidentCount, degree,
    ← hunion, Finset.card_union_of_disjoint hdisjoint]

/-- Exact complementary-boundary relation after removing the center from the
ground set. -/
theorem boundary_card_add_centerIncidentCount_compl
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset W)
    (hX : X ⊆ Finset.univ.erase s) :
    (H.boundary X).card +
        H.centerIncidentCount s ((Finset.univ.erase s) \ X) =
      (H.boundary ((Finset.univ.erase s) \ X)).card +
        H.centerIncidentCount s X := by
  classical
  let Y := (Finset.univ.erase s) \ X
  have hsX : s ∉ X := by
    intro hs
    exact (Finset.mem_erase.mp (hX hs)).1 rfl
  have hinter : X ∩ {s} = ∅ := by
    ext z
    simp [hsX]
  have hunionCompl : (X ∪ {s})ᶜ = Y := by
    ext z
    simp only [Y, Finset.mem_compl, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h
      exact ⟨fun hzs => h (Or.inr hzs), fun hzX => h (Or.inl hzX)⟩
    · intro h hz
      exact hz.elim h.2 (fun hzs => h.1 hzs)
  have hboundaryUnion : H.boundary (X ∪ {s}) = H.boundary Y := by
    rw [← hunionCompl, H.boundary_compl]
  have hdiffX : X \ {s} = X := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro hz
      exact ⟨hz, fun hzs => hsX (hzs ▸ hz)⟩
  have hdiffCenter : {s} \ X = {s} := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro hzs
      refine ⟨hzs, ?_⟩
      intro hzX
      exact hsX (hzs.symm ▸ hzX)
  have hedgesBetweenComm (A B : Finset W) :
      H.edgesBetween A B = H.edgesBetween B A := by
    ext e
    simp only [H.mem_edgesBetween]
    tauto
  have hcorrection :
      H.unionInterCorrectionEdges X {s} = H.edgesBetween {s} X := by
    rw [unionInterCorrectionEdges, hdiffX, hdiffCenter,
      hedgesBetweenComm]
  have hcut := H.boundary_union_inter_card_identity X {s}
  rw [hinter, H.boundary_empty, Finset.card_empty, zero_add,
    hboundaryUnion, H.boundary_singleton, ← degree,
    hcorrection] at hcut
  have hdegree := H.centerIncidentCount_add_compl s X
  simp only [centerIncidentCount] at hdegree hcut ⊢
  dsimp [Y] at hcut
  omega

/-- If the center has even degree, a dangerous set contains at most half of
the named edge copies incident with the center. -/
theorem dangerous_incident_count_le_compl
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hdegree : Even (H.degree s)) (hX : H.MaderDangerous s X) :
    H.centerIncidentCount s X ≤
      H.centerIncidentCount s ((Finset.univ.erase s) \ X) := by
  have hpartition := H.centerIncidentCount_add_compl s X
  have hboundary :=
    H.boundary_card_add_centerIncidentCount_compl s X hX.subset_ground
  have hreqCompl :=
    H.centerAvoidingRequirement_complement hX.subset_ground
  have hreqLe := H.centerAvoidingRequirement_le_boundary s
    ((Finset.univ.erase s) \ X)
  have hdanger := hX.boundary_le
  rcases hdegree with ⟨d, hd⟩
  omega

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
