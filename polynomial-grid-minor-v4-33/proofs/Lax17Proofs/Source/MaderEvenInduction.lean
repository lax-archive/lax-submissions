import Lax17Proofs.Source.MaderTightContraction

namespace Lax17Proofs

universe u v w

/-!
# Induction step for the even-degree Mader theorem

The only input left abstract in this module is the finite dangerous-cover
argument for a graph with no non-singleton tight set.  Tight-set contraction
then supplies the full even-degree theorem by strong induction on the vertex
count.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

/-- The irreducible even case: if every tight center-avoiding set is a
singleton, an admissible pair exists. -/
def MaderEvenCoreStatement : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : FiniteEdgeIndexedGraph W) (s : W),
    2 ≤ H.degree s → Even (H.degree s) → H.NoIncidentCutEdge s →
      (∀ T : Finset W, H.MaderTight s T → T.card = 1) →
        ∃ p : H.MaderSplitPair s, H.MaderAdmissible p

/-- Strong induction reduces the even-degree theorem to the irreducible
dangerous-cover argument. -/
theorem exists_maderAdmissible_of_even_of_core
    (hcore : MaderEvenCoreStatement.{u}) :
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : FiniteEdgeIndexedGraph W) (s : W),
      2 ≤ H.degree s → Even (H.degree s) → H.NoIncidentCutEdge s →
        ∃ p : H.MaderSplitPair s, H.MaderAdmissible p := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ (W : Type u) [Fintype W] [DecidableEq W],
      Fintype.card W = n →
      ∀ (H : FiniteEdgeIndexedGraph W) (s : W),
        2 ≤ H.degree s → Even (H.degree s) → H.NoIncidentCutEdge s →
          ∃ p : H.MaderSplitPair s, H.MaderAdmissible p
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro W _ _ hW H s hdegree heven hno
        by_cases hsingle :
            ∀ T : Finset W, H.MaderTight s T → T.card = 1
        · exact hcore H s hdegree heven hno hsingle
        · push_neg at hsingle
          rcases hsingle with ⟨T, hT, hcard⟩
          have hTtwo : 2 ≤ T.card := by
            have hpositive : 0 < T.card := Finset.card_pos.mpr hT.1
            omega
          have hs : s ∉ T := by
            intro hsT
            exact (Finset.mem_erase.mp (hT.2.1 hsT)).1 rfl
          have hTproper : T ⊂ Finset.univ.erase s := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hT.2.1, ?_⟩
            intro heq
            have hboundary := H.boundary_ground_card s
            have hreq := H.centerAvoidingRequirement_eq_zero_of_ground_subset
              (s := s) (X := T) (by simpa [heq])
            rw [← heq] at hboundary
            rw [hT.2.2, hreq] at hboundary
            omega
          let K := H.contractSet T
          let s' := SetContractVertex.projection (T := T) s
          have hcardContract :
              Fintype.card (SetContractVertex W T) < n := by
            rw [SetContractVertex.card, hW]
            have hTle : T.card ≤ n := by
              rw [← hW, ← Finset.card_univ]
              exact Finset.card_le_card (Finset.subset_univ T)
            omega
          have hdegreeK : 2 ≤ K.degree s' := by
            simpa [K, s', H.contractSet_degree_outside T s hs] using hdegree
          have hevenK : Even (K.degree s') := by
            simpa [K, s', H.contractSet_degree_outside T s hs] using heven
          have hnoK : K.NoIncidentCutEdge s' := by
            exact hno.contractSet T hT.1 hs
          rcases ih (Fintype.card (SetContractVertex W T)) hcardContract
              (SetContractVertex W T) rfl K s' hdegreeK hevenK hnoK with
            ⟨q, hq⟩
          rcases MaderSplitPair.exists_preimage_contractSet H T hs q with
            ⟨p, hp⟩
          refine ⟨p, H.tight_contraction_lifts_admissible T hT.1 hT
            hTproper hdegree p ?_⟩
          simpa [hp] using hq
  intro W _ _ H s hdegree heven hno
  exact hP (Fintype.card W) W rfl H s hdegree heven hno

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
