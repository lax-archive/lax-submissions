import Lax17Proofs.Source.GenericCutMatchingBudget
import Lax17Proofs.Source.RoutedCutMatchingSupport
import Lax17Proofs.Source.WellLinkedComponent

namespace Lax17Proofs

universe u v w

/-!
# Producing the cut-well-linked low-degree core

This module closes the cut-matching step of Chekuri--Chuzhoy Appendix A.4.
The generic cut-matching game supplies a logarithmic half-expander transcript;
integral routability realizes its matchings by node-disjoint paths.  Their
union has logarithmic degree and is cut-well-linked, and all terminals lie in
one connected component.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy

open CutMatchingGame
open RoutedCutMatchingSupport


/-- The routed cut-matching construction supplies the low-degree,
cut-well-linked core required by the direct proof of Theorem 2.21. -/
theorem exists_cutWellLinkedCoreFromRoutableSet_proved :
    ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
      CutWellLinkedCoreFromRoutableSet.{u}
        cDeg cDegLog cAlpha cAlphaLog := by
  rcases exists_generic_log_round_halfExpander_with_followsResponder
    with ⟨cRound, hcRound, hround⟩
  refine ⟨cRound, 1, 2 * cRound, 1,
    hcRound, by decide, by positivity, by decide, ?_⟩
  intro V _ _ G k κ eta X hk hκ hκeven hκk hXcard hroute
  dsimp
  have hXpos : 0 < X.card := by omega
  have hXeven : Even X.card := by
    simpa [hXcard] using hκeven
  have hterminalCard : Fintype.card {v : V // v ∈ X} = κ := by
    simpa [hXcard]
  have hterminalPos : 0 < Fintype.card {v : V // v ∈ X} := by
    omega
  have hterminalEven : Even (Fintype.card {v : V // v ∈ X}) := by
    simpa [hterminalCard] using hκeven
  have hterminalLe : Fintype.card {v : V // v ∈ X} ≤ k := by
    omega
  rcases hround (X := {v : V // v ∈ X}) hk hterminalPos
      hterminalEven hterminalLe (routedResponder hroute) with
    ⟨rounds, hlength, hhalf, hfollow⟩
  let H := supportGraph hroute rounds
  have heta : 1 ≤ eta := Nat.succ_le_of_lt hroute.1
  have hdegree :
      2 * rounds.length ≤
        3 * cRound * eta * (Nat.log 2 k) ^ 1 := by
    calc
      2 * rounds.length ≤ 2 * (cRound * Nat.log 2 k) :=
        Nat.mul_le_mul_left 2 hlength
      _ ≤ 3 * cRound * eta * (Nat.log 2 k) ^ 1 := by
        simp only [pow_one]
        nlinarith
  have halpha :
      2 * rounds.length ≤
        (2 * cRound) * eta * (Nat.log 2 k) ^ 1 := by
    calc
      2 * rounds.length ≤ 2 * (cRound * Nat.log 2 k) :=
        Nat.mul_le_mul_left 2 hlength
      _ ≤ (2 * cRound) * eta * (Nat.log 2 k) ^ 1 := by
        simp only [pow_one]
        nlinarith
  have hwellUniv :
      Section46.ScaledEdgeWellLinkedIn H Finset.univ X 1
        ((2 * cRound) * eta * (Nat.log 2 k) ^ 1) := by
    exact supportGraph_scaledEdgeWellLinkedIn_univ hroute rounds
      hXpos hXeven hhalf hfollow halpha
  rcases Section46.exists_cluster_scaledEdgeWellLinkedIn_of_univ
      (Finset.card_pos.mp hXpos) hwellUniv with
    ⟨C, hCcluster, _hXC, hwellC⟩
  refine ⟨H, supportGraph_le hroute rounds, ?_, C, X,
    hCcluster, hXcard, hwellC⟩
  exact maxDegreeAtMost_mono
    (supportGraph_maxDegreeAtMost hroute rounds) hdegree

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
