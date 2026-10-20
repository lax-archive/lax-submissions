import Lax457868Proofs.RefinedRoundSource
import Lax457868Proofs.SamplerInitialRetries
import Lax457868Proofs.SaturatedCutoff

/-! The paper's sampler probability hypotheses for the actual numeric
active sets, derived from the graph's neighborhood complexity. -/
namespace Lax457868Proofs.NumericGraphProbability
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax457868Proofs.GraphTraceBounds
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.VerifiedPartitionBridge
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.SamplerInitialRetries
open Lax457868Proofs.SamplerInitialProbability
open Lax457868Proofs.SamplerWeightedRetries
set_option maxHeartbeats 1000000

lemma numeric_trace_bound {n c : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (A C Y : Finset ℕ) (hA : A ⊆ Finset.range n)
    (hC : C ⊆ Finset.range n) (hYA : Y ⊆ A) (hY : Y.Nonempty) :
    (traceClasses (fun b => numericNeighborhood G b ∩ A) Y C).card ≤ c * Y.card := by
  classical
  have hYn := hYA.trans hA
  have hfY : (finsetOfNumeric (n := n) Y).Nonempty := by
    obtain ⟨y, hy⟩ := hY
    exact ⟨⟨y, Finset.mem_range.mp (hYn hy)⟩, by simpa [finsetOfNumeric] using hy⟩
  have hfYA : finsetOfNumeric (n := n) Y ⊆ finsetOfNumeric A := by
    intro y hy
    simp only [finsetOfNumeric, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hYA hy
  have hbound := traceClasses_finiteNeighborhood_bound hG
    (finsetOfNumeric A) (finsetOfNumeric C) (finsetOfNumeric Y) hfYA hfY
  rw [numeric_card_eq hYn] at hbound
  apply le_trans ?_ hbound
  apply Finset.card_le_card_of_injOn (finsetOfNumeric (n := n))
  · intro T hT
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hT
    let bf : Fin n := ⟨b, Finset.mem_range.mp (hC hb)⟩
    apply Finset.mem_image.mpr
    refine ⟨bf, by simpa [finsetOfNumeric, bf] using hb, ?_⟩
    ext v
    simp only [trace, finiteNeighborhood, finsetOfNumeric, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and, numericNeighborhood,
      Finset.mem_range]
    simp [Lax11Proofs.CC.Adjn, bf, v.isLt, Finset.mem_range.mp (hC hb),
      G.adj_comm, and_comm]
  · intro T hT U hU heq
    have hTsub : T ⊆ Y := by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hT
      exact Finset.inter_subset_right
    have hUsub : U ⊆ Y := by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hU
      exact Finset.inter_subset_right
    ext v
    by_cases hv : v < n
    · have h := Finset.ext_iff.mp heq ⟨v, hv⟩
      simpa [finsetOfNumeric] using h
    · have ht : v ∉ T := fun h => hv (Finset.mem_range.mp (hYn (hTsub h)))
      have hu : v ∉ U := fun h => hv (Finset.mem_range.mp (hYn (hUsub h)))
      simp [ht, hu]

/-- Distinct active full traces imply distinct numeric restricted neighborhoods. -/
lemma numeric_neighborhood_injective {n : ℕ} {G : SimpleGraph (Fin n)}
    (A C : Finset ℕ) (hA : A ⊆ Finset.range n) (hC : C ⊆ Finset.range n)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (finSetAsSet A)) (finSetAsSet C)) :
    ∀ u ∈ C, ∀ v ∈ C,
      numericNeighborhood G u ∩ A = numericNeighborhood G v ∩ A → u = v := by
  intro u hu v hv heq
  let uf : Fin n := ⟨u, Finset.mem_range.mp (hC hu)⟩
  let vf : Fin n := ⟨v, Finset.mem_range.mp (hC hv)⟩
  have ht := (numeric_trace_iff G hA uf vf).mpr heq
  exact congrArg Fin.val (hsep hu hv ht)

lemma numeric_active_card_bound {n c : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (A C : Finset ℕ) (hA : A ⊆ Finset.range n) (hC : C ⊆ Finset.range n)
    (hne : A.Nonempty)
    (hinj : ∀ u ∈ C, ∀ v ∈ C,
      numericNeighborhood G u ∩ A = numericNeighborhood G v ∩ A → u = v) :
    C.card ≤ c * A.card := by
  classical
  have ht := numeric_trace_bound hG A C A hA hC subset_rfl hne
  have heq : traceClasses (fun b => numericNeighborhood G b ∩ A) A C =
      C.image (fun b => numericNeighborhood G b ∩ A) := by
    apply Finset.image_congr
    intro b hb
    simp [trace]
  rw [heq, Finset.card_image_iff.mpr (by intro u hu v hv h; exact hinj u hu v hv h)] at ht
  exact ht

/-- The literal initial sampler parameters satisfy the paper's rejection
bound, using the graph hypothesis and the maintained full-trace separation. -/
lemma numeric_initial_badMass_half {n c : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c) (hc : 2 ≤ c)
    (A C : Finset ℕ) (hA : A ⊆ Finset.range n) (hC : C ⊆ Finset.range n)
    (hne : A.Nonempty)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (finSetAsSet A)) (finSetAsSet C)) :
    badMass (outcomeWeight A C (fun b => numericNeighborhood G b ∩ A)
        (A.card / (4 * c ^ 2)))
      (outcomeBad A C (fun b => numericNeighborhood G b ∩ A)
        (A.card / (4 * c ^ 2)) (Lax457868Proofs.refinedCutoffK c)
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)))) ≤ (1 / 2 : ℚ) := by
  have hinj := numeric_neighborhood_injective A C hA hC hsep
  have hsize := numeric_active_card_bound hG A C hA hC hne hinj
  have hN : ∀ b ∈ C, numericNeighborhood G b ∩ A ⊆ A := by
    intro b hb
    exact Finset.inter_subset_right
  exact outcomeBad_mass_le_half A C (fun b => numericNeighborhood G b ∩ A) c
    hne hN hc hsize
    (deduplicated_linear_trace_bound A C (fun b => numericNeighborhood G b ∩ A)
      c hN hc (fun Y hYA hY => numeric_trace_bound hG A C Y hA hC hYA hY))

end Lax457868Proofs.NumericGraphProbability
