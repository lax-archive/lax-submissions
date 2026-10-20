import Lax457868Proofs.InitialFlatLaw
import Lax457868Proofs.SamplerRepresentativeCharge

/-! Transfer nonnegative charges from the exact executed initial outcome
fibers to the already proved hierarchical law. Aborted selectors contribute
zero to a later accepted-outcome charge. -/
namespace Lax457868Proofs.InitialOutcomeCharge
open Lax457868Proofs.InitialFlatLaw
open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.SamplerInitialRetries
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

lemma actual_outcome_charge_le
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (decoded : FlatTape I.bits.length → Option (InitialOutcome A
      (activeVertices n I.activeB) (fun b => numericNeighborhood G b ∩ A) r))
    (hdecoded : ∀ ρ ω, decoded ρ = some ω → ρ ∈ sourceInitialOutcomeFiber I ω)
    (reward : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r → ℚ)
    (hreward : ∀ ω, 0 ≤ reward ω) :
    (∑ ρ, (decoded ρ).elim 0 reward) / (2 ^ I.bits.length : ℚ) ≤
      ∑ ω, outcomeWeight A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r ω * reward ω := by
  classical
  have hpoint (ρ : FlatTape I.bits.length) : (decoded ρ).elim 0 reward =
      ∑ ω, if decoded ρ = some ω then reward ω else 0 := by
    cases h : decoded ρ with
    | none => simp
    | some ω => simp
  simp_rw [hpoint]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_le_sum
  intro ω hω
  have hsub : (Finset.univ.filter fun ρ => decoded ρ = some ω) ⊆
      sourceInitialOutcomeFiber I ω := by
    intro ρ hρ
    exact hdecoded ρ ω (Finset.mem_filter.mp hρ).2
  have hcard : ((Finset.univ.filter fun ρ => decoded ρ = some ω).card : ℚ) ≤
      (sourceInitialOutcomeFiber I ω).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hcount := div_le_div_of_nonneg_right hcard
    (show (0 : ℚ) ≤ 2 ^ I.bits.length by positivity)
  have h := mul_le_mul_of_nonneg_right
    (hcount.trans (sourceInitialOutcomeFiber_probability_le_outcomeWeight I ω))
    (hreward ω)
  have heq : (∑ ρ, if decoded ρ = some ω then reward ω else 0) =
      ((Finset.univ.filter fun ρ => decoded ρ = some ω).card : ℚ) * reward ω := by
    rw [← Finset.sum_filter]
    simp
  rw [heq]
  convert h using 1 <;> ring

/-- Repeated representative rows have at most their one-pass weight in the
actual one-attempt subprobability law, including selector aborts. -/
lemma actual_representative_charge_le
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (decoded : FlatTape I.bits.length → Option (InitialOutcome A
      (activeVertices n I.activeB) (fun b => numericNeighborhood G b ∩ A) r))
    (hdecoded : ∀ ρ ω, decoded ρ = some ω → ρ ∈ sourceInitialOutcomeFiber I ω)
    (weight : ℕ → ℚ) (hweight : ∀ b, 0 ≤ weight b) :
    (∑ ρ, (decoded ρ).elim 0 (fun ω =>
      ∑ b ∈ activeVertices n I.activeB,
        weight ((outcomeChoice A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r ω).representative b))) /
        (2 ^ I.bits.length : ℚ) ≤
      ∑ b ∈ activeVertices n I.activeB, weight b := by
  have hh := actual_outcome_charge_le I decoded hdecoded
    (fun ω => ∑ b ∈ activeVertices n I.activeB,
      weight ((outcomeChoice A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r ω).representative b))
    (fun ω => Finset.sum_nonneg (fun b hb => hweight _))
  rw [SamplerRepresentativeCharge.outcome_representative_charge
    A (activeVertices n I.activeB) (fun b => numericNeighborhood G b ∩ A)
      r I.hAnonempty weight] at hh
  exact hh

end Lax457868Proofs.InitialOutcomeCharge
