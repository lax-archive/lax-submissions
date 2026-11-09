import Lax457868Proofs.NumericGraphProbability
import Lax457868Proofs.CompleteSamplerSource
import Lax457868Proofs.LocalFlatLaw

/-! The graph hypothesis supplies the rejection-half estimate for each actual
far exception, including the scan restricted to its phase-two class. -/
namespace Lax457868Proofs.NumericRepairProbability
open scoped symmDiff
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax457868Proofs.NumericGraphProbability
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerOutputSize
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult

lemma numeric_local_failure_half {n c r k b : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c) (hc : 2 ≤ c)
    (A C D : Finset ℕ) (hA : A ⊆ Finset.range n) (hC : C ⊆ Finset.range n)
    (hDC : D ⊆ C)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (finSetAsSet A)) (finSetAsSet C))
    (choice : InitialChoice A C (fun v => numericNeighborhood G v ∩ A) r)
    (hb : b ∈ C)
    (hfar : 2 * k / 3 < disagreement (fun v => numericNeighborhood G v ∩ A)
      b (choice.representative b)) :
    2 * (SamplerLocalSuccess.localTrialFailureSet (numericNeighborhood G) D
      (phaseTwoSample G (choice.exceptions k) A choice.sample) b
      (((numericNeighborhood G b ∩ A) \ (numericNeighborhood G (choice.representative b) ∩ A)) ∪
        ((numericNeighborhood G (choice.representative b) ∩ A) \ (numericNeighborhood G b ∩ A)))
      (64 * Nat.clog 2 c)).card ≤
      (disagreement (fun v => numericNeighborhood G v ∩ A)
        b (choice.representative b)) ^ (64 * Nat.clog 2 c) := by
  classical
  have hsample : choice.sample ⊆ A := by
    intro a ha
    exact choice.draws_mem a (List.mem_toFinset.mp ha)
  have has : (((List.range n).filter fun a => a ∈ A).toFinset) = A := by
    ext a
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨Finset.mem_range.mp (hA ha), ha⟩⟩
  have hW : phaseTwoSample G (choice.exceptions k) A choice.sample ⊆ A := by
    unfold phaseTwoSample
    apply phase2Scan_subset_of_ground (numericNeighborhood G) (choice.exceptions k) A
      ((List.range n).filter fun a => a ∈ A) choice.sample hsample
    intro a ha
    simpa using (List.mem_filter.mp ha).2
  exact LocalFlatLaw.localFailure_half_restricted_paper_subgroup
    A D C _ _ (numericNeighborhood G) r k c b (64 * Nat.clog 2 c) choice
    ((List.range n).filter fun a => a ∈ A) has (List.nodup_range.filter _)
    hDC (numeric_neighborhood_injective A C hA hC hsep) hb (by omega) hc
    (fun Y hYA hY => numeric_trace_bound hG A C Y hA hC hYA hY) rfl
    (CompleteSamplerSource.phaseTwoSample_restrict G (choice.exceptions k) A
      choice.sample hsample) rfl hW


/-- The phase-two classes used by the physical repair loop are disjoint on
exceptions; this follows from the maintained full-neighborhood separation. -/
lemma accepted_loop_separate
    {B n c r k t bufferCap targetCap q repairCap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A C : Finset ℕ}
    (choice : InitialChoice A C (fun v => numericNeighborhood G v ∩ A) r)
    (L : ExceptionRepairLoop.LoopInput B n (64*Nat.clog 2 c) t bufferCap targetCap
      q repairCap k (choice.exceptions k).card G x (choice.exceptions k) C
      (phaseTwoSample G (choice.exceptions k) A choice.sample) A
      (phaseTwoSample G (choice.exceptions k) A choice.sample))
    (hC : C ⊆ Finset.range n)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (finSetAsSet A)) (finSetAsSet C)) :
    ∀ u ∈ choice.exceptions k, ∀ v ∈ choice.exceptions k,
      trace (numericNeighborhood G) (phaseTwoSample G (choice.exceptions k) A choice.sample) u =
      trace (numericNeighborhood G) (phaseTwoSample G (choice.exceptions k) A choice.sample) v →
      u = v := by
  classical
  have has : (((List.range n).filter fun a => a ∈ A).toFinset) = A := by
    ext a
    simp only [List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨And.right,fun ha => ⟨Finset.mem_range.mp (L.hA ha),ha⟩⟩
  have hsample : choice.sample ⊆ A := by
    intro a ha
    exact choice.draws_mem a (List.mem_toFinset.mp ha)
  apply L.separate_exceptions_of_phase2 choice
    ((List.range n).filter fun a => a ∈ A) has (List.nodup_range.filter _) rfl
    (CompleteSamplerSource.phaseTwoSample_restrict G (choice.exceptions k) A
      choice.sample hsample)
  intro u hu v hv he
  exact numeric_neighborhood_injective A C L.hA hC hsep
    u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 he

/-- Every far exception in the prepared physical loop has rejection
probability at most one half, with its stored representative. -/
lemma accepted_loop_half
    {B n c r k t bufferCap targetCap q repairCap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A C : Finset ℕ}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c) (hc : 2 ≤ c)
    (choice : InitialChoice A C (fun v => numericNeighborhood G v ∩ A) r)
    (L : ExceptionRepairLoop.LoopInput B n (64*Nat.clog 2 c) t bufferCap targetCap
      q repairCap k (choice.exceptions k).card G x (choice.exceptions k) C
      (phaseTwoSample G (choice.exceptions k) A choice.sample) A
      (phaseTwoSample G (choice.exceptions k) A choice.sample))
    (hC : C ⊆ Finset.range n)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (finSetAsSet A)) (finSetAsSet C))
    (hrep : ∀ b ∈ C, choice.representative b = L.rep b)
    (b : ℕ) (hb : b ∈ choice.exceptions k)
    (hf : 2*k/3 < (((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G (L.rep b) ∩ A))).card) :
    2*(SamplerLocalSuccess.localTrialFailureSet (numericNeighborhood G) C
      (phaseTwoSample G (choice.exceptions k) A choice.sample) b
      ((numericNeighborhood G b ∩ A) ∆ (numericNeighborhood G (L.rep b) ∩ A))
      (64*Nat.clog 2 c)).card ≤
      (((numericNeighborhood G b ∩ A) ∆ (numericNeighborhood G (L.rep b) ∩ A))).card ^
        (64*Nat.clog 2 c) := by
  have hbC := (Finset.mem_filter.mp hb).1
  have h := numeric_local_failure_half hG hc A C C L.hA hC subset_rfl hsep choice hbC
    (by simpa [disagreement,← Finset.symmDiff_def,hrep b hbC] using hf)
  simp only [disagreement,← Finset.symmDiff_def] at h
  rw [hrep b hbC] at h
  exact h

end Lax457868Proofs.NumericRepairProbability
