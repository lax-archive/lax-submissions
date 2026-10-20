import Lax457868Proofs.NumericGraphProbability
import Lax457868Proofs.CompleteSamplerSource
import Lax457868Proofs.LocalFlatLaw

/-! The graph hypothesis supplies the rejection-half estimate for each actual
far exception, including the scan restricted to its phase-two class. -/
namespace Lax457868Proofs.NumericRepairProbability
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

end Lax457868Proofs.NumericRepairProbability
