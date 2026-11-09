import Lax457868Proofs.RefinedRoundMean
import Lax457868Proofs.RefinedSamplerMean
import Lax457868Proofs.RefinedPrefixMean
namespace Lax457868Proofs.RefinedPreparedMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundMean
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open scoped BigOperators
lemma fixed_prepared_mean
    {B c n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hB : 4*(x.length+1) ≤ B) :
    RefinedPrefixMean.FixedPreparedRoundMean (B := B) (c := c) (n := n)
      (M := 8931) (D := 701) (G := G) (x := x) := by
  classical
  intro σ N hready hguard hlength hreserve final cost hrun
  obtain ⟨A,C,bits,sizes,D,hA,hC,hCne,hsep,⟨hstore⟩,hbounded,hcapacity,
    hroundCap,hacount,hsizes,hpot,hpower,hroundLog,hout,hin,hbudget⟩ := hready
  have hlarge : 2*refinedCutoffK c < A.card := by
    obtain ⟨a,b,ha,hb,he⟩ := evalB_condLt_iff.mp hguard
    obtain ⟨rfl,_⟩ := evalB_var_iff.mp ha
    obtain ⟨rfl,_⟩ := evalB_var_iff.mp hb
    simpa [D.cutoff,hacount] using he
  have hm : A.card ≤ n := by simpa using Finset.card_le_card hA
  have hn : 1 ≤ n := by omega
  have htotal := (RefinedTapeReserve.round_budget_le (c := c) hm).trans hreserve
  have hper : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N :=
    (Nat.le_mul_of_pos_left _ hn).trans (by omega)
  have hbitsLen : bits.length = N := by
    have h := congrArg List.length hin
    simpa [hlength] using h.symm
  obtain ⟨R,S,hprep,hbits,hrest,hactive,hretry,harrays⟩ :=
    prepare_sampler_input D hx hc hA hC hlarge hB hin
      (by simpa [attemptBitBudget,hbitsLen] using hper)
  obtain ⟨samplerFinal,samplerCost,hsampler,hcost⟩ :=
    actual_prepared_family D hG hc hC hCne hlarge hbounded hstore hcapacity
      (by omega) R S hprep hactive hretry htotal final cost
      (by intro ρ; simpa [hrest] using hrun ρ)
  have hsep' : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (ReusedOriginal.Construction.PartitionResult.finSetAsSet A))
      (ReusedOriginal.Construction.PartitionResult.finSetAsSet
        (activeVertices n R.I.activeB)) := by
    have hCeq : activeVertices n (setFlag C) = C := flagged_setFlag hC
    rw [hactive,hCeq]
    exact hsep
  have hmean := RefinedSamplerMean.actual_mean R S hG hc hsep' hretry
    htotal samplerFinal samplerCost hsampler
  have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) =>
    (show (cost ρ:ℚ) ≤ samplerCost ρ+(1946*(x.length+1):ℕ) by exact_mod_cast hcost ρ))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    card_tape,nsmul_eq_mul] at hsum
  rw [hacount]
  push_cast at hmean hsum ⊢
  nlinarith only [hmean,hsum]
end Lax457868Proofs.RefinedPreparedMean
