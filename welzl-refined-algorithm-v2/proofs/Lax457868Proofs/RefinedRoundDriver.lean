import Lax457868Proofs.RefinedRoundSource
import Lax457868Proofs.RefinedRoundInput
import Lax457868Proofs.RefinedTapeReserve

/-! Sequential refined reduction rounds from the source workspace. -/

namespace Lax457868Proofs.RefinedRoundDriver

set_option maxRecDepth 4000

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.PrepareRefinedRound
open Lax457868Proofs.ExceptionRefinementStep

/-- Preparation followed by the full sampler, both partitions, and commit. -/
def preparedRefinedRoundSource : Com :=
  prepareRefinedRound.seq refinedRoundSource

/-- The command run carries the sampler's fixed fields and the accepted
reduction's new active sets into the next round. -/
lemma roundData_after_commit {B c n K : ℕ} {x : List ℕ}
    {A C R S : Finset ℕ} {σ τ : Env} {nextA nextB : ℕ → ℕ}
    (D : RoundData c n x A C σ)
    (hrun : Run B preparedRefinedRoundSource σ τ K)
    (F : NextFrame n (2 ^ Nat.clog 2 n) n (2 * edgeCount x) x τ nextA nextB)
    (ha : τ.arrs "activeA" = arrOf n (setFlag S))
    (hb : τ.arrs "activeB" = arrOf n (setFlag R))
    (hbitsA : ∀ v ∈ τ.arrs "nextA", v ≤ 1)
    (hbitsB : ∀ v ∈ τ.arrs "nextB", v ≤ 1) :
    RoundData c n x S R τ := by
  refine ⟨?_, F.hn, F.hqpow, ?_, ?_, F.hoff, F.htgt, ha, hb,
    ?_, ?_, hbitsA, hbitsB⟩
  · rw [hrun.frame_var "c" (by decide)]; exact D.parameter
  · rw [hrun.frame_var "cutoffResult" (by decide)]; exact D.cutoff
  · rw [hrun.frame_var "refinedLogC" (by decide)]; exact D.logParameter
  · intro a
    rw [run_array_length_eq hrun]
    exact D.lengths a
  · intro a haMark
    simp only [repairMarks, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at haMark
    rcases haMark with rfl | rfl | rfl | rfl | rfl
    · exact F.htrialActive
    · exact F.htrialRowMarks
    · exact F.htrialDesiredMarks
    · exact F.hrepairBMarks
    · exact F.hrepairRMarks

end Lax457868Proofs.RefinedRoundDriver

namespace Lax457868Proofs.RefinedRoundDriver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.PrepareRefinedRound
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.RefinedSampleSpec
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ExceptionRepairLoop

lemma accepted_prepared_round
    {B c n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A C W : Finset ℕ} {σ : Env}
    (D : RoundData c n x A C σ)
    (hstore : Stored G (refinedCutoffK c) σ)
    (hbounded : Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B σ)
    (hcapacity : σ.vars "removedCount" + A.card ≤ n)
    (hround : σ.vars "round" < n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hCsub : C ⊆ Finset.range n)
    (R : ReadyInput B n A.card n (A.card / (4 * c ^ 2)) n n
      (2 * edgeCount x) (2 ^ Nat.clog 2 n) (refinedCutoffK c)
      (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) G x A)
    (S : RuntimeInput R (64 * Nat.clog 2 c) n)
    (hprep : Run B prepareRefinedRound σ R.I.σ (40 * n + 58))
    (hCarray : R.I.activeB = setFlag C)
    {τ : Env} {samplerCost : ℕ}
    (hsampler : Run B completeSamplerSource R.I.σ τ samplerCost)
    (hframe : FinalFrame R S τ)
    (hstatus₁ : τ.vars "initialRetryStatus" = 1)
    (hstatus₂ : τ.vars "repairRetryStatus" = 1)
    (hord : ∃ packed : ℕ → ℕ,
      τ.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (τ.vars "sampleCount") packed W)
    (hcount : τ.vars "sampleCount" = W.card)
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily
        (activeVertices n R.I.activeB)
        (fun b => numericNeighborhood G b ∩ A))
      (A : Set ℕ) (W : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) (refinedCutoffK c))
    (hC : C.Nonempty) :
    ∃ τout : Env, ∃ Rnum Snum : Finset ℕ, ∃ partCostB partCostA : ℕ,
      Run B preparedRefinedRoundSource σ τout
        ((40 * n + 58) +
          (samplerCost +
            (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size +
              (1 + (Cond.eq (.var "repairRetryStatus") (.lit 1)).size +
              (partCostB + (partCostA + 80 * (n + 1))))))) ∧
      τout.inp = τ.inp ∧
      RoundData c n x Snum Rnum τout ∧
      Nonempty (Stored G (refinedCutoffK c) τout) ∧
      Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B τout ∧
      τout.vars "round" = σ.vars "round" + 1 ∧
      τout.vars "acount" = Snum.card ∧
      τout.vars "removedCount" + Snum.card ≤ n ∧
      2 * Snum.card ≤ A.card + 2 * c ^ 2 ∧
      partCostB + partCostA ≤ 1800 * (x.length + 1) ∧
      Snum ⊆ Finset.range n ∧ Rnum ⊆ Finset.range n ∧
      Snum ⊆ A ∧ Rnum ⊆ C ∧ W ⊆ A ∧ Rnum.Nonempty ∧
      (∃ repA repB,
        Nonempty (ConcreteTracePartition G (setFlag A) (finSetAsSet Rnum) Snum repA) ∧
        Nonempty (ConcreteTracePartition G R.I.activeB (finSetAsSet W) Rnum repB)) := by
  classical
  have hroundR : R.I.σ.vars "round" < n := by
    rw [hprep.frame_var "round" (by decide)]
    exact hround
  have hcapacityR : R.I.σ.vars "removedCount" + A.card ≤ n := by
    rw [hprep.frame_var "removedCount" (by decide)]
    exact hcapacity
  have hstoreR : Stored G (refinedCutoffK c) R.I.σ := hstore.frame
    (hprep.frame_var "round" (by decide))
    (hprep.frame_var "removedCount" (by decide))
    (hprep.frame_arr "activeA" (by decide))
    (hprep.frame_arr "activeB" (by decide))
    (hprep.frame_arr "roundStart" (by decide))
    (hprep.frame_arr "roundEnd" (by decide))
    (hprep.frame_arr "removed" (by decide))
    (hprep.frame_arr "removedRep" (by decide))
  have hboundedR :=
    Lax457868Proofs.RefinedRecordedCommit.run_preserves hprep hbounded
  have hlength (a : String) : (R.I.σ.arrs a).length =
      welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a := by
    rw [run_array_length_eq hprep a]
    exact D.lengths a
  have hlengthN (a : String) (hoff : a ≠ "off") (htgt : a ≠ "tgt")
      (hcount : a ≠ "count") : (R.I.σ.arrs a).length = n := by
    simpa [welzlExt, hoff, htgt, hcount] using hlength a
  have hscratch : RoundScratch n R.I.σ := by
    exact ⟨hlengthN "classA" (by decide) (by decide) (by decide),
      hlengthN "repsA" (by decide) (by decide) (by decide),
      hlengthN "repsB" (by decide) (by decide) (by decide),
      hlengthN "nextA" (by decide) (by decide) (by decide),
      hlengthN "nextB" (by decide) (by decide) (by decide),
      hlengthN "repA" (by decide) (by decide) (by decide),
      hlengthN "roundStart" (by decide) (by decide) (by decide),
      hlengthN "roundEnd" (by decide) (by decide) (by decide),
      hlengthN "removed" (by decide) (by decide) (by decide),
      hlengthN "removedRep" (by decide) (by decide) (by decide)⟩
  have hnextABits : arrayBits R.I.σ "nextA" := by
    unfold arrayBits
    rw [hprep.frame_arr "nextA" (by decide)]
    exact D.nextA_bits
  have hnextBBits : arrayBits R.I.σ "nextB" := by
    unfold arrayBits
    rw [hprep.frame_arr "nextB" (by decide)]
    exact D.nextB_bits
  have hCnonempty : (activeVertices n R.I.activeB).Nonempty := by
    rw [hCarray]
    obtain ⟨v, hv⟩ := hC
    exact ⟨v, mem_activeVertices.mpr ⟨Finset.mem_range.mp (hCsub hv),
      by simp [setFlag, hv]⟩⟩
  obtain ⟨τ₂, τout, Rnum, Snum, nextA, nextB, repA, repB,
      partCostB, partCostA, hsuffix, hstored, hroundOut, hacountOut,
      hshrink, hcost, hnextFrame, hactiveA, hactiveB, hbitsA, hbitsB,
      hboundedOut, hcapOut, hpartA, hpartB, hSrange, hRrange,
      hSsub, hRsub⟩ :=
    accepted_commit_stored_run R S hscratch hnextABits hnextBBits hboundedR
      hstoreR hcapacityR hroundR hG hc hsampler hframe hord hcount hsample hCnonempty
  have hguard₁ : (Cond.eq (.var "initialRetryStatus") (.lit 1)).evalB B τ =
      some true := by
    have hB : 1 < B := R.I.honeB
    rw [evalB_condEq (evalB_var (by rw [hstatus₁]; exact hB :
      τ.vars "initialRetryStatus" < B)) (evalB_lit hB)]
    simp [hstatus₁]
  have hguard₂ : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB B τ =
      some true := by
    have hB : 1 < B := R.I.honeB
    rw [evalB_condEq (evalB_var (by rw [hstatus₂]; exact hB :
      τ.vars "repairRetryStatus" < B)) (evalB_lit hB)]
    simp [hstatus₂]
  have hroundRun : Run B refinedRoundSource R.I.σ τout
      (samplerCost +
        (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size +
          (1 + (Cond.eq (.var "repairRetryStatus") (.lit 1)).size +
            (partCostB + (partCostA + 80 * (n + 1)))))) := by
    have hh := hsampler.seq
      (Run.ite_true (d := .assign "acount" (.lit 0)) hguard₁
        (Run.ite_true (d := .assign "acount" (.lit 0)) hguard₂ hsuffix))
    simpa only [refinedRoundSource] using hh
  have hwhole : Run B preparedRefinedRoundSource σ τout
      ((40 * n + 58) +
        (samplerCost +
          (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size +
            (1 + (Cond.eq (.var "repairRetryStatus") (.lit 1)).size +
              (partCostB + (partCostA + 80 * (n + 1))))))) := by
    simpa only [preparedRefinedRoundSource] using hprep.seq hroundRun
  have hdata := roundData_after_commit D hwhole hnextFrame
    hactiveA hactiveB hbitsA hbitsB
  have hRsubC : Rnum ⊆ C := by
    intro v hv
    have hh := (mem_activeVertices.mp (hRsub hv)).2
    simpa [hCarray, setFlag] using hh
  have hWsubA : W ⊆ A := hsample.2.2.1
  have hRnonempty : Rnum.Nonempty := by
    obtain ⟨b, hb⟩ := hC
    let partB := Classical.choice hpartB
    let bf : Fin n := ⟨b, Finset.mem_range.mp (hCsub hb)⟩
    have hbflag : R.I.activeB bf.val = 1 := by
      rw [hCarray]
      change setFlag C b = 1
      simp [setFlag, hb]
    have hrep := partB.partition.representative_mem bf hbflag
    exact ⟨(partB.partition.representative bf).val, hrep⟩
  refine ⟨τout, Rnum, Snum, partCostB, partCostA, hwhole,
    hsuffix.frame_inp (by decide), hdata,
    hstored, hboundedOut, ?_, hacountOut, hcapOut, hshrink, hcost, hSrange, hRrange,
    hSsub, hRsubC, hWsubA, hRnonempty,
    repA, repB, hpartA, hpartB⟩
  rw [hroundOut, hprep.frame_var "round" (by decide)]

end Lax457868Proofs.RefinedRoundDriver

namespace Lax457868Proofs.RefinedRoundDriver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.PrepareRefinedRound
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.RefinedSampleSpec
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult

/-- Success means the actual source commit extended the physical history and
left a ready next-round workspace. The charge is the literal sum of the
preparation, sampler, two partitions, and commit. -/
def AcceptedRound {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ)
    (x : List ℕ) (A C : Finset ℕ) (σ τ : Env) (cost : ℕ) : Prop :=
  ∃ W Rnum Snum : Finset ℕ,
  ∃ repA repB : ℕ → ℕ,
  ∃ samplerCost partCostB partCostA : ℕ,
    cost = (40 * n + 58) +
      (samplerCost +
        (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size +
          (1 + (Cond.eq (.var "repairRetryStatus") (.lit 1)).size +
            (partCostB + (partCostA + 80 * (n + 1)))))) ∧
    RoundData c n x Snum Rnum τ ∧
    Nonempty (Stored G (refinedCutoffK c) τ) ∧
    τ.vars "round" = σ.vars "round" + 1 ∧
    τ.vars "acount" = Snum.card ∧
    τ.vars "removedCount" + Snum.card ≤ n ∧
    2 * Snum.card ≤ A.card + 2 * c ^ 2 ∧
    partCostB + partCostA ≤ 1800 * (x.length + 1) ∧
    Snum ⊆ Finset.range n ∧ Rnum ⊆ Finset.range n ∧
    Snum ⊆ A ∧ Rnum ⊆ C ∧ W ⊆ A ∧ Rnum.Nonempty ∧
    Nonempty (ConcreteTracePartition G (setFlag A) (finSetAsSet Rnum) Snum repA) ∧
    Nonempty (ConcreteTracePartition G (setFlag C) (finSetAsSet W) Rnum repB)

end Lax457868Proofs.RefinedRoundDriver

namespace Lax457868Proofs.RefinedRoundDriver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.PrepareRefinedRound
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.RefinedSampleSpec
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ExceptionRepairLoop

lemma failed_initial_ne {B K : ℕ} {σ τ : Env}
    (hrun : Run B completeSamplerSource σ τ K)
    (hbound : τ.vars "initialRetryStatus" < B)
    (hne : τ.vars "initialRetryStatus" ≠ 1)
    (hB : 1 < B) :
    Run B refinedRoundSource σ (τ.setVar "acount" 0)
      (K + (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size + 2)) := by
  have hguard : (Cond.eq (.var "initialRetryStatus") (.lit 1)).evalB B τ =
      some false := by
    rw [evalB_condEq (evalB_var hbound) (evalB_lit hB)]
    simp [hne]
  have hstop : Run B (.assign "acount" (.lit 0)) τ (τ.setVar "acount" 0) 2 :=
    Run.assign (evalB_lit (by omega : 0 < B))
  simpa only [refinedRoundSource, Nat.add_assoc] using
    hrun.seq (Run.ite_false hguard hstop)

/-- One source round is constructed from the factual workspace and random
input. Acceptance extends the stored history; either retry failure executes
the explicit source stop. No sampler or partition run is an input premise. -/
lemma preparedRefinedRoundSource_run
    {B c n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A C : Finset ℕ} {σ : Env} {bits : List Bool} {rest : List ℕ}
    (D : RoundData c n x A C σ)
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hA : A ⊆ Finset.range n) (hCsub : C ⊆ Finset.range n)
    (hC : C.Nonempty)
    (hlarge : 2 * refinedCutoffK c < A.card)
    (hB : 4 * (x.length + 1) ≤ B)
    (hbounded : Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B σ)
    (hstore : Stored G (refinedCutoffK c) σ)
    (hcapacity : σ.vars "removedCount" + A.card ≤ n)
    (hround : σ.vars "round" < n)
    (hinput : σ.inp = bits.map Bool.toNat ++ rest)
    (hbudget : n * attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n +
      (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) *
        (n * ((64 * Nat.clog 2 c) * n * Nat.clog 2 n)) ≤ bits.length) :
    ∃ τ : Env, ∃ cost : ℕ,
      Run B preparedRefinedRoundSource σ τ cost ∧
      τ.vars "n" = n ∧
      ((AcceptedRound G c x A C σ τ cost ∧
          Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B τ ∧
          ∃ used : ℕ,
            used ≤ n * attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n +
              (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) *
                (n * ((64 * Nat.clog 2 c) * n * Nat.clog 2 n)) ∧
            τ.inp = (bits.drop used).map Bool.toNat ++ rest) ∨
        τ.vars "acount" = 0 ∧
          ((τ.vars "initialRetryStatus" = 2 ∨
              τ.vars "initialRetryStatus" = 3) ∨
            (τ.vars "repairRetryStatus" = 2 ∨
              τ.vars "repairRetryStatus" = 3))) := by
  classical
  have hnpos : 0 < n := by
    obtain ⟨v, hv⟩ := hC
    have hvn := Finset.mem_range.mp (hCsub hv)
    omega
  have hOneBudget : attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n ≤
      bits.length := by
    have hmul : attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n ≤
        n * attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n := by
      have hh := Nat.mul_le_mul_right
        (attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n)
        (show 1 ≤ n by omega)
      simpa using hh
    omega
  have hPrepBudget : (A.card / (4 * c ^ 2)) * n * Nat.clog 2 A.card +
      n * n * Nat.clog 2 n ≤ bits.length := by
    simpa only [attemptBitBudget] using hOneBudget
  obtain ⟨R, S, hprep, hbits, hrest, hCarray, hretryCap, hframePrep⟩ :=
    prepare_sampler_input D hx hc hA hCsub hlarge hB hinput hPrepBudget
  have hCnonempty : (activeVertices n R.I.activeB).Nonempty := by
    rw [hCarray]
    obtain ⟨v, hv⟩ := hC
    exact ⟨v, mem_activeVertices.mpr ⟨Finset.mem_range.mp (hCsub hv),
      by simp [setFlag, hv]⟩⟩
  have hSamplerBudget :
      n * attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n +
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) *
          (n * ((64 * Nat.clog 2 c) * n * Nat.clog 2 n)) ≤ R.I.bits.length := by
    simpa only [hbits] using hbudget
  obtain ⟨τsam, charges, phaseCost, partitionCost, groupCost, offsetCost,
      repairCost, samplerCost, hsampler, hchecked, hcharges, hsamCost,
      hsamInput, hsamFrame, houtcome⟩ :=
    completeSamplerSource_run R S hretryCap (by have := R.hnB; omega) hSamplerBudget
      hCnonempty (by omega : refinedCutoffK c < A.card)
      (by omega : 0 < c) rfl rfl
  rcases houtcome with hsuccess | hfailInitial | hfailRepair
  · obtain ⟨W, packed, hstatus₂, hflags, hordArray, hprefix, hcount,
        hsample, haccepted⟩ := hsuccess
    obtain ⟨τpre, consumed, hrunPre, hinputPre, husedPre,
      hacceptedExecution⟩ := haccepted
    obtain ⟨choice, q, L, Lfinal, steps, initialPacked, phaseTwoPacked,
      hprestatus, hstatus₁, hcapChoice, hrepChoice, hphaseCost,
      hpartCost, hgroupCost, hoffsetCost, hinitialPrefix, hphasePrefix,
      hLqpow, hrprep, hrrepair, hrepairCost, hLbits, hLrest,
      hrepairBudget, hLfinalBits, hfixed, hmap, hsteps,
      hinputFinal, harrFinal, hvarsFinal⟩ := hacceptedExecution
    obtain ⟨τout, Rnum, Snum, partCostB, partCostA, hwhole, hinputFrame, hdata,
        hstored, hboundedOut, hroundOut, hacountOut, hcapOut, hshrink, hcost,
        hSrange, hRrange, hSsub, hRsubC, hWsubA, hRnonempty,
        repA, repB, hpartA, hpartB⟩ :=
      accepted_prepared_round D hstore hbounded hcapacity hround hG hc
        hCsub R S hprep hCarray hsampler hsamFrame hstatus₁ hstatus₂
        ⟨packed, hordArray, hprefix⟩ hcount hsample hC
    have hstepLen := Lax457868Proofs.RefinedTapeReserve.steps_length_le hmap
    have hrepairBits := Lax457868Proofs.RefinedTapeReserve.traceBitCost_le
      (G := G) (rep := L.rep) hA hstepLen hsteps
    have hrepairTotal : traceBitCost G A L.rep steps ≤
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) *
          (n * ((64 * Nat.clog 2 c) * n * Nat.clog 2 n)) := by
      exact hrepairBits.trans (Nat.mul_le_mul_right _ hcapChoice)
    have husedTotal : consumed + traceBitCost G A L.rep steps ≤
        n * attemptBitBudget n A.card (A.card / (4 * c ^ 2)) n +
          (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) *
            (n * ((64 * Nat.clog 2 c) * n * Nat.clog 2 n)) := by omega
    have hinputSam : τsam.inp =
        (bits.drop (consumed + traceBitCost G A L.rep steps)).map Bool.toNat ++ rest := by
      rw [hLfinalBits, hLbits, hbits, hLrest, hrest] at hinputFinal
      simpa only [List.drop_drop] using hinputFinal
    have hinputOut : τout.inp =
        (bits.drop (consumed + traceBitCost G A L.rep steps)).map Bool.toNat ++ rest := by
      rw [hinputFrame]
      exact hinputSam
    refine ⟨τout, _, hwhole, hdata.vertices, Or.inl ⟨?_, hboundedOut,
      consumed + traceBitCost G A L.rep steps, husedTotal, hinputOut⟩⟩
    refine ⟨W, Rnum, Snum, repA, repB, samplerCost, partCostB, partCostA,
      rfl, hdata, hstored, hroundOut, hacountOut, hcapOut, hshrink,
      hcost, hSrange, hRrange, hSsub, hRsubC, hWsubA, hRnonempty,
      hpartA, ?_⟩
    simpa only [hCarray] using hpartB
  · have hfail := failed_initial_round_run hsampler hfailInitial
      (by have := R.hnB; omega : 3 < B)
    have hwhole : Run B preparedRefinedRoundSource σ (τsam.setVar "acount" 0)
        ((40 * n + 58) +
          (samplerCost + (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size + 2))) := by
      simpa only [preparedRefinedRoundSource] using hprep.seq hfail
    exact ⟨_, _, hwhole, by simpa [Env.setVar] using hsamFrame.1,
      Or.inr ⟨by simp [Env.setVar], Or.inl (by simpa [Env.setVar] using hfailInitial)⟩⟩
  · by_cases hinit : τsam.vars "initialRetryStatus" = 1
    · have hfail := failed_repair_round_run hsampler hinit hfailRepair
        (by have := R.hnB; omega : 3 < B)
      have hwhole : Run B preparedRefinedRoundSource σ (τsam.setVar "acount" 0)
          ((40 * n + 58) +
            (samplerCost +
              (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size +
                (1 + (Cond.eq (.var "repairRetryStatus") (.lit 1)).size + 2)))) := by
        simpa only [preparedRefinedRoundSource] using hprep.seq hfail
      exact ⟨_, _, hwhole, by simpa [Env.setVar] using hsamFrame.1,
        Or.inr ⟨by simp [Env.setVar], Or.inr (by simpa [Env.setVar] using hfailRepair)⟩⟩
    · have hboundR :=
        Lax457868Proofs.RefinedRecordedCommit.run_preserves hprep hbounded
      have hboundOut :=
        Lax457868Proofs.RefinedRecordedCommit.run_preserves hsampler hboundR
      have hfail := failed_initial_ne hsampler
        (hboundOut.vars "initialRetryStatus") hinit R.I.honeB
      have hwhole : Run B preparedRefinedRoundSource σ (τsam.setVar "acount" 0)
          ((40 * n + 58) +
            (samplerCost + (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size + 2))) := by
        simpa only [preparedRefinedRoundSource] using hprep.seq hfail
      exact ⟨_, _, hwhole, by simpa [Env.setVar] using hsamFrame.1,
        Or.inr ⟨by simp [Env.setVar], Or.inr (by simpa [Env.setVar] using hfailRepair)⟩⟩

end Lax457868Proofs.RefinedRoundDriver
