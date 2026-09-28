import Lax235315Proofs.Construction.ConcreteSampleAcceptance
import Lax235315Proofs.Construction.CertifiedBranch
import Lax235315Proofs.Construction.ReductionRoundSource
import Lax235315Proofs.Construction.SamplingFrontier
import Mathlib.Tactic

/-! A good literal sample forces the collision-free certificate branch to
accept and commit. -/

namespace Lax235315Proofs.Construction.SampledGoodBranch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.ConcreteSampleAcceptance
open Lax235315Proofs.Construction.CertificateFrontier
open Lax235315Proofs.Construction.CertifiedBranch
open Lax235315Proofs.Construction.ReductionRoundSource
open Lax235315Proofs.Construction.SamplingFrontier
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.RadixMath

noncomputable section

set_option maxRecDepth 4096

/-- Numeric members of a source sample, retyped as graph vertices. -/
def finSample (n : ℕ) (W : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val ∈ W

@[simp] lemma coe_finSample (n : ℕ) (W : Finset ℕ) :
    (finSample n W : Set (Fin n)) =
      Lax235315Proofs.Construction.PartitionResult.finSetAsSet W := by
  ext v
  simp [finSample, Lax235315Proofs.Construction.PartitionResult.finSetAsSet]

lemma finSample_card {n : ℕ} {W : Finset ℕ}
    (hrange : ∀ v ∈ W, v < n) : (finSample n W).card = W.card := by
  rw [← Set.ncard_coe_finset, coe_finSample]
  exact Lax235315Proofs.Construction.ActiveBookkeeping.finSetAsSet_ncard hrange

lemma finSample_subset_active {n : ℕ} {W : Finset ℕ} {active : ℕ → ℕ}
    (hsub : W ⊆ activeVertices n active) :
    finSample n W ⊆ Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset active := by
  intro v hv
  have hvW : v.val ∈ W := by simpa [finSample] using hv
  rw [Lax235315Proofs.Construction.NearCounterCorrectness.mem_activeFinset]
  exact (mem_activeVertices.mp (hsub hvW)).2

/-- At a sampled frontier, a sample outside the graph bad family makes the
literal verifier set `good=1`. If collision is zero, the actual dispatch
therefore follows the commit branch and retains that flag. -/
lemma dispatchRound_run_good_sample
    {B c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)} {σ : Env}
    {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2)
    (hbound : σ.vars "nearBound" = 6 * c ^ 2 * Nat.clog 2 n)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c)
      (view σ "ord") W)
    (hWrange : ∀ v ∈ W, v < n)
    (hWactive : W ⊆ activeVertices n (view σ "activeA"))
    (hcollision : σ.vars "collision" = 0)
    (hbad : finSample n W ∉ familyBadSamples
      (traceFamily G
        (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
          (view σ "activeA"))
        (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
          (view σ "activeB"))) id
      (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
        (view σ "activeA")) c (Nat.clog 2 n))
    (hnB : 2 * n + 1 < B)
    (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B)
    (hboundB : 6 * c ^ 2 * Nat.clog 2 n < B) :
    ∃ σ', Run B dispatchRound σ σ' (2300 * (x.length + 1) + 4) ∧
      σ'.vars "good" = 1 ∧ Frontier B c n x σ' ∧
      σ'.vars "round" = σ.vars "round" + 1 ∧
      σ'.vars "acount" ≤ σ.vars "acount" / 2 + c ^ 2 := by
  let WFin := finSample n W
  have hsampleSet : (WFin : Set (Fin n)) =
      Lax235315Proofs.Construction.PartitionResult.finSetAsSet W := by
    exact coe_finSample n W
  have hsampleSub : WFin ⊆
      Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
        (view σ "activeA") :=
    finSample_subset_active hWactive
  have hWcard : W.card = sampleSize
      (activeVertices n (view σ "activeA")).card c := by
    rw [CertificateFrontier.prefix_card henum, ← h.activeCount]
  have hactiveSet :
      (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
        (n := n) (view σ "activeA") : Set (Fin n)) =
        {v : Fin n | (view σ "activeA") v.val = 1} := by
    ext v
    simp [Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset]
  have hactiveCard :
      (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
        (n := n) (view σ "activeA")).card =
        (activeVertices n (view σ "activeA")).card := by
    rw [← Set.ncard_coe_finset, hactiveSet]
    exact Lax235315Proofs.Construction.ActiveBookkeeping.activeSet_ncard n
      (view σ "activeA")
  have hsampleCard : WFin.card = sampleSize
      (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
        (n := n) (view σ "activeA")).card c := by
    rw [finSample_card hWrange, hWcard, ← hactiveCard]
  have hgoodCertificate := frontier_preparePartitionsAndVerify_accepts_good_sample
    hx h hc hn hcsq hbound henum hWrange hsampleSet hsampleSub hsampleCard hbad
    hnB htargetB hdenomB hboundB
  obtain ⟨τ, hτrun, hτgood⟩ := hgoodCertificate
  obtain ⟨τc, hcert, hcand⟩ := certificate_candidate_run hx hG h hc (by omega)
    hcsq hbound henum hWrange hnB htargetB hdenomB hboundB
  obtain ⟨_, _, hbGood⟩ := hτrun.bigStep
  obtain ⟨_, _, hbCand⟩ := hcert.bigStep
  have hτeq : τ = τc := (BigStep.unique hbGood hbCand).1
  have hgoodC : τc.vars "good" = 1 := by rw [← hτeq]; exact hτgood
  have hcand' := hcand hgoodC
  have hcommit := hcand'.commit hc hn (by omega) (by rwa [hcert.frame_var "acount" (by decide)])
  obtain ⟨τ', hcommitRun, hfront', hrnd', hac'⟩ := hcommit
  have hboundedCert := SourceBounds.run_preserves hcert h.workspace.bounded
  have htestGood := evalB_condEq
    (evalB_var (hboundedCert.vars "good"))
    (evalB_lit (by omega : 1 < B))
  have hbranch : Run B certifiedBranch σ τ' (2300 * (x.length + 1)) := by
    have hseq := hcert.seq (Run.ite_true
      (d := .assign "acount" (.lit 0))
      (b := .eq (.var "good") (.lit 1))
      (by simpa only [hgoodC, beq_self_eq_true] using htestGood) hcommitRun)
    apply hseq.mono
    have hxlen := hx.length_eq
    simp only [Cond.size, Expr.size]
    omega
  have hdispatchTest := evalB_condEq
    (evalB_var (h.workspace.bounded.vars "collision"))
    (evalB_lit (by omega : 0 < B))
  have hdispatchStep := Run.ite_true (c := certifiedBranch)
    (d := ReductionRoundSource.rejectCollision)
    (b := .eq (.var "collision") (.lit 0))
    (by simpa only [hcollision, beq_self_eq_true] using hdispatchTest) hbranch
  have hdispatch : Run B dispatchRound σ τ'
      (2300 * (x.length + 1) + 4) := by
    apply hdispatchStep.mono
    simp [Cond.size, Expr.size]
    omega
  have hgood' : τ'.vars "good" = 1 := by
    have hframe := hcommitRun.frame_var "good" (by decide)
    simpa [hframe] using hgoodC
  have hrnd : τc.vars "round" = σ.vars "round" :=
    hcert.frame_var "round" (by decide)
  have hacount : τc.vars "acount" = σ.vars "acount" :=
    hcert.frame_var "acount" (by decide)
  refine ⟨τ', hdispatch, hgood', hfront', ?_, ?_⟩
  · simpa [hrnd] using hrnd'
  · rw [hac', hcand'.nextCount]
    simpa [hacount] using hcand'.shrinks

/-- Run the actual `SamplingFrontier` source, retaining its canonical radix
sample and attaching the collision-free good-sample dispatch consequence. -/
lemma samplingFrontier_good_sample_dispatch
    {B c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2)
    (hbound : σ.vars "nearBound" = 6 * c ^ 2 * Nat.clog 2 n)
    (htape : 8 * Nat.clog 2 n * σ.vars "acount" ≤ σ.inp.length)
    (hqB : 2 ^ Nat.clog 2 n < B)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B)
    (hboundB : 6 * c ^ 2 * Nat.clog 2 n < B) :
    ∃ bits : ℕ → Fin 8 → List ℕ,
    let vertices := scanList (view σ "activeA") 0 n
    let digits := filledKey (fun d => view σ (keyName d))
      (view σ "activeA") bits n
    let sorted := radixSort8 (2 ^ Nat.clog 2 n) digits vertices
    ∃ τ : Env, ∃ ord : ℕ → ℕ,
      Run B SamplingPrefixSource.samplingPrefix σ τ
        ((120 * n + 120 * Nat.clog 2 n * σ.vars "acount" + 8) +
          512 * (σ.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
          300 * (σ.vars "acount" + 1)) ∧
      Frontier B c n x τ ∧
      τ.arrs "ord" = arrOf n ord ∧
      PrefixEnumerates (sampleSize (σ.vars "acount") c) ord
        (sorted.take (sampleSize (σ.vars "acount") c)).toFinset ∧
      (∀ v ∈ (sorted.take (sampleSize (σ.vars "acount") c)).toFinset, v < n) ∧
      (sorted.take (sampleSize (σ.vars "acount") c)).toFinset ⊆
        activeVertices n (view σ "activeA") ∧
      (sorted.take (sampleSize (σ.vars "acount") c)).toFinset.card =
        sampleSize (σ.vars "acount") c ∧
      (τ.vars "collision" = 0 →
        finSample n (sorted.take (sampleSize (σ.vars "acount") c)).toFinset ∉
          familyBadSamples
            (traceFamily G
              (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
                (view τ "activeA"))
              (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
                (view τ "activeB"))) id
            (Lax235315Proofs.Construction.NearCounterCorrectness.activeFinset
              (view τ "activeA")) c (Nat.clog 2 n) →
        ∃ τ' : Env,
          Run B dispatchRound τ τ' (2300 * (x.length + 1) + 4) ∧
          τ'.vars "good" = 1 ∧ Frontier B c n x τ' ∧
          τ'.vars "round" = τ.vars "round" + 1 ∧
          τ'.vars "acount" ≤ τ.vars "acount" / 2 + c ^ 2) := by
  have ha : 0 < σ.vars "acount" := by omega
  have hs := Sampling.sampleSize_le_self hc ha
  obtain ⟨bits, τ, ord, hsampleRun, hcost, hfront, hinp, hord,
      hprefix, hrange, hsubset, hcard⟩ :=
    SamplingFrontier.run h htape hqB (by omega) (by omega) hs
  refine ⟨bits, ?_⟩
  dsimp only
  refine ⟨τ, ord, hsampleRun, hfront, hord, hprefix, hrange, hsubset, hcard, ?_⟩
  intro hcollision hbad
  let W := (RadixMath.radixSort8 (2 ^ Nat.clog 2 n)
    (ReadKeys.filledKey (fun d => view σ (RandomKeysRead.keyName d))
      (view σ "activeA") bits n)
    (ReadKeys.scanList (view σ "activeA") 0 n)).take
      (sampleSize (σ.vars "acount") c) |>.toFinset
  have hac := hsampleRun.frame_var "acount" (by decide)
  have hcsq' := (hsampleRun.frame_var "csq" (by decide)).trans hcsq
  have hbound' := (hsampleRun.frame_var "nearBound" (by decide)).trans hbound
  have hordArray := hord
  have hacN : σ.vars "acount" ≤ n := by
    rw [h.activeCount]
    exact activeVertices_card_le _ _
  have hsN : sampleSize (σ.vars "acount") c ≤ n := hs.trans hacN
  have hlist : Lax808846Proofs.Reasoning.Lib.Stack.toList
      (sampleSize (σ.vars "acount") c) (view τ "ord") =
      Lax808846Proofs.Reasoning.Lib.Stack.toList
        (sampleSize (σ.vars "acount") c) ord := by
    exact arrOf_congr (fun i hi => view_of_array hordArray (hi.trans_le hsN))
  have henum : PrefixEnumerates (sampleSize (τ.vars "acount") c)
      (view τ "ord") W := by
    simpa only [hac, PrefixEnumerates, hlist] using hprefix
  have hactiveArray := hsampleRun.frame_arr "activeA" (by decide)
  have hactiveEq : view τ "activeA" = view σ "activeA" := by
    funext i
    simp [view, hactiveArray]
  have hsubsetτ : W ⊆ activeVertices n (view τ "activeA") := by
    simpa [W, hactiveEq] using hsubset
  have hrangeW : ∀ v ∈ W, v < n := by
    simpa [W] using hrange
  have hsuccess := dispatchRound_run_good_sample hx hG hfront hc hn
    (by rwa [hac]) hcsq' hbound' henum hrangeW hsubsetτ hcollision
    (by simpa [W] using hbad) hnB htargetB hdenomB hboundB
  simpa [W] using hsuccess

end

end Lax235315Proofs.Construction.SampledGoodBranch
