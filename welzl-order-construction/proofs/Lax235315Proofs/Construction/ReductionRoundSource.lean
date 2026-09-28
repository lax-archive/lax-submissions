import Lax235315Proofs.Construction.CertifiedBranch
import Lax235315Proofs.Construction.SamplingFrontier

/-! Composition of the random sampling prefix with both literal round paths. -/
namespace Lax235315Proofs.Construction.ReductionRoundSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.CertifiedBranch
open Lax235315Proofs.Construction.SamplingPrefixSource
open Lax235315Proofs.Construction.TracePartitions

/-- The literal collision rejection path. -/
def rejectCollision : Com := seqs [.assign "good" (.lit 0), .assign "acount" (.lit 0)]

def dispatchRound : Com :=
  .ite (.eq (.var "collision") (.lit 0)) certifiedBranch rejectCollision

lemma sampling_dispatch {B K K' : ℕ} {σ τ τ' : Env}
    (hp : Run B samplingPrefix σ τ K) (hd : Run B dispatchRound τ τ' K') :
    Run B reductionRound σ τ' (K + K') := by
  obtain ⟨kp, hkp, hp⟩ := hp
  obtain ⟨kd, hkd, hd⟩ := hd
  change BigStepB B (.seq readKeys (.seq (seqs (keyNames.reverse.map radixPass))
    detectCollision)) σ τ kp at hp
  cases hp with
  | seq hread hsort =>
    cases hsort with
    | seq hsort hdetect =>
      exact ⟨_, by omega, .seq hread (.seq hsort (.seq hdetect hd))⟩

lemma dispatchRound_run {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env} {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W)
    (hWr : ∀ v ∈ W, v < n)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B dispatchRound σ σ' (2300 * (x.length + 1) + 4) ∧
      ((Frontier B c n x σ' ∧ σ'.vars "round" = σ.vars "round" + 1 ∧
          σ'.vars "acount" ≤ σ.vars "acount" / 2 + c ^ 2) ∨
        (σ'.vars "good" ≠ 1 ∧ σ'.vars "acount" = 0)) := by
  have htest := evalB_condEq (evalB_var (h.workspace.bounded.vars "collision"))
    (evalB_lit (by omega : 0 < B))
  by_cases hcollision : σ.vars "collision" = 0
  · obtain ⟨τ, hr, hout⟩ := certifiedBranch_run hx hG h hc hn hlarge hcsq hbound
      henum hWr hnB htargetB hdenomB hboundB
    refine ⟨τ, ?_, hout⟩
    exact (Run.ite_true (b := .eq (.var "collision") (.lit 0))
      (by simpa only [hcollision, beq_self_eq_true] using htest) hr).mono (by
        simp [Cond.size, Expr.size]; omega)
  · let τ := σ.setVar "good" 0
    let τ' := τ.setVar "acount" 0
    have r₁ : Run B (.assign "good" (.lit 0)) σ τ 2 :=
      Run.assign (evalB_lit (by omega))
    have r₂ : Run B (.assign "acount" (.lit 0)) τ τ' 2 :=
      Run.assign (evalB_lit (by omega))
    have rr : Run B rejectCollision σ τ' 4 := r₁.seq r₂
    refine ⟨τ', ?_, Or.inr ⟨by simp [τ', τ], by simp [τ']⟩⟩
    exact (Run.ite_false (b := .eq (.var "collision") (.lit 0))
      (by simpa only [beq_eq_false_iff_ne.mpr hcollision] using htest) rr).mono (by
        simp [Cond.size, Expr.size]; omega)

set_option maxRecDepth 4096 in
/-- A complete literal reduction round on an arbitrary sufficiently long
binary suffix. No sampling, certificate, or commit execution is assumed. -/
lemma reductionRound_run {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (htape : 8 * Nat.clog 2 n * σ.vars "acount" ≤ σ.inp.length)
    (hqB : 2 ^ Nat.clog 2 n < B)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B reductionRound σ σ'
        (4500 * (x.length + 1) + 120 * Nat.clog 2 n * σ.vars "acount") ∧
      Workspace B c n x σ' ∧
      σ'.inp = σ.inp.drop (8 * Nat.clog 2 n * σ.vars "acount") ∧
      ((Frontier B c n x σ' ∧ σ'.vars "round" = σ.vars "round" + 1 ∧
          σ'.vars "acount" ≤ σ.vars "acount" / 2 + c ^ 2) ∨
        (σ'.vars "good" ≠ 1 ∧ σ'.vars "acount" = 0)) := by
  have ha : 0 < σ.vars "acount" := by omega
  have hs := Sampling.sampleSize_le_self hc ha
  obtain ⟨bits, τ, ord, hp, hcost, hfront, hinp, hord, hprefix, hcollisions,
      hbitsCanonical, hkeyBound, hsortedBound, hrange,
      hsubset, hcard⟩ :=
    SamplingFrontier.run h htape hqB (by omega) (by omega) hs
  have hac := hp.frame_var "acount" (by decide)
  have hrnd := hp.frame_var "round" (by decide)
  have hcsq' := (hp.frame_var "csq" (by decide)).trans hcsq
  have hbound' := (hp.frame_var "nearBound" (by decide)).trans hbound
  have hsN : sampleSize (σ.vars "acount") c ≤ n :=
    hs.trans (by rw [h.activeCount]; exact activeVertices_card_le _ _)
  have hlist : Lax808846Proofs.Reasoning.Lib.Stack.toList
      (sampleSize (σ.vars "acount") c) (view τ "ord") =
      Lax808846Proofs.Reasoning.Lib.Stack.toList
      (sampleSize (σ.vars "acount") c) ord := by
    exact arrOf_congr (fun i hi => view_of_array hord (hi.trans_le hsN))
  let W := ((RadixMath.radixSort8 (2 ^ Nat.clog 2 n)
    (ReadKeys.filledKey (fun d => view σ (RandomKeysRead.keyName d))
      (view σ "activeA") bits n) (ReadKeys.scanList (view σ "activeA") 0 n)).take
        (sampleSize (σ.vars "acount") c)).toFinset
  have hpref : PrefixEnumerates (sampleSize (τ.vars "acount") c)
      (view τ "ord") W := by
    simpa only [hac, PrefixEnumerates, hlist] using hprefix
  obtain ⟨τ', hd, hout⟩ := dispatchRound_run hx hG hfront hc hn
    (by rwa [hac]) hcsq' hbound' hpref hrange hnB htargetB hdenomB hboundB
  have hrun : Run B reductionRound σ τ'
      (4500 * (x.length + 1) + 120 * Nat.clog 2 n * σ.vars "acount") := by
    apply (sampling_dispatch hp hd).mono
    have hlen := hx.length_eq
    omega
  refine ⟨τ', hrun, h.workspace.reductionRound hrun, ?_, ?_⟩
  · exact (hd.frame_inp (by decide)).trans hinp
  · simpa only [hac, hrnd] using hout

end Lax235315Proofs.Construction.ReductionRoundSource
