import Lax235315Proofs.Construction.RecordedCommit
import Lax235315Proofs.Construction.ReductionRoundSource

/-! A literal reduction round that carries the accepted graph history stored
in the source's round-boundary and removal arrays. -/

namespace Lax235315Proofs.Construction.HistoryRoundSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.CertifiedBranch
open Lax235315Proofs.Construction.CertificateFrontier
open Lax235315Proofs.Construction.RecordedCommit
open Lax235315Proofs.Construction.ReductionRoundSource
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.SamplingFrontier
open Lax235315Proofs.Construction.SamplingPrefixSource
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.TracePartitions

/-- The certificate and both commit branches preserve or extend the stored
history attached to the concrete log arrays. -/
lemma certifiedBranch_run_stored {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env} {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hstore : Stored G bound σ)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W)
    (hWr : ∀ v ∈ W, v < n)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B certifiedBranch σ σ' (2300 * (x.length + 1)) ∧
      ((Frontier B c n x σ' ∧ σ'.vars "round" = σ.vars "round" + 1 ∧
          σ'.vars "acount" ≤ σ.vars "acount" / 2 + c ^ 2 ∧
          Nonempty (Stored G bound σ')) ∨
        (σ'.vars "good" ≠ 1 ∧ σ'.vars "acount" = 0)) := by
  obtain ⟨τ, hr, hsnap⟩ := certificate_candidate_run_full hx hG h hc (by omega)
    hcsq hbound henum hWr hnB htargetB hdenomB hboundB
  have hvals := SourceBounds.run_preserves hr h.workspace.bounded
  have htestEval := evalB_condEq (evalB_var (hvals.vars "good"))
    (evalB_lit (by omega : 1 < B))
  have hac := hr.frame_var "acount" (by decide)
  have hround := hr.frame_var "round" (by decide)
  have hlen := hx.length_eq
  have hstoreτ : Stored G bound τ := hstore.frame
    (hr.frame_var "round" (by decide))
    (hr.frame_var "removedCount" (by decide))
    (hr.frame_arr "activeA" (by decide))
    (hr.frame_arr "activeB" (by decide))
    (hr.frame_arr "roundStart" (by decide))
    (hr.frame_arr "roundEnd" (by decide))
    (hr.frame_arr "removed" (by decide))
    (hr.frame_arr "removedRep" (by decide))
  by_cases hg : τ.vars "good" = 1
  · have hcandidate := (hsnap hg).candidate
    have hnB' : n < B := by omega
    obtain ⟨τ', hcommit, hfront, hrnext, hacnext, hstoreNext⟩ :=
      Lax235315Proofs.Construction.RecordedCommit.CertificateSnapshot.commit_stored_run
        (hsnap hg) hstoreτ hc hn hnB' (by rwa [hac])
    have hrun := hr.seq
      (Run.ite_true (d := .assign "acount" (.lit 0))
        (b := .eq (.var "good") (.lit 1))
        (by simpa only [hg, beq_self_eq_true] using htestEval) hcommit)
    refine ⟨τ', hrun.mono ?_, Or.inl ⟨hfront, ?_, ?_, hstoreNext⟩⟩
    · simp only [Cond.size, Expr.size]; omega
    · rwa [hround] at hrnext
    · calc
        τ'.vars "acount" = τ.vars "nextACount" := hacnext
        _ = (activeVertices n (view τ "nextA")).card := hcandidate.nextCount
        _ ≤ τ.vars "acount" / 2 + c ^ 2 := hcandidate.shrinks
        _ = σ.vars "acount" / 2 + c ^ 2 := by rw [hac]
  · let τ' := τ.setVar "acount" 0
    have hreset : Run B (.assign "acount" (.lit 0)) τ τ' 2 :=
      Run.assign (evalB_lit (by omega))
    have hrun := hr.seq
      (Run.ite_false (c := commitReduction) (b := .eq (.var "good") (.lit 1))
        (by simpa only [beq_eq_false_iff_ne.mpr hg] using htestEval) hreset)
    refine ⟨τ', hrun.mono ?_, Or.inr ⟨?_, ?_⟩⟩
    · simp only [Cond.size, Expr.size]; omega
    · simpa [τ'] using hg
    · simp [τ']

lemma dispatchRound_run_stored {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env} {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hstore : Stored G bound σ)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W)
    (hWr : ∀ v ∈ W, v < n)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B dispatchRound σ σ' (2300 * (x.length + 1) + 4) ∧
      ((Frontier B c n x σ' ∧ σ'.vars "round" = σ.vars "round" + 1 ∧
          σ'.vars "acount" ≤ σ.vars "acount" / 2 + c ^ 2 ∧
          Nonempty (Stored G bound σ')) ∨
        (σ'.vars "good" ≠ 1 ∧ σ'.vars "acount" = 0)) := by
  have htest := evalB_condEq (evalB_var (h.workspace.bounded.vars "collision"))
    (evalB_lit (by omega : 0 < B))
  by_cases hcollision : σ.vars "collision" = 0
  · obtain ⟨τ, hr, hout⟩ := certifiedBranch_run_stored hx hG h hstore hc hn
      hlarge hcsq hbound henum hWr hnB htargetB hdenomB hboundB
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
binary suffix, carrying the graph history stored in its concrete log arrays. -/
lemma reductionRound_run_stored {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hstore : Stored G bound σ)
    (hc : 1 ≤ c) (hn : 1 < n)
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
          σ'.vars "acount" ≤ σ.vars "acount" / 2 + c ^ 2 ∧
          Nonempty (Stored G bound σ')) ∨
        (σ'.vars "good" ≠ 1 ∧ σ'.vars "acount" = 0)) := by
  have ha : 0 < σ.vars "acount" := by omega
  have hs := Sampling.sampleSize_le_self hc ha
  obtain ⟨bits, τ, ord, hp, hcost, hfront, hinp, hord, hprefix, hcollisions,
      hbitsCanonical, hkeyBound, hsortedBound, hrange, hcard⟩ :=
    SamplingFrontier.run h htape hqB (by omega) (by omega) hs
  have hac := hp.frame_var "acount" (by decide)
  have hrnd := hp.frame_var "round" (by decide)
  have hcsq' := (hp.frame_var "csq" (by decide)).trans hcsq
  have hbound' := (hp.frame_var "nearBound" (by decide)).trans hbound
  have hstoreτ := hstore.frame
    (hp.frame_var "round" (by decide))
    (hp.frame_var "removedCount" (by decide))
    (hp.frame_arr "activeA" (by decide))
    (hp.frame_arr "activeB" (by decide))
    (hp.frame_arr "roundStart" (by decide))
    (hp.frame_arr "roundEnd" (by decide))
    (hp.frame_arr "removed" (by decide))
    (hp.frame_arr "removedRep" (by decide))
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
  obtain ⟨τ', hd, hout⟩ := dispatchRound_run_stored hx hG hfront hstoreτ hc hn
    (by rwa [hac]) hcsq' hbound' hpref hrange hnB htargetB hdenomB hboundB
  have hrun : Run B reductionRound σ τ'
      (4500 * (x.length + 1) + 120 * Nat.clog 2 n * σ.vars "acount") := by
    apply (sampling_dispatch hp hd).mono
    have hlen := hx.length_eq
    omega
  refine ⟨τ', hrun, h.workspace.reductionRound hrun, ?_, ?_⟩
  · exact (hd.frame_inp (by decide)).trans hinp
  · simpa only [hac, hrnd] using hout

end Lax235315Proofs.Construction.HistoryRoundSource
