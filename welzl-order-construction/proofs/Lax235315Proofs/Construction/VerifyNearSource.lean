import Lax235315Proofs.Construction.NearCounterCorrectness
import Lax235315Proofs.Construction.WelzlStraight
import Mathlib.Tactic

/-! End-to-end source verification of the batched near-twin checker. -/

namespace Lax235315Proofs.Construction.VerifyNearSource

open scoped symmDiff
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.NearCheckSource
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.NearSweepMath
open Lax235315Proofs.Construction.NearSweepSource
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlStraight

/-- The three clears and the outer-counter reset establish the exact empty
prefix invariant of the batched sweep. -/
theorem prepareNearSweep_run
    {B n targetCap : ℕ} {target off activeA activeB rep : ℕ → ℕ}
    {degree inter stamp neighbors : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n)
    (hoff : σ.arrs "off" = arrOf (n + 1) off)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hactiveA : σ.arrs "activeA" = arrOf n activeA)
    (hactiveB : σ.arrs "activeB" = arrOf n activeB)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hneighbors : σ.arrs "neighbors" = arrOf n neighbors)
    (hnB : n < B) :
    ∃ σ', Run B prepareNearSweep σ σ' (33 * n + 20) ∧
      NearSweepInv B n targetCap target off activeA activeB rep σ' ∧
      σ'.vars "a" = 0 := by
  obtain ⟨σ₁, degree₁, rdegree, hdegree₁, hzeroDegree⟩ :=
    clearArray_run hdegree hn (by decide) hnB
  have hn₁ : σ₁.vars "n" = n := by
    rw [rdegree.frame_var "n" (by decide), hn]
  have hinter₁ : σ₁.arrs "inter" = arrOf n inter := by
    rw [rdegree.frame_arr "inter" (by decide), hinter]
  obtain ⟨σ₂, inter₂, rinter, hinter₂, hzeroInter⟩ :=
    clearArray_run hinter₁ hn₁ (by decide) hnB
  have hn₂ : σ₂.vars "n" = n := by
    rw [rinter.frame_var "n" (by decide), hn₁]
  have hstamp₂ : σ₂.arrs "stamp" = arrOf n stamp := by
    rw [rinter.frame_arr "stamp" (by decide),
      rdegree.frame_arr "stamp" (by decide), hstamp]
  obtain ⟨σ₃, stamp₃, rstamp, hstamp₃, hzeroStamp⟩ :=
    clearArray_run hstamp₂ hn₂ (by decide) hnB
  let σ₄ := σ₃.setVar "a" 0
  have ra : Run B (.assign "a" (.lit 0)) σ₃ σ₄ 2 :=
    Run.assign (evalB_lit (by omega))
  have hstatic (name : String)
      (hd : name ≠ "degree") (hi : name ≠ "inter")
      (hs : name ≠ "stamp") : σ₄.arrs name = σ.arrs name := by
    simp [σ₄]
    rw [rstamp.frame_arr name (by
        simp [clearArray, seqs, inc, Com.warrs, hs]),
      rinter.frame_arr name (by
        simp [clearArray, seqs, inc, Com.warrs, hi]),
      rdegree.frame_arr name (by
        simp [clearArray, seqs, inc, Com.warrs, hd])]
  have hdegree₄ : σ₄.arrs "degree" = arrOf n
      (degreePrefix target off activeA activeB 0) := by
    simp [σ₄]
    rw [rstamp.frame_arr "degree" (by decide),
      rinter.frame_arr "degree" (by decide), hdegree₁]
    apply arrOf_congr
    intro i hi
    rw [hzeroDegree i hi]
    simp
  have hinter₄ : σ₄.arrs "inter" = arrOf n
      (commonPrefix target off activeA activeB rep 0) := by
    simp [σ₄]
    rw [rstamp.frame_arr "inter" (by decide), hinter₂]
    apply arrOf_congr
    intro i hi
    rw [hzeroInter i hi]
    simp
  have hn₄ : σ₄.vars "n" = n := by
    simp [σ₄]
    rw [rstamp.frame_var "n" (by decide), hn₂]
  refine ⟨σ₄, ?_, ?_, by simp [σ₄]⟩
  · have r := rdegree.seq (rinter.seq (rstamp.seq ra))
    simpa [prepareNearSweep, seqs] using r.mono (by omega)
  · refine ⟨stamp₃, neighbors, by simp [σ₄], hn₄,
      by rw [hstatic "off" (by decide) (by decide) (by decide), hoff],
      by rw [hstatic "tgt" (by decide) (by decide) (by decide), htarget],
      by rw [hstatic "activeA" (by decide) (by decide) (by decide), hactiveA],
      by rw [hstatic "activeB" (by decide) (by decide) (by decide), hactiveB],
      by rw [hstatic "repB" (by decide) (by decide) (by decide), hrep],
      by simpa [σ₄] using hstamp₃,
      by rw [hstatic "neighbors" (by decide) (by decide) (by decide), hneighbors],
      by simpa [σ₄] using hdegree₄,
      by simpa [σ₄] using hinter₄, ?_, ?_⟩
    · intro v hv
      rw [hzeroStamp v hv]
      simp [σ₄]
    · intro v hv
      rw [hzeroStamp v hv]
      omega

/-- A successful `verifyNear` run certifies every active set-side vertex as
near its representative on the current active ground set. -/
theorem verifyNear_run
    {B n targetCap bound : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB rep : ℕ → ℕ}
    {degree inter stamp neighbors : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    (hn : σ.vars "n" = n) (hbound : σ.vars "nearBound" = bound)
    (hgoodB : σ.vars "good" < B)
    (hoff : σ.arrs "off" = arrOf (n + 1) off)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hactiveA : σ.arrs "activeA" = arrOf n activeA)
    (hactiveB : σ.arrs "activeB" = arrOf n activeB)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hneighbors : σ.arrs "neighbors" = arrOf n neighbors)
    (hactiveAB : ∀ v < n, activeA v < B)
    (hactiveBB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hrepActive : ∀ v < n, activeB v = 1 → activeB (rep v) = 1)
    (hnB : 2 * n + 1 < B) (htargetCapB : targetCap < B)
    (hboundB : bound < B) :
    ∃ σ', Run B verifyNear σ σ' (400 * (n + targetCap + 1)) ∧
      (σ'.vars "good" = 1 →
        ∀ (v : Fin n) (hv : activeB v.val = 1),
          ((G.neighborSet v ∩
              (activeFinset (n := n) activeA : Set (Fin n))) ∆
            (G.neighborSet ⟨rep v.val, hrepN v.val v.isLt hv⟩ ∩
              (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound) := by
  obtain ⟨σ₁, rprepare, hI₁, haZero⟩ := prepareNearSweep_run (B := B) hn hoff htarget
    hactiveA hactiveB hrep hdegree hinter hstamp hneighbors (by omega)
  obtain ⟨σ₂, rsweep, hI₂, haDone⟩ := nearSweepLoop_run hx htargetCap
    hoffEq htargetEq hactiveAB hactiveBB hrepN (by omega) htargetCapB hI₁
  rcases hI₂ with ⟨stamp₂, neighbors₂, haLe₂, hn₂, hoff₂, htarget₂,
    hactiveA₂, hactiveB₂, hrep₂, hstamp₂, hneighbors₂, hdegree₂,
    hinter₂, hstampLe₂, hstampB₂⟩
  have hprefix := rprepare.seq rsweep
  have hbound₂ : σ₂.vars "nearBound" = bound := by
    rw [rsweep.frame_var "nearBound" (by
        simp [sweepNearBody, processActiveNearBody, collectNeighborBody,
          accumulateNearBody, seqs, inc, Com.wvars]),
      rprepare.frame_var "nearBound" (by
        simp [prepareNearSweep, clearArray, seqs, inc, Com.wvars]), hbound]
  have hgoodB₂ : σ₂.vars "good" < B := by
    rw [rsweep.frame_var "good" (by
        simp [sweepNearBody, processActiveNearBody, collectNeighborBody,
          accumulateNearBody, seqs, inc, Com.wvars]),
      rprepare.frame_var "good" (by
        simp [prepareNearSweep, clearArray, seqs, inc, Com.wvars])]
    exact hgoodB
  obtain ⟨σ₃, rcheck, hchecked⟩ := checkNearLoop_run hn₂ hbound₂
    hgoodB₂ hactiveB₂ hrep₂ (by simpa [haDone] using hdegree₂)
    (by simpa [haDone] using hinter₂) hnB hboundB hactiveBB hrepN
    (fun v hv => degreePrefix_le target off activeA activeB n v)
    (fun v hv => commonPrefix_le target off activeA activeB rep n v)
  refine ⟨σ₃, ?_, ?_⟩
  · have r := rprepare.seq (rsweep.seq rcheck)
    have hoffZero : off 0 = 0 := by
      rw [hoffEq 0 (by omega), hx.offset_zero]
    have hpot : nearSweepPotential n targetCap off σ₁ =
        220 * (targetCap + n) := by
      simp [nearSweepPotential, haZero, hoffZero]
    simpa [verifyNear, seqs, hpot] using r.mono (by omega)
  · intro hgood v hactivev
    have hnum := hchecked hgood v.val v.isLt hactivev
    have hrActive := hrepActive v.val v.isLt hactivev
    rw [nearDistance_eq_neighborhood_symmDiff hx htargetCap hoffEq htargetEq
      v.isLt (hrepN v.val v.isLt hactivev) hactivev hrActive] at hnum
    exact hnum

end Lax235315Proofs.Construction.VerifyNearSource
