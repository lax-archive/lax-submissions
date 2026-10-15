import Lax457868Proofs.ReusedOriginal.Construction.VerifyNearSource
import Mathlib.Tactic

/-!
Adapter from the audited CSR degree/intersection sweep to exact restricted
neighborhood distances on the active ground set.
-/

namespace Lax457868Proofs.BatchedDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open scoped symmDiff
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.NearCheckSource
open Lax457868Proofs.ReusedOriginal.Construction.NearCounterCorrectness
open Lax457868Proofs.ReusedOriginal.Construction.NearSweepMath
open Lax457868Proofs.ReusedOriginal.Construction.NearSweepSource
open Lax457868Proofs.ReusedOriginal.Construction.VerifyNearSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- Clear the counters and then run the batched CSR sweep.  The final
threshold-check loop is intentionally absent: this pass exposes every
numeric distance for later sampling logic. -/
def batchedDistanceSweep : Com :=
  seqs [prepareNearSweep,
    .while (.lt (.var "a") (.var "n")) sweepNearBody]

/-- One invocation computes all active-A degrees and representative
intersections in one CSR sweep.  The result retains the representative map,
both active masks, and the graph's CSR arrays. -/
lemma batchedDistanceSweep_run
    {B n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB rep : ℕ → ℕ}
    {degree inter stamp neighbors : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap,
      target j = Lax11.GraphEncoding.target x j)
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
    (hactiveAB : ∀ v < n, activeA v < B)
    (hactiveBB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hrepActive : ∀ v < n, activeB v = 1 → activeB (rep v) = 1)
    (hnB : n + 1 < B)
    (htargetCapB : targetCap < B) :
    ∃ σ', Run B batchedDistanceSweep σ σ'
        (300 * (n + targetCap + 1)) ∧
      σ'.arrs "degree" =
        arrOf n (degreePrefix target off activeA activeB n) ∧
      σ'.arrs "inter" =
        arrOf n (commonPrefix target off activeA activeB rep n) ∧
      σ'.arrs "off" = arrOf (n + 1) off ∧
      σ'.arrs "tgt" = arrOf targetCap target ∧
      σ'.arrs "activeA" = arrOf n activeA ∧
      σ'.arrs "activeB" = arrOf n activeB ∧
      σ'.arrs "repB" = arrOf n rep ∧
      σ'.vars "n" = n ∧
      σ'.inp = σ.inp ∧
      σ'.out = σ.out ∧
      ∀ (b : ℕ) (hbN : b < n) (hb : activeB b = 1),
        nearDistance
            (degreePrefix target off activeA activeB n)
            (commonPrefix target off activeA activeB rep n) rep b =
          ((G.neighborSet ⟨b, hbN⟩ ∩
              (activeFinset (n := n) activeA : Set (Fin n))) ∆
            (G.neighborSet ⟨rep b, hrepN b hbN hb⟩ ∩
              (activeFinset (n := n) activeA : Set (Fin n)))).ncard := by
  have hnltB : n < B := by omega
  obtain ⟨σ₁, rprepare, hprepared, haZero⟩ :=
    prepareNearSweep_run hn hoff htarget hactiveA hactiveB hrep hdegree
      hinter hstamp hneighbors hnltB
  obtain ⟨σ₂, rsweep, hfinished, haFinal⟩ :=
    nearSweepLoop_run hx htargetCap hoffEq htargetEq hactiveAB hactiveBB
      hrepN hnB htargetCapB hprepared
  have hoffZero : off 0 = 0 := by
    rw [hoffEq 0 (by omega), hx.offset_zero]
  have hpotential : nearSweepPotential n targetCap off σ₁ + 4 =
      220 * (targetCap + n) + 4 := by
    simp [nearSweepPotential, haZero, hoffZero]
  have hcost : 33 * n + 20 +
      (nearSweepPotential n targetCap off σ₁ + 4) ≤
      300 * (n + targetCap + 1) := by
    rw [hpotential]
    omega
  rcases hfinished with
    ⟨stamp', neighbors', ha, hn', hoff', htarget', hactiveA',
      hactiveB', hrep', hstamp', hneighbors', hdegree', hinter',
      hstampLe, hstampB⟩
  rw [haFinal] at hdegree' hinter'
  have hr := rprepare.seq rsweep
  have hinp := hr.frame_inp (by
    simp [prepareNearSweep, sweepNearBody,
      processActiveNearBody, collectNeighborBody, accumulateNearBody,
      clearArray, seqs, inc, Com.reads])
  have hout := hr.out_eq (by
    simp [prepareNearSweep, sweepNearBody,
      processActiveNearBody, collectNeighborBody, accumulateNearBody,
      clearArray, seqs, inc, Com.NoWrite])
  refine ⟨σ₂, ?_, hdegree', hinter', hoff', htarget', hactiveA',
    hactiveB', hrep', hn', hinp, hout, ?_⟩
  · simpa [batchedDistanceSweep, seqs] using hr.mono hcost
  · intro b hbN hb
    exact nearDistance_eq_neighborhood_symmDiff hx htargetCap hoffEq
      htargetEq hbN (hrepN b hbN hb) hb (hrepActive b hbN hb)

end Lax457868Proofs.BatchedDistances
