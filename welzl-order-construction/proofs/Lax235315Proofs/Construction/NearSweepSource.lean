import Lax235315Proofs.Construction.NearSweepMath
import Lax11Proofs.CCGraph
import Mathlib.Tactic

/-! Composition of neighborhood collection and counter accumulation for the
outer CSR sweep of the batched near-twin verifier. -/

namespace Lax235315Proofs.Construction.NearSweepSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax11Proofs.CC
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearAccumulateSource
open Lax235315Proofs.Construction.NearCollectSource
open Lax235315Proofs.Construction.NeighborScan
open Lax235315Proofs.Construction.NearSweepMath
open Lax235315Proofs.Construction.WelzlProgram

/-- State between iterations of the outer near-verification sweep. -/
def NearSweepInv (B n targetCap : ℕ)
    (target off activeA activeB rep : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ stamp neighbors : ℕ → ℕ,
    τ.vars "a" ≤ n ∧ τ.vars "n" = n ∧
    τ.arrs "off" = arrOf (n + 1) off ∧
    τ.arrs "tgt" = arrOf targetCap target ∧
    τ.arrs "activeA" = arrOf n activeA ∧
    τ.arrs "activeB" = arrOf n activeB ∧
    τ.arrs "repB" = arrOf n rep ∧
    τ.arrs "stamp" = arrOf n stamp ∧
    τ.arrs "neighbors" = arrOf n neighbors ∧
    τ.arrs "degree" = arrOf n
      (degreePrefix target off activeA activeB (τ.vars "a")) ∧
    τ.arrs "inter" = arrOf n
      (commonPrefix target off activeA activeB rep (τ.vars "a")) ∧
    (∀ v < n, stamp v ≤ τ.vars "a") ∧
    ∀ v < n, stamp v < B

/-- State after processing active vertex `a`, before incrementing the outer
loop counter. -/
def ProcessActivePost (B n targetCap a : ℕ)
    (target off activeA activeB rep : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ stamp neighbors : ℕ → ℕ,
    τ.vars "a" = a ∧ τ.vars "n" = n ∧
    τ.arrs "off" = arrOf (n + 1) off ∧
    τ.arrs "tgt" = arrOf targetCap target ∧
    τ.arrs "activeA" = arrOf n activeA ∧
    τ.arrs "activeB" = arrOf n activeB ∧
    τ.arrs "repB" = arrOf n rep ∧
    τ.arrs "stamp" = arrOf n stamp ∧
    τ.arrs "neighbors" = arrOf n neighbors ∧
    τ.arrs "degree" = arrOf n
      (degreePrefix target off activeA activeB (a + 1)) ∧
    τ.arrs "inter" = arrOf n
      (commonPrefix target off activeA activeB rep (a + 1)) ∧
    (∀ v < n, stamp v ≤ a + 1) ∧
    ∀ v < n, stamp v < B

/-- The active branch of one outer sweep iteration. -/
theorem processActiveNearBody_run
    {B n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB rep : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    (hI : NearSweepInv B n targetCap target off activeA activeB rep σ)
    (halt : σ.vars "a" < n) (ha : activeA (σ.vars "a") = 1)
    (hactiveBB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hnB : n + 1 < B) (htargetCapB : targetCap < B) :
    ∃ σ', Run B processActiveNearBody σ σ'
        (200 * (off (σ.vars "a" + 1) - off (σ.vars "a") + 1)) ∧
      ProcessActivePost B n targetCap (σ.vars "a")
        target off activeA activeB rep σ' := by
  rcases hI with ⟨stamp, neighbors, haLe, hn, hoff, htarget, hactiveA,
    hactiveB, hrep, hstamp, hneighbors, hdegree, hinter, hstampLe,
    hstampB⟩
  let a := σ.vars "a"
  let lo := off a
  let hi := off (a + 1)
  let M := neighborBlock target off activeB a
  have haN : a < n := by simpa [a] using halt
  have haB : a < B := haN.trans (by omega)
  have ha1B : a + 1 < B := by omega
  have hlohi : lo ≤ hi := by
    change off a ≤ off (a + 1)
    rw [hoffEq a (Nat.le_of_lt haN), hoffEq (a + 1) (by omega)]
    exact hx.offset_mono a haN
  have hloCap : lo ≤ targetCap := by
    change off a ≤ targetCap
    rw [hoffEq a (Nat.le_of_lt haN),
      show targetCap = offset x n by rw [htargetCap, hx.offset_last]]
    exact offset_mono' hx (Nat.le_of_lt haN) le_rfl
  have hhiCap : hi ≤ targetCap := by
    change off (a + 1) ≤ targetCap
    rw [hoffEq (a + 1) (by omega),
      show targetCap = offset x n by rw [htargetCap, hx.offset_last]]
    exact offset_mono' hx (by omega) le_rfl
  have hloB : lo < B := hloCap.trans_lt htargetCapB
  have hhiB : hi < B := hhiCap.trans_lt htargetCapB
  let σ₁ := σ.setVar "token" (a + 1)
  have rtoken : Run B (.assign "token" (.add (.var "a") (.lit 1)))
      σ σ₁ 4 := by
    apply Run.assign
    exact evalB_bin (evalB_var haB) (evalB_lit (by omega)) ha1B
  let σ₂ := σ₁.setVar "neighborLen" 0
  have rlen : Run B (.assign "neighborLen" (.lit 0)) σ₁ σ₂ 2 := by
    simpa [σ₂] using Run.assign (evalB_lit (by omega : 0 < B))
  have hloGet : (σ₂.arrs "off")[σ₂.vars "a"]? = some lo := by
    have hai : σ₂.vars "a" < n + 1 := by simp [σ₂, σ₁, a]; omega
    rw [show σ₂.arrs "off" = σ.arrs "off" by simp [σ₂, σ₁], hoff,
      getElem?_arrOf off hai]
    simp [σ₂, σ₁, lo, a]
  have hloEval : (Expr.get "off" (.var "a")).evalB B σ₂ = some lo := by
    apply evalB_get
    · exact evalB_var (by simp [σ₂, σ₁]; exact haB)
    · exact hloGet
    · exact hloB
  let σ₃ := σ₂.setVar "j" lo
  have rj : Run B (.assign "j" (.get "off" (.var "a"))) σ₂ σ₃ 6 :=
    (Run.assign hloEval).mono (by norm_num [Expr.size])
  have haAddEval : (Expr.add (.var "a") (.lit 1)).evalB B σ₃ =
      some (a + 1) := by
    apply evalB_bin
    · exact evalB_var (by simp [σ₃, σ₂, σ₁]; exact haB)
    · exact evalB_lit (by omega)
    · exact ha1B
  have hhiGet : (σ₃.arrs "off")[a + 1]? = some hi := by
    simp [σ₃, σ₂, σ₁, hoff, getElem?_arrOf off (show a + 1 < n + 1 by
      omega), hi]
  have hhiEval : (Expr.get "off" (.add (.var "a") (.lit 1))).evalB B σ₃ =
      some hi := evalB_get haAddEval hhiGet hhiB
  let σ₄ := σ₃.setVar "jend" hi
  have rjend : Run B
      (.assign "jend" (.get "off" (.add (.var "a") (.lit 1))))
      σ₃ σ₄ 8 := (Run.assign hhiEval).mono (by norm_num [Expr.size])
  have hcollectInit : NeighborInv B n targetCap lo hi (a + 1)
      activeB target σ₄ := by
    apply neighborInv_initial (stamp := stamp) (neighbors := neighbors)
    · simp [σ₄, σ₃]
    · simp [σ₄]
    · simp [σ₄, σ₃, σ₂, σ₁]
    · simp [σ₄, σ₃, σ₂, σ₁, hn]
    · exact hlohi
    · exact hhiCap
    · simp [σ₄, σ₃, σ₂, σ₁, hactiveB]
    · simp [σ₄, σ₃, σ₂, σ₁, htarget]
    · simp [σ₄, σ₃, σ₂, σ₁, hstamp]
    · simp [σ₄, σ₃, σ₂, σ₁, hneighbors]
    · simp [σ₄, σ₃, σ₂, σ₁]
    · intro v hv heq
      have := hstampLe v hv
      omega
    · intro v hv
      have := hstampLe v hv
      omega
    · exact hstampB
  have htargetRange : ∀ j, lo ≤ j → j < hi → target j < n := by
    intro j hlj hjh
    rw [htargetEq j (hjh.trans_le hhiCap)]
    exact hx.target_lt j (by rw [← htargetCap]; exact hjh.trans_le hhiCap)
  obtain ⟨σ₅, rcollect, hcollect, hjDone⟩ :=
    collectNeighborLoop_run hcollectInit htargetRange hactiveBB
      (by omega) htargetCapB ha1B (by omega)
  rcases hcollect with ⟨stamp', neighbors', hlo₅, hjhi₅, hjend₅,
    htoken₅, hn₅, hhi₅, hactiveB₅, htarget₅, hstamp₅, hstack₅,
    henum₅, hstampMem₅, hstampLe₅, hstampB₅⟩
  have hMdef : activeTargets target activeB lo hi = M := rfl
  have hheight : (activeTargets target activeB lo hi).card ≤ n := by
    exact card_activeTargets_le htargetRange
  have hMcardInterval : (activeTargets target activeB lo hi).card ≤ hi - lo :=
    card_activeTargets_le_interval
  have henumFinal : PrefixEnumerates
      (activeTargets target activeB lo hi).card neighbors'
      (activeTargets target activeB lo hi) := by
    simpa [hjDone] using henum₅
  have hstampMemFinal : ∀ v < n, stamp' v = a + 1 ↔
      v ∈ activeTargets target activeB lo hi := by
    intro v hv
    simpa [hjDone] using hstampMem₅ v hv
  let σ₆ := σ₅.setVar "i" 0
  have ri : Run B (.assign "i" (.lit 0)) σ₅ σ₆ 2 := by
    simpa [σ₆] using Run.assign (evalB_lit (by omega : 0 < B))
  have hdegree₅ : σ₅.arrs "degree" = arrOf n
      (degreePrefix target off activeA activeB a) := by
    rw [rcollect.frame_arr "degree" (by
      simp [collectNeighborBody, seqs, inc, Com.warrs])]
    simpa [σ₄, σ₃, σ₂, σ₁, a] using hdegree
  have hinter₅ : σ₅.arrs "inter" = arrOf n
      (commonPrefix target off activeA activeB rep a) := by
    rw [rcollect.frame_arr "inter" (by
      simp [collectNeighborBody, seqs, inc, Com.warrs])]
    simpa [σ₄, σ₃, σ₂, σ₁, a] using hinter
  have hrep₅ : σ₅.arrs "repB" = arrOf n rep := by
    rw [rcollect.frame_arr "repB" (by
      simp [collectNeighborBody, seqs, inc, Com.warrs])]
    simpa [σ₄, σ₃, σ₂, σ₁] using hrep
  have hneighbors₅ : σ₅.arrs "neighbors" = arrOf n neighbors' :=
    hstack₅.arr
  have hneighborLen₅ : σ₅.vars "neighborLen" =
      (activeTargets target activeB lo hi).card := by
    simpa [hjDone] using hstack₅.height
  have haccInit : AccumulateInv n
      (activeTargets target activeB lo hi).card (a + 1) neighbors' rep
      (degreePrefix target off activeA activeB a)
      (commonPrefix target off activeA activeB rep a)
      (activeTargets target activeB lo hi) σ₆ := by
    apply accumulateInv_initial (stamp := stamp')
    · simp [σ₆]
    · exact hheight
    · simp [σ₆, hn₅]
    · simp [σ₆, hneighborLen₅]
    · simp [σ₆, htoken₅]
    · simp [σ₆, hneighbors₅]
    · simp [σ₆, hrep₅]
    · simp [σ₆, hstamp₅]
    · exact hstampMemFinal
    · intro v hv
      exact (hstampLe₅ v hv).trans_lt (by omega)
    · simp [σ₆, hdegree₅]
    · simp [σ₆, hinter₅]
    · exact henumFinal
  have hvertexN : ∀ q ∈ activeTargets target activeB lo hi, q < n := by
    intro q hq
    rw [mem_activeTargets] at hq
    obtain ⟨-, j, hlj, hjh, rfl⟩ := hq
    exact htargetRange j hlj hjh
  have hrepRange : ∀ q ∈ activeTargets target activeB lo hi, rep q < n := by
    intro q hq
    have hmem := (mem_activeTargets.mp hq).1
    exact hrepN q (hvertexN q hq) hmem
  have hdegreeB' : ∀ q ∈ activeTargets target activeB lo hi,
      degreePrefix target off activeA activeB a q + 1 < B := by
    intro q hq
    have := degreePrefix_le target off activeA activeB a q
    omega
  have hinterB' : ∀ q ∈ activeTargets target activeB lo hi,
      commonPrefix target off activeA activeB rep a q + 1 < B := by
    intro q hq
    have := commonPrefix_le target off activeA activeB rep a q
    omega
  obtain ⟨σ₇, racc, hacc, hiDone, hdegree₇, hinter₇⟩ :=
    accumulateNearLoop_run haccInit hnB hvertexN hrepRange hdegreeB' hinterB'
  have hstatic (name : String)
      (hwrite : name ≠ "degree" ∧ name ≠ "inter") :
      σ₇.arrs name = σ₅.arrs name := by
    rw [racc.frame_arr name (by
      simp [accumulateNearBody, seqs, inc, Com.warrs, hwrite.1, hwrite.2])]
    simp [σ₆]
  refine ⟨σ₇, ?_, ?_⟩
  · have hrun := rtoken.seq (rlen.seq (rj.seq (rjend.seq
      (rcollect.seq (ri.seq racc)))))
    have hrun' : Run B processActiveNearBody σ σ₇
        (200 * (hi - lo + 1)) := by
      simpa [processActiveNearBody, seqs] using hrun.mono (by
        have hc := hMcardInterval
        omega)
    simpa [hi, lo, a] using hrun'
  · refine ⟨stamp', neighbors',
      ?_, -- `a`
      ?_, -- `n`
      ?_, -- offsets
      ?_, -- targets
      ?_, -- active A
      ?_, -- active B
      ?_, -- representatives
      ?_, -- stamps
      ?_, -- neighbor stack
      ?_, -- degrees
      ?_, -- intersections
      ?_, -- stamp order
      ?_⟩ -- stamp word bound
    · calc
        σ₇.vars "a" = σ₆.vars "a" := racc.frame_var "a" (by
          simp [accumulateNearBody, seqs, inc, Com.wvars])
        _ = σ₅.vars "a" := by simp [σ₆]
        _ = σ₄.vars "a" := rcollect.frame_var "a" (by
          simp [collectNeighborBody, seqs, inc, Com.wvars])
        _ = a := by simp [σ₄, σ₃, σ₂, σ₁, a]
    · rw [racc.frame_var "n" (by
        simp [accumulateNearBody, seqs, inc, Com.wvars])]
      simp [σ₆, hn₅]
    · rw [hstatic "off" (by decide), rcollect.frame_arr "off" (by
        simp [collectNeighborBody, seqs, inc, Com.warrs])]
      simp [σ₄, σ₃, σ₂, σ₁, hoff]
    · rw [hstatic "tgt" (by decide)]
      exact htarget₅
    · rw [hstatic "activeA" (by decide), rcollect.frame_arr "activeA" (by
        simp [collectNeighborBody, seqs, inc, Com.warrs])]
      simp [σ₄, σ₃, σ₂, σ₁, hactiveA]
    · rw [hstatic "activeB" (by decide)]
      exact hactiveB₅
    · rw [hstatic "repB" (by decide)]
      exact hrep₅
    · rw [hstatic "stamp" (by decide)]
      exact hstamp₅
    · rw [hstatic "neighbors" (by decide)]
      exact hneighbors₅
    · rw [degreePrefix_succ_of_active (by simpa [a] using ha)]
      simpa [hMdef] using hdegree₇
    · rw [commonPrefix_succ_of_active (by simpa [a] using ha)]
      simpa [hMdef] using hinter₇
    · exact hstampLe₅
    · exact hstampB₅

/-- One outer sweep iteration advances the exact prefix semantics by one
vertex.  Its charge is proportional to the size of that vertex's CSR block,
including one unit for an empty block. -/
theorem sweepNearBody_run
    {B n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB rep : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    (hactiveAB : ∀ v < n, activeA v < B)
    (hactiveBB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hnB : n + 1 < B) (htargetCapB : targetCap < B)
    (hI : NearSweepInv B n targetCap target off activeA activeB rep σ)
    (halt : σ.vars "a" < n) :
    ∃ σ', Run B sweepNearBody σ σ'
        (210 * (off (σ.vars "a" + 1) - off (σ.vars "a") + 1)) ∧
      NearSweepInv B n targetCap target off activeA activeB rep σ' ∧
      σ'.vars "a" = σ.vars "a" + 1 := by
  have hI₀ := hI
  rcases hI with ⟨stamp, neighbors, haLe, hn, hoff, htarget, hactiveA,
    hactiveB, hrep, hstamp, hneighbors, hdegree, hinter, hstampLe,
    hstampB⟩
  let a := σ.vars "a"
  have haN : a < n := by simpa [a] using halt
  have haB : a < B := by omega
  have ha1B : a + 1 < B := by omega
  have hactiveGet : (σ.arrs "activeA")[a]? = some (activeA a) := by
    rw [hactiveA, getElem?_arrOf activeA haN]
  have hactiveEval : (Expr.get "activeA" (.var "a")).evalB B σ =
      some (activeA a) :=
    evalB_get (evalB_var (by simpa [a] using haB)) hactiveGet
      (hactiveAB a haN)
  let test := Cond.eq (.get "activeA" (.var "a")) (.lit 1)
  by_cases ha : activeA a = 1
  · have htest : test.evalB B σ = some true := by
      simpa [test, ha] using evalB_condEq hactiveEval
        (evalB_lit (by omega : 1 < B))
    obtain ⟨σ₁, ractive, hpost⟩ := processActiveNearBody_run hx
      htargetCap hoffEq htargetEq hI₀ halt (by simpa [a] using ha)
      hactiveBB hrepN hnB htargetCapB
    rcases hpost with ⟨stamp', neighbors', ha₁, hn₁, hoff₁, htarget₁,
      hactiveA₁, hactiveB₁, hrep₁, hstamp₁, hneighbors₁, hdegree₁,
      hinter₁, hstampLe₁, hstampB₁⟩
    let σ₂ := σ₁.setVar "a" (a + 1)
    have rinc : Run B (inc "a") σ₁ σ₂ 4 := by
      apply Run.assign
      have ha₁eq : σ₁.vars "a" = a := by simpa [a] using ha₁
      have ha₁B : σ₁.vars "a" < B := by rw [ha₁eq]; exact haB
      have hva : (Expr.var "a").evalB B σ₁ = some a := by
        have h := evalB_var ha₁B
        rwa [ha₁eq] at h
      exact evalB_bin hva (evalB_lit (by omega)) (by simp; exact ha1B)
    have hrun : Run B sweepNearBody σ σ₂
        (210 * (off (a + 1) - off a + 1)) := by
      have rite : Run B (.ite test processActiveNearBody .skip) σ σ₁
          (1 + test.size +
            200 * (off (σ.vars "a" + 1) - off (σ.vars "a") + 1)) :=
        Run.ite_true htest ractive
      have r := Run.seq rite rinc
      simpa [sweepNearBody, seqs, test, a] using r.mono (by
        have : 0 < off (a + 1) - off a + 1 := by omega
        norm_num [test, Cond.size, Expr.size]
        omega)
    refine ⟨σ₂, hrun, ?_, by simp [σ₂, a]⟩
    refine ⟨stamp', neighbors', by simp [σ₂, a]; omega,
      by simp [σ₂, hn₁], by simp [σ₂, hoff₁],
      by simp [σ₂, htarget₁], by simp [σ₂, hactiveA₁],
      by simp [σ₂, hactiveB₁], by simp [σ₂, hrep₁],
      by simp [σ₂, hstamp₁], by simp [σ₂, hneighbors₁],
      ?_, ?_, ?_, hstampB₁⟩
    · simpa [σ₂, a] using hdegree₁
    · simpa [σ₂, a] using hinter₁
    · simpa [σ₂, a] using hstampLe₁
  · have htest : test.evalB B σ = some false := by
      simpa [test, ha] using evalB_condEq hactiveEval
        (evalB_lit (by omega : 1 < B))
    let σ₁ := σ.setVar "a" (a + 1)
    have rinc : Run B (inc "a") σ σ₁ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [a] using evalB_var haB)
        (evalB_lit (by omega)) (by simpa [a] using ha1B)
    have hrun : Run B sweepNearBody σ σ₁
        (210 * (off (a + 1) - off a + 1)) := by
      have rite : Run B (.ite test processActiveNearBody .skip) σ σ
          (1 + test.size + 1) := Run.ite_false htest Run.skip
      have r := Run.seq rite rinc
      simpa [sweepNearBody, seqs, test, a] using r.mono (by
        have : 0 < off (a + 1) - off a + 1 := by omega
        norm_num [test, Cond.size, Expr.size]
        omega)
    refine ⟨σ₁, hrun, ?_, by simp [σ₁, a]⟩
    refine ⟨stamp, neighbors, by simp [σ₁, a]; omega,
      by simp [σ₁, hn], by simp [σ₁, hoff],
      by simp [σ₁, htarget], by simp [σ₁, hactiveA],
      by simp [σ₁, hactiveB], by simp [σ₁, hrep],
      by simp [σ₁, hstamp], by simp [σ₁, hneighbors],
      ?_, ?_, ?_, hstampB⟩
    · change σ.arrs "degree" = arrOf n
        (degreePrefix target off activeA activeB (a + 1))
      rw [degreePrefix_succ_of_inactive ha]
      simpa [a] using hdegree
    · change σ.arrs "inter" = arrOf n
        (commonPrefix target off activeA activeB rep (a + 1))
      rw [commonPrefix_succ_of_inactive ha]
      simpa [a] using hinter
    · intro v hv
      have := hstampLe v hv
      simp [σ₁, a]
      omega

/-- Remaining-work potential for the outer sweep.  Advancing an active
vertex consumes its CSR block; advancing any vertex consumes one unit. -/
def nearSweepPotential (n targetCap : ℕ) (off : ℕ → ℕ)
    (τ : Env) : ℕ :=
  220 * ((targetCap - off (τ.vars "a")) + (n - τ.vars "a"))

/-- The complete outer sweep computes all degree and common-neighborhood
counters in time linear in the CSR input size. -/
theorem nearSweepLoop_run
    {B n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB rep : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    (hactiveAB : ∀ v < n, activeA v < B)
    (hactiveBB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hnB : n + 1 < B) (htargetCapB : targetCap < B)
    (hI : NearSweepInv B n targetCap target off activeA activeB rep σ) :
    ∃ σ', Run B (.while (.lt (.var "a") (.var "n")) sweepNearBody)
        σ σ' (nearSweepPotential n targetCap off σ + 4) ∧
      NearSweepInv B n targetCap target off activeA activeB rep σ' ∧
      σ'.vars "a" = n := by
  let I := NearSweepInv B n targetCap target off activeA activeB rep
  let Φ := nearSweepPotential n targetCap off
  have hdef : ∀ τ, I τ → ∃ v,
      (Cond.lt (.var "a") (.var "n")).evalB B τ = some v := by
    intro τ hτ
    rcases hτ with ⟨_, _, haLe, hn, -⟩
    apply evalB_condLt_vars
    · exact haLe.trans_lt (by omega)
    · rw [hn]
      omega
  have hstep : ∀ τ, I τ →
      (Cond.lt (.var "a") (.var "n")).evalB B τ = some true →
      ∃ τ' K, Run B sweepNearBody τ τ' K ∧ I τ' ∧
        1 + (Cond.lt (.var "a") (.var "n")).size + K + Φ τ' ≤
          Φ τ := by
    intro τ hτ hcond
    have haltVar := lt_of_condLt_true hcond
    have hn : τ.vars "n" = n := by
      rcases hτ with ⟨_, _, _, hn, -⟩
      exact hn
    have halt : τ.vars "a" < n := by simpa [hn] using haltVar
    obtain ⟨τ', rbody, hτ', ha'⟩ := sweepNearBody_run hx htargetCap
      hoffEq htargetEq hactiveAB hactiveBB hrepN hnB htargetCapB hτ halt
    let a := τ.vars "a"
    have haN : a < n := by simpa [a] using halt
    have hoffMono : off a ≤ off (a + 1) := by
      rw [hoffEq a (Nat.le_of_lt haN), hoffEq (a + 1) (by omega)]
      exact hx.offset_mono a haN
    have hoffCap : off a ≤ targetCap := by
      rw [hoffEq a (Nat.le_of_lt haN),
        show targetCap = offset x n by rw [htargetCap, hx.offset_last]]
      exact offset_mono' hx (Nat.le_of_lt haN) le_rfl
    have hoffNextCap : off (a + 1) ≤ targetCap := by
      rw [hoffEq (a + 1) (by omega),
        show targetCap = offset x n by rw [htargetCap, hx.offset_last]]
      exact offset_mono' hx (by omega) le_rfl
    refine ⟨τ', 210 * (off (τ.vars "a" + 1) - off (τ.vars "a") + 1),
      rbody, hτ', ?_⟩
    dsimp [Φ, nearSweepPotential]
    rw [ha']
    change 4 + 210 * (off (a + 1) - off a + 1) +
        220 * ((targetCap - off (a + 1)) + (n - (a + 1))) ≤
      220 * ((targetCap - off a) + (n - a))
    omega
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential I Φ hdef hstep hI
  have hn' : σ'.vars "n" = n := by
    rcases hI' with ⟨_, _, _, hn', -⟩
    exact hn'
  have haLe : σ'.vars "a" ≤ n := by
    rcases hI' with ⟨_, _, haLe, -⟩
    exact haLe
  have haFinal : σ'.vars "a" = n := by
    have hge := le_of_condLt_false hfalse
    rw [hn'] at hge
    omega
  have hoffLast : off n = targetCap := by
    rw [hoffEq n le_rfl, hx.offset_last, ← htargetCap]
  have hPhiFinal : Φ σ' = 0 := by
    simp [Φ, nearSweepPotential, haFinal, hoffLast]
  refine ⟨σ', hrun.mono ?_, hI', haFinal⟩
  rw [hPhiFinal] at hpay
  norm_num [Cond.size, Expr.size] at hpay
  exact hpay

end Lax235315Proofs.Construction.NearSweepSource
