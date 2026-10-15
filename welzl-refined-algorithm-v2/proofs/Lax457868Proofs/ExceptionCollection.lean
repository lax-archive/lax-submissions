import Lax457868Proofs.BatchedDistances
import Lax457868Proofs.SamplePacking
import Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight
import Mathlib.Tactic

/-!
Fixed-source collection of the vertices whose restricted neighborhood
distance from their representative exceeds the supplied threshold.
-/

namespace Lax457868Proofs.ExceptionCollection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.BatchedDistances
open Lax457868Proofs.ReusedOriginal.Construction.NearCheckSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

/-- One fixed iteration checks the representative distance for the current
vertex and marks it exactly when it is active and farther than the threshold.
The source reads the representative and both batched counters dynamically. -/
def exceptionBody : Com := seqs [
  .ite (.eq (.get "activeB" (.var "b")) (.lit 1))
    (seqs [
      .assign "r" (.get "repB" (.var "b")),
      .assign "diff" (.sub
        (.add (.get "degree" (.var "b")) (.get "degree" (.var "r")))
        (.mul (.lit 2) (.get "inter" (.var "b")))),
      .ite (.lt (.var "nearBound") (.var "diff"))
        (.store "exceptionFlags" (.var "b") (.lit 1))
        (.store "exceptionFlags" (.var "b") (.lit 0))])
    (.store "exceptionFlags" (.var "b") (.lit 0)),
  inc "b"]

/-- The collector scans every vertex, writing a one for an active exception
and zero for all other vertices. -/
def collectExceptions : Com := seqs [
  .assign "b" (.lit 0),
  .while (.lt (.var "b") (.var "n")) exceptionBody]

/-- The exact mathematical exception set over the bounded vertex range. -/
def exceptionSet (n threshold : ℕ) (activeB rep degree inter : ℕ → ℕ) :
    Finset ℕ :=
  (Finset.range n).filter fun b =>
    activeB b = 1 ∧ threshold < nearDistance degree inter rep b

/-- The scan invariant records the flags in the already processed prefix. -/
def ExceptionInv (n threshold : ℕ) (activeB rep degree inter flags : ℕ → ℕ)
    (τ : Env) : Prop :=
  τ.vars "b" ≤ n ∧ τ.vars "n" = n ∧
  τ.vars "nearBound" = threshold ∧
  τ.arrs "activeB" = arrOf n activeB ∧
  τ.arrs "repB" = arrOf n rep ∧
  τ.arrs "degree" = arrOf n degree ∧
  τ.arrs "inter" = arrOf n inter ∧
  τ.arrs "exceptionFlags" = arrOf n flags ∧
  (∀ v < τ.vars "b", flags v =
    if activeB v = 1 ∧ threshold < nearDistance degree inter rep v then 1 else 0)

/-- The zero-one value written for a vertex by the exception scan. -/
def exceptionValue (threshold : ℕ)
    (activeB rep degree inter : ℕ → ℕ) (b : ℕ) : ℕ :=
  if activeB b = 1 ∧ threshold < nearDistance degree inter rep b then 1 else 0

private lemma upd_prefix {threshold : ℕ} {activeB rep degree inter f : ℕ → ℕ}
    {b x : ℕ}
    (h : ∀ v < b, f v = exceptionValue threshold activeB rep degree inter v)
    (hx : x = exceptionValue threshold activeB rep degree inter b) :
    ∀ v < b + 1,
      upd f b x v = exceptionValue threshold activeB rep degree inter v := by
  intro v hv
  by_cases hvb : v = b
  · subst v
    simpa [upd] using hx
  · have hv' : v < b := by omega
    simpa [upd, hvb] using h v hv'

/-- A single iteration writes the exact flag at the current vertex. -/
lemma exceptionBody_spec
    {B n threshold : ℕ} {activeB rep degree inter : ℕ → ℕ}
    (hnB : 2 * n + 1 < B) (hthresholdB : threshold < B)
    (hactiveB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hdegreeN : ∀ v < n, degree v ≤ n)
    (hinterN : ∀ v < n, inter v ≤ n) :
    Spec B
      (fun τ => (∃ flags, ExceptionInv n threshold activeB rep degree inter flags τ) ∧
        τ.vars "b" < n)
      exceptionBody
      (fun τ τ' => (∃ flags, ExceptionInv n threshold activeB rep degree inter flags τ') ∧
        τ'.vars "b" = τ.vars "b" + 1)
      70 := by
  intro σ hσ
  rcases hσ with ⟨⟨flags, hbLe, hn, hbound, hactive, hrep, hdegree,
    hinter, hflags, hchecked⟩, hbN⟩
  let b := σ.vars "b"
  have hbB : b < B := by omega
  have hb1B : b + 1 < B := by omega
  have hactiveGet : (σ.arrs "activeB")[b]? = some (activeB b) := by
    rw [hactive, getElem?_arrOf activeB hbN]
  have hactiveEval : (Expr.get "activeB" (.var "b")).evalB B σ =
      some (activeB b) :=
    evalB_get (evalB_var (by simpa [b] using hbB)) hactiveGet
      (hactiveB b hbN)
  let activeTest := Cond.eq (.get "activeB" (.var "b")) (.lit 1)
  by_cases hba : activeB b = 1
  · have hactiveTest : activeTest.evalB B σ = some true := by
      simpa [activeTest, hba] using evalB_condEq hactiveEval
        (evalB_lit (by omega : 1 < B))
    let r := rep b
    have hrN : r < n := hrepN b hbN hba
    have hrB : r < B := by omega
    have hrepGet : (σ.arrs "repB")[b]? = some r := by
      rw [hrep, getElem?_arrOf rep hbN]
    have hrepEval : (Expr.get "repB" (.var "b")).evalB B σ = some r :=
      evalB_get (evalB_var (by simpa [b] using hbB)) hrepGet hrB
    let σ₁ := σ.setVar "r" r
    have rr : Run B (.assign "r" (.get "repB" (.var "b"))) σ σ₁ 6 :=
      (Run.assign hrepEval).mono (by norm_num [Expr.size])
    have hdegreeBEval : (Expr.get "degree" (.var "b")).evalB B σ₁ =
        some (degree b) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₁]; exact hbB)
      · simp [σ₁, hdegree, getElem?_arrOf degree hbN, b]
      · exact (hdegreeN b hbN).trans_lt (by omega)
    have hdegreeREval : (Expr.get "degree" (.var "r")).evalB B σ₁ =
        some (degree r) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₁, r]; exact hrB)
      · simp [σ₁, hdegree, getElem?_arrOf degree hrN, r]
      · exact (hdegreeN r hrN).trans_lt (by omega)
    have haddB : degree b + degree r < B := by
      have := hdegreeN b hbN
      have := hdegreeN r hrN
      omega
    have haddEval : (Expr.add (.get "degree" (.var "b"))
        (.get "degree" (.var "r"))).evalB B σ₁ =
        some (degree b + degree r) :=
      evalB_bin hdegreeBEval hdegreeREval (by simpa using haddB)
    have hinterEval : (Expr.get "inter" (.var "b")).evalB B σ₁ =
        some (inter b) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₁]; exact hbB)
      · simp [σ₁, hinter, getElem?_arrOf inter hbN, b]
      · exact (hinterN b hbN).trans_lt (by omega)
    have htwiceB : 2 * inter b < B := by
      have := hinterN b hbN
      omega
    have htwiceEval : (Expr.mul (.lit 2)
        (.get "inter" (.var "b"))).evalB B σ₁ =
        some (2 * inter b) :=
      evalB_bin (evalB_lit (by omega)) hinterEval (by simpa using htwiceB)
    let d := nearDistance degree inter rep b
    have hdB : d < B := by
      dsimp [d, nearDistance, r]
      exact (Nat.sub_le _ _).trans_lt haddB
    have hdiffEval : (Expr.sub
        (.add (.get "degree" (.var "b")) (.get "degree" (.var "r")))
        (.mul (.lit 2) (.get "inter" (.var "b")))).evalB B σ₁ =
        some d := by
      have hsubB : degree b + degree r - 2 * inter b < B :=
        (Nat.sub_le _ _).trans_lt haddB
      simpa [d, nearDistance, r] using
        evalB_bin (op := .sub) haddEval htwiceEval hsubB
    let σ₂ := σ₁.setVar "diff" d
    have rdiff : Run B (.assign "diff"
        (.sub (.add (.get "degree" (.var "b"))
            (.get "degree" (.var "r")))
          (.mul (.lit 2) (.get "inter" (.var "b"))))) σ₁ σ₂ 20 :=
      (Run.assign hdiffEval).mono (by norm_num [Expr.size])
    have hboundEval : (Expr.var "nearBound").evalB B σ₂ = some threshold := by
      rw [show (Expr.var "nearBound").evalB B σ₂ =
        some (σ₂.vars "nearBound") from evalB_var (by
          simp [σ₂, σ₁, hbound]
          exact hthresholdB)]
      simp [σ₂, σ₁, hbound]
    have hdiffVarEval : (Expr.var "diff").evalB B σ₂ = some d := by
      rw [show (Expr.var "diff").evalB B σ₂ = some (σ₂.vars "diff") from
        evalB_var (by simp [σ₂]; exact hdB)]
      simp [σ₂]
    let farTest := Cond.lt (.var "nearBound") (.var "diff")
    by_cases hfar : threshold < d
    · have hfarTest : farTest.evalB B σ₂ = some true := by
        simpa [farTest, hfar] using evalB_condLt hboundEval hdiffVarEval
      let σ₃ := σ₂.setArr "exceptionFlags" b 1
      let σ₄ := σ₃.setVar "b" (b + 1)
      let flags' := upd flags b 1
      have hstore : Run B (.store "exceptionFlags" (.var "b") (.lit 1))
          σ₂ σ₃ 3 := by
        apply Run.store (by simpa [σ₂, σ₁, b] using evalB_var hbB)
          (evalB_lit (by omega))
        simp [σ₂, σ₁, hflags, length_arrOf]
        exact hbN
      have rb : Run B (inc "b") σ₃ σ₄ 4 := by
        apply Run.assign
        exact evalB_bin (by simpa [σ₃, σ₂, σ₁, b] using evalB_var hbB)
          (evalB_lit (by omega)) (by simp; exact hb1B)
      have ractive : Run B
          (seqs [
            .assign "r" (.get "repB" (.var "b")),
            .assign "diff"
              (.sub (.add (.get "degree" (.var "b"))
                  (.get "degree" (.var "r")))
                (.mul (.lit 2) (.get "inter" (.var "b")))),
            .ite (.lt (.var "nearBound") (.var "diff"))
              (.store "exceptionFlags" (.var "b") (.lit 1))
              (.store "exceptionFlags" (.var "b") (.lit 0))]) σ σ₃
          (6 + 20 + (1 + farTest.size + 3)) := by
        simpa [seqs, farTest] using rr.seq (rdiff.seq
          (Run.ite_true hfarTest hstore))
      have hr : Run B exceptionBody σ σ₄ 70 :=
        (Run.seq (Run.ite_true hactiveTest ractive) rb).mono (by
          norm_num [exceptionBody, seqs, activeTest, farTest,
            Cond.size, Expr.size])
      have hflags' : σ₄.arrs "exceptionFlags" = arrOf n flags' := by
        simp [σ₄, σ₃, σ₂, σ₁, hflags, set_arrOf_eq_upd, flags']
      have hx : 1 = exceptionValue threshold activeB rep degree inter b := by
        simp [exceptionValue, hba, d, hfar]
      refine ⟨σ₄, hr, ⟨flags', ?_⟩, by simp [σ₄, b]⟩
      refine ⟨by simp [σ₄, b]; omega,
        by simp [σ₄, σ₃, σ₂, σ₁, hn],
        by simp [σ₄, σ₃, σ₂, σ₁, hbound],
        by simp [σ₄, σ₃, σ₂, σ₁, hactive],
        by simp [σ₄, σ₃, σ₂, σ₁, hrep],
        by simp [σ₄, σ₃, σ₂, σ₁, hdegree],
        by simp [σ₄, σ₃, σ₂, σ₁, hinter], hflags', ?_⟩
      simpa [σ₄, b, flags', exceptionValue] using
        (upd_prefix (f := flags) (b := b) hchecked hx)
    · have hfarTest : farTest.evalB B σ₂ = some false := by
        simpa [farTest, hfar] using evalB_condLt hboundEval hdiffVarEval
      let σ₃ := σ₂.setArr "exceptionFlags" b 0
      let σ₄ := σ₃.setVar "b" (b + 1)
      let flags' := upd flags b 0
      have hstore : Run B (.store "exceptionFlags" (.var "b") (.lit 0))
          σ₂ σ₃ 3 := by
        apply Run.store (by simpa [σ₂, σ₁, b] using evalB_var hbB)
          (evalB_lit (by omega))
        simp [σ₂, σ₁, hflags, length_arrOf]
        exact hbN
      have rb : Run B (inc "b") σ₃ σ₄ 4 := by
        apply Run.assign
        exact evalB_bin (by simpa [σ₃, σ₂, σ₁, b] using evalB_var hbB)
          (evalB_lit (by omega)) (by simp; exact hb1B)
      have ractive : Run B
          (seqs [
            .assign "r" (.get "repB" (.var "b")),
            .assign "diff"
              (.sub (.add (.get "degree" (.var "b"))
                  (.get "degree" (.var "r")))
                (.mul (.lit 2) (.get "inter" (.var "b")))),
            .ite (.lt (.var "nearBound") (.var "diff"))
              (.store "exceptionFlags" (.var "b") (.lit 1))
              (.store "exceptionFlags" (.var "b") (.lit 0))]) σ σ₃
          (6 + 20 + (1 + farTest.size + 3)) := by
        simpa [seqs, farTest] using rr.seq (rdiff.seq
          (Run.ite_false hfarTest hstore))
      have hr : Run B exceptionBody σ σ₄ 70 :=
        (Run.seq (Run.ite_true hactiveTest ractive) rb).mono (by
          norm_num [exceptionBody, seqs, activeTest, farTest,
            Cond.size, Expr.size])
      have hflags' : σ₄.arrs "exceptionFlags" = arrOf n flags' := by
        simp [σ₄, σ₃, σ₂, σ₁, hflags, set_arrOf_eq_upd, flags']
      have hx : 0 = exceptionValue threshold activeB rep degree inter b := by
        simp [exceptionValue, hba, d, hfar]
      refine ⟨σ₄, hr, ⟨flags', ?_⟩, by simp [σ₄, b]⟩
      refine ⟨by simp [σ₄, b]; omega,
        by simp [σ₄, σ₃, σ₂, σ₁, hn],
        by simp [σ₄, σ₃, σ₂, σ₁, hbound],
        by simp [σ₄, σ₃, σ₂, σ₁, hactive],
        by simp [σ₄, σ₃, σ₂, σ₁, hrep],
        by simp [σ₄, σ₃, σ₂, σ₁, hdegree],
        by simp [σ₄, σ₃, σ₂, σ₁, hinter], hflags', ?_⟩
      simpa [σ₄, b, flags', exceptionValue] using
        (upd_prefix (f := flags) (b := b) hchecked hx)
  · have hactiveTest : activeTest.evalB B σ = some false := by
      simpa [activeTest, hba] using evalB_condEq hactiveEval
        (evalB_lit (by omega : 1 < B))
    let σ₁ := σ.setArr "exceptionFlags" b 0
    let σ₂ := σ₁.setVar "b" (b + 1)
    let flags' := upd flags b 0
    have hstore : Run B (.store "exceptionFlags" (.var "b") (.lit 0))
        σ σ₁ 3 := by
      apply Run.store (by simpa [b] using evalB_var hbB)
        (evalB_lit (by omega))
      simp [hflags, length_arrOf]
      exact hbN
    have rb : Run B (inc "b") σ₁ σ₂ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [σ₁, b] using evalB_var hbB)
        (evalB_lit (by omega)) (by simp; exact hb1B)
    have hr : Run B exceptionBody σ σ₂ 70 :=
      (Run.seq (Run.ite_false hactiveTest hstore) rb).mono (by
        norm_num [exceptionBody, seqs, activeTest, Cond.size, Expr.size])
    have hflags' : σ₂.arrs "exceptionFlags" = arrOf n flags' := by
      simp [σ₂, σ₁, hflags, set_arrOf_eq_upd, flags']
    have hx : 0 = exceptionValue threshold activeB rep degree inter b := by
      simp [exceptionValue, hba]
    refine ⟨σ₂, hr, ⟨flags', ?_⟩, by simp [σ₂, b]⟩
    refine ⟨by simp [σ₂, b]; omega,
      by simp [σ₂, σ₁, hn],
      by simp [σ₂, σ₁, hbound],
      by simp [σ₂, σ₁, hactive],
      by simp [σ₂, σ₁, hrep],
      by simp [σ₂, σ₁, hdegree],
      by simp [σ₂, σ₁, hinter], hflags', ?_⟩
    simpa [σ₂, b, flags', exceptionValue] using
      (upd_prefix (f := flags) (b := b) hchecked hx)

/-- The scan executes from any initial flag array. Each cell in range is
overwritten with the exact exception indicator, with linear source cost. -/
lemma collectExceptions_run
    {B n threshold : ℕ} {activeB rep degree inter initialFlags : ℕ → ℕ}
    {σ : Env}
    (hn : σ.vars "n" = n) (hbound : σ.vars "nearBound" = threshold)
    (hactive : σ.arrs "activeB" = arrOf n activeB)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hflags : σ.arrs "exceptionFlags" = arrOf n initialFlags)
    (hnB : 2 * n + 1 < B) (hthresholdB : threshold < B)
    (hactiveB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hdegreeN : ∀ v < n, degree v ≤ n)
    (hinterN : ∀ v < n, inter v ≤ n) :
    ∃ σ', Run B collectExceptions σ σ' (74 * n + 6) ∧
      σ'.arrs "exceptionFlags" = arrOf n
        (exceptionValue threshold activeB rep degree inter) ∧
      σ'.vars "b" = n ∧
      (∀ a, a ≠ "exceptionFlags" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "b" → v ≠ "r" → v ≠ "diff" →
        σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let I := fun τ => ∃ flags, ExceptionInv n threshold activeB rep degree inter flags τ
  have hbody := exceptionBody_spec hnB hthresholdB hactiveB hrepN hdegreeN hinterN
  obtain ⟨σ', hrun, ⟨flags, hbLe, hn', hbound', hactive', hrep', hdegree',
    hinter', hflags', hseen⟩, hbFinal⟩ :=
    (Spec.forRangeZero "b" "n" I n 70 (by omega)
      (fun _ h => by rcases h with ⟨_, hI⟩; exact hI.1)
      (fun _ h => by rcases h with ⟨_, hI⟩; exact hI.2.1)
      hbody).run (σ := σ) (by
        refine ⟨initialFlags, by simp, by simp [hn], by simp [hbound],
          by simp [hactive], by simp [hrep], by simp [hdegree],
          by simp [hinter], by simp [hflags], ?_⟩
        intro v hv
        simp at hv)
  have hflagsExact : σ'.arrs "exceptionFlags" = arrOf n
      (exceptionValue threshold activeB rep degree inter) := by
    rw [hflags']
    apply arrOf_congr
    intro i hi
    have h := hseen i (by simpa [hbFinal] using hi)
    simpa [exceptionValue] using h
  have hrun' : Run B collectExceptions σ σ' (74 * n + 6) := by
    simpa [collectExceptions, seqs] using hrun
  have hframes : ∀ a, a ≠ "exceptionFlags" → σ'.arrs a = σ.arrs a := by
    intro a ha
    exact hrun'.frame_arr a (by
      simp [collectExceptions, exceptionBody, seqs, inc, Com.warrs, ha])
  have hframeVars : ∀ v, v ≠ "b" → v ≠ "r" → v ≠ "diff" →
      σ'.vars v = σ.vars v := by
    intro v hb hr hd
    exact hrun'.frame_var v (by
      simp [collectExceptions, exceptionBody, seqs, inc, Com.wvars, hb, hr, hd])
  have hinp := hrun'.frame_inp (by
    simp [collectExceptions, exceptionBody, seqs, inc, Com.reads])
  have hout := hrun'.out_eq (by
    simp [collectExceptions, exceptionBody, seqs, inc, Com.NoWrite])
  exact ⟨σ', hrun', hflagsExact, hbFinal, hframes, hframeVars, hinp, hout⟩

/-- Append a marked vertex, if present, then advance the scan cursor. -/
private def exceptionPackBody : Com :=
  seqs [
    .ite (.eq (.get "exceptionFlags" (.var "exceptionCursor")) (.lit 1))
      (Fill.put "exceptionList" "exceptionCount" (.var "exceptionCursor")) .skip,
    inc "exceptionCursor"]

/-- Scan every vertex and append those marked in `exceptionFlags` to the
`exceptionList` prefix in increasing order. -/
def packExceptionFlags : Com :=
  seqs [
    .assign "exceptionCount" (.lit 0),
    .assign "exceptionCursor" (.lit 0),
    .while (.lt (.var "exceptionCursor") (.var "n")) exceptionPackBody]


/-- The loop invariant for packing. `exceptionList` contains the active vertices in
the scanned prefix, in increasing order, and `exceptionCount` is its length. -/
def ExceptionPackInv (n : ℕ) (flags : ℕ → ℕ) (τ : Env) : Prop :=
  τ.arrs "exceptionFlags" = arrOf n flags ∧
  τ.vars "n" = n ∧
  τ.vars "exceptionCursor" ≤ n ∧
  τ.vars "exceptionCount" = (scanList flags 0 (τ.vars "exceptionCursor")).length ∧
  Fill.Below "exceptionList" "exceptionCount" n
    (fun i => (scanList flags 0 n).getD i 0) τ

private def exceptionPackTest : Cond :=
  .eq (.get "exceptionFlags" (.var "exceptionCursor")) (.lit 1)

private def exceptionPackBodyCost : ℕ := 1 + exceptionPackTest.size + 7 + 4

/-- One scan turn either appends the current marked vertex or leaves the
prefix alone, then advances the scan cursor. -/
private lemma exceptionPackBody_run {B n : ℕ} {flags : ℕ → ℕ} {σ : Env}
    (hI : ExceptionPackInv n flags σ)
    (hcursor : σ.vars "exceptionCursor" < n)
    (hflags01 : ∀ v < n, flags v ≤ 1)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B exceptionPackBody σ σ' exceptionPackBodyCost ∧ ExceptionPackInv n flags σ' ∧
      σ'.vars "exceptionCursor" = σ.vars "exceptionCursor" + 1 := by
  obtain ⟨hflags, hn, hcle, hcount, hfill⟩ := hI
  let k := σ.vars "exceptionCursor"
  let count := σ.vars "exceptionCount"
  have hflagsB : flags k < B := by
    have hk : k < n := by simpa [k] using hcursor
    have := hflags01 k hk
    omega
  have hkB : k < B := hcursor.trans hnB
  have hget : (Expr.get "exceptionFlags" (.var "exceptionCursor")).evalB B σ =
      some (flags k) := by
    apply evalB_get (evalB_var (by simpa [k] using hkB)) _ hflagsB
    rw [hflags, getElem?_arrOf _ (by simpa [k] using hcursor)]
  have htestEval : exceptionPackTest.evalB B σ = some (flags k == 1) := by
    simpa [exceptionPackTest] using
      evalB_condEq hget (evalB_lit (by omega : 1 < B))
  by_cases hactive : flags k = 1
  · have htestTrue : exceptionPackTest.evalB B σ = some true := by
      simpa [hactive] using htestEval
    have hcountlt : count < n := by
      change σ.vars "exceptionCount" < n
      rw [hcount]
      exact (scanList_length_le flags 0 k).trans_lt (by simpa [k] using hcursor)
    have hvalue : (scanList flags 0 n).getD count 0 = k := by
      change (scanList flags 0 n).getD (σ.vars "exceptionCount") 0 = k
      rw [hcount]
      exact scanList_active_getD (by simpa [k] using hcursor) hactive
    let P : Env → Prop := fun τ => ExceptionPackInv n flags τ ∧
      τ.vars "exceptionCursor" = k ∧ τ.vars "exceptionCursor" < n ∧
      exceptionPackTest.evalB B τ = some true
    have hputSpec : Spec B P (Fill.put "exceptionList" "exceptionCount" (.var "exceptionCursor"))
        (Fill.PutPost "exceptionList" "exceptionCount" n
          (fun i => (scanList flags 0 n).getD i 0)) 7 := by
      have hput := Fill.put_spec B n "exceptionList" "exceptionCount" (.var "exceptionCursor")
        (fun i => (scanList flags 0 n).getD i 0) P
        (by
          intro τ ⟨hτ, _, hτlt, _⟩
          have hcnt : τ.vars "exceptionCount" =
              (scanList flags 0 (τ.vars "exceptionCursor")).length := hτ.2.2.2.1
          refine ⟨hτ.2.2.2.2, ?_⟩
          rw [hcnt]
          exact (scanList_length_le flags 0 (τ.vars "exceptionCursor")).trans_lt hτlt)
        hnB
        (by
          intro τ ⟨hτ, heq, hτlt, _⟩
          have hcnt : τ.vars "exceptionCount" =
              (scanList flags 0 (τ.vars "exceptionCursor")).length := hτ.2.2.2.1
          have hcur : τ.vars "exceptionCursor" < n := hτlt
          have hactiveτ : flags (τ.vars "exceptionCursor") = 1 := by
            simpa [heq] using hactive
          have hval := scanList_active_getD hcur hactiveτ
          rw [evalB_var (by omega : τ.vars "exceptionCursor" < B)]
          rw [← hcnt] at hval
          rw [hval]
            )
      simpa using hput
    have htestEvalAfter : exceptionPackTest.evalB B σ = some true := htestTrue
    obtain ⟨σ₁, hputRun, ⟨hfill₁, hcount₁⟩⟩ :=
      hputSpec σ ⟨⟨hflags, hn, hcle, hcount, hfill⟩, rfl, hcursor, htestEvalAfter⟩
    let σ₂ := σ₁.setVar "exceptionCursor" (k + 1)
    have hcursor₁ : σ₁.vars "exceptionCursor" = k := by
      simpa [k] using hputRun.frame_var "exceptionCursor" (by decide)
    have hcursorEval : (Expr.add (.var "exceptionCursor") (.lit 1)).evalB B σ₁ =
        some (k + 1) := by
      have hvar : (Expr.var "exceptionCursor").evalB B σ₁ = some k := by
        have hkB₁ : σ₁.vars "exceptionCursor" < B := by rw [hcursor₁]; exact hkB
        simpa [hcursor₁] using evalB_var hkB₁
      have hone : (Expr.lit 1).evalB B σ₁ = some 1 := evalB_lit (by omega)
      have hadd : Bop.apply Bop.add k 1 < B := by
        change k + 1 < B
        omega
      have hbin := evalB_bin hvar hone hadd
      simpa [Bop.apply] using hbin
    have hcursorRun : Run B (inc "exceptionCursor") σ₁ σ₂ 4 := by
      simpa [inc, σ₂] using Run.assign hcursorEval
    have hrun : Run B exceptionPackBody σ σ₂ exceptionPackBodyCost := by
      have hite : Run B
          (.ite exceptionPackTest (Fill.put "exceptionList" "exceptionCount" (.var "exceptionCursor")) .skip)
          σ σ₁ (1 + exceptionPackTest.size + 7) :=
        Run.ite_true htestTrue hputRun
      have hseq := Run.seq hite hcursorRun
      simpa [exceptionPackBody, exceptionPackTest, exceptionPackBodyCost, seqs, Nat.add_assoc] using hseq
    have hflags₂ : σ₂.arrs "exceptionFlags" = arrOf n flags := by
      rw [hcursorRun.frame_arr "exceptionFlags" (by decide)]
      exact (hputRun.frame_arr "exceptionFlags" (by decide)).trans hflags
    have hn₂ : σ₂.vars "n" = n := by
      rw [hcursorRun.frame_var "n" (by decide)]
      exact (hputRun.frame_var "n" (by decide)).trans hn
    have hcount₂ : σ₂.vars "exceptionCount" =
        (scanList flags 0 (σ₂.vars "exceptionCursor")).length := by
      rw [show σ₂.vars "exceptionCursor" = k + 1 by simp [σ₂, k]]
      rw [scanList_zero_add]
      rw [show σ₂.vars "exceptionCount" = σ₁.vars "exceptionCount" by simp [σ₂]]
      rw [hcount₁]
      rw [hcount]
      simp [hactive, k]
    have hfill₂ : Fill.Below "exceptionList" "exceptionCount" n
        (fun i => (scanList flags 0 n).getD i 0) σ₂ := by
      apply hfill₁.of_eq
      · exact hcursorRun.frame_arr "exceptionList" (by decide)
      · exact hcursorRun.frame_var "exceptionCount" (by decide)
    refine ⟨σ₂, hrun, ⟨hflags₂, hn₂, ?_, hcount₂, hfill₂⟩, ?_⟩
    · simp [σ₂, k]
      omega
    · simp [σ₂, k]
  · have htestFalse : exceptionPackTest.evalB B σ = some false := by
      have hflagzero : flags k = 0 := by have := hflags01 k (by simpa [k] using hcursor); omega
      simpa [hflagzero] using htestEval
    let σ₁ := σ.setVar "exceptionCursor" (k + 1)
    have hcursorEval : (Expr.add (.var "exceptionCursor") (.lit 1)).evalB B σ =
        some (k + 1) := by
      have hvar : (Expr.var "exceptionCursor").evalB B σ = some k := by
        have hkB₀ : σ.vars "exceptionCursor" < B := by simpa [k] using hkB
        simpa [k] using evalB_var hkB₀
      have hone : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by omega)
      have hadd : Bop.apply Bop.add k 1 < B := by
        change k + 1 < B
        omega
      have hbin := evalB_bin hvar hone hadd
      simpa [Bop.apply] using hbin
    have hcursorRun : Run B (inc "exceptionCursor") σ σ₁ 4 := by
      simpa [inc, σ₁] using Run.assign hcursorEval
    have hrun : Run B exceptionPackBody σ σ₁ exceptionPackBodyCost := by
      have hite : Run B
          (.ite exceptionPackTest (Fill.put "exceptionList" "exceptionCount" (.var "exceptionCursor")) .skip)
          σ σ (1 + exceptionPackTest.size + 1) :=
        Run.ite_false htestFalse Run.skip
      have hseq := Run.seq hite hcursorRun
      simpa [exceptionPackBody, exceptionPackTest, exceptionPackBodyCost, seqs, Nat.add_assoc] using
        hseq.mono (by norm_num [exceptionPackBodyCost, exceptionPackTest, Cond.size, Expr.size])
    have hflags₁ : σ₁.arrs "exceptionFlags" = arrOf n flags := by simp [σ₁, hflags]
    have hn₁ : σ₁.vars "n" = n := by simp [σ₁, hn]
    have hcount₁ : σ₁.vars "exceptionCount" =
        (scanList flags 0 (σ₁.vars "exceptionCursor")).length := by
      rw [show σ₁.vars "exceptionCursor" = k + 1 by simp [σ₁]]
      rw [scanList_zero_add]
      rw [show σ₁.vars "exceptionCount" = σ.vars "exceptionCount" by simp [σ₁]]
      rw [hcount]
      simp [hactive, k]
    have hfill₁ : Fill.Below "exceptionList" "exceptionCount" n
        (fun i => (scanList flags 0 n).getD i 0) σ₁ := by
      exact hfill.of_eq (by simp [σ₁]) (by simp [σ₁])
    refine ⟨σ₁, hrun, ⟨hflags₁, hn₁, ?_, hcount₁, hfill₁⟩, ?_⟩
    · simp [σ₁, k]
      omega
    · simp [σ₁, k]


/-- Execute the actual IMP+ packing pass. The flags must already be a
zero-one array. The pass scans all `n` vertices, writes exactly the marked
ones to `exceptionList` in increasing order, and consumes no input. Its cost is
`20 * n + 9` source steps. -/
lemma packExceptionFlags_run {B n : ℕ} {σ : Env} {flags exceptionList : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hflags : σ.arrs "exceptionFlags" = arrOf n flags)
    (hord : σ.arrs "exceptionList" = arrOf n exceptionList)
    (hflags01 : ∀ v < n, flags v ≤ 1)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' : Env, ∃ packed : ℕ → ℕ,
      Run B packExceptionFlags σ σ' (20 * n + 9) ∧
      σ'.arrs "exceptionFlags" = arrOf n flags ∧
      σ'.arrs "exceptionList" = arrOf n packed ∧
      PrefixEnumerates (σ'.vars "exceptionCount") packed (flaggedVertices n flags) ∧
      σ'.vars "exceptionCount" = (flaggedVertices n flags).card ∧
      σ'.vars "exceptionCursor" = n ∧
      (∀ a, a ≠ "exceptionList" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "exceptionCount" → v ≠ "exceptionCursor" →
        σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hbody : Spec B (fun τ => ExceptionPackInv n flags τ ∧ τ.vars "exceptionCursor" < n)
      exceptionPackBody
      (fun σ₁ σ₂ => ExceptionPackInv n flags σ₂ ∧
        σ₂.vars "exceptionCursor" = σ₁.vars "exceptionCursor" + 1)
      exceptionPackBodyCost := by
    intro τ ⟨hτ, hcur⟩
    obtain ⟨τ', hr, hτ', hcursor'⟩ :=
      exceptionPackBody_run hτ hcur hflags01 hnB honeB
    exact ⟨τ', hr, hτ', hcursor'⟩
  have hloop := Spec.forRangeZero "exceptionCursor" "n" (ExceptionPackInv n flags)
      n exceptionPackBodyCost hnB
      (fun _ h => h.2.2.1)
      (fun τ h => h.2.1)
      hbody
  let σ₁ := σ.setVar "exceptionCount" 0
  have hcountRun : Run B (.assign "exceptionCount" (.lit 0)) σ σ₁ 2 := by
    simpa [σ₁] using Run.assign (evalB_lit (by omega : 0 < B))
  have hstart : ExceptionPackInv n flags (σ₁.setVar "exceptionCursor" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₁, hflags]
    · simp [σ₁, hn]
    · simp
    · simp [σ₁, scanList]
    · have hOrd₁ : (σ₁.setVar "exceptionCursor" 0).arrs "exceptionList" = arrOf n exceptionList := by
        simp [σ₁, hord]
      exact Fill.below_zero hOrd₁ (by simp [σ₁])
  obtain ⟨σ', hloopRun, hfinal, hcursor⟩ := hloop.run (σ := σ₁) hstart
  have hrunRaw := Run.seq hcountRun hloopRun
  have hrun : Run B packExceptionFlags σ σ' (20 * n + 9) := by
    simpa [packExceptionFlags, exceptionPackBody, exceptionPackBodyCost, exceptionPackTest, seqs,
      Cond.size, Expr.size, Nat.add_assoc, Nat.mul_add] using
        hrunRaw.mono (by norm_num [exceptionPackBodyCost, exceptionPackTest, Cond.size, Expr.size]; omega)
  have hcountFinal : σ'.vars "exceptionCount" = (scanList flags 0 n).length := by
    have h := hfinal.2.2.2.1
    rw [hcursor] at h
    exact h
  have hflagsFinal : σ'.arrs "exceptionFlags" = arrOf n flags := by
    exact (hrun.frame_arr "exceptionFlags" (by decide)).trans hflags
  have hordFinal : ∃ packed : ℕ → ℕ,
      σ'.arrs "exceptionList" = arrOf n packed ∧
      (∀ i < σ'.vars "exceptionCount", packed i = (scanList flags 0 n).getD i 0) := by
    rcases hfinal.2.2.2.2 with ⟨packed, hfill⟩
    rcases hfill with ⟨harr, hcount, hle, hcell⟩
    exact ⟨packed, harr, fun i hi => hcell i hi⟩
  obtain ⟨packed, hordPacked, hordCells⟩ := hordFinal
  have hcountBound : σ'.vars "exceptionCount" ≤ n := by
    rw [hcountFinal]
    exact (scanList_length_le flags 0 n).trans (Nat.le_refl n)
  have hprefix : PrefixEnumerates (σ'.vars "exceptionCount") packed
      (scanList flags 0 n).toFinset := by
    have hentry : ∀ i < σ'.vars "exceptionCount",
        packed i = (scanList flags 0 n).getD i 0 := hordCells
    have h := PrefixEnumerates.of_list_prefix
      (height := σ'.vars "exceptionCount") (entry := packed)
      (by rw [hcountFinal])
      (by
        intro i hi
        exact hentry i hi)
      (scanList_nodup flags 0 n)
    simpa [hcountFinal, List.take_length] using h
  have hprefix' : PrefixEnumerates (σ'.vars "exceptionCount") packed
      (flaggedVertices n flags) := by
    rw [← scanList_toFinset]
    exact hprefix
  have hcard : σ'.vars "exceptionCount" = (flaggedVertices n flags).card := by
    rw [hcountFinal, scanList_length_eq_card]
  have hframeVars : ∀ v, v ≠ "exceptionCount" → v ≠ "exceptionCursor" →
      σ'.vars v = σ.vars v := by
    intro v hv hc
    exact hrun.frame_var v (by
      simp [packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.wvars, hv, hc])
  have hframeArrs : ∀ a, a ≠ "exceptionList" → σ'.arrs a = σ.arrs a := by
    intro a ha
    exact hrun.frame_arr a (by
      simp [packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.warrs, ha])
  have hinp := hrun.frame_inp (by simp [packExceptionFlags, exceptionPackBody,
    seqs, Fill.put, inc, Com.reads])
  have hout := hrun.out_eq (by simp [packExceptionFlags, exceptionPackBody,
    seqs, Fill.put, inc, Com.NoWrite])
  refine ⟨σ', packed, hrun, hflagsFinal, hordPacked, hprefix', hcard,
    hcursor, hframeArrs, hframeVars, hinp, hout⟩

/-- Mark the exceptions, then pack them into `exceptionList`. -/
def collectAndPackExceptions : Com := seqs [collectExceptions, packExceptionFlags]

private lemma flaggedVertices_exceptionValue (n threshold : ℕ)
    (activeB rep degree inter : ℕ → ℕ) :
    flaggedVertices n (exceptionValue threshold activeB rep degree inter) =
      exceptionSet n threshold activeB rep degree inter := by
  ext v
  rw [show v ∈ flaggedVertices n
      (exceptionValue threshold activeB rep degree inter) ↔
      v < n ∧ exceptionValue threshold activeB rep degree inter v = 1 from
      mem_activeVertices]
  simp only [exceptionSet, Finset.mem_filter, Finset.mem_range]
  by_cases hv : activeB v = 1 ∧
      threshold < nearDistance degree inter rep v
  · simp [exceptionValue, hv]
  · simp [exceptionValue, hv]

/-- The fixed IMP+ routine marks every exception, packs the marked vertices
in increasing order, and records their exact cardinality. It reads its
degree, intersection, representative, active, and threshold values from the
runtime state; the input and output tapes are preserved. -/
lemma collectAndPackExceptions_run
    {B n threshold : ℕ} {activeB rep degree inter initialFlags initialList : ℕ → ℕ}
    {σ : Env}
    (hn : σ.vars "n" = n) (hbound : σ.vars "nearBound" = threshold)
    (hactive : σ.arrs "activeB" = arrOf n activeB)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hflags : σ.arrs "exceptionFlags" = arrOf n initialFlags)
    (hlist : σ.arrs "exceptionList" = arrOf n initialList)
    (hnB : 2 * n + 1 < B) (hthresholdB : threshold < B)
    (hactiveB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hdegreeN : ∀ v < n, degree v ≤ n)
    (hinterN : ∀ v < n, inter v ≤ n) :
    ∃ σ' packed, Run B collectAndPackExceptions σ σ' (94 * n + 15) ∧
      σ'.arrs "exceptionFlags" = arrOf n
        (exceptionValue threshold activeB rep degree inter) ∧
      σ'.arrs "exceptionList" = arrOf n packed ∧
      PrefixEnumerates (σ'.vars "exceptionCount") packed
        (exceptionSet n threshold activeB rep degree inter) ∧
      σ'.vars "exceptionCount" =
        (exceptionSet n threshold activeB rep degree inter).card ∧
      σ'.vars "exceptionCursor" = n ∧ σ'.vars "b" = n ∧
      σ'.arrs "activeB" = arrOf n activeB ∧
      σ'.arrs "repB" = arrOf n rep ∧
      σ'.arrs "degree" = arrOf n degree ∧
      σ'.arrs "inter" = arrOf n inter ∧
      σ'.vars "n" = n ∧ σ'.vars "nearBound" = threshold ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σc, hc, hflagsC, hbC, hframesC, hvarsC, hinpC, houtC⟩ :=
    collectExceptions_run hn hbound hactive hrep hdegree hinter hflags
      hnB hthresholdB hactiveB hrepN hdegreeN hinterN
  have hnC : σc.vars "n" = n := (hvarsC "n" (by decide) (by decide)
    (by decide)).trans hn
  have hlistC : σc.arrs "exceptionList" = arrOf n initialList :=
    (hframesC "exceptionList" (by decide)).trans hlist
  have hflags01 : ∀ v < n,
      exceptionValue threshold activeB rep degree inter v ≤ 1 := by
    intro v hv
    simp [exceptionValue]
    split_ifs <;> omega
  obtain ⟨σ', packed, hp, hflagsP, hlistP, hprefix, hcount,
      hcursor, _, hvarsP, hinpP, houtP⟩ :=
    packExceptionFlags_run hnC hflagsC hlistC hflags01 (by omega : n < B)
      (by omega : 1 < B)
  have hrun : Run B collectAndPackExceptions σ σ' (94 * n + 15) := by
    change Run B (collectExceptions.seq packExceptionFlags) σ σ' (94 * n + 15)
    convert Run.seq hc hp using 1; omega
  refine ⟨σ', packed, hrun, hflagsP, hlistP, ?_, ?_, hcursor, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hinpP.trans hinpC, houtP.trans houtC⟩
  · rwa [flaggedVertices_exceptionValue] at hprefix
  · rwa [flaggedVertices_exceptionValue] at hcount
  · exact (hvarsP "b" (by decide) (by decide)).trans hbC
  · exact (hrun.frame_arr "activeB" (by
      simp [collectAndPackExceptions, collectExceptions, exceptionBody,
        packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.warrs])).trans hactive
  · exact (hrun.frame_arr "repB" (by
      simp [collectAndPackExceptions, collectExceptions, exceptionBody,
        packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.warrs])).trans hrep
  · exact (hrun.frame_arr "degree" (by
      simp [collectAndPackExceptions, collectExceptions, exceptionBody,
        packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.warrs])).trans hdegree
  · exact (hrun.frame_arr "inter" (by
      simp [collectAndPackExceptions, collectExceptions, exceptionBody,
        packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.warrs])).trans hinter
  · exact (hrun.frame_var "n" (by
      simp [collectAndPackExceptions, collectExceptions, exceptionBody,
        packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.wvars])).trans hn
  · exact (hrun.frame_var "nearBound" (by
      simp [collectAndPackExceptions, collectExceptions, exceptionBody,
        packExceptionFlags, exceptionPackBody, seqs, Fill.put, inc, Com.wvars])).trans hbound

end Lax457868Proofs.ExceptionCollection
