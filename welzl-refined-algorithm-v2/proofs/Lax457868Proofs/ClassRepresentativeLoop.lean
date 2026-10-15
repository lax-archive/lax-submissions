import Mathlib.Tactic
import Lax457868Proofs.ClassRepresentativeTrace
import Lax457868Proofs.ClassOffsetDraw
import Lax457868Proofs.DrawLogSetup

/-!
The source loop chooses one representative from each contiguous class slice
of `ord`, stopping at the first exhausted rejection cap.
-/

namespace Lax457868Proofs.ClassRepresentativeLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.FairBitIndices Lax457868Proofs.FairBitRam
open Lax457868Proofs.StoppingPrefix
open Lax457868Proofs.ClassOffsetDraw Lax457868Proofs.DrawLogSetup
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- Start of class `d` in the contiguous order array. -/
def classStart (size : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => classStart size d + size d

lemma classStart_mono (size : ℕ → ℕ) {d q : ℕ} (hdq : d ≤ q) :
    classStart size d ≤ classStart size q := by
  induction q generalizing d with
  | zero =>
      have hd0 : d = 0 := by omega
      simp [hd0]
  | succ q ih =>
      by_cases h : d = q + 1
      · subst d; rfl
      · have hd : d ≤ q := by omega
        calc
          classStart size d ≤ classStart size q := ih hd
          _ ≤ classStart size (q + 1) := by simp [classStart]

/-- One source iteration reads the actual class size, computes its binary
width, draws from that class slice, and either writes its representative or
stops on exhaustion. -/
def representativeClassBody : Com :=
  seqs [
    .assign "drawModulus" (.get "classSize" (.var "repIndex")),
    drawLogSetup,
    seqs [countedRejectionSelector, classOffsetDrawLookup],
    .ite (.eq (.var "drawFound") (.lit 1))
      (seqs [
        .store "repClass" (.var "repIndex") (.var "drawVertex"),
        .assign "drawOffset" (.add (.var "drawOffset") (.var "drawModulus")),
        inc "repIndex"])
      (seqs [
        .assign "repFailed" (.lit 1),
        .assign "repStop" (.var "repIndex")])]

/-- Initialize the class cursor, slice cursor, and first-failure flag. -/
def representativeClassLoop : Com :=
  seqs [
    .assign "repIndex" (.lit 0),
    .assign "drawOffset" (.lit 0),
    .assign "repFailed" (.lit 0),
    .assign "repStop" (.var "classCount"),
    .while (.lt (.var "repIndex") (.var "repStop")) representativeClassBody]

/-- Write the values selected by successive classes into the representative
table, leaving all other cells untouched. -/
def writeClassReps (ord rep : ℕ → ℕ) (d : ℕ) : List ℕ → ℕ → ℕ
  | [] => rep
  | p :: more => writeClassReps ord (upd rep d (ord p)) (d + 1) more

lemma writeClassReps_outside (ord rep : ℕ → ℕ) (d j : ℕ)
    (values : List ℕ) (hj : j < d ∨ d + values.length ≤ j) :
    writeClassReps ord rep d values j = rep j := by
  induction values generalizing rep d with
  | nil => rfl
  | cons p more ih =>
      have hj' : j < d + 1 ∨ d + 1 + more.length ≤ j := by
        simp only [List.length_cons] at hj
        omega
      rw [writeClassReps, ih (upd rep d (ord p)) (d + 1) hj']
      have hne : j ≠ d := by
        simp only [List.length_cons] at hj
        rcases hj with h | h <;> omega
      simp [upd, hne]

lemma writeClassReps_at (ord rep : ℕ → ℕ) (d : ℕ)
    (values : List ℕ) (j : ℕ) (hj : j < values.length) :
    writeClassReps ord rep d values (d + j) = ord values[j] := by
  induction values generalizing rep d j with
  | nil => simp at hj
  | cons p more ih =>
      cases j with
      | zero =>
          have hout := writeClassReps_outside ord
            (upd rep d (ord p)) (d + 1) d more (Or.inl (by omega))
          simpa [writeClassReps, upd] using hout
      | succ k =>
          have hk : k < more.length := by simpa using hj
          have h := ih (upd rep d (ord p)) (d + 1) k hk
          have heq : d + 1 + k = d + (k + 1) := by omega
          rw [heq] at h
          simpa [writeClassReps] using h

private lemma guard_true {B d q : ℕ} {σ : Env}
    (hd : σ.vars "repIndex" = d) (hq : σ.vars "repStop" = q)
    (hlt : d < q) (hqB : q < B) :
    (Cond.lt (.var "repIndex") (.var "repStop")).evalB B σ = some true := by
  simpa [hd, hq, hlt] using
    evalB_condLt (evalB_var (by rw [hd]; omega : σ.vars "repIndex" < B))
      (evalB_var (by rw [hq]; exact hqB : σ.vars "repStop" < B))

private lemma guard_false {B d q : ℕ} {σ : Env}
    (hd : σ.vars "repIndex" = d) (hq : σ.vars "repStop" = q)
    (hle : q ≤ d) (hdB : d < B) (hqB : q < B) :
    (Cond.lt (.var "repIndex") (.var "repStop")).evalB B σ = some false := by
  simpa [hd, hq, Nat.not_lt.mpr hle] using
    evalB_condLt (evalB_var (by rw [hd]; exact hdB : σ.vars "repIndex" < B))
      (evalB_var (by rw [hq]; exact hqB : σ.vars "repStop" < B))

private lemma runWhileTrue {B : ℕ} {b : Cond} {c : Com}
    {σ σ₁ σ₂ : Env} {P Q : ℕ}
    (hb : b.evalB B σ = some true)
    (hbody : Run B c σ σ₁ P)
    (hloop : Run B (.while b c) σ₁ σ₂ Q) :
    Run B (.while b c) σ σ₂ (1 + b.size + P + Q) := by
  obtain ⟨k, hk, hbs⟩ := hbody
  obtain ⟨k', hk', hbs'⟩ := hloop
  exact ⟨1 + b.size + k + k', by omega,
    BigStepB.while_true hb hbs hbs'⟩

/-- One actual class iteration.  The lookup and the rejection selector see
the current class's size and slice, while the next iteration receives exactly
the unread suffix returned by the selector. -/
private lemma body_run_tape
    {B n q v t d m offset : ℕ} {σ : Env}
    {size ord rep g : ℕ → ℕ} {rest : List ℕ}
    (tape : BitTape m t)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hrep : σ.arrs "repClass" = arrOf n rep)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hindex : σ.vars "repIndex" = d)
    (hstop : σ.vars "repStop" = q)
    (hbad : σ.vars "repFailed" = 0)
    (hoffset : σ.vars "drawOffset" = offset)
    (hcount : σ.vars "classCount" = q)
    (hn : σ.vars "n" = n) (hqpow : σ.vars "qpow" < B)
    (hcap : σ.vars "drawCap" = t)
    (hv : σ.vars "v" = v)
    (hm : size d = m) (hmpos : 0 < m)
    (hdq : d < q) (hqn : q ≤ n) (hvn : v < n)
    (hactive : offset + m ≤ n)
    (hordValue : ∀ j < m, ord (offset + j) < n)
    (hinp : σ.inp = flattenBitBlocks tape ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B)
    (hnB : n < B) (hqB : q < B)
    (htB : t < B) (htwoB : 2 < B) :
    ∃ σ' g',
      Run B representativeClassBody σ σ'
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape +
          12 * Nat.clog 2 m + 57) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ j < n, j ≠ v → g' j = g j) ∧
      σ'.arrs "classSize" = arrOf n size ∧
      σ'.arrs "ord" = arrOf n ord ∧
      (∀ i, (selectBitIndexWithCount m hmpos t tape).1 = some i →
        σ'.arrs "repClass" = arrOf n (upd rep d (ord (offset + i.val))) ∧
        σ'.vars "repIndex" = d + 1 ∧
        σ'.vars "drawOffset" = offset + m ∧
        σ'.vars "repFailed" = 0 ∧ σ'.vars "repStop" = q) ∧
      ((selectBitIndexWithCount m hmpos t tape).1 = none →
        σ'.arrs "repClass" = arrOf n rep ∧
        σ'.vars "repIndex" = d ∧
        σ'.vars "drawOffset" = offset ∧
        σ'.vars "repFailed" = 1 ∧ σ'.vars "repStop" = d) ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = σ.vars "qpow" ∧
      σ'.vars "classCount" = q ∧ σ'.vars "drawCap" = t ∧
      σ'.vars "v" = v ∧
      σ'.inp = flattenBitBlockList
        ((List.ofFn tape).drop (bitTapeAttemptsUsed m t tape)) ++ rest ∧
      (∀ a, a ≠ "key0" → a ≠ "repClass" → σ'.arrs a = σ.arrs a) := by
  let σ₁ := σ.setVar "drawModulus" m
  have hdB : d < B := lt_of_lt_of_le hdq (hqB.le)
  have hmB : m < B := by omega
  have hloadEval : (Expr.get "classSize" (.var "repIndex")).evalB B σ =
      some m := by
    apply evalB_get (evalB_var (by rw [hindex]; exact hdB))
    · rw [hsize, hindex, getElem?_arrOf size (by omega : d < n), hm]
    · exact hmB
  have hload : Run B
      (.assign "drawModulus" (.get "classSize" (.var "repIndex")))
      σ σ₁ 3 := by
    simpa [σ₁] using (Run.assign hloadEval)
  have hlogN : σ₁.vars "n" < B := by simp [σ₁, hn, hnB]
  have hlogQ : σ₁.vars "qpow" < B := by simpa [σ₁] using hqpow
  obtain ⟨σ₂, hlog, hn₂, hqpow₂, hL₂, hmod₂, hcap₂,
    hoffset₂, hv₂, harr₂, hinp₂, _⟩ :=
    drawLogSetup_run hlogN hlogQ (by simp [σ₁]) hmB hpowB
  have hsize₂ : σ₂.arrs "classSize" = arrOf n size := by
    exact (harr₂ "classSize").trans (by simpa [σ₁] using hsize)
  have hord₂ : σ₂.arrs "ord" = arrOf n ord := by
    exact (harr₂ "ord").trans (by simpa [σ₁] using hord)
  have hrep₂ : σ₂.arrs "repClass" = arrOf n rep := by
    exact (harr₂ "repClass").trans (by simpa [σ₁] using hrep)
  have hkey₂ : σ₂.arrs "key0" = arrOf n g := by
    exact (harr₂ "key0").trans (by simpa [σ₁] using hkey)
  have hinp₂' : σ₂.inp = flattenBitBlocks tape ++ rest := by
    simpa [σ₁] using hinp₂.trans hinp
  have hoffset₂' : σ₂.vars "drawOffset" = offset := by
    simpa [σ₁, hoffset] using hoffset₂
  have hv₂' : σ₂.vars "v" = v := by simpa [σ₁, hv] using hv₂
  have hcap₂' : σ₂.vars "drawCap" = t := by simpa [σ₁, hcap] using hcap₂
  obtain ⟨σ₃, g', hdraw, hkey₃, hframeKey, hvertex₃, _,
    _, hfound₃, hinp₃, hord₃, harrFrame₃, hv₃, _, hmod₃,
    hcap₃, hoffset₃⟩ :=
    countedClassOffsetDraw_run_tape tape hmpos hkey₂ hord₂ hnB
      (by intro j hj; exact (hordValue j hj).trans hnB)
      hactive hoffset₂' hv₂' hvn hL₂ hmod₂ hcap₂' hinp₂'
      hpowB hnB htwoB htB hmB
  have hsize₃ : σ₃.arrs "classSize" = arrOf n size :=
    (harrFrame₃ "classSize" (by decide)).trans hsize₂
  have hrep₃ : σ₃.arrs "repClass" = arrOf n rep :=
    (harrFrame₃ "repClass" (by decide)).trans hrep₂
  have hindex₃ : σ₃.vars "repIndex" = d := by
    have h := hdraw.frame_var "repIndex" (by decide)
    have h' := hlog.frame_var "repIndex" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact h.trans (h'.trans (by simpa [σ₁] using hindex))
  have hstop₃ : σ₃.vars "repStop" = q := by
    have h := hdraw.frame_var "repStop" (by decide)
    have h' := hlog.frame_var "repStop" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact h.trans (h'.trans (by simpa [σ₁] using hstop))
  have hbad₃ : σ₃.vars "repFailed" = 0 := by
    have h := hdraw.frame_var "repFailed" (by decide)
    have h' := hlog.frame_var "repFailed" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact h.trans (h'.trans (by simpa [σ₁] using hbad))
  have hn₃ : σ₃.vars "n" = n := by
    have h := hdraw.frame_var "n" (by decide)
    exact h.trans (hn₂.trans (by simpa [σ₁] using hn))
  have hqpow₃ : σ₃.vars "qpow" = σ.vars "qpow" := by
    have h := hdraw.frame_var "qpow" (by decide)
    simpa [σ₁] using h.trans hqpow₂
  have hcount₃ : σ₃.vars "classCount" = q := by
    have h := hdraw.frame_var "classCount" (by decide)
    have h' := hlog.frame_var "classCount" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact h.trans (h'.trans (by simpa [σ₁] using hcount))
  have harrayFrame₃ (a : String) (ha : a ≠ "key0") : σ₃.arrs a = σ.arrs a := by
    exact (harrFrame₃ a ha).trans ((harr₂ a).trans (by simp [σ₁]))
  let choice := (selectBitIndexWithCount m hmpos t tape).1
  by_cases hsuccess : choice ≠ none
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hsuccess
    have hi' : (selectBitIndexWithCount m hmpos t tape).1 = some i := hi
    have hfound : σ₃.vars "drawFound" = 1 := by
      simp [hfound₃, choice, hsuccess]
    have hvertex : σ₃.vars "drawVertex" = ord (offset + i.val) :=
      hvertex₃ i hi'
    let σ₄ := σ₃.setArr "repClass" d (ord (offset + i.val))
    have hstore : Run B (.store "repClass" (.var "repIndex") (.var "drawVertex"))
        σ₃ σ₄ 3 := by
      apply Run.store
      · simpa [hindex₃] using
          (evalB_var (by rw [hindex₃]; exact hdB : σ₃.vars "repIndex" < B))
      · have hvalB : ord (offset + i.val) < B :=
          (hordValue i.val i.isLt).trans hnB
        simpa [hvertex] using
          (evalB_var (by rw [hvertex]; exact hvalB : σ₃.vars "drawVertex" < B))
      · simpa [hrep₃] using (lt_of_lt_of_le hdq hqn)
    let σ₅ := σ₄.setVar "drawOffset" (offset + m)
    have hoffEval : (Expr.add (.var "drawOffset") (.var "drawModulus")).evalB B σ₄ =
        some (offset + m) := by
      apply evalB_bin
      · simpa [σ₄, hoffset₃] using
          (evalB_var (by rw [hoffset₃]; omega : σ₃.vars "drawOffset" < B))
      · simpa [σ₄, hmod₃] using
          (evalB_var (by rw [hmod₃]; exact hmB : σ₃.vars "drawModulus" < B))
      · simpa using (show offset + m < B by omega)
    have hsetOff : Run B
        (.assign "drawOffset" (.add (.var "drawOffset") (.var "drawModulus")))
        σ₄ σ₅ 4 := by simpa [σ₅] using (Run.assign hoffEval)
    let σ₆ := σ₅.setVar "repIndex" (d + 1)
    have hinc : Run B (inc "repIndex") σ₅ σ₆ 4 := by
      have heval : (Expr.add (.var "repIndex") (.lit 1)).evalB B σ₅ =
          some (d + 1) := by
        apply evalB_bin
        · simpa [σ₅, σ₄, hindex₃] using
            (evalB_var (by rw [hindex₃]; exact hdB : σ₃.vars "repIndex" < B))
        · exact evalB_lit (by omega : 1 < B)
        · simpa using (show d + 1 < B by omega)
      simpa [inc, σ₆] using (Run.assign heval)
    have hbranch : Run B
        (.ite (.eq (.var "drawFound") (.lit 1))
          (seqs [.store "repClass" (.var "repIndex") (.var "drawVertex"),
            .assign "drawOffset" (.add (.var "drawOffset") (.var "drawModulus")),
            inc "repIndex"])
          (seqs [.assign "repFailed" (.lit 1),
            .assign "repStop" (.var "repIndex")])) σ₃ σ₆ 15 := by
      have hcond : (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ₃ = some true := by
        rw [evalB_condEq (evalB_var (by rw [hfound]; omega))
          (evalB_lit (by omega : 1 < B))]
        simp [hfound]
      have hseq : Run B (seqs [.store "repClass" (.var "repIndex") (.var "drawVertex"),
          .assign "drawOffset" (.add (.var "drawOffset") (.var "drawModulus")),
          inc "repIndex"]) σ₃ σ₆ 11 := by
        simpa [seqs] using Run.seq hstore (Run.seq hsetOff hinc)
      exact (Run.ite_true hcond hseq).mono (by decide)
    have hwhole : Run B representativeClassBody σ σ₆
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape +
          12 * Nat.clog 2 m + 57) := by
      have h := Run.seq hload (Run.seq hlog (Run.seq hdraw hbranch))
      have hraw : Run B representativeClassBody σ σ₆
          (3 + ((12 * Nat.clog 2 m + 18) +
            (((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 21) + 15))) := by
        simpa [representativeClassBody, seqs] using h
      exact hraw.mono (by omega)
    refine ⟨σ₆, g', hwhole, ?_, hframeKey, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [σ₆, σ₅, σ₄] using hkey₃
    · simpa [σ₆, σ₅, σ₄] using hsize₃
    · simpa [σ₆, σ₅, σ₄] using hord₃
    · intro j hj
      have hji : j = i := by
        have hopt : (some j : Option (Fin m)) = some i := hj.symm.trans hi'
        exact Option.some.inj hopt
      subst j
      simp [σ₆, σ₅, σ₄, hrep₃, set_arrOf_eq_upd, hbad₃, hstop₃]
    · intro hnone
      rw [hnone] at hi'
      cases hi'
    · simpa [σ₆, σ₅, σ₄] using hn₃
    · simpa [σ₆, σ₅, σ₄] using hqpow₃
    · simpa [σ₆, σ₅, σ₄] using hcount₃
    · simpa [σ₆, σ₅, σ₄] using hcap₃
    · simpa [σ₆, σ₅, σ₄] using hv₃
    · simpa [σ₆, σ₅, σ₄] using hinp₃
    · intro a ha hb
      simpa [σ₆, σ₅, σ₄, hb, Ne.symm hb] using harrayFrame₃ a ha
  · have hnone : choice = none := by
      cases h : choice with
      | none => rfl
      | some i => simp [h] at hsuccess
    have hfound : σ₃.vars "drawFound" = 0 := by
      simpa [choice, hnone] using hfound₃
    let σ₄ := σ₃.setVar "repFailed" 1
    let σ₅ := σ₄.setVar "repStop" d
    have hsetFailed : Run B (.assign "repFailed" (.lit 1)) σ₃ σ₄ 2 := by
      simpa [σ₄] using (Run.assign (evalB_lit (by omega : 1 < B)))
    have hindex₄ : σ₄.vars "repIndex" = d := by simp [σ₄, hindex₃]
    have hsetStop : Run B (.assign "repStop" (.var "repIndex")) σ₄ σ₅ 2 := by
      simpa [σ₅, hindex₄] using
        (Run.assign (evalB_var (by rw [hindex₄]; exact hdB : σ₄.vars "repIndex" < B)))
    have hbranch : Run B
        (.ite (.eq (.var "drawFound") (.lit 1))
          (seqs [.store "repClass" (.var "repIndex") (.var "drawVertex"),
            .assign "drawOffset" (.add (.var "drawOffset") (.var "drawModulus")),
            inc "repIndex"])
          (seqs [.assign "repFailed" (.lit 1),
            .assign "repStop" (.var "repIndex")])) σ₃ σ₅ 15 := by
      have hcond : (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ₃ = some false := by
        rw [evalB_condEq (evalB_var (by rw [hfound]; omega))
          (evalB_lit (by omega : 1 < B))]
        simp [hfound]
      have hseq : Run B (seqs [.assign "repFailed" (.lit 1),
          .assign "repStop" (.var "repIndex")]) σ₃ σ₅ 4 := by
        simpa [seqs] using Run.seq hsetFailed hsetStop
      exact (Run.ite_false hcond hseq).mono (by decide)
    have hwhole : Run B representativeClassBody σ σ₅
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape +
          12 * Nat.clog 2 m + 57) := by
      have h := Run.seq hload (Run.seq hlog (Run.seq hdraw hbranch))
      have hraw : Run B representativeClassBody σ σ₅
          (3 + ((12 * Nat.clog 2 m + 18) +
            (((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 21) + 15))) := by
        simpa [representativeClassBody, seqs] using h
      exact hraw.mono (by omega)
    refine ⟨σ₅, g', hwhole, ?_, hframeKey, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [σ₅, σ₄] using hkey₃
    · simpa [σ₅, σ₄] using hsize₃
    · simpa [σ₅, σ₄] using hord₃
    · intro i hi
      have hnone' : (selectBitIndexWithCount m hmpos t tape).1 = none := by
        simpa [choice] using hnone
      rw [hnone'] at hi
      cases hi
    · intro _
      simp [σ₅, σ₄, hrep₃, hindex₃, hoffset₃]
    · simpa [σ₅, σ₄] using hn₃
    · simpa [σ₅, σ₄] using hqpow₃
    · simpa [σ₅, σ₄] using hcount₃
    · simpa [σ₅, σ₄] using hcap₃
    · simpa [σ₅, σ₄] using hv₃
    · simpa [σ₅, σ₄] using hinp₃
    · intro a ha hb
      simpa [σ₅, σ₄] using harrayFrame₃ a ha

/-- Execute the source while-loop against a varying-width trace.  The charge
is the sum of each attempted class's actual selector attempts at its own
width, plus the log setup and fixed loop overhead for that class. -/
lemma loop_run_trace
    {B n q v t d r : ℕ} {σ : Env}
    {size ord rep g : ℕ → ℕ} {bits : List Bool} {rest : List ℕ}
    {values : List ℕ} {used charge : ℕ} {failed : Bool}
    (htrace : ClassTrace size t (classStart size) d r bits values used charge failed)
    (hremaining : d + r = q)
    (hpowB : ∀ j < q, 2 ^ Nat.clog 2 (size j) < B)
    (htotal : classStart size q ≤ n)
    (hqn : q ≤ n)
    (hordValue : ∀ j < classStart size q, ord j < n)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hrep : σ.arrs "repClass" = arrOf n rep)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hindex : σ.vars "repIndex" = d)
    (hstop : σ.vars "repStop" = q)
    (hbad : σ.vars "repFailed" = 0)
    (hoffset : σ.vars "drawOffset" = classStart size d)
    (hcount : σ.vars "classCount" = q)
    (hn : σ.vars "n" = n) (hqpow : σ.vars "qpow" < B)
    (hcap : σ.vars "drawCap" = t)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hinp : σ.inp = bits.map Bool.toNat ++ rest)
    (hnB : n < B) (hqB : q < B)
    (htB : t < B) (htwoB : 2 < B) :
    ∃ σ' g',
      Run B (.while (.lt (.var "repIndex") (.var "repStop"))
        representativeClassBody) σ σ' (charge + 4) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ j < n, j ≠ v → g' j = g j) ∧
      σ'.arrs "classSize" = arrOf n size ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "repClass" =
        arrOf n (writeClassReps ord rep d values) ∧
      σ'.vars "repIndex" = d + values.length ∧
      σ'.vars "repStop" =
        (if failed then d + values.length else q) ∧
      σ'.vars "repFailed" = (if failed then 1 else 0) ∧
      σ'.vars "drawOffset" = classStart size (d + values.length) ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = σ.vars "qpow" ∧
      σ'.vars "classCount" = q ∧ σ'.vars "drawCap" = t ∧
      σ'.vars "v" = v ∧
      σ'.inp = (bits.drop used).map Bool.toNat ++ rest ∧
      (∀ a, a ≠ "key0" → a ≠ "repClass" → σ'.arrs a = σ.arrs a) := by
  induction r generalizing d bits values used charge failed σ rep g with
  | zero =>
      cases htrace with
      | done =>
          have hd : d = q := by omega
          have hguard := guard_false hindex hstop (by omega : q ≤ d)
            (by omega : d < B) hqB
          refine ⟨σ, g, ?_, hkey, ?_, hsize, hord, ?_, ?_, ?_, hbad,
            ?_, hn, rfl, hcount, hcap, hv, ?_, ?_⟩
          · simpa using Run.while_false hguard
          · intro j hj hneq; rfl
          · simpa [writeClassReps] using hrep
          · simpa using hindex
          · simpa [hd] using hstop
          · simpa using hoffset
          · simpa using hinp
          · intro a ha hb; rfl
  | succ r ih =>
      cases htrace with
      | failed tape tail u hm hsel =>
          have hdq : d < q := by omega
          have hmReal : size d = size d := rfl
          have hactive : classStart size d + size d ≤ n := by
            calc
              classStart size d + size d = classStart size (d + 1) := rfl
              _ ≤ classStart size q := classStart_mono size (by omega)
              _ ≤ n := htotal
          have hordLocal : ∀ j < size d,
              ord (classStart size d + j) < n := by
            intro j hj
            apply hordValue
            have hstart := classStart_mono size (show d + 1 ≤ q by omega)
            simp only [classStart] at hstart
            omega
          have hinput : σ.inp = flattenBitBlocks tape ++
              (tail.map Bool.toNat ++ rest) := by
            simpa [tapeBits_words, List.map_append, List.append_assoc] using hinp
          obtain ⟨σ₁, g₁, hbody, hkey₁, hframe₁, hsize₁, hord₁,
            _, hfail₁, hn₁, hqpow₁, hcount₁, hcap₁, hv₁, hinp₁,
            harrayFrame₁⟩ :=
            body_run_tape tape hsize hord hrep hkey hindex hstop hbad
              hoffset hcount hn hqpow hcap hv hmReal hm hdq hqn
              hvn hactive hordLocal hinput (hpowB d hdq) hnB hqB htB htwoB
          have hnone : (selectBitIndexWithCount (size d) hm t tape).1 = none :=
            congrArg Prod.fst hsel
          obtain ⟨hrep₁, hindex₁, hoffset₁, hbad₁, hstop₁⟩ := hfail₁ hnone
          have hu : u = t := by
            have hcomplete := (selector_complete_rejection_iff (size d) hm t tape).mpr
              ((selectBitIndex_eq_none_iff (size d) hm t tape).mp (by
                have h := congrArg Prod.fst hsel
                simpa [selectBitIndexWithCount_eq (size d) hm t tape] using h))
            exact congrArg Prod.snd (hsel.symm.trans hcomplete)
          have hattempt : bitTapeAttemptsUsed (size d) t tape = u := by
            have h := selectBitIndexWithCount_eq (size d) hm t tape
            rw [hsel] at h
            exact (congrArg Prod.snd h).symm
          have hinput₁ : σ₁.inp =
              ((tapeBits tape ++ tail).drop (u * Nat.clog 2 (size d))).map
                Bool.toNat ++ rest := by
            have hdrop : (tapeBits tape ++ tail).drop
                (u * Nat.clog 2 (size d)) = tail := by
              rw [hu]
              simp [tapeBits_length]
            have hleft : flattenBitBlockList ((List.ofFn tape).drop u) = [] := by
              rw [hu]
              have hnil : (List.ofFn tape).drop t = [] :=
                List.drop_eq_nil_of_le (by simp)
              simp [hnil, flattenBitBlockList]
            rw [hdrop]
            simpa [hattempt, hleft, List.append_assoc] using hinp₁
          have hguard₁ := guard_false hindex₁ hstop₁ (by omega : d ≤ d)
            (by omega : d < B) (by omega : d < B)
          have hloop₁ : Run B (.while (.lt (.var "repIndex") (.var "repStop"))
              representativeClassBody) σ₁ σ₁ 4 := by
            simpa using Run.while_false hguard₁
          have hguard := guard_true hindex hstop hdq hqB
          have hwhole : Run B (.while (.lt (.var "repIndex") (.var "repStop"))
              representativeClassBody) σ σ₁
              ((15 * Nat.clog 2 (size d) + 30) * u +
                12 * Nat.clog 2 (size d) + 61 + 4) := by
            have h := runWhileTrue hguard hbody hloop₁
            rw [hattempt] at h
            have hsz : (Cond.lt (.var "repIndex") (.var "repStop")).size = 3 := by decide
            rw [hsz] at h
            exact h.mono (by omega)
          refine ⟨σ₁, g₁, ?_, hkey₁, hframe₁, hsize₁, hord₁,
            ?_, ?_, ?_, ?_, ?_, hn₁, hqpow₁, hcount₁,
            hcap₁, hv₁, ?_, harrayFrame₁⟩
          · simpa using hwhole
          · simpa [writeClassReps] using hrep₁
          · simpa using hindex₁
          · simpa using hstop₁
          · simpa using hbad₁
          · simpa using hoffset₁
          · simpa using hinput₁
      | accepted tape tail i u hm hsel hnext =>
          rename_i valuesTail usedTail chargeTail
          let failedTail := failed
          have hdq : d < q := by omega
          have hactive : classStart size d + size d ≤ n := by
            calc
              classStart size d + size d = classStart size (d + 1) := rfl
              _ ≤ classStart size q := classStart_mono size (by omega)
              _ ≤ n := htotal
          have hordLocal : ∀ j < size d,
              ord (classStart size d + j) < n := by
            intro j hj
            apply hordValue
            have hstart := classStart_mono size (show d + 1 ≤ q by omega)
            simp only [classStart] at hstart
            omega
          have hinput : σ.inp = flattenBitBlocks tape ++
              (tail.map Bool.toNat ++ rest) := by
            simpa [tapeBits_words, List.map_append, List.append_assoc] using hinp
          obtain ⟨σ₁, g₁, hbody, hkey₁, hframe₁, hsize₁, hord₁,
            hsuccess₁, _, hn₁, hqpow₁, hcount₁, hcap₁, hv₁, hinp₁,
            harrayFrame₁⟩ :=
            body_run_tape tape hsize hord hrep hkey hindex hstop hbad
              hoffset hcount hn hqpow hcap hv rfl hm hdq hqn
              hvn hactive hordLocal hinput (hpowB d hdq) hnB hqB htB htwoB
          have hsome : (selectBitIndexWithCount (size d) hm t tape).1 = some i :=
            congrArg Prod.fst hsel
          obtain ⟨hrep₁, hindex₁, hoffset₁, hbad₁, hstop₁⟩ := hsuccess₁ i hsome
          have hattempt : bitTapeAttemptsUsed (size d) t tape = u := by
            have h := selectBitIndexWithCount_eq (size d) hm t tape
            rw [hsel] at h
            exact (congrArg Prod.snd h).symm
          have hu : u ≤ t :=
            (stoppedEvent_bounds (size d) hm t u i tape hsel).2
          have hinput₁ : σ₁.inp =
              (((tapeBits tape).drop (u * Nat.clog 2 (size d)) ++ tail).map
                Bool.toNat) ++ rest := by
            rw [hattempt] at hinp₁
            rw [← tapeWords_drop] at hinp₁
            simpa [List.map_append, List.append_assoc] using hinp₁
          have hremain : d + 1 + r = q := by omega
          have hoffsetNext : σ₁.vars "drawOffset" = classStart size (d + 1) := by
            simpa [classStart] using hoffset₁
          have hqpowB₁ : σ₁.vars "qpow" < B := by rw [hqpow₁]; exact hqpow
          obtain ⟨σ₂, g₂, hloop₂, hkey₂, hframe₂, hsize₂, hord₂,
            hrep₂, hindex₂, hstop₂, hbad₂, hoffset₂, hn₂,
            hqpow₂, hcount₂, hcap₂, hv₂, hinp₂, harrayFrame₂⟩ :=
            ih hnext hremain
              hsize₁ hord₁ hrep₁ hkey₁ hindex₁ hstop₁ hbad₁
              hoffsetNext hcount₁ hn₁ hqpowB₁ hcap₁ hv₁ hinput₁
          have hguard := guard_true hindex hstop hdq hqB
          have hwhole : Run B (.while (.lt (.var "repIndex") (.var "repStop"))
              representativeClassBody) σ σ₂
              (((15 * Nat.clog 2 (size d) + 30) * u +
                12 * Nat.clog 2 (size d) + 61 + chargeTail) + 4) := by
            have h := runWhileTrue hguard hbody hloop₂
            rw [hattempt] at h
            have hsz : (Cond.lt (.var "repIndex") (.var "repStop")).size = 3 := by decide
            rw [hsz] at h
            exact h.mono (by omega)
          refine ⟨σ₂, g₂, ?_, hkey₂, ?_, hsize₂, hord₂,
            ?_, ?_, ?_, hbad₂, ?_, hn₂, ?_, hcount₂,
            hcap₂, hv₂, ?_, ?_⟩
          · simpa using hwhole
          · intro j hj hneq
            exact (hframe₂ j hj hneq).trans (hframe₁ j hj hneq)
          · simpa [writeClassReps] using hrep₂
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hindex₂
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstop₂
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hoffset₂
          · exact hqpow₂.trans hqpow₁
          · have hdrop : (tapeBits tape ++ tail).drop
                (u * Nat.clog 2 (size d)) =
                  (tapeBits tape).drop (u * Nat.clog 2 (size d)) ++ tail := by
              rw [List.drop_append]
              have hmul : u * Nat.clog 2 (size d) ≤
                  t * Nat.clog 2 (size d) := Nat.mul_le_mul_right _ hu
              simp [tapeBits_length, hmul]
            have hdrop₂ : (((tapeBits tape).drop
                (u * Nat.clog 2 (size d)) ++ tail).drop usedTail) =
                (tapeBits tape ++ tail).drop
                  (u * Nat.clog 2 (size d) + usedTail) := by
              rw [← hdrop, List.drop_drop]
            rw [hdrop₂] at hinp₂
            exact hinp₂
          · intro a ha hb
            exact (harrayFrame₂ a ha hb).trans (harrayFrame₁ a ha hb)

/-- The fixed source loop chooses from all compact nonempty classes on one
flat fair-bit input.  The proof-side budget is a sum of capped bit lengths;
no such product or sum is stored in a RAM word.  A successful call exposes
every unused bit to the next class, including unused attempts in its cap. -/
lemma representativeClassLoop_run_bits
    {B n q v t : ℕ} {σ : Env}
    {size ord rep g : ℕ → ℕ} {bits : List Bool} {rest : List ℕ}
    (hbudget : bitBudget size t 0 q ≤ bits.length)
    (hpositive : ∀ d < q, 0 < size d)
    (hpowB : ∀ d < q, 2 ^ Nat.clog 2 (size d) < B)
    (htotal : classStart size q ≤ n)
    (hordValue : ∀ j < classStart size q, ord j < n)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hrep : σ.arrs "repClass" = arrOf n rep)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hcount : σ.vars "classCount" = q)
    (hn : σ.vars "n" = n) (hqpow : σ.vars "qpow" < B)
    (hcap : σ.vars "drawCap" = t)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hinp : σ.inp = bits.map Bool.toNat ++ rest)
    (hqn : q ≤ n) (hnB : n < B)
    (htB : t < B) (htwoB : 2 < B) :
    ∃ (values : List ℕ) (used charge : ℕ) (failed : Bool)
      (σ' : Env) (g' : ℕ → ℕ),
      ClassTrace size t (classStart size) 0 q bits values used charge failed ∧
      Run B representativeClassLoop σ σ' (charge + 12) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ j < n, j ≠ v → g' j = g j) ∧
      σ'.arrs "classSize" = arrOf n size ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "repClass" =
        arrOf n (writeClassReps ord rep 0 values) ∧
      (∀ j (hj : j < values.length),
        (σ'.arrs "repClass")[j]? = some (ord values[j])) ∧
      (∀ j (_hj : j < n), values.length ≤ j →
        (σ'.arrs "repClass")[j]? = some (rep j)) ∧
      σ'.vars "repIndex" = values.length ∧
      σ'.vars "repStop" = (if failed then values.length else q) ∧
      σ'.vars "repFailed" = (if failed then 1 else 0) ∧
      (failed = false ↔ σ'.vars "repIndex" = q) ∧
      values.length ≤ q ∧ used ≤ bits.length ∧
      σ'.vars "drawOffset" = classStart size values.length ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = σ.vars "qpow" ∧
      σ'.vars "classCount" = q ∧ σ'.vars "drawCap" = t ∧
      σ'.vars "v" = v ∧
      σ'.inp = (bits.drop used).map Bool.toNat ++ rest ∧
      σ'.out = σ.out ∧
      (∀ a, a ≠ "key0" → a ≠ "repClass" → σ'.arrs a = σ.arrs a) := by
  obtain ⟨values, used, charge, failed, htrace⟩ :=
    trace_exists size t (classStart size) 0 q bits
      (by intro j hjlo hjhi; exact hpositive j (by simpa using hjhi)) hbudget
  let σ₁ := σ.setVar "repIndex" 0
  let σ₂ := σ₁.setVar "drawOffset" 0
  let σ₃ := σ₂.setVar "repFailed" 0
  let σ₄ := σ₃.setVar "repStop" q
  have hqnB : q < B := lt_of_le_of_lt hqn hnB
  have hinit₁ : Run B (.assign "repIndex" (.lit 0)) σ σ₁ 2 := by
    simpa [σ₁] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hinit₂ : Run B (.assign "drawOffset" (.lit 0)) σ₁ σ₂ 2 := by
    simpa [σ₂] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hinit₃ : Run B (.assign "repFailed" (.lit 0)) σ₂ σ₃ 2 := by
    simpa [σ₃] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hcount₃ : σ₃.vars "classCount" = q := by
    simp [σ₃, σ₂, σ₁, hcount]
  have hinit₄ : Run B (.assign "repStop" (.var "classCount")) σ₃ σ₄ 2 := by
    simpa [σ₄, hcount₃] using
      (Run.assign (evalB_var (by rw [hcount₃]; exact hqnB :
        σ₃.vars "classCount" < B)))
  have hsize₄ : σ₄.arrs "classSize" = arrOf n size := by
    simp [σ₄, σ₃, σ₂, σ₁, hsize]
  have hord₄ : σ₄.arrs "ord" = arrOf n ord := by
    simp [σ₄, σ₃, σ₂, σ₁, hord]
  have hrep₄ : σ₄.arrs "repClass" = arrOf n rep := by
    simp [σ₄, σ₃, σ₂, σ₁, hrep]
  have hkey₄ : σ₄.arrs "key0" = arrOf n g := by
    simp [σ₄, σ₃, σ₂, σ₁, hkey]
  have hindex₄ : σ₄.vars "repIndex" = 0 := by simp [σ₄, σ₃, σ₂, σ₁]
  have hstop₄ : σ₄.vars "repStop" = q := by simp [σ₄]
  have hbad₄ : σ₄.vars "repFailed" = 0 := by simp [σ₄, σ₃]
  have hoffset₄ : σ₄.vars "drawOffset" = classStart size 0 := by
    simp [σ₄, σ₃, σ₂, classStart]
  have hcount₄ : σ₄.vars "classCount" = q := by simp [σ₄, hcount₃]
  have hn₄ : σ₄.vars "n" = n := by simp [σ₄, σ₃, σ₂, σ₁, hn]
  have hqpow₄ : σ₄.vars "qpow" < B := by simpa [σ₄, σ₃, σ₂, σ₁] using hqpow
  have hcap₄ : σ₄.vars "drawCap" = t := by simp [σ₄, σ₃, σ₂, σ₁, hcap]
  have hv₄ : σ₄.vars "v" = v := by simp [σ₄, σ₃, σ₂, σ₁, hv]
  have hinp₄ : σ₄.inp = bits.map Bool.toNat ++ rest := by
    simpa [σ₄, σ₃, σ₂, σ₁] using hinp
  obtain ⟨σ', g', hloop, hkey', hframeKey, hsize', hord', hrep',
    hindex', hstop', hbad', hoffset', hn', hqpow', hcount', hcap',
    hv', hinp', harrayFrame'⟩ :=
    loop_run_trace htrace (by omega : 0 + q = q) hpowB
      htotal hqn hordValue hsize₄ hord₄ hrep₄ hkey₄ hindex₄ hstop₄
      hbad₄ hoffset₄ hcount₄ hn₄ hqpow₄ hcap₄ hv₄ hvn hinp₄
      hnB hqnB htB htwoB
  have hwhole : Run B representativeClassLoop σ σ' (charge + 12) := by
    have h := Run.seq hinit₁
      (Run.seq hinit₂ (Run.seq hinit₃ (Run.seq hinit₄ hloop)))
    have hraw : Run B representativeClassLoop σ σ' (2 + (2 + (2 + (2 + (charge + 4))))) := by
      simpa [representativeClassLoop, seqs] using h
    exact hraw.mono (by omega)
  have hlength := ClassTrace.length_status size t (classStart size) htrace
  have hused := ClassTrace.used_le size t (classStart size) htrace
  refine ⟨values, used, charge, failed, σ', g', htrace, hwhole,
    hkey', hframeKey, hsize', hord', ?_, ?_, ?_, ?_, ?_, hbad',
    ?_, hlength.1, hused, ?_, hn', ?_, hcount', hcap', hv',
    hinp', ?_, ?_⟩
  · simpa using hrep'
  · intro j hj
    rw [hrep', getElem?_arrOf _ (by omega : j < n)]
    exact congrArg some (by simpa using
      (writeClassReps_at ord rep 0 values j hj))
  · intro j hj hout
    rw [hrep', getElem?_arrOf _ hj]
    exact congrArg some (writeClassReps_outside ord rep 0 j values
      (Or.inr (by simpa using hout)))
  · simpa using hindex'
  · simpa using hstop'
  · simpa [hindex'] using hlength.2
  · simpa using hoffset'
  · simpa [σ₄, σ₃, σ₂, σ₁] using hqpow'
  · have hinitOut : σ₄.out = σ.out := by simp [σ₄, σ₃, σ₂, σ₁]
    have hloopOut := hloop.out_eq (by
      simp [representativeClassBody, seqs, drawLogSetup, computeLog,
        countedRejectionSelector, classOffsetDrawLookup, inc,
        Com.NoWrite]; decide)
    exact hloopOut.trans hinitOut
  · intro a ha hb
    exact (harrayFrame' a ha hb).trans (by simp [σ₄, σ₃, σ₂, σ₁])

end Lax457868Proofs.ClassRepresentativeLoop
