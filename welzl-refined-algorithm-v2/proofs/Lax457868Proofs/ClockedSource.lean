import Lax808846Proofs.Imp
import Lax808846Proofs.Reasoning
import Lax808846Proofs.Frame
import Mathlib.Tactic

/-!
A source-level clock for the refined randomized construction.  The budget is
`blockSize * blocksLeft + slotsLeft` mathematically, but no source expression
multiplies these values.  A tick either decreases `slotsLeft`, or decreases
`blocksLeft` and reloads `slotsLeft` with `blockSize - 1`.  Once both counters
are zero the next tick sets `timedOut` and the instrumented source stops
performing original work.
-/

set_option autoImplicit false

namespace Lax457868Proofs.ClockedSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def blockSizeName : String := "__clockBlockSize"
def blocksName : String := "__clockBlocksLeft"
def slotsName : String := "__clockSlotsLeft"
def timedOutName : String := "__clockTimedOut"

/-- Shared loop control. Every enclosing true iteration resets this cell after
its body, so an inner loop may use the same cell without escaping its parent. -/
def continueName : String := "__clockContinue"

/-- One guarded decrement.  The only arithmetic is subtraction by one; in
particular the product of the two budget parameters is never a machine word. -/
def tick : Com :=
  .ite (.lt (.lit 0) (.var slotsName))
    (.assign slotsName (.sub (.var slotsName) (.lit 1)))
    (.ite (.lt (.lit 0) (.var blocksName))
      ((Com.assign blocksName (.sub (.var blocksName) (.lit 1))).seq
       (.assign slotsName (.sub (.var blockSizeName) (.lit 1))))
      (.assign timedOutName (.lit 1)))

/-- Run a tick only while the clock is active. -/
def guardedTick : Com :=
  .ite (.eq (.var timedOutName) (.lit 0)) tick .skip

/-- A source command executed only while the clock is active.  The tick is
charged before the original action. -/
def clockedAtom (c : Com) : Com :=
  guardedTick.seq (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)

/-- Instrument every atomic action and every branching test.  The loop test
uses a private control cell so a naturally completed inner loop cannot stop
its surrounding command.  After timeout, every remaining command is skipped.
The caller reserves the four clock names and the continuation cell. -/
def clockedAt : String → Com → Com
  | _, .skip => clockedAtom .skip
  | _, .assign x e => clockedAtom (.assign x e)
  | _, .store a i e => clockedAtom (.store a i e)
  | _, .read x => clockedAtom (.read x)
  | _, .write e => clockedAtom (.write e)
  | tag, .seq c d => .seq (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d)
  | tag, .ite b c d =>
      guardedTick.seq
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip)
  | tag, .while b c =>
      .ite (.eq (.var timedOutName) (.lit 0))
        ((Com.assign continueName (.lit 1)).seq
          (.while (.eq (.var continueName) (.lit 1))
            (guardedTick.seq
              (.ite (.eq (.var timedOutName) (.lit 0))
                (.ite b ((clockedAt (tag ++ "0") c).seq
                    (.assign continueName (.lit 1)))
                  (.assign continueName (.lit 0)))
                (.assign continueName (.lit 0))))))
        .skip

def clocked (c : Com) : Com := clockedAt "" c

def loopStep (tag : String) (b : Cond) (c : Com) : Com :=
  guardedTick.seq
    (.ite (.eq (.var timedOutName) (.lit 0))
      (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
        (.assign continueName (.lit 0)))
      (.assign continueName (.lit 0)))

def loopCore (tag : String) (b : Cond) (c : Com) : Com :=
  .while (.eq (.var continueName) (.lit 1)) (loopStep tag b c)

/-- Mathematical remaining capacity.  This value is used only in proofs. -/
def capacity (S : ℕ) (σ : Env) : ℕ :=
  S * σ.vars blocksName + σ.vars slotsName

/-- All scalar names read by an expression. -/
def Expr.usedVars : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get _ i => (Expr.usedVars i)
  | .bin _ e f => (Expr.usedVars e) ++ (Expr.usedVars f)

/-- All scalar names read by a condition. -/
def Cond.usedVars : Cond → List String
  | .eq e f => (Expr.usedVars e) ++ (Expr.usedVars f)
  | .lt e f => (Expr.usedVars e) ++ (Expr.usedVars f)

/-- Both read and written scalar names of a source command. -/
def Com.usedVars : Com → List String
  | .skip => []
  | .assign x e => x :: (Expr.usedVars e)
  | .store _ i e => (Expr.usedVars i) ++ (Expr.usedVars e)
  | .seq c d => (Com.usedVars c) ++ (Com.usedVars d)
  | .ite b c d => (Cond.usedVars b) ++ (Com.usedVars c) ++ (Com.usedVars d)
  | .while b c => (Cond.usedVars b) ++ (Com.usedVars c)
  | .read x => [x]
  | .write e => (Expr.usedVars e)

/-- Explicit reservation of the four counter cells and loop control cell.
A source command is fresh when none of its read or written
scalar names is protected. -/
def protectedName (x : String) : Prop :=
  x = blockSizeName ∨ x = blocksName ∨ x = slotsName ∨
  x = timedOutName ∨ x = continueName

def Fresh (c : Com) : Prop :=
  ∀ x ∈ (Com.usedVars c), ¬ protectedName x

lemma wvars_subset_usedVars (c : Com) (x : String)
    (hx : x ∈ c.wvars) : x ∈ Com.usedVars c := by
  induction c with
  | skip => simp [Com.wvars] at hx
  | assign y e => simpa [Com.wvars, Com.usedVars] using Or.inl hx
  | store a i e => simp [Com.wvars] at hx
  | seq c d ihc ihd =>
      simp only [Com.wvars, List.mem_append] at hx
      simp only [Com.usedVars, List.mem_append]
      exact hx.elim (fun h => Or.inl (ihc h)) (fun h => Or.inr (ihd h))
  | ite b c d ihc ihd =>
      simp only [Com.wvars, List.mem_append] at hx
      simp only [Com.usedVars, List.mem_append]
      exact hx.elim (fun h => Or.inl (Or.inr (ihc h)))
        (fun h => Or.inr (ihd h))
  | «while» b c ih =>
      simp only [Com.wvars] at hx
      simp only [Com.usedVars, List.mem_append]
      exact Or.inr (ih hx)
  | read y => simpa [Com.wvars, Com.usedVars] using hx
  | write e => simp [Com.wvars] at hx

lemma fresh_no_write {c : Com} (hf : Fresh c) {x : String}
    (hx : protectedName x) : x ∉ c.wvars :=
  fun hm => hf x (wvars_subset_usedVars c x hm) hx

/-- The clock changes only reserved scalars.  Arrays and both tapes are exact,
which allows a later proof to transfer a read prefix to a shorter tape. -/
def SameSource (σ τ : Env) : Prop :=
  (∀ x, ¬ protectedName x → σ.vars x = τ.vars x) ∧
    σ.arrs = τ.arrs ∧ σ.inp = τ.inp ∧ σ.out = τ.out

lemma sameSource_refl (σ : Env) : SameSource σ σ :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

lemma sameSource_trans {σ τ υ : Env}
    (h₁ : SameSource σ τ) (h₂ : SameSource τ υ) : SameSource σ υ :=
  ⟨fun x hx => (h₁.1 x hx).trans (h₂.1 x hx),
    h₁.2.1.trans h₂.2.1,
    h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.trans h₂.2.2.2⟩

lemma sameSource_setVar {σ τ : Env} (h : SameSource σ τ)
    (x : String) (v : ℕ) :
    SameSource (σ.setVar x v) (τ.setVar x v) := by
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2⟩
  intro y hy
  simp only [Env.setVar]
  split_ifs with he
  · rfl
  · exact h.1 y hy

lemma sameSource_setArr {σ τ : Env} (h : SameSource σ τ)
    (a : String) (i v : ℕ) :
    SameSource (σ.setArr a i v) (τ.setArr a i v) := by
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
  funext b
  simp only [Env.setArr]
  split_ifs
  · exact congrArg (fun l : List ℕ => l.set i v) (congrFun h.2.1 a)
  · exact congrFun h.2.1 b

lemma sameSource_read {σ τ : Env} (h : SameSource σ τ)
    (x : String) (v : ℕ) (rest : List ℕ) :
    SameSource { σ.setVar x v with inp := rest }
      { τ.setVar x v with inp := rest } := by
  exact ⟨(sameSource_setVar h x v).1,
    (sameSource_setVar h x v).2.1, rfl,
    (sameSource_setVar h x v).2.2.2⟩

lemma sameSource_write {σ τ : Env} (h : SameSource σ τ)
    (v : ℕ) :
    SameSource { σ with out := σ.out ++ [v] }
      { τ with out := τ.out ++ [v] } := by
  exact ⟨h.1, h.2.1, h.2.2.1, by rw [h.2.2.2]⟩

lemma sameSource_setClock (σ τ : Env) (x : String)
    (hx : protectedName x) (h : SameSource σ τ) (v : ℕ) :
    SameSource σ (τ.setVar x v) := by
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2⟩
  intro y hy
  simp [Env.setVar]
  split_ifs with he
  · exact (hy (he ▸ hx)).elim
  · exact h.1 y hy

lemma evalB_sameSource {B : ℕ} {σ τ : Env} (h : SameSource σ τ)
    (e : Expr) (hfresh : ∀ x ∈ (Expr.usedVars e), ¬ protectedName x) :
    e.evalB B σ = e.evalB B τ := by
  induction e with
  | lit n => rfl
  | var x =>
      have hx : ¬ protectedName x := hfresh x (by simp [Expr.usedVars])
      simpa [Expr.evalB] using congrArg (fit B) (h.1 x hx)
  | get a i ih =>
      have hi : i.evalB B σ = i.evalB B τ :=
        ih (by simpa [Expr.usedVars] using hfresh)
      simp [Expr.evalB, hi, h.2.1]
  | bin op e f ihe ihf =>
      have he : e.evalB B σ = e.evalB B τ :=
        ihe (by intro x hx; exact hfresh x (by simp [Expr.usedVars, hx]))
      have hf : f.evalB B σ = f.evalB B τ :=
        ihf (by intro x hx; exact hfresh x (by simp [Expr.usedVars, hx]))
      simp [Expr.evalB, he, hf]

lemma condEvalB_sameSource {B : ℕ} {σ τ : Env} (h : SameSource σ τ)
    (b : Cond) (hfresh : ∀ x ∈ (Cond.usedVars b), ¬ protectedName x) :
    b.evalB B σ = b.evalB B τ := by
  cases b with
  | eq e f =>
      have he := evalB_sameSource (B := B) h e
        (by intro x hx; exact hfresh x (by simp [Cond.usedVars, hx]))
      have hf := evalB_sameSource (B := B) h f
        (by intro x hx; exact hfresh x (by simp [Cond.usedVars, hx]))
      simp [Cond.evalB, he, hf]
  | lt e f =>
      have he := evalB_sameSource (B := B) h e
        (by intro x hx; exact hfresh x (by simp [Cond.usedVars, hx]))
      have hf := evalB_sameSource (B := B) h f
        (by intro x hx; exact hfresh x (by simp [Cond.usedVars, hx]))
      simp [Cond.evalB, he, hf]

/-- A safe original run can be replayed in an environment which differs only
on the reserved clock cells.  In particular this transports all bounded
expression evaluations, array accesses and input reads exactly. -/
lemma transport_run {B k : ℕ} {c : Com} {σ σ' τ : Env}
    (hr : BigStepB B c σ σ' k) (hf : Fresh c)
    (hs : SameSource σ τ) :
    ∃ υ, BigStepB B c τ υ k ∧ SameSource σ' υ := by
  induction hr generalizing τ with
  | skip => exact ⟨τ, .skip, hs⟩
  | assign he =>
      rename_i σ₀ x e v
      have he' := evalB_sameSource (B := B) hs e
        (by intro x hx; exact hf x (by simp [Com.usedVars, hx]))
      refine ⟨_, .assign ?_, sameSource_setVar hs _ _⟩
      rwa [← he']
  | store hi he hk =>
      rename_i σ₀ a i e idx v
      have hfi : ∀ x ∈ Expr.usedVars i, ¬ protectedName x := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hfe : ∀ x ∈ Expr.usedVars e, ¬ protectedName x := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hi' := evalB_sameSource (B := B) hs i hfi
      have he' := evalB_sameSource (B := B) hs e hfe
      refine ⟨_, .store ?_ ?_ ?_, sameSource_setArr hs _ _ _⟩
      · rwa [← hi']
      · rwa [← he']
      · simpa [← congrFun hs.2.1 a] using hk
  | seq hc hd ihc ihd =>
      rename_i c d σ₀ σ₁ σ₂ k₀ k₁
      have hfc : Fresh c := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hfd : Fresh d := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      obtain ⟨τ', hc', hs'⟩ := ihc hfc hs
      obtain ⟨υ, hd', hs''⟩ := ihd hfd hs'
      exact ⟨υ, .seq hc' hd', hs''⟩
  | ite_true hb hc ih =>
      rename_i b c d σ₀ σ₁ k₀
      have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hfc : Fresh c := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hb' := condEvalB_sameSource (B := B) hs b hfb
      obtain ⟨υ, hc', hs'⟩ := ih hfc hs
      refine ⟨υ, .ite_true ?_ hc', hs'⟩
      rwa [← hb']
  | ite_false hb hd ih =>
      rename_i b c d σ₀ σ₁ k₀
      have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hfd : Fresh d := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hb' := condEvalB_sameSource (B := B) hs b hfb
      obtain ⟨υ, hd', hs'⟩ := ih hfd hs
      refine ⟨υ, .ite_false ?_ hd', hs'⟩
      rwa [← hb']
  | while_true hb hc hw ihc ihw =>
      rename_i b c σ₀ σ₁ σ₂ k₀ k₁
      have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hfc : Fresh c := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hb' := condEvalB_sameSource (B := B) hs b hfb
      obtain ⟨τ', hc', hs'⟩ := ihc hfc hs
      obtain ⟨υ, hw', hs''⟩ := ihw hf hs'
      refine ⟨υ, .while_true ?_ hc' hw', hs''⟩
      rwa [← hb']
  | while_false hb =>
      rename_i b c σ₀
      have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
        intro x hx; exact hf x (by simp [Com.usedVars, hx])
      have hb' := condEvalB_sameSource (B := B) hs b hfb
      refine ⟨τ, .while_false ?_, hs⟩
      rwa [← hb']
  | read hin =>
      refine ⟨_, .read ?_, sameSource_read hs _ _ _⟩
      simpa [← hs.2.2.1] using hin
  | write he =>
      rename_i σ₀ e v
      have he' := evalB_sameSource (B := B) hs e
        (by intro x hx; exact hf x (by simp [Com.usedVars, hx]))
      refine ⟨_, .write ?_, sameSource_write hs _⟩
      rwa [← he']

private lemma tick_only_clock_writes (x : String) (hx : x ∈ tick.wvars) :
    protectedName x := by
  simp [tick, Com.wvars] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

lemma sameSource_of_tick {B : ℕ} {σ τ υ : Env} {K : ℕ}
    (h : SameSource σ τ) (hr : Run B tick τ υ K) :
    SameSource σ υ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [h.1 x hx]
    exact (hr.frame_var x (fun hm => hx (tick_only_clock_writes x hm))).symm
  · funext a
    rw [hr.frame_arr a (by simp [tick, Com.warrs])]
    exact congrFun h.2.1 a
  · rw [hr.frame_inp (by simp [tick, Com.reads])]
    exact h.2.2.1
  · rw [hr.out_eq (by simp [tick, Com.NoWrite])]
    exact h.2.2.2

/-- The four clock cells have pairwise distinct names. -/
lemma clockNames_distinct :
    blockSizeName ≠ blocksName ∧ blockSizeName ≠ slotsName ∧
    blockSizeName ≠ timedOutName ∧ blocksName ≠ slotsName ∧
    blocksName ≠ timedOutName ∧ slotsName ≠ timedOutName := by
  decide

lemma continueName_ne_clock :
    continueName ≠ blockSizeName ∧ continueName ≠ blocksName ∧
    continueName ≠ slotsName ∧ continueName ≠ timedOutName := by
  decide

/-- Conditions on the two machine-word counters.  The mathematical capacity
may be much larger than `B`; neither field stores it. -/
structure Ready (B S : ℕ) (σ : Env) : Prop where
  positive : 0 < S
  sizeBound : S < B
  blockSize : σ.vars blockSizeName = S
  blocksBound : σ.vars blocksName < B
  slotsBound : σ.vars slotsName < S
  active : σ.vars timedOutName = 0

lemma ready_of_fresh_run {B S K : ℕ} {c : Com} {σ τ : Env}
    (hready : Ready B S σ) (hf : Fresh c) (hr : Run B c σ τ K) :
    Ready B S τ ∧ capacity S τ = capacity S σ := by
  have hsize := hr.frame_var blockSizeName
    (fresh_no_write hf (Or.inl rfl))
  have hblocks := hr.frame_var blocksName
    (fresh_no_write hf (Or.inr (Or.inl rfl)))
  have hslots := hr.frame_var slotsName
    (fresh_no_write hf (Or.inr (Or.inr (Or.inl rfl))))
  have hactive := hr.frame_var timedOutName
    (fresh_no_write hf (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  refine ⟨⟨hready.positive, hready.sizeBound, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hsize]; exact hready.blockSize
  · rw [hblocks]; exact hready.blocksBound
  · rw [hslots]; exact hready.slotsBound
  · rw [hactive]; exact hready.active
  · simp [capacity, hblocks, hslots]

lemma ready_setContinue {B S : ℕ} {σ : Env}
    (h : Ready B S σ) (v : ℕ) :
    Ready B S (σ.setVar continueName v) ∧
      capacity S (σ.setVar continueName v) = capacity S σ := by
  have hn := continueName_ne_clock
  refine ⟨⟨h.positive, h.sizeBound, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa [Env.setVar, hn.1.symm] using h.blockSize
  · simpa [Env.setVar, hn.2.1.symm] using h.blocksBound
  · simpa [Env.setVar, hn.2.2.1.symm] using h.slotsBound
  · simpa [Env.setVar, hn.2.2.2.symm] using h.active
  · simp [capacity, Env.setVar, hn.2.1.symm, hn.2.2.1.symm]

lemma timeout_setContinue {S : ℕ} {σ : Env}
    (h : σ.vars timedOutName = 1 ∧ capacity S σ = 0) (v : ℕ) :
    (σ.setVar continueName v).vars timedOutName = 1 ∧
      capacity S (σ.setVar continueName v) = 0 := by
  have hn := continueName_ne_clock
  refine ⟨?_, ?_⟩
  · simpa [Env.setVar, hn.2.2.2.symm] using h.1
  · simpa [capacity, Env.setVar, hn.2.1.symm, hn.2.2.1.symm] using h.2

lemma run_setContinue {B : ℕ} {σ : Env} (v : ℕ)
    (hv : v < B) :
    Run B (.assign continueName (.lit v)) σ
      (σ.setVar continueName v) 2 := by
  simpa using (Run.assign (x := continueName) (evalB_lit hv))

lemma continue_test_true {B : ℕ} {σ : Env}
    (hB : 1 < B) (hv : σ.vars continueName = 1) :
    (Cond.eq (.var continueName) (.lit 1)).evalB B σ = some true := by
  have hvar : (Expr.var continueName).evalB B σ = some 1 := by
    simpa [hv] using (evalB_var (x := continueName)
      (by rw [hv]; omega : σ.vars continueName < B))
  simpa using (evalB_condEq hvar (evalB_lit (n := 1) hB))

lemma continue_test_false {B : ℕ} {σ : Env}
    (hB : 1 < B) (hv : σ.vars continueName = 0) :
    (Cond.eq (.var continueName) (.lit 1)).evalB B σ = some false := by
  have hvar : (Expr.var continueName).evalB B σ = some 0 := by
    simpa [hv] using (evalB_var (x := continueName)
      (by rw [hv]; omega : σ.vars continueName < B))
  simpa using (evalB_condEq hvar (evalB_lit (n := 1) hB))

private lemma run_while_true {B K K' : ℕ} {b : Cond} {c : Com}
    {σ τ υ : Env} (hb : b.evalB B σ = some true)
    (hc : Run B c σ τ K) (hw : Run B (.while b c) τ υ K') :
    Run B (.while b c) σ υ (1 + b.size + K + K') := by
  obtain ⟨k, hk, hbc⟩ := hc
  obtain ⟨k', hk', hbw⟩ := hw
  exact ⟨1 + b.size + k + k', by omega, .while_true hb hbc hbw⟩

/-- A successful tick consumes one unit of the mathematical capacity. -/
lemma tick_run_positive {B S : ℕ} {σ : Env}
    (h : Ready B S σ) (hcap : 0 < capacity S σ) :
    ∃ τ, Run B tick σ τ 40 ∧ Ready B S τ ∧
      capacity S τ + 1 = capacity S σ ∧
      τ.inp = σ.inp ∧ τ.out = σ.out ∧ τ.arrs = σ.arrs := by
  have hB : 1 < B := by have := h.positive; have := h.sizeBound; omega
  have hslots := h.slotsBound
  have hblocks := h.blocksBound
  have hsize := h.blockSize
  have hactive := h.active
  by_cases hs : 0 < σ.vars slotsName
  · let τ := σ.setVar slotsName (σ.vars slotsName - 1)
    have hcond : (Cond.lt (.lit 0) (.var slotsName)).evalB B σ = some true := by
      simpa [hs] using
        (evalB_condLt (evalB_lit (by omega : 0 < B))
          (evalB_var (hslots.trans h.sizeBound)))
    have hsub : (Expr.sub (.var slotsName) (.lit 1)).evalB B σ =
        some (σ.vars slotsName - 1) := by
      simpa using (evalB_bin (op := .sub)
        (evalB_var (x := slotsName) (hslots.trans h.sizeBound))
        (evalB_lit (n := 1) hB)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hslots.trans h.sizeBound)))
    have hr : Run B tick σ τ 40 := by
      have ha := Run.assign (x := slotsName) hsub
      exact (Run.ite_true (d := .ite (.lt (.lit 0) (.var blocksName))
        ((Com.assign blocksName (.sub (.var blocksName) (.lit 1))).seq
          (.assign slotsName (.sub (.var blockSizeName) (.lit 1))))
        (.assign timedOutName (.lit 1))) hcond ha).mono (by decide)
    refine ⟨τ, hr, ?_, ?_, rfl, rfl, rfl⟩
    · refine ⟨h.positive, h.sizeBound, ?_, ?_, ?_, ?_⟩
      · simpa [τ, Env.setVar, blockSizeName, slotsName] using h.blockSize
      · simpa [τ, Env.setVar, blocksName, slotsName] using h.blocksBound
      · simpa [τ, Env.setVar, slotsName] using
          (lt_of_le_of_lt (Nat.sub_le (σ.vars slotsName) 1) hslots)
      · simpa [τ, Env.setVar, timedOutName, slotsName] using h.active
    · have ha : S * σ.vars blocksName + (σ.vars slotsName - 1) + 1 =
          S * σ.vars blocksName + σ.vars slotsName := by omega
      simpa [capacity, τ, Env.setVar, blocksName, slotsName] using ha
  · have hs0 : σ.vars slotsName = 0 := by omega
    have hb : 0 < σ.vars blocksName := by
      dsimp [capacity] at hcap
      have hS : 0 < S := h.positive
      nlinarith
    let σ₁ := σ.setVar blocksName (σ.vars blocksName - 1)
    let τ := σ₁.setVar slotsName (S - 1)
    have hfirst : (Cond.lt (.lit 0) (.var slotsName)).evalB B σ = some false := by
      simpa [hs] using
        (evalB_condLt (evalB_lit (by omega : 0 < B))
          (evalB_var (hslots.trans h.sizeBound)))
    have hsecond : (Cond.lt (.lit 0) (.var blocksName)).evalB B σ = some true := by
      simpa [hb] using
        (evalB_condLt (evalB_lit (by omega : 0 < B))
          (evalB_var h.blocksBound))
    have hsubBlock : (Expr.sub (.var blocksName) (.lit 1)).evalB B σ =
        some (σ.vars blocksName - 1) := by
      simpa using (evalB_bin (op := .sub)
        (evalB_var (x := blocksName) hblocks)
        (evalB_lit (n := 1) hB)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hblocks))
    have hsubSlot : (Expr.sub (.var blockSizeName) (.lit 1)).evalB B σ₁ =
        some (S - 1) := by
      have hvar : σ₁.vars blockSizeName = S := by
        simpa [σ₁, Env.setVar, blockSizeName, blocksName] using h.blockSize
      have hr : (Expr.sub (.var blockSizeName) (.lit 1)).evalB B σ₁ =
          some (σ₁.vars blockSizeName - 1) := by
        simpa using (evalB_bin (op := .sub)
          (evalB_var (x := blockSizeName) (by rw [hvar]; exact h.sizeBound))
          (evalB_lit (n := 1) hB)
          (by rw [hvar]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h.sizeBound))
      rw [hvar] at hr
      exact hr
    have hr : Run B tick σ τ 40 := by
      have ha := Run.assign (x := blocksName) hsubBlock
      have hz := Run.assign (x := slotsName) hsubSlot
      have hseq : Run B
          ((Com.assign blocksName (.sub (.var blocksName) (.lit 1))).seq
            (.assign slotsName (.sub (.var blockSizeName) (.lit 1))))
          σ τ 8 := by simpa [σ₁, τ] using ha.seq hz
      have hi := Run.ite_true
        (d := .assign timedOutName (.lit 1)) hsecond hseq
      exact (Run.ite_false (d := .ite (.lt (.lit 0) (.var blocksName))
        ((Com.assign blocksName (.sub (.var blocksName) (.lit 1))).seq
          (.assign slotsName (.sub (.var blockSizeName) (.lit 1))))
        (.assign timedOutName (.lit 1))) hfirst hi).mono (by decide)
    refine ⟨τ, hr, ?_, ?_, rfl, rfl, rfl⟩
    · refine ⟨h.positive, h.sizeBound, ?_, ?_, ?_, ?_⟩
      · simpa [τ, σ₁, Env.setVar, blockSizeName, blocksName, slotsName] using h.blockSize
      · simpa [τ, σ₁, Env.setVar, blocksName, slotsName] using
          (Nat.lt_of_le_of_lt (Nat.sub_le (σ.vars blocksName) 1) hblocks)
      · simp [τ, Env.setVar, slotsName]
        omega
      · simpa [τ, σ₁, Env.setVar, timedOutName, blocksName, slotsName] using h.active
    · have heq : S * (σ.vars blocksName - 1) + S = S * σ.vars blocksName := by
        have hbsub : σ.vars blocksName - 1 + 1 = σ.vars blocksName := by omega
        calc
          S * (σ.vars blocksName - 1) + S = S * (σ.vars blocksName - 1 + 1) := by ring
          _ = S * σ.vars blocksName := by rw [hbsub]
      have hSsub : S - 1 + 1 = S := by omega
      have ha : S * (σ.vars blocksName - 1) + (S - 1) + 1 =
          S * σ.vars blocksName + σ.vars slotsName := by omega
      simpa [capacity, τ, σ₁, Env.setVar, blocksName, slotsName] using ha

/-- At capacity zero a tick changes only the timeout flag. -/
lemma tick_run_exhausted {B S : ℕ} {σ : Env}
    (h : Ready B S σ) (hcap : capacity S σ = 0) :
    Run B tick σ (σ.setVar timedOutName 1) 40 := by
  have hB : 1 < B := by have := h.positive; have := h.sizeBound; omega
  have hslots := h.slotsBound
  have hblocks := h.blocksBound
  have hs : σ.vars slotsName = 0 := by
    dsimp [capacity] at hcap
    omega
  have hb : σ.vars blocksName = 0 := by
    dsimp [capacity] at hcap
    have : 0 < S := h.positive
    nlinarith
  have hfirst : (Cond.lt (.lit 0) (.var slotsName)).evalB B σ = some false := by
    simpa [hs] using
      (evalB_condLt (evalB_lit (by omega : 0 < B))
        (evalB_var (hslots.trans h.sizeBound)))
  have hsecond : (Cond.lt (.lit 0) (.var blocksName)).evalB B σ = some false := by
    simpa [hb] using
      (evalB_condLt (evalB_lit (by omega : 0 < B))
        (evalB_var h.blocksBound))
  have ha : Run B (.assign timedOutName (.lit 1)) σ
      (σ.setVar timedOutName 1) 2 :=
    Run.assign (evalB_lit hB)
  have hi := Run.ite_false
    (c := (Com.assign blocksName (.sub (.var blocksName) (.lit 1))).seq
      (.assign slotsName (.sub (.var blockSizeName) (.lit 1)))) hsecond ha
  exact (Run.ite_false (d := .ite (.lt (.lit 0) (.var blocksName))
    ((Com.assign blocksName (.sub (.var blocksName) (.lit 1))).seq
      (.assign slotsName (.sub (.var blockSizeName) (.lit 1))))
    (.assign timedOutName (.lit 1))) hfirst hi).mono (by decide)

/-- A guarded tick is total for an active, well-formed clock.  Positive
capacity advances by exactly one; exhausted capacity sets the timeout bit.
Both cases leave the input, output, and every array untouched. -/
lemma guardedTick_run {B S : ℕ} {σ : Env} (h : Ready B S σ) :
    ∃ τ, Run B guardedTick σ τ 44 ∧ SameSource σ τ ∧
      ((0 < capacity S σ ∧ Ready B S τ ∧
          capacity S τ + 1 = capacity S σ) ∨
       (capacity S σ = 0 ∧ τ.vars timedOutName = 1 ∧
          capacity S τ = 0)) := by
  have hzero : 0 < B := by have := h.sizeBound; omega
  have ht : (Cond.eq (.var timedOutName) (.lit 0)).evalB B σ = some true := by
    have hv : (Expr.var timedOutName).evalB B σ = some 0 := by
      simpa [h.active] using
        (evalB_var (x := timedOutName) (by rw [h.active]; omega :
          σ.vars timedOutName < B))
    simpa using (evalB_condEq hv (evalB_lit (n := 0) hzero))
  by_cases hcap : 0 < capacity S σ
  · obtain ⟨τ, hr, hready, hdrop, -, -, -⟩ := tick_run_positive h hcap
    refine ⟨τ, ?_, sameSource_of_tick (sameSource_refl σ) hr,
      Or.inl ⟨hcap, hready, hdrop⟩⟩
    simpa [guardedTick] using (Run.ite_true (d := .skip) ht hr)
  · have hzeroCap : capacity S σ = 0 := by omega
    let τ := σ.setVar timedOutName 1
    have hr := tick_run_exhausted h hzeroCap
    refine ⟨τ, ?_, sameSource_of_tick (sameSource_refl σ) hr,
      Or.inr ⟨hzeroCap, ?_, ?_⟩⟩
    · simpa [guardedTick] using (Run.ite_true (d := .skip) ht hr)
    · simp [τ, Env.setVar]
    · simpa [capacity, τ, Env.setVar, timedOutName, blocksName,
        slotsName] using hzeroCap

/-- Source cost of skipping a command after timeout.  It depends only on the
fixed syntax, not on data or on the mathematical budget. -/
def offCost : Com → ℕ
  | .seq c d => offCost c + offCost d
  | .while _ _ => 5
  | _ => 10

private lemma timedOut_test_false {B : ℕ} {σ : Env}
    (hB : 1 < B) (hoff : σ.vars timedOutName = 1) :
    (Cond.eq (.var timedOutName) (.lit 0)).evalB B σ = some false := by
  have hv : (Expr.var timedOutName).evalB B σ = some 1 := by
    simpa [hoff] using (evalB_var (x := timedOutName) (by rw [hoff]; omega :
      σ.vars timedOutName < B))
  simpa using (evalB_condEq hv (evalB_lit (n := 0) (by omega : 0 < B)))

private lemma timedOut_test_true {B : ℕ} {σ : Env}
    (hB : 0 < B) (hon : σ.vars timedOutName = 0) :
    (Cond.eq (.var timedOutName) (.lit 0)).evalB B σ = some true := by
  have hv : (Expr.var timedOutName).evalB B σ = some 0 := by
    have hlt : σ.vars timedOutName < B := by rw [hon]; exact hB
    rw [evalB_var hlt, hon]
  simpa using (evalB_condEq hv (evalB_lit (n := 0) hB))

private lemma guardedTick_off {B : ℕ} {σ : Env}
    (hB : 1 < B) (hoff : σ.vars timedOutName = 1) :
    Run B guardedTick σ σ 5 := by
  have ht := timedOut_test_false hB hoff
  simpa [guardedTick] using (Run.ite_false (c := tick) ht Run.skip)

lemma loopCore_exit_timeout {B : ℕ} {σ : Env} {tag : String}
    {b : Cond} {c : Com} (hB : 1 < B)
    (hoff : σ.vars timedOutName = 1)
    (hcont : σ.vars continueName = 1) :
    Run B (loopCore tag b c) σ (σ.setVar continueName 0) 19 := by
  let τ := σ.setVar continueName 0
  have hguard := continue_test_true hB hcont
  have hstop := continue_test_false hB (σ := τ) (by simp [τ, Env.setVar])
  have hbranch := timedOut_test_false hB hoff
  have hz : Run B (.assign continueName (.lit 0)) σ τ 2 :=
    run_setContinue 0 (by omega)
  have hi : Run B
      (.ite (.eq (.var timedOutName) (.lit 0))
        (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
          (.assign continueName (.lit 0)))
        (.assign continueName (.lit 0))) σ τ 6 := by
    simpa using (Run.ite_false hbranch hz)
  have hstep : Run B (loopStep tag b c) σ τ 11 := by
    simpa [loopStep] using (guardedTick_off hB hoff).seq hi
  have htail : Run B (loopCore tag b c) τ τ 4 := by
    simpa [loopCore] using (Run.while_false (c := loopStep tag b c) hstop)
  have hrun := run_while_true hguard hstep htail
  simpa [loopCore] using hrun

private lemma clockedAtom_off {B : ℕ} {σ : Env} {c : Com}
    (hB : 1 < B) (hoff : σ.vars timedOutName = 1) :
    Run B (clockedAtom c) σ σ 10 := by
  have hg := guardedTick_off hB hoff
  have ht := timedOut_test_false hB hoff
  have hi : Run B (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
      σ σ 5 := by
    simpa using (Run.ite_false (c := c) ht Run.skip)
  simpa [clockedAtom] using hg.seq hi

/-- A source action with a transportable bounded-run contract passes through
one positive tick unchanged.  At zero capacity the action is skipped, with
both tapes still at the prefix reached so far.  A caller may instantiate
`hbody` with an atomic `BigStepB` transport lemma. -/
lemma clockedAtom_run {B S K : ℕ} {σ σ' : Env} {c : Com}
    (h : Ready B S σ)
    (hclock : timedOutName ∉ c.wvars)
    (hbody : ∀ τ, SameSource σ τ → ∃ υ, Run B c τ υ K ∧ SameSource σ' υ) :
    ∃ υ, Run B (clockedAtom c) σ υ (49 + K) ∧
      ((0 < capacity S σ ∧ υ.vars timedOutName = 0 ∧ SameSource σ' υ) ∨
       (capacity S σ = 0 ∧ υ.vars timedOutName = 1 ∧ SameSource σ υ)) := by
  obtain ⟨τ, htick, hsame, hcase⟩ := guardedTick_run h
  rcases hcase with ⟨hcap, hready, -⟩ | ⟨hcap, hoff, -⟩
  · obtain ⟨υ, hrun, hout⟩ := hbody τ hsame
    have ht := timedOut_test_true (B := B)
      (by have := h.sizeBound; omega) hready.active
    have hbranch : Run B
        (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
        τ υ (4 + K) := by
      simpa using (Run.ite_true (d := .skip) ht hrun)
    refine ⟨υ, ?_, Or.inl ⟨hcap, ?_, hout⟩⟩
    · simpa [clockedAtom] using (htick.seq hbranch).mono (by omega)
    · rw [hrun.frame_var timedOutName hclock]
      exact hready.active
  · have hB : 1 < B := by have := h.sizeBound; have := h.positive; omega
    have ht := timedOut_test_false hB hoff
    have hbranch : Run B
        (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
        τ τ 5 := by
      simpa using (Run.ite_false (c := c) ht Run.skip)
    refine ⟨τ, ?_, Or.inr ⟨hcap, hoff, hsame⟩⟩
    simpa [clockedAtom] using (htick.seq hbranch).mono (by omega)

/-- A timed-out subprogram evaluates no original expression and reads no
input.  This is also the unwinding rule for nested loops. -/
lemma clockedAt_off {B : ℕ} {σ : Env} (hB : 1 < B)
    (hoff : σ.vars timedOutName = 1) :
    ∀ (tag : String) (c : Com), Run B (clockedAt tag c) σ σ (offCost c) := by
  intro tag c
  induction c generalizing tag with
  | skip => exact clockedAtom_off hB hoff
  | assign x e => exact clockedAtom_off hB hoff
  | store a i e => exact clockedAtom_off hB hoff
  | read x => exact clockedAtom_off hB hoff
  | write e => exact clockedAtom_off hB hoff
  | seq c d ihc ihd =>
      simpa [clockedAt, offCost] using
        (ihc (tag ++ "0")).seq (ihd (tag ++ "1"))
  | ite b c d ihc ihd =>
      have hg := guardedTick_off hB hoff
      have ht := timedOut_test_false hB hoff
      have hi : Run B
          (.ite (.eq (.var timedOutName) (.lit 0))
            (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
            .skip) σ σ 5 := by
        simpa using (Run.ite_false
          (c := .ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          ht Run.skip)

      simpa [clockedAt, offCost] using hg.seq hi
  | «while» b c ih =>
      have ht := timedOut_test_false hB hoff
      simpa [clockedAt, offCost] using
        (Run.ite_false
          (c := (Com.assign continueName (.lit 1)).seq
            (.while (.eq (.var continueName) (.lit 1))
              (guardedTick.seq
                (.ite (.eq (.var timedOutName) (.lit 0))
                  (.ite b ((clockedAt (tag ++ "0") c).seq
                      (.assign continueName (.lit 1)))
                    (.assign continueName (.lit 0)))
                  (.assign continueName (.lit 0))))))
          ht Run.skip)

/-- A successful clocked fragment matches the corresponding source result.
A timed-out fragment has drained the mathematical clock and never resumes. -/
def Outcome (B S : ℕ) (sourceFinal initial final : Env) : Prop :=
  capacity S final ≤ capacity S initial ∧
    ((Ready B S final ∧ SameSource sourceFinal final) ∨
     (final.vars timedOutName = 1 ∧ capacity S final = 0))

private lemma atom_good {B S k : ℕ} {c : Com} {σ σ' τ : Env}
    (hr : BigStepB B c σ σ' k) (hf : Fresh c)
    (hready : Ready B S τ) (hs : SameSource σ τ) :
    ∃ υ K, Run B (clockedAtom c) τ υ K ∧
      Outcome B S σ' τ υ ∧ K ≤ 49 + k := by
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨_, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · obtain ⟨υ, hbody, hsameBody⟩ :=
      transport_run hr hf (sameSource_trans hs hsameTick)
    have hrunBody : Run B c θ υ k := Run.of_bigStepB hbody
    obtain ⟨hreadyυ, hcapEq⟩ := ready_of_fresh_run hreadyθ hf hrunBody
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hbranch : Run B
        (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
        θ υ (4 + k) := by
      simpa using (Run.ite_true (d := .skip) ht hrunBody)
    refine ⟨υ, 48 + k, ?_, ?_, by omega⟩
    · simpa [clockedAtom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using htick.seq hbranch
    · refine ⟨?_, Or.inl ⟨hreadyυ, hsameBody⟩⟩
      omega
  · have hB : 1 < B := by
      have := hready.positive; have := hready.sizeBound; omega
    have ht := timedOut_test_false hB hoff
    have hbranch : Run B
        (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
        θ θ 5 := by
      simpa using (Run.ite_false (c := c) ht Run.skip)
    refine ⟨θ, 49, ?_, ?_, by omega⟩
    · simpa [clockedAtom] using htick.seq hbranch
    · exact ⟨by omega, Or.inr ⟨hoff, hcapθ⟩⟩

def ClockedGood (B S : ℕ) (c : Com) (σ σ' : Env) : Prop :=
  ∀ tag τ, Ready B S τ → SameSource σ τ →
    ∃ υ K, Run B (clockedAt tag c) τ υ K ∧
      Outcome B S σ' τ υ

def LoopGood (B S : ℕ) (b : Cond) (c : Com)
    (σ σ' : Env) : Prop :=
  ∀ tag τ, Ready B S τ → SameSource σ τ →
    τ.vars continueName = 1 →
    ∃ υ K, Run B (loopCore tag b c) τ υ K ∧
      Outcome B S σ' τ υ

def ExtraGood (B S : ℕ) (c : Com) (σ σ' : Env) : Prop :=
  match c with
  | .while b body => LoopGood B S b body σ σ'
  | _ => True

private lemma simple_good {B S k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) (hf : Fresh c)
    (hshape : ∀ tag, clockedAt tag c = clockedAtom c) :
    ClockedGood B S c σ σ' := by
  intro tag τ hready hs
  obtain ⟨υ, K, hrun, hout, -⟩ := atom_good hr hf hready hs
  exact ⟨υ, K, hshape tag ▸ hrun, hout⟩

private lemma seq_good {B S : ℕ} {c d : Com} {σ μ σ' : Env}
    (hc : ClockedGood B S c σ μ)
    (hd : ClockedGood B S d μ σ') :
    ClockedGood B S (.seq c d) σ σ' := by
  intro tag τ hready hs
  obtain ⟨θ, Kc, hrunC, hresC⟩ := hc (tag ++ "0") τ hready hs
  rcases hresC.2 with ⟨hreadyθ, hsameθ⟩ | ⟨hoff, hcap⟩
  · obtain ⟨υ, Kd, hrunD, hresD⟩ :=
      hd (tag ++ "1") θ hreadyθ hsameθ
    refine ⟨υ, Kc + Kd, ?_, ?_⟩
    · simpa [clockedAt] using hrunC.seq hrunD
    · exact ⟨le_trans hresD.1 hresC.1, hresD.2⟩
  · have hB : 1 < B := by
      have := hready.positive; have := hready.sizeBound; omega
    have hrunD := clockedAt_off hB hoff (tag ++ "1") d
    refine ⟨θ, Kc + offCost d, ?_, ?_⟩
    · simpa [clockedAt] using hrunC.seq hrunD
    · exact ⟨hresC.1, Or.inr ⟨hoff, hcap⟩⟩

private lemma ite_good_true {B S : ℕ} {b : Cond} {c d : Com}
    {σ σ' : Env} (hb : b.evalB B σ = some true)
    (hf : Fresh (.ite b c d))
    (hc : ClockedGood B S c σ σ') :
    ClockedGood B S (.ite b c d) σ σ' := by
  intro tag τ hready hs
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some true := by rwa [← hbθ]
    obtain ⟨υ, K, hrunC, hout⟩ :=
      hc (tag ++ "0") θ hreadyθ (sameSource_trans hs hsameTick)
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hinner : Run B
        (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        θ υ (1 + b.size + K) := Run.ite_true hb' hrunC
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ υ (4 + 1 + b.size + K) := by
      convert Run.ite_true (d := .skip) ht hinner using 1
      simp [Cond.size, Expr.size]
      omega
    refine ⟨υ, 44 + (4 + 1 + b.size + K), ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by have := hout.1; omega, hout.2⟩
  · have hB : 1 < B := by
      have := hready.positive; have := hready.sizeBound; omega
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ θ 5 := by
      simpa using Run.ite_false
        (c := .ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        ht Run.skip
    refine ⟨θ, 49, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by omega, Or.inr ⟨hoff, hcapθ⟩⟩

private lemma ite_good_false {B S : ℕ} {b : Cond} {c d : Com}
    {σ σ' : Env} (hb : b.evalB B σ = some false)
    (hf : Fresh (.ite b c d))
    (hd : ClockedGood B S d σ σ') :
    ClockedGood B S (.ite b c d) σ σ' := by
  intro tag τ hready hs
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some false := by rwa [← hbθ]
    obtain ⟨υ, K, hrunD, hout⟩ :=
      hd (tag ++ "1") θ hreadyθ (sameSource_trans hs hsameTick)
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hinner : Run B
        (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        θ υ (1 + b.size + K) := Run.ite_false hb' hrunD
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ υ (4 + 1 + b.size + K) := by
      convert Run.ite_true (d := .skip) ht hinner using 1
      simp [Cond.size, Expr.size]
      omega
    refine ⟨υ, 44 + (4 + 1 + b.size + K), ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by have := hout.1; omega, hout.2⟩
  · have hB : 1 < B := by
      have := hready.positive; have := hready.sizeBound; omega
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ θ 5 := by
      simpa using Run.ite_false
        (c := .ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        ht Run.skip
    refine ⟨θ, 49, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by omega, Or.inr ⟨hoff, hcapθ⟩⟩

private lemma loop_good_false {B S : ℕ} {b : Cond} {c : Com}
    {σ : Env} (hb : b.evalB B σ = some false)
    (hf : Fresh (.while b c)) :
    LoopGood B S b c σ σ := by
  intro tag τ hready hs hcontinue
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  have hguard := continue_test_true hB hcontinue
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some false := by rwa [← hbθ]
    let υ := θ.setVar continueName 0
    have hset : Run B (.assign continueName (.lit 0)) θ υ 2 := by
      simpa [υ] using run_setContinue (B := B) (σ := θ) 0 (by omega)
    have hinner : Run B
        (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
          (.assign continueName (.lit 0))) θ υ (1 + b.size + 2) :=
      Run.ite_false hb' hset
    have ht := timedOut_test_true (B := B)
      (by omega) hreadyθ.active
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ υ
        (4 + (1 + b.size + 2)) := by
      convert Run.ite_true (d := .assign continueName (.lit 0)) ht hinner using 1
      simp [Cond.size, Expr.size]
    have hstep : Run B (loopStep tag b c) τ υ
        (44 + (4 + (1 + b.size + 2))) := by
      simpa [loopStep] using htick.seq houter
    have hstop : Run B (loopCore tag b c) υ υ 4 := by
      have ht0 := continue_test_false hB (σ := υ) (by simp [υ, Env.setVar])
      simpa [loopCore] using (Run.while_false (c := loopStep tag b c) ht0)
    have hrun := run_while_true hguard hstep hstop
    have hreadyυ := (ready_setContinue hreadyθ 0).1
    have hcapυ := (ready_setContinue hreadyθ 0).2
    have hsameυ : SameSource σ υ :=
      sameSource_trans (sameSource_trans hs hsameTick)
        (sameSource_setClock θ θ continueName
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          (sameSource_refl θ) 0)
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size +
        (44 + (4 + (1 + b.size + 2))) + 4, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · have hcapυ' : capacity S υ = capacity S θ := hcapυ
      exact ⟨by omega, Or.inl ⟨hreadyυ, hsameυ⟩⟩
  · let υ := θ.setVar continueName 0
    have hset : Run B (.assign continueName (.lit 0)) θ υ 2 := by
      simpa [υ] using run_setContinue (B := B) (σ := θ) 0 (by omega)
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ υ 6 := by
      simpa using Run.ite_false ht hset
    have hstep : Run B (loopStep tag b c) τ υ 50 := by
      simpa [loopStep] using htick.seq houter
    have hstop : Run B (loopCore tag b c) υ υ 4 := by
      have ht0 := continue_test_false hB (σ := υ) (by simp [υ, Env.setVar])
      simpa [loopCore] using (Run.while_false (c := loopStep tag b c) ht0)
    have hrun := run_while_true hguard hstep hstop
    have htimeoutυ := timeout_setContinue ⟨hoff, hcapθ⟩ 0
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size + 50 + 4, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · have htimeoutυ' : υ.vars timedOutName = 1 ∧ capacity S υ = 0 := htimeoutυ
      exact ⟨by omega, Or.inr htimeoutυ'⟩

private lemma loop_good_true {B S : ℕ} {b : Cond} {c : Com}
    {σ μ σ' : Env} (hb : b.evalB B σ = some true)
    (hf : Fresh (.while b c))
    (hc : ClockedGood B S c σ μ)
    (hw : LoopGood B S b c μ σ') :
    LoopGood B S b c σ σ' := by
  intro tag τ hready hs hcontinue
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  have hguard := continue_test_true hB hcontinue
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some true := by rwa [← hbθ]
    obtain ⟨ρ, Kbody, hrunBody, houtBody⟩ :=
      hc (tag ++ "0") θ hreadyθ (sameSource_trans hs hsameTick)
    let δ := ρ.setVar continueName 1
    have hset : Run B (.assign continueName (.lit 1)) ρ δ 2 := by
      simpa [δ] using run_setContinue (B := B) (σ := ρ) 1 (by omega)
    have hinner : Run B
        (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
          (.assign continueName (.lit 0))) θ δ
        (1 + b.size + (Kbody + 2)) :=
      Run.ite_true hb' (hrunBody.seq hset)
    have ht := timedOut_test_true (B := B)
      (by omega) hreadyθ.active
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ δ
        (4 + (1 + b.size + (Kbody + 2))) := by
      convert Run.ite_true (d := .assign continueName (.lit 0)) ht hinner using 1
      simp [Cond.size, Expr.size]
    have hstep : Run B (loopStep tag b c) τ δ
        (44 + (4 + (1 + b.size + (Kbody + 2)))) := by
      simpa [loopStep] using htick.seq houter
    have hcapBody := houtBody.1
    rcases houtBody.2 with ⟨hreadyρ, hsameρ⟩ | ⟨hoffρ, hcapρ⟩
    · have hreadyδ := (ready_setContinue hreadyρ 1).1
      have hcapδ : capacity S δ = capacity S ρ := (ready_setContinue hreadyρ 1).2
      have hsameδ : SameSource μ δ :=
        sameSource_trans hsameρ
          (sameSource_setClock ρ ρ continueName
            (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
            (sameSource_refl ρ) 1)
      obtain ⟨υ, Kloop, hrunLoop, houtLoop⟩ :=
        hw tag δ hreadyδ hsameδ (by simp [δ, Env.setVar])
      have hrun := run_while_true hguard hstep hrunLoop
      refine ⟨υ,
        1 + (Cond.eq (.var continueName) (.lit 1)).size +
          (44 + (4 + (1 + b.size + (Kbody + 2)))) + Kloop,
        ?_, ?_⟩
      · simpa [loopCore] using hrun
      · have hcapLoop : capacity S υ ≤ capacity S δ := houtLoop.1
        have hcapBody : capacity S ρ ≤ capacity S θ := houtBody.1
        exact ⟨by omega, houtLoop.2⟩
    · have htimeoutδ : δ.vars timedOutName = 1 ∧ capacity S δ = 0 :=
        timeout_setContinue ⟨hoffρ, hcapρ⟩ 1
      have hrunLoop := loopCore_exit_timeout (tag := tag) (b := b) (c := c)
        hB htimeoutδ.1 (by simp [δ, Env.setVar])
      let υ := δ.setVar continueName 0
      have htimeoutυ : υ.vars timedOutName = 1 ∧ capacity S υ = 0 :=
        timeout_setContinue htimeoutδ 0
      have hrun := run_while_true hguard hstep hrunLoop
      refine ⟨υ,
        1 + (Cond.eq (.var continueName) (.lit 1)).size +
          (44 + (4 + (1 + b.size + (Kbody + 2)))) + 19,
        ?_, ?_⟩
      · simpa [loopCore, υ] using hrun
      · exact ⟨by omega, Or.inr htimeoutυ⟩
  · let υ := θ.setVar continueName 0
    have hset : Run B (.assign continueName (.lit 0)) θ υ 2 := by
      simpa [υ] using run_setContinue (B := B) (σ := θ) 0 (by omega)
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ υ 6 := by
      simpa using Run.ite_false ht hset
    have hstep : Run B (loopStep tag b c) τ υ 50 := by
      simpa [loopStep] using htick.seq houter
    have hstop : Run B (loopCore tag b c) υ υ 4 := by
      have ht0 := continue_test_false hB (σ := υ) (by simp [υ, Env.setVar])
      simpa [loopCore] using (Run.while_false (c := loopStep tag b c) ht0)
    have hrun := run_while_true hguard hstep hstop
    have htimeoutυ : υ.vars timedOutName = 1 ∧ capacity S υ = 0 :=
      timeout_setContinue ⟨hoff, hcapθ⟩ 0
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size + 50 + 4, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · exact ⟨by omega, Or.inr htimeoutυ⟩

private lemma while_good {B S : ℕ} {b : Cond} {c : Com}
    {σ σ' : Env} (hl : LoopGood B S b c σ σ') :
    ClockedGood B S (.while b c) σ σ' := by
  intro tag τ hready hs
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  let θ := τ.setVar continueName 1
  have hset : Run B (.assign continueName (.lit 1)) τ θ 2 := by
    simpa [θ] using run_setContinue (B := B) (σ := τ) 1 (by omega)
  have hreadyθ := (ready_setContinue hready 1).1
  have hcapθ : capacity S θ = capacity S τ := (ready_setContinue hready 1).2
  have hsameθ : SameSource σ θ :=
    sameSource_trans hs
      (sameSource_setClock τ τ continueName
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        (sameSource_refl τ) 1)
  obtain ⟨υ, K, hrun, hout⟩ :=
    hl tag θ hreadyθ hsameθ (by simp [θ, Env.setVar])
  have ht := timedOut_test_true (B := B)
    (by omega) hready.active
  have hbranch : Run B
      ((Com.assign continueName (.lit 1)).seq (loopCore tag b c))
      τ υ (2 + K) := hset.seq hrun
  have hfull : Run B
      (.ite (.eq (.var timedOutName) (.lit 0))
        ((Com.assign continueName (.lit 1)).seq (loopCore tag b c)) .skip)
      τ υ (4 + (2 + K)) := by
    convert Run.ite_true (d := .skip) ht hbranch using 1
    simp [Cond.size, Expr.size]
  refine ⟨υ, 4 + (2 + K), ?_, ?_⟩
  · simpa [clockedAt, loopCore, loopStep] using hfull
  · exact ⟨by have := hout.1; omega, hout.2⟩

/-- Every bounded source derivation has an actual clocked run at every
well-formed initial clock.  Even when the clock expires, the run terminates
with the flag set and zero remaining capacity. -/
theorem clocked_good_of_bigStepB {B S k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) :
    Fresh c → ClockedGood B S c σ σ' ∧ ExtraGood B S c σ σ' := by
  induction hr with
  | skip =>
      intro hf
      exact ⟨simple_good .skip hf (by intro tag; rfl), trivial⟩
  | assign he =>
      intro hf
      exact ⟨simple_good (.assign he) hf (by intro tag; rfl), trivial⟩
  | store hi he hk =>
      intro hf
      exact ⟨simple_good (.store hi he hk) hf (by intro tag; rfl), trivial⟩
  | read hin =>
      intro hf
      exact ⟨simple_good (.read hin) hf (by intro tag; rfl), trivial⟩
  | write he =>
      intro hf
      exact ⟨simple_good (.write he) hf (by intro tag; rfl), trivial⟩
  | seq hc hd ihc ihd =>
      rename_i c₀ d₀ σ₀ σ₁ σ₂ k₀ k₁
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      have hfd : Fresh d₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨seq_good (ihc hfc).1 (ihd hfd).1, trivial⟩
  | ite_true hb hc ihc =>
      rename_i b₀ c₀ d₀ σ₀ σ₁ k₀
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨ite_good_true hb hf (ihc hfc).1, trivial⟩
  | ite_false hb hd ihd =>
      rename_i b₀ c₀ d₀ σ₀ σ₁ k₀
      intro hf
      have hfd : Fresh d₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨ite_good_false hb hf (ihd hfd).1, trivial⟩
  | while_true hb hc hw ihc ihw =>
      rename_i b₀ c₀ σ₀ σ₁ σ₂ k₀ k₁
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      have hloop := loop_good_true hb hf (ihc hfc).1 (ihw hf).2
      exact ⟨while_good hloop, hloop⟩
  | while_false hb =>
      intro hf
      have hloop := loop_good_false (S := S) hb hf
      exact ⟨while_good hloop, hloop⟩

/-- Sufficient capacity preserves the source result.  The source charge
dominates the number of successful clock ticks; the concrete instrumented
run costs at most one hundred times the source charge. -/
def ClockedSuccess (B S : ℕ) (c : Com) (σ σ' : Env) (k : ℕ) : Prop :=
  ∀ tag τ, Ready B S τ → SameSource σ τ → k ≤ capacity S τ →
    ∃ υ K, Run B (clockedAt tag c) τ υ K ∧
      Ready B S υ ∧ SameSource σ' υ ∧
      capacity S τ ≤ capacity S υ + k ∧ K ≤ 100 * k

def LoopSuccess (B S : ℕ) (b : Cond) (c : Com)
    (σ σ' : Env) (k : ℕ) : Prop :=
  ∀ tag τ, Ready B S τ → SameSource σ τ →
    τ.vars continueName = 1 → k ≤ capacity S τ →
    ∃ υ K, Run B (loopCore tag b c) τ υ K ∧
      Ready B S υ ∧ SameSource σ' υ ∧
      capacity S τ ≤ capacity S υ + k ∧ K + 6 ≤ 100 * k

def ExtraSuccess (B S : ℕ) (c : Com) (σ σ' : Env) (k : ℕ) : Prop :=
  match c with
  | .while b body => LoopSuccess B S b body σ σ' k
  | _ => True

private lemma atom_success {B S k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) (hf : Fresh c) (hk : 0 < k)
    (hshape : ∀ tag, clockedAt tag c = clockedAtom c) :
    ClockedSuccess B S c σ σ' k := by
  intro tag τ hready hs hbudget
  have hcap : 0 < capacity S τ := by omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hzero, -, -⟩
  · obtain ⟨υ, hbody, hsameυ⟩ :=
      transport_run hr hf (sameSource_trans hs hsameTick)
    have hrunBody : Run B c θ υ k := Run.of_bigStepB hbody
    obtain ⟨hreadyυ, hcapEq⟩ := ready_of_fresh_run hreadyθ hf hrunBody
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hbranch : Run B
        (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
        θ υ (4 + k) := by
      simpa using Run.ite_true (d := .skip) ht hrunBody
    refine ⟨υ, 48 + k, ?_, hreadyυ, hsameυ, ?_, ?_⟩
    · simpa [hshape tag, clockedAtom, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htick.seq hbranch
    · omega
    · omega
  · omega

private lemma seq_success {B S k₀ k₁ : ℕ} {c d : Com}
    {σ μ σ' : Env}
    (hc : ClockedSuccess B S c σ μ k₀)
    (hd : ClockedSuccess B S d μ σ' k₁) :
    ClockedSuccess B S (.seq c d) σ σ' (k₀ + k₁) := by
  intro tag τ hready hs hbudget
  obtain ⟨θ, Kc, hrunC, hreadyθ, hsameθ, hcapC, hcostC⟩ :=
    hc (tag ++ "0") τ hready hs (by omega)
  obtain ⟨υ, Kd, hrunD, hreadyυ, hsameυ, hcapD, hcostD⟩ :=
    hd (tag ++ "1") θ hreadyθ hsameθ (by omega)
  refine ⟨υ, Kc + Kd, ?_, hreadyυ, hsameυ, ?_, ?_⟩
  · simpa [clockedAt] using hrunC.seq hrunD
  · omega
  · omega

private lemma ite_success_true {B S k : ℕ} {b : Cond} {c d : Com}
    {σ σ' : Env} (hb : b.evalB B σ = some true)
    (hf : Fresh (.ite b c d))
    (hc : ClockedSuccess B S c σ σ' k) :
    ClockedSuccess B S (.ite b c d) σ σ' (1 + b.size + k) := by
  intro tag τ hready hs hbudget
  have hcap : 0 < capacity S τ := by omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hzero, -, -⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some true := by rwa [← hbθ]
    obtain ⟨υ, K, hrunC, hreadyυ, hsameυ, hcapC, hcostC⟩ :=
      hc (tag ++ "0") θ hreadyθ (sameSource_trans hs hsameTick)
        (by omega)
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hinner : Run B
        (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        θ υ (1 + b.size + K) := Run.ite_true hb' hrunC
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ υ (4 + (1 + b.size + K)) := by
      convert Run.ite_true (d := .skip) ht hinner using 1
      simp [Cond.size, Expr.size]
    refine ⟨υ, 44 + (4 + (1 + b.size + K)), ?_,
      hreadyυ, hsameυ, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · omega
    · omega
  · omega

private lemma ite_success_false {B S k : ℕ} {b : Cond} {c d : Com}
    {σ σ' : Env} (hb : b.evalB B σ = some false)
    (hf : Fresh (.ite b c d))
    (hd : ClockedSuccess B S d σ σ' k) :
    ClockedSuccess B S (.ite b c d) σ σ' (1 + b.size + k) := by
  intro tag τ hready hs hbudget
  have hcap : 0 < capacity S τ := by omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hzero, -, -⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some false := by rwa [← hbθ]
    obtain ⟨υ, K, hrunD, hreadyυ, hsameυ, hcapD, hcostD⟩ :=
      hd (tag ++ "1") θ hreadyθ (sameSource_trans hs hsameTick)
        (by omega)
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hinner : Run B
        (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        θ υ (1 + b.size + K) := Run.ite_false hb' hrunD
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ υ (4 + (1 + b.size + K)) := by
      convert Run.ite_true (d := .skip) ht hinner using 1
      simp [Cond.size, Expr.size]
    refine ⟨υ, 44 + (4 + (1 + b.size + K)), ?_,
      hreadyυ, hsameυ, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · omega
    · omega
  · omega

private lemma loop_success_false {B S : ℕ} {b : Cond} {c : Com}
    {σ : Env} (hb : b.evalB B σ = some false)
    (hf : Fresh (.while b c)) :
    LoopSuccess B S b c σ σ (1 + b.size) := by
  intro tag τ hready hs hcontinue hbudget
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  have hcap : 0 < capacity S τ := by omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hzero, -, -⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some false := by rwa [← hbθ]
    let υ := θ.setVar continueName 0
    have hset : Run B (.assign continueName (.lit 0)) θ υ 2 := by
      simpa [υ] using run_setContinue (B := B) (σ := θ) 0 (by omega)
    have hinner : Run B
        (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
          (.assign continueName (.lit 0))) θ υ (1 + b.size + 2) :=
      Run.ite_false hb' hset
    have ht := timedOut_test_true (B := B)
      (by omega) hreadyθ.active
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ υ
        (4 + (1 + b.size + 2)) := by
      convert Run.ite_true (d := .assign continueName (.lit 0)) ht hinner using 1
      simp [Cond.size, Expr.size]
    have hstep : Run B (loopStep tag b c) τ υ
        (44 + (4 + (1 + b.size + 2))) := by
      simpa [loopStep] using htick.seq houter
    have hstop : Run B (loopCore tag b c) υ υ 4 := by
      have ht0 := continue_test_false hB (σ := υ) (by simp [υ, Env.setVar])
      simpa [loopCore] using (Run.while_false (c := loopStep tag b c) ht0)
    have hguard := continue_test_true hB hcontinue
    have hrun := run_while_true hguard hstep hstop
    have hreadyυ := (ready_setContinue hreadyθ 0).1
    have hcapυ : capacity S υ = capacity S θ := (ready_setContinue hreadyθ 0).2
    have hsameυ : SameSource σ υ :=
      sameSource_trans (sameSource_trans hs hsameTick)
        (sameSource_setClock θ θ continueName
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          (sameSource_refl θ) 0)
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size +
        (44 + (4 + (1 + b.size + 2))) + 4,
      ?_, hreadyυ, hsameυ, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · omega
    · simp [Cond.size, Expr.size]
      omega
  · omega

private lemma loop_success_true {B S kbody ktail : ℕ}
    {b : Cond} {c : Com} {σ μ σ' : Env}
    (hb : b.evalB B σ = some true)
    (hf : Fresh (.while b c))
    (hc : ClockedSuccess B S c σ μ kbody)
    (hw : LoopSuccess B S b c μ σ' ktail) :
    LoopSuccess B S b c σ σ' (1 + b.size + kbody + ktail) := by
  intro tag τ hready hs hcontinue hbudget
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  have hcap : 0 < capacity S τ := by omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hzero, -, -⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some true := by rwa [← hbθ]
    obtain ⟨ρ, Kbody, hrunBody, hreadyρ, hsameρ,
      hcapBody, hcostBody⟩ :=
      hc (tag ++ "0") θ hreadyθ (sameSource_trans hs hsameTick)
        (by omega)
    let δ := ρ.setVar continueName 1
    have hset : Run B (.assign continueName (.lit 1)) ρ δ 2 := by
      simpa [δ] using run_setContinue (B := B) (σ := ρ) 1 (by omega)
    have hreadyδ := (ready_setContinue hreadyρ 1).1
    have hcapδ : capacity S δ = capacity S ρ := (ready_setContinue hreadyρ 1).2
    have hsameδ : SameSource μ δ :=
      sameSource_trans hsameρ
        (sameSource_setClock ρ ρ continueName
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          (sameSource_refl ρ) 1)
    obtain ⟨υ, Kloop, hrunLoop, hreadyυ, hsameυ,
      hcapLoop, hcostLoop⟩ :=
      hw tag δ hreadyδ hsameδ
        (by simp [δ, Env.setVar]) (by omega)
    have hinner : Run B
        (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
          (.assign continueName (.lit 0))) θ δ
        (1 + b.size + (Kbody + 2)) :=
      Run.ite_true hb' (hrunBody.seq hset)
    have ht := timedOut_test_true (B := B)
      (by omega) hreadyθ.active
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ δ
        (4 + (1 + b.size + (Kbody + 2))) := by
      convert Run.ite_true (d := .assign continueName (.lit 0)) ht hinner using 1
      simp [Cond.size, Expr.size]
    have hstep : Run B (loopStep tag b c) τ δ
        (44 + (4 + (1 + b.size + (Kbody + 2)))) := by
      simpa [loopStep] using htick.seq houter
    have hguard := continue_test_true hB hcontinue
    have hrun := run_while_true hguard hstep hrunLoop
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size +
        (44 + (4 + (1 + b.size + (Kbody + 2)))) + Kloop,
      ?_, hreadyυ, hsameυ, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · omega
    · simp [Cond.size, Expr.size]
      omega
  · omega

private lemma while_success {B S k : ℕ} {b : Cond} {c : Com}
    {σ σ' : Env} (hl : LoopSuccess B S b c σ σ' k) :
    ClockedSuccess B S (.while b c) σ σ' k := by
  intro tag τ hready hs hbudget
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  let θ := τ.setVar continueName 1
  have hset : Run B (.assign continueName (.lit 1)) τ θ 2 := by
    simpa [θ] using run_setContinue (B := B) (σ := τ) 1 (by omega)
  have hreadyθ := (ready_setContinue hready 1).1
  have hcapθ : capacity S θ = capacity S τ := (ready_setContinue hready 1).2
  have hsameθ : SameSource σ θ :=
    sameSource_trans hs
      (sameSource_setClock τ τ continueName
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        (sameSource_refl τ) 1)
  obtain ⟨υ, K, hrun, hreadyυ, hsameυ, hcap, hcost⟩ :=
    hl tag θ hreadyθ hsameθ (by simp [θ, Env.setVar]) (by omega)
  have ht := timedOut_test_true (B := B)
    (by omega) hready.active
  have hbranch : Run B
      ((Com.assign continueName (.lit 1)).seq (loopCore tag b c))
      τ υ (2 + K) := hset.seq hrun
  have hfull : Run B
      (.ite (.eq (.var timedOutName) (.lit 0))
        ((Com.assign continueName (.lit 1)).seq (loopCore tag b c)) .skip)
      τ υ (4 + (2 + K)) := by
    convert Run.ite_true (d := .skip) ht hbranch using 1
    simp [Cond.size, Expr.size]
  refine ⟨υ, 4 + (2 + K), ?_, hreadyυ, hsameυ, ?_, ?_⟩
  · simpa [clockedAt, loopCore, loopStep] using hfull
  · omega
  · omega

/-- A clock with capacity at least the source charge finishes successfully.
The number of successful ticks is at most that charge, and the instrumented
source costs at most one hundred times the original run. -/
theorem clocked_success_of_bigStepB {B S k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) :
    Fresh c →
      ClockedSuccess B S c σ σ' k ∧ ExtraSuccess B S c σ σ' k := by
  induction hr with
  | skip =>
      intro hf
      exact ⟨atom_success .skip hf (by omega) (by intro tag; rfl), trivial⟩
  | assign he =>
      intro hf
      exact ⟨atom_success (.assign he) hf (by omega)
        (by intro tag; rfl), trivial⟩
  | store hi he hk =>
      intro hf
      exact ⟨atom_success (.store hi he hk) hf (by omega)
        (by intro tag; rfl), trivial⟩
  | read hin =>
      intro hf
      exact ⟨atom_success (.read hin) hf (by omega)
        (by intro tag; rfl), trivial⟩
  | write he =>
      intro hf
      exact ⟨atom_success (.write he) hf (by omega)
        (by intro tag; rfl), trivial⟩
  | seq hc hd ihc ihd =>
      rename_i c₀ d₀ σ₀ σ₁ σ₂ k₀ k₁
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      have hfd : Fresh d₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨seq_success (ihc hfc).1 (ihd hfd).1, trivial⟩
  | ite_true hb hc ihc =>
      rename_i b₀ c₀ d₀ σ₀ σ₁ k₀
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨ite_success_true hb hf (ihc hfc).1, trivial⟩
  | ite_false hb hd ihd =>
      rename_i b₀ c₀ d₀ σ₀ σ₁ k₀
      intro hf
      have hfd : Fresh d₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨ite_success_false hb hf (ihd hfd).1, trivial⟩
  | while_true hb hc hw ihc ihw =>
      rename_i b₀ c₀ σ₀ σ₁ σ₂ k₀ k₁
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      have hloop := loop_success_true hb hf (ihc hfc).1 (ihw hf).2
      exact ⟨while_success hloop, hloop⟩
  | while_false hb =>
      intro hf
      have hloop := loop_success_false (S := S) hb hf
      exact ⟨while_success hloop, hloop⟩

/-- A syntax-dependent multiplier for the worst case, including executions
that exhaust the clock in the middle of a nested loop. -/
def clockFactor : Com → ℕ
  | .skip => 100
  | .assign _ e => 100 + e.size
  | .store _ i e => 100 + i.size + e.size
  | .read _ => 100
  | .write e => 100 + e.size
  | .seq c d => clockFactor c + clockFactor d
  | .ite b c d => 100 + b.size + clockFactor c + clockFactor d
  | .while b c => 150 + b.size + clockFactor c

lemma clockFactor_at_least_100 (c : Com) : 100 ≤ clockFactor c := by
  induction c with
  | skip => simp [clockFactor]
  | assign x e => simp [clockFactor]
  | store a i e => simp [clockFactor]; omega
  | read x => simp [clockFactor]
  | write e => simp [clockFactor]
  | seq c d ihc ihd =>
      simp only [clockFactor]
      omega
  | ite b c d ihc ihd =>
      simp only [clockFactor]
      omega
  | «while» b c ih =>
      simp only [clockFactor]
      omega

private lemma offCost_le_factor (c : Com) : offCost c ≤ clockFactor c := by
  induction c with
  | skip => simp [offCost, clockFactor]
  | assign x e => simp [offCost, clockFactor]; omega
  | store a i e => simp [offCost, clockFactor]; omega
  | read x => simp [offCost, clockFactor]
  | write e => simp [offCost, clockFactor]; omega
  | seq c d ihc ihd =>
      simp only [offCost, clockFactor]
      omega
  | ite b c d ihc ihd =>
      simp [offCost, clockFactor]; omega
  | «while» b c ih =>
      simp [offCost, clockFactor]; omega

def ClockedTimed (B S : ℕ) (c : Com) (σ σ' : Env) : Prop :=
  ∀ tag τ, Ready B S τ → SameSource σ τ →
    ∃ υ K, Run B (clockedAt tag c) τ υ K ∧
      Outcome B S σ' τ υ ∧
      K + clockFactor c * capacity S υ ≤
        clockFactor c * (capacity S τ + 1)

def LoopTimed (B S : ℕ) (b : Cond) (c : Com)
    (σ σ' : Env) : Prop :=
  ∀ tag τ, Ready B S τ → SameSource σ τ →
    τ.vars continueName = 1 →
    ∃ υ K, Run B (loopCore tag b c) τ υ K ∧
      Outcome B S σ' τ υ ∧
      K + 6 + clockFactor (.while b c) * capacity S υ ≤
        clockFactor (.while b c) * (capacity S τ + 1)

def ExtraTimed (B S : ℕ) (c : Com) (σ σ' : Env) : Prop :=
  match c with
  | .while b body => LoopTimed B S b body σ σ'
  | _ => True

private lemma budget_seq (F G a b c K L : ℕ)
    (h₁ : K + F * b ≤ F * (a + 1))
    (h₂ : L + G * c ≤ G * (b + 1))
    (hba : b ≤ a) (hcb : c ≤ b) :
    K + L + (F + G) * c ≤ (F + G) * (a + 1) := by
  have hfc : F * c ≤ F * b := Nat.mul_le_mul_left F hcb
  have hga : G * (b + 1) ≤ G * (a + 1) :=
    Nat.mul_le_mul_left G (by omega)
  nlinarith

private lemma budget_step (O H D X Y K : ℕ)
    (hK : K + H * Y ≤ H * (X + 1))
    (hY : Y ≤ X) (hO : O ≤ H + D) :
    O + K + (H + D) * Y ≤ (H + D) * (X + 2) := by
  have hDY : D * Y ≤ D * (X + 1) :=
    Nat.mul_le_mul_left D (by omega)
  nlinarith

private lemma budget_loop_step (O H D X Y K : ℕ)
    (hK : K + H * Y ≤ H * (X + 1))
    (hY : Y ≤ X) (hO : O ≤ D) :
    O + K + (H + D) * (Y + 1) ≤ (H + D) * (X + 2) := by
  have hDY : D * (Y + 1) ≤ D * (X + 1) :=
    Nat.mul_le_mul_left D (by omega)
  nlinarith

private lemma atom_timed {B S k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) (hf : Fresh c)
    (hfactor : 49 + k ≤ clockFactor c)
    (hshape : ∀ tag, clockedAt tag c = clockedAtom c) :
    ClockedTimed B S c σ σ' := by
  intro tag τ hready hs
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨hpos, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · obtain ⟨υ, hbody, hsameυ⟩ :=
      transport_run hr hf (sameSource_trans hs hsameTick)
    have hrunBody : Run B c θ υ k := Run.of_bigStepB hbody
    obtain ⟨hreadyυ, hcapEq⟩ := ready_of_fresh_run hreadyθ hf hrunBody
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hbranch : Run B
        (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
        θ υ (4 + k) := by
      simpa using Run.ite_true (d := .skip) ht hrunBody
    refine ⟨υ, 48 + k, ?_, ?_, ?_⟩
    · simpa [hshape tag, clockedAtom, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htick.seq hbranch
    · exact ⟨by omega, Or.inl ⟨hreadyυ, hsameυ⟩⟩
    · rw [hcapEq]
      nlinarith
  · have hB : 1 < B := by
      have := hready.positive
      have := hready.sizeBound
      omega
    have ht := timedOut_test_false hB hoff
    have hbranch : Run B
        (.ite (.eq (.var timedOutName) (.lit 0)) c .skip)
        θ θ 5 := by
      simpa using Run.ite_false (c := c) ht Run.skip
    refine ⟨θ, 49, ?_, ?_, ?_⟩
    · simpa [hshape tag, clockedAtom] using htick.seq hbranch
    · exact ⟨by omega, Or.inr ⟨hoff, hcapθ⟩⟩
    · simp [hcap, hcapθ]
      omega

private lemma seq_timed {B S : ℕ} {c d : Com} {σ μ σ' : Env}
    (hc : ClockedTimed B S c σ μ)
    (hd : ClockedTimed B S d μ σ') :
    ClockedTimed B S (.seq c d) σ σ' := by
  intro tag τ hready hs
  obtain ⟨θ, Kc, hrunC, houtC, hboundC⟩ :=
    hc (tag ++ "0") τ hready hs
  rcases houtC.2 with ⟨hreadyθ, hsameθ⟩ | ⟨hoff, hcapθ⟩
  · obtain ⟨υ, Kd, hrunD, houtD, hboundD⟩ :=
      hd (tag ++ "1") θ hreadyθ hsameθ
    refine ⟨υ, Kc + Kd, ?_, ?_, ?_⟩
    · simpa [clockedAt] using hrunC.seq hrunD
    · exact ⟨le_trans houtD.1 houtC.1, houtD.2⟩
    · simp only [clockFactor]
      exact budget_seq (clockFactor c) (clockFactor d)
        (capacity S τ) (capacity S θ) (capacity S υ) Kc Kd
        hboundC hboundD houtC.1 houtD.1
  · have hB : 1 < B := by
      have := hready.positive
      have := hready.sizeBound
      omega
    have hrunD := clockedAt_off hB hoff (tag ++ "1") d
    refine ⟨θ, Kc + offCost d, ?_, ?_, ?_⟩
    · simpa [clockedAt] using hrunC.seq hrunD
    · exact ⟨houtC.1, Or.inr ⟨hoff, hcapθ⟩⟩
    · have hOff := offCost_le_factor d
      simp only [clockFactor]
      rw [hcapθ] at hboundC ⊢
      simp only [Nat.mul_zero, Nat.add_zero] at hboundC ⊢
      nlinarith

private lemma ite_timed_true {B S : ℕ} {b : Cond} {c d : Com}
    {σ σ' : Env} (hb : b.evalB B σ = some true)
    (hf : Fresh (.ite b c d))
    (hc : ClockedTimed B S c σ σ') :
    ClockedTimed B S (.ite b c d) σ σ' := by
  intro tag τ hready hs
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some true := by rwa [← hbθ]
    obtain ⟨υ, K, hrunC, hout, hbound⟩ :=
      hc (tag ++ "0") θ hreadyθ (sameSource_trans hs hsameTick)
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hinner : Run B
        (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        θ υ (1 + b.size + K) := Run.ite_true hb' hrunC
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ υ (4 + (1 + b.size + K)) := by
      convert Run.ite_true (d := .skip) ht hinner using 1
      simp [Cond.size, Expr.size]
    refine ⟨υ, 44 + (4 + (1 + b.size + K)), ?_, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by have := hout.1; omega, hout.2⟩
    · have hstep := budget_step (49 + b.size)
        (clockFactor c) (100 + b.size + clockFactor d)
        (capacity S θ) (capacity S υ) K
        hbound hout.1 (by omega)
      have hτ : capacity S τ + 1 = capacity S θ + 2 := by omega
      rw [hτ]
      convert hstep using 1 <;> simp only [clockFactor] <;> ring
  · have hB : 1 < B := by
      have := hready.positive
      have := hready.sizeBound
      omega
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ θ 5 := by
      simpa using Run.ite_false
        (c := .ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        ht Run.skip
    refine ⟨θ, 49, ?_, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by omega, Or.inr ⟨hoff, hcapθ⟩⟩
    · simp [clockFactor, hcap, hcapθ]
      omega

private lemma ite_timed_false {B S : ℕ} {b : Cond} {c d : Com}
    {σ σ' : Env} (hb : b.evalB B σ = some false)
    (hf : Fresh (.ite b c d))
    (hd : ClockedTimed B S d σ σ') :
    ClockedTimed B S (.ite b c d) σ σ' := by
  intro tag τ hready hs
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some false := by rwa [← hbθ]
    obtain ⟨υ, K, hrunD, hout, hbound⟩ :=
      hd (tag ++ "1") θ hreadyθ (sameSource_trans hs hsameTick)
    have ht := timedOut_test_true (B := B)
      (by have := hready.sizeBound; omega) hreadyθ.active
    have hinner : Run B
        (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        θ υ (1 + b.size + K) := Run.ite_false hb' hrunD
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ υ (4 + (1 + b.size + K)) := by
      convert Run.ite_true (d := .skip) ht hinner using 1
      simp [Cond.size, Expr.size]
    refine ⟨υ, 44 + (4 + (1 + b.size + K)), ?_, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by have := hout.1; omega, hout.2⟩
    · have hstep := budget_step (49 + b.size)
        (clockFactor d) (100 + b.size + clockFactor c)
        (capacity S θ) (capacity S υ) K
        hbound hout.1 (by omega)
      have hτ : capacity S τ + 1 = capacity S θ + 2 := by omega
      rw [hτ]
      convert hstep using 1 <;> simp only [clockFactor] <;> ring
  · have hB : 1 < B := by
      have := hready.positive
      have := hready.sizeBound
      omega
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
          .skip) θ θ 5 := by
      simpa using Run.ite_false
        (c := .ite b (clockedAt (tag ++ "0") c) (clockedAt (tag ++ "1") d))
        ht Run.skip
    refine ⟨θ, 49, ?_, ?_, ?_⟩
    · simpa [clockedAt] using htick.seq houter
    · exact ⟨by omega, Or.inr ⟨hoff, hcapθ⟩⟩
    · simp [clockFactor, hcap, hcapθ]
      omega

private lemma loop_timed_false {B S : ℕ} {b : Cond} {c : Com}
    {σ : Env} (hb : b.evalB B σ = some false)
    (hf : Fresh (.while b c)) :
    LoopTimed B S b c σ σ := by
  intro tag τ hready hs hcontinue
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  have hguard := continue_test_true hB hcontinue
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some false := by rwa [← hbθ]
    let υ := θ.setVar continueName 0
    have hset : Run B (.assign continueName (.lit 0)) θ υ 2 := by
      simpa [υ] using run_setContinue (B := B) (σ := θ) 0 (by omega)
    have hinner : Run B
        (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
          (.assign continueName (.lit 0))) θ υ (1 + b.size + 2) :=
      Run.ite_false hb' hset
    have ht := timedOut_test_true (B := B)
      (by omega) hreadyθ.active
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ υ
        (4 + (1 + b.size + 2)) := by
      convert Run.ite_true (d := .assign continueName (.lit 0)) ht hinner using 1
      simp [Cond.size, Expr.size]
    have hstep : Run B (loopStep tag b c) τ υ
        (44 + (4 + (1 + b.size + 2))) := by
      simpa [loopStep] using htick.seq houter
    have hstop : Run B (loopCore tag b c) υ υ 4 := by
      have ht0 := continue_test_false hB (σ := υ) (by simp [υ, Env.setVar])
      simpa [loopCore] using (Run.while_false (c := loopStep tag b c) ht0)
    have hrun := run_while_true hguard hstep hstop
    have hreadyυ := (ready_setContinue hreadyθ 0).1
    have hcapυ : capacity S υ = capacity S θ := (ready_setContinue hreadyθ 0).2
    have hsameυ : SameSource σ υ :=
      sameSource_trans (sameSource_trans hs hsameTick)
        (sameSource_setClock θ θ continueName
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          (sameSource_refl θ) 0)
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size +
        (44 + (4 + (1 + b.size + 2))) + 4,
      ?_, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · exact ⟨by omega, Or.inl ⟨hreadyυ, hsameυ⟩⟩
    · rw [hcapυ]
      have hτ : capacity S τ + 1 = capacity S θ + 2 := by omega
      rw [hτ]
      simp only [clockFactor, Cond.size, Expr.size]
      nlinarith
  · let υ := θ.setVar continueName 0
    have hset : Run B (.assign continueName (.lit 0)) θ υ 2 := by
      simpa [υ] using run_setContinue (B := B) (σ := θ) 0 (by omega)
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ υ 6 := by
      simpa using Run.ite_false ht hset
    have hstep : Run B (loopStep tag b c) τ υ 50 := by
      simpa [loopStep] using htick.seq houter
    have hstop : Run B (loopCore tag b c) υ υ 4 := by
      have ht0 := continue_test_false hB (σ := υ) (by simp [υ, Env.setVar])
      simpa [loopCore] using (Run.while_false (c := loopStep tag b c) ht0)
    have hrun := run_while_true hguard hstep hstop
    have htimeoutυ : υ.vars timedOutName = 1 ∧ capacity S υ = 0 :=
      timeout_setContinue ⟨hoff, hcapθ⟩ 0
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size + 50 + 4,
      ?_, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · exact ⟨by omega, Or.inr htimeoutυ⟩
    · simp [clockFactor, hcap, htimeoutυ.2, Cond.size, Expr.size]
      omega

private lemma loop_timed_true {B S : ℕ} {b : Cond} {c : Com}
    {σ μ σ' : Env} (hb : b.evalB B σ = some true)
    (hf : Fresh (.while b c))
    (hc : ClockedTimed B S c σ μ)
    (hw : LoopTimed B S b c μ σ') :
    LoopTimed B S b c σ σ' := by
  intro tag τ hready hs hcontinue
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  obtain ⟨θ, htick, hsameTick, hcase⟩ := guardedTick_run hready
  have hguard := continue_test_true hB hcontinue
  rcases hcase with ⟨-, hreadyθ, hdrop⟩ | ⟨hcap, hoff, hcapθ⟩
  · have hfb : ∀ x ∈ Cond.usedVars b, ¬ protectedName x := by
      intro x hx
      exact hf x (by simp [Com.usedVars, hx])
    have hbθ := condEvalB_sameSource (B := B)
      (sameSource_trans hs hsameTick) b hfb
    have hb' : b.evalB B θ = some true := by rwa [← hbθ]
    obtain ⟨ρ, Kbody, hrunBody, houtBody, hboundBody⟩ :=
      hc (tag ++ "0") θ hreadyθ (sameSource_trans hs hsameTick)
    let δ := ρ.setVar continueName 1
    have hset : Run B (.assign continueName (.lit 1)) ρ δ 2 := by
      simpa [δ] using run_setContinue (B := B) (σ := ρ) 1 (by omega)
    have hinner : Run B
        (.ite b ((clockedAt (tag ++ "0") c).seq
          (.assign continueName (.lit 1)))
          (.assign continueName (.lit 0))) θ δ
        (1 + b.size + (Kbody + 2)) :=
      Run.ite_true hb' (hrunBody.seq hset)
    have ht := timedOut_test_true (B := B)
      (by omega) hreadyθ.active
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ δ
        (4 + (1 + b.size + (Kbody + 2))) := by
      convert Run.ite_true (d := .assign continueName (.lit 0)) ht hinner using 1
      simp [Cond.size, Expr.size]
    have hstep : Run B (loopStep tag b c) τ δ
        (44 + (4 + (1 + b.size + (Kbody + 2)))) := by
      simpa [loopStep] using htick.seq houter
    rcases houtBody.2 with ⟨hreadyρ, hsameρ⟩ | ⟨hoffρ, hcapρ⟩
    · have hreadyδ := (ready_setContinue hreadyρ 1).1
      have hcapδ : capacity S δ = capacity S ρ := (ready_setContinue hreadyρ 1).2
      have hsameδ : SameSource μ δ :=
        sameSource_trans hsameρ
          (sameSource_setClock ρ ρ continueName
            (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
            (sameSource_refl ρ) 1)
      obtain ⟨υ, Kloop, hrunLoop, houtLoop, hboundLoop⟩ :=
        hw tag δ hreadyδ hsameδ (by simp [δ, Env.setVar])
      have hrun := run_while_true hguard hstep hrunLoop
      refine ⟨υ,
        1 + (Cond.eq (.var continueName) (.lit 1)).size +
          (44 + (4 + (1 + b.size + (Kbody + 2)))) + Kloop,
        ?_, ?_, ?_⟩
      · simpa [loopCore] using hrun
      · have hcapLoop : capacity S υ ≤ capacity S δ := houtLoop.1
        have hcapBody : capacity S ρ ≤ capacity S θ := houtBody.1
        exact ⟨by omega, houtLoop.2⟩
      · let F := clockFactor (.while b c)
        have hboundLoop' :
            Kloop + 6 + F * capacity S υ ≤ F * (capacity S ρ + 1) := by
          simpa [F, hcapδ] using hboundLoop
        have hmid :
            (55 + b.size) + Kbody + F * (capacity S ρ + 1) ≤
              F * (capacity S θ + 2) := by
          have hh := budget_loop_step (55 + b.size)
            (clockFactor c) (150 + b.size)
            (capacity S θ) (capacity S ρ) Kbody
            hboundBody houtBody.1 (by omega)
          convert hh using 1 <;> simp only [F, clockFactor] <;> ring
        have hτ : capacity S τ + 1 = capacity S θ + 2 := by omega
        rw [hτ]
        change (1 + (Cond.eq (.var continueName) (.lit 1)).size +
          (44 + (4 + (1 + b.size + (Kbody + 2)))) + Kloop) +
          6 + F * capacity S υ ≤ F * (capacity S θ + 2)
        have hcostshape :
            (1 + (Cond.eq (.var continueName) (.lit 1)).size +
              (44 + (4 + (1 + b.size + (Kbody + 2)))) + Kloop) + 6 =
              (55 + b.size) + Kbody + Kloop + 6 := by
          simp [Cond.size, Expr.size]
          omega
        rw [hcostshape]
        omega
    · have htimeoutδ : δ.vars timedOutName = 1 ∧ capacity S δ = 0 :=
        timeout_setContinue ⟨hoffρ, hcapρ⟩ 1
      have hrunLoop := loopCore_exit_timeout (tag := tag) (b := b) (c := c)
        hB htimeoutδ.1 (by simp [δ, Env.setVar])
      let υ := δ.setVar continueName 0
      have htimeoutυ : υ.vars timedOutName = 1 ∧ capacity S υ = 0 :=
        timeout_setContinue htimeoutδ 0
      have hrun := run_while_true hguard hstep hrunLoop
      refine ⟨υ,
        1 + (Cond.eq (.var continueName) (.lit 1)).size +
          (44 + (4 + (1 + b.size + (Kbody + 2)))) + 19,
        ?_, ?_, ?_⟩
      · simpa [loopCore, υ] using hrun
      · exact ⟨by omega, Or.inr htimeoutυ⟩
      · have hτ : capacity S τ + 1 = capacity S θ + 2 := by omega
        rw [hτ, htimeoutυ.2]
        rw [hcapρ] at hboundBody
        simp only [Nat.mul_zero, Nat.add_zero] at hboundBody ⊢
        simp only [clockFactor, Cond.size, Expr.size]
        nlinarith
  · let υ := θ.setVar continueName 0
    have hset : Run B (.assign continueName (.lit 0)) θ υ 2 := by
      simpa [υ] using run_setContinue (B := B) (σ := θ) 0 (by omega)
    have ht := timedOut_test_false hB hoff
    have houter : Run B
        (.ite (.eq (.var timedOutName) (.lit 0))
          (.ite b ((clockedAt (tag ++ "0") c).seq
            (.assign continueName (.lit 1)))
            (.assign continueName (.lit 0)))
          (.assign continueName (.lit 0))) θ υ 6 := by
      simpa using Run.ite_false ht hset
    have hstep : Run B (loopStep tag b c) τ υ 50 := by
      simpa [loopStep] using htick.seq houter
    have hstop : Run B (loopCore tag b c) υ υ 4 := by
      have ht0 := continue_test_false hB (σ := υ) (by simp [υ, Env.setVar])
      simpa [loopCore] using (Run.while_false (c := loopStep tag b c) ht0)
    have hrun := run_while_true hguard hstep hstop
    have htimeoutυ : υ.vars timedOutName = 1 ∧ capacity S υ = 0 :=
      timeout_setContinue ⟨hoff, hcapθ⟩ 0
    refine ⟨υ,
      1 + (Cond.eq (.var continueName) (.lit 1)).size + 50 + 4,
      ?_, ?_, ?_⟩
    · simpa [loopCore] using hrun
    · exact ⟨by omega, Or.inr htimeoutυ⟩
    · simp [clockFactor, hcap, htimeoutυ.2, Cond.size, Expr.size]
      omega

private lemma while_timed {B S : ℕ} {b : Cond} {c : Com}
    {σ σ' : Env} (hl : LoopTimed B S b c σ σ') :
    ClockedTimed B S (.while b c) σ σ' := by
  intro tag τ hready hs
  have hB : 1 < B := by
    have := hready.positive
    have := hready.sizeBound
    omega
  let θ := τ.setVar continueName 1
  have hset : Run B (.assign continueName (.lit 1)) τ θ 2 := by
    simpa [θ] using run_setContinue (B := B) (σ := τ) 1 (by omega)
  have hreadyθ := (ready_setContinue hready 1).1
  have hcapθ : capacity S θ = capacity S τ := (ready_setContinue hready 1).2
  have hsameθ : SameSource σ θ :=
    sameSource_trans hs
      (sameSource_setClock τ τ continueName
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        (sameSource_refl τ) 1)
  obtain ⟨υ, K, hrun, hout, hbound⟩ :=
    hl tag θ hreadyθ hsameθ (by simp [θ, Env.setVar])
  have ht := timedOut_test_true (B := B)
    (by omega) hready.active
  have hbranch : Run B
      ((Com.assign continueName (.lit 1)).seq (loopCore tag b c))
      τ υ (2 + K) := hset.seq hrun
  have hfull : Run B
      (.ite (.eq (.var timedOutName) (.lit 0))
        ((Com.assign continueName (.lit 1)).seq (loopCore tag b c)) .skip)
      τ υ (4 + (2 + K)) := by
    convert Run.ite_true (d := .skip) ht hbranch using 1
    simp [Cond.size, Expr.size]
  refine ⟨υ, 4 + (2 + K), ?_, ?_, ?_⟩
  · simpa [clockedAt, loopCore, loopStep] using hfull
  · exact ⟨by have := hout.1; omega, hout.2⟩
  · rw [hcapθ] at hbound
    omega

/-- A source derivation supplies an actual clocked run with a cost bound
proportional to the mathematical clock capacity, even if that capacity is
far below the source's own running time. -/
theorem clocked_timed_of_bigStepB {B S k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) :
    Fresh c → ClockedTimed B S c σ σ' ∧ ExtraTimed B S c σ σ' := by
  induction hr with
  | skip =>
      intro hf
      exact ⟨atom_timed .skip hf (by simp [clockFactor])
        (by intro tag; rfl), trivial⟩
  | assign he =>
      intro hf
      exact ⟨atom_timed (.assign he) hf (by simp [clockFactor]; omega)
        (by intro tag; rfl), trivial⟩
  | store hi he hk =>
      intro hf
      exact ⟨atom_timed (.store hi he hk) hf (by simp [clockFactor]; omega)
        (by intro tag; rfl), trivial⟩
  | read hin =>
      intro hf
      exact ⟨atom_timed (.read hin) hf (by simp [clockFactor])
        (by intro tag; rfl), trivial⟩
  | write he =>
      intro hf
      exact ⟨atom_timed (.write he) hf (by simp [clockFactor]; omega)
        (by intro tag; rfl), trivial⟩
  | seq hc hd ihc ihd =>
      rename_i c₀ d₀ σ₀ σ₁ σ₂ k₀ k₁
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      have hfd : Fresh d₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨seq_timed (ihc hfc).1 (ihd hfd).1, trivial⟩
  | ite_true hb hc ihc =>
      rename_i b₀ c₀ d₀ σ₀ σ₁ k₀
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨ite_timed_true hb hf (ihc hfc).1, trivial⟩
  | ite_false hb hd ihd =>
      rename_i b₀ c₀ d₀ σ₀ σ₁ k₀
      intro hf
      have hfd : Fresh d₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      exact ⟨ite_timed_false hb hf (ihd hfd).1, trivial⟩
  | while_true hb hc hw ihc ihw =>
      rename_i b₀ c₀ σ₀ σ₁ σ₂ k₀ k₁
      intro hf
      have hfc : Fresh c₀ := by
        intro x hx
        exact hf x (by simp [Com.usedVars, hx])
      have hloop := loop_timed_true hb hf (ihc hfc).1 (ihw hf).2
      exact ⟨while_timed hloop, hloop⟩
  | while_false hb =>
      intro hf
      have hloop := loop_timed_false (S := S) hb hf
      exact ⟨while_timed hloop, hloop⟩

/-- A clocked source program always has an actual bounded run when the
original program does.  Its cost depends on the syntax and mathematical
capacity, not on the potentially much larger original running time.  When
capacity covers that running time, the original final state and tape are
recovered and the cost is also bounded by the source charge. -/
theorem clocked_run {B S k : ℕ} {c : Com} {σ σ' τ : Env}
    (hr : BigStepB B c σ σ' k) (hf : Fresh c)
    (hready : Ready B S τ) (hs : SameSource σ τ) :
    ∃ υ K, Run B (clocked c) τ υ K ∧
      K ≤ clockFactor c * (capacity S τ + 1) ∧
      capacity S υ ≤ capacity S τ ∧
      ((Ready B S υ ∧ SameSource σ' υ) ∨
       (υ.vars timedOutName = 1 ∧ capacity S υ = 0)) ∧
      (k ≤ capacity S τ →
        Ready B S υ ∧ SameSource σ' υ ∧ K ≤ 100 * k) := by
  obtain ⟨υ, K, hrun, hout, hbound⟩ :=
    (clocked_timed_of_bigStepB (S := S) hr hf).1 "" τ hready hs
  obtain ⟨κ, hκ, hactual⟩ := hrun
  refine ⟨υ, κ, ?_, ?_, hout.1, hout.2, ?_⟩
  · simpa [clocked] using (Run.of_bigStepB hactual)
  · omega
  · intro hbudget
    obtain ⟨υs, Ks, hrunS, hreadyS, hsameS, -, hcostS⟩ :=
      (clocked_success_of_bigStepB (S := S) hr hf).1 "" τ hready hs hbudget
    obtain ⟨κs, hκs, hactualS⟩ := hrunS
    obtain ⟨hfinal, hcost⟩ :=
      BigStep.unique hactual.bigStep hactualS.bigStep
    subst υs
    exact ⟨hreadyS, hsameS, by omega⟩

end Lax457868Proofs.ClockedSource
