import Mathlib.Tactic
import Lax457868Proofs.DrawBuffer
import Lax457868Proofs.StoppingPrefix

/-!
Sequential indexed draws from one residual bit tape. Every call uses the same
domain, and a successful call leaves the unread part of its cap available to
the following call. This is sampling with replacement: equal selected values
occupy separate buffer cells.
-/

namespace Lax457868Proofs.SequentialDraws

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.DrawBuffer
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FairBitRam
open Lax457868Proofs.StoppingPrefix
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

private abbrev Block (m : ℕ) := Fin (Nat.clog 2 m) → Bool

/-- The source has one stopping counter for the requested number of draws.
Its per-draw rejection cap remains the independent `drawCap` variable. -/
def sequentialDrawBody : Com :=
  seqs [countedIndexedDrawAppend,
    .ite (.eq (.var "drawFound") (.lit 0))
      (seqs [.assign "batchFailed" (.lit 1),
        .assign "batchStop" (.var "drawCount")]) .skip]

/-- Initialize the occupied buffer length and execute the fixed draw loop. -/
def sequentialDraws : Com :=
  seqs [.assign "drawCount" (.lit 0),
    .assign "batchStop" (.var "batchTarget"),
    .assign "batchFailed" (.lit 0),
    .while (.lt (.var "drawCount") (.var "batchStop")) sequentialDrawBody]

/-- A finite semantic trace of the existing capped selector. `used` counts
only blocks actually read, including the exhausted final call. -/
inductive DrawTrace (m : ℕ) (hm : 0 < m) (t : ℕ) :
    ℕ → List (Block m) → List (Fin m) → ℕ → Bool → Prop
  | done (blocks : List (Block m)) : DrawTrace m hm t 0 blocks [] 0 false
  | failed {r : ℕ} (tape : BitTape m t) (tail : List (Block m)) (u : ℕ)
      (hsel : selectBitIndexWithCount m hm t tape = (none, u)) :
      DrawTrace m hm t (r + 1) (List.ofFn tape ++ tail) [] u true
  | accepted {r : ℕ} (tape : BitTape m t) (tail : List (Block m))
      (i : Fin m) (u : ℕ) {values : List (Fin m)} {used : ℕ} {failed : Bool}
      (hsel : selectBitIndexWithCount m hm t tape = (some i, u))
      (hnext : DrawTrace m hm t r ((List.ofFn tape).drop u ++ tail)
        values used failed) :
      DrawTrace m hm t (r + 1) (List.ofFn tape ++ tail)
        (i :: values) (u + used) failed

/-- A sufficiently long list supplies the next capped call, without
reserving its unread suffix for that call. The product is only a proof-side
length bound; the program never stores it in a RAM word. -/
lemma drawTrace_exists (m : ℕ) (hm : 0 < m) (t r : ℕ)
    (blocks : List (Block m)) (hlen : r * t ≤ blocks.length) :
    ∃ values used failed, DrawTrace m hm t r blocks values used failed := by
  induction r generalizing blocks with
  | zero => exact ⟨[], 0, false, DrawTrace.done blocks⟩
  | succ r ih =>
      have ht : t ≤ blocks.length := by
        have hmul : (r + 1) * t = r * t + t := by ring
        omega
      let pre := blocks.take t
      have hp : pre.length = t := by simp [pre, List.length_take, Nat.min_eq_left ht]
      let tape : BitTape m t := fun i => pre[i.val]'(by simpa [hp] using i.isLt)
      have htape : List.ofFn tape = pre := by
        have h := List.ofFn_getElem (xs := pre)
        simpa [tape, hp] using h
      let tail := blocks.drop t
      have hsplit : blocks = List.ofFn tape ++ tail := by
        rw [htape]
        exact (List.take_append_drop t blocks).symm
      let choice := selectBitIndexWithCount m hm t tape
      cases hc : choice.1 with
      | none =>
          have hsel : selectBitIndexWithCount m hm t tape = (none, choice.2) := by
            cases h : selectBitIndexWithCount m hm t tape with
            | mk a b => simpa [choice, h] using hc
          refine ⟨[], choice.2, true, ?_⟩
          rw [hsplit]
          exact DrawTrace.failed tape tail choice.2 hsel
      | some i =>
          have hsel : selectBitIndexWithCount m hm t tape = (some i, choice.2) := by
            cases h : selectBitIndexWithCount m hm t tape with
            | mk a b => simpa [choice, h] using hc
          have hu : choice.2 ≤ t := (stoppedEvent_bounds m hm t choice.2 i tape hsel).2
          have htail : r * t ≤ ((List.ofFn tape).drop choice.2 ++ tail).length := by
            have hblocks : blocks.length = t + tail.length := by
              rw [hsplit]
              simp
            have hmul : (r + 1) * t = r * t + t := by ring
            simp only [List.length_append, List.length_drop, List.length_ofFn]
            omega
          obtain ⟨values, used, failed, hnext⟩ :=
            ih ((List.ofFn tape).drop choice.2 ++ tail) htail
          refine ⟨i :: values, choice.2 + used, failed, ?_⟩
          rw [hsplit]
          exact DrawTrace.accepted tape tail i choice.2 hsel hnext

/-- The trace reports exactly the number of completed draws; failure means
the requested count was not reached. -/
lemma DrawTrace.length_and_status (m : ℕ) (hm : 0 < m) (t : ℕ) :
    ∀ {r : ℕ} {blocks : List (Block m)} {values : List (Fin m)}
      {used : ℕ} {failed : Bool},
      DrawTrace m hm t r blocks values used failed →
        values.length ≤ r ∧ (failed = false ↔ values.length = r)
  | _, _, _, _, _, .done _ => by simp
  | _, _, _, _, _, .failed _ _ _ _ => by simp
  | _, _, _, _, _, .accepted _ _ _ _ _ hnext => by
      obtain ⟨hle, hiff⟩ := DrawTrace.length_and_status m hm t hnext
      simp only [List.length_cons, Nat.succ_eq_add_one]
      constructor
      · omega
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hiff

/-- Write each accepted value at the next occupied cell. -/
def writeDraws {m : ℕ} (domain draws : ℕ → ℕ) (start : ℕ) : List (Fin m) → ℕ → ℕ
  | [] => draws
  | i :: more => writeDraws domain (upd draws start (domain i.val)) (start + 1) more

/-- A batch leaves every cell outside its occupied segment unchanged. -/
lemma writeDraws_outside {m : ℕ} (domain draws : ℕ → ℕ)
    (start j : ℕ) (values : List (Fin m))
    (hj : j < start ∨ start + values.length ≤ j) :
    writeDraws domain draws start values j = draws j := by
  induction values generalizing draws start with
  | nil => rfl
  | cons i more ih =>
      have hj' : j < start + 1 ∨ start + 1 + more.length ≤ j := by
        simp only [List.length_cons] at hj
        omega
      rw [writeDraws, ih (upd draws start (domain i.val)) (start + 1) hj']
      have hne : j ≠ start := by
        simp only [List.length_cons] at hj
        rcases hj with h | h <;> omega
      simp [upd, hne]

/-- The occupied segment contains the selected domain values in call order,
including repetitions. -/
lemma writeDraws_at {m : ℕ} (domain draws : ℕ → ℕ)
    (start : ℕ) (values : List (Fin m)) (j : ℕ)
    (hj : j < values.length) :
    writeDraws domain draws start values (start + j) = domain values[j].val := by
  induction values generalizing draws start j with
  | nil => simp at hj
  | cons i more ih =>
      cases j with
      | zero =>
          have hout := writeDraws_outside domain
            (upd draws start (domain i.val)) (start + 1) start more
            (Or.inl (by omega))
          simpa [writeDraws, upd] using hout
      | succ k =>
          have hk : k < more.length := by simpa using hj
          have h := ih (upd draws start (domain i.val)) (start + 1) k hk
          have heq : start + 1 + k = start + (k + 1) := by omega
          rw [heq] at h
          simpa [writeDraws] using h

/-- Concrete buffer reads show both the occupied prefix and the untouched
cells, subject only to the buffer's ordinary capacity bound. -/
lemma writeDraws_buffer_cells {m cap : ℕ} (domain draws : ℕ → ℕ)
    (start : ℕ) (values : List (Fin m))
    (hcapacity : start + values.length ≤ cap) :
    (∀ j (hj : j < values.length),
      (arrOf cap (writeDraws domain draws start values))[start + j]? =
        some (domain values[j].val)) ∧
    (∀ j (hj : j < cap),
      (j < start ∨ start + values.length ≤ j) →
        (arrOf cap (writeDraws domain draws start values))[j]? =
          some (draws j)) := by
  constructor
  · intro j hj
    rw [getElem?_arrOf _ (by omega : start + j < cap)]
    exact congrArg some (writeDraws_at domain draws start values j hj)
  · intro j hj hout
    rw [getElem?_arrOf _ hj]
    exact congrArg some (writeDraws_outside domain draws start j values hout)

private lemma drop_ofFn_append {m t u : ℕ} (tape : BitTape m t)
    (tail : List (Block m)) (hu : u ≤ t) :
    (List.ofFn tape ++ tail).drop u = (List.ofFn tape).drop u ++ tail := by
  rw [List.drop_append]
  simp [hu]

private lemma flatten_append {m : ℕ} (xs ys : List (Block m)) :
    flattenBitBlockList (xs ++ ys) =
      flattenBitBlockList xs ++ flattenBitBlockList ys := by
  simp [flattenBitBlockList_eq_flatMap, List.flatMap_append]

private lemma batchGuard_true {B d stop : ℕ} {σ : Env}
    (hc : σ.vars "drawCount" = d) (hs : σ.vars "batchStop" = stop)
    (hd : d < stop) (hB : stop < B) :
    (Cond.lt (.var "drawCount") (.var "batchStop")).evalB B σ = some true := by
  have hcb : σ.vars "drawCount" < B := by rw [hc]; omega
  have hsb : σ.vars "batchStop" < B := by rw [hs]; exact hB
  simpa [hc, hs, hd] using evalB_condLt (evalB_var hcb) (evalB_var hsb)

private lemma batchGuard_false {B d stop : ℕ} {σ : Env}
    (hc : σ.vars "drawCount" = d) (hs : σ.vars "batchStop" = stop)
    (hd : stop ≤ d) (hcB : d < B) (hsB : stop < B) :
    (Cond.lt (.var "drawCount") (.var "batchStop")).evalB B σ = some false := by
  have hcb : σ.vars "drawCount" < B := by rw [hc]; exact hcB
  have hsb : σ.vars "batchStop" < B := by rw [hs]; exact hsB
  simpa [hc, hs, Nat.not_lt.mpr hd] using
    evalB_condLt (evalB_var hcb) (evalB_var hsb)

private lemma batchBranch_success {B : ℕ} {σ : Env}
    (hfound : σ.vars "drawFound" = 1) (hone : 1 < B) :
    Run B (.ite (.eq (.var "drawFound") (.lit 0))
      (seqs [.assign "batchFailed" (.lit 1),
        .assign "batchStop" (.var "drawCount")]) .skip) σ σ 8 := by
  have hcond : (Cond.eq (.var "drawFound") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var (by simpa [hfound] using hone))
      (evalB_lit (by omega : 0 < B))]
    simp [hfound]
  exact (Run.ite_false hcond Run.skip).mono (by decide)

private lemma batchBranch_failure {B d : ℕ} {σ : Env}
    (hfound : σ.vars "drawFound" = 0)
    (hcount : σ.vars "drawCount" = d) (hdB : d < B) (hone : 1 < B) :
    ∃ σ', Run B (.ite (.eq (.var "drawFound") (.lit 0))
        (seqs [.assign "batchFailed" (.lit 1),
          .assign "batchStop" (.var "drawCount")]) .skip) σ σ' 8 ∧
      σ'.vars "batchFailed" = 1 ∧ σ'.vars "batchStop" = d := by
  let σ₁ := σ.setVar "batchFailed" 1
  let σ₂ := σ₁.setVar "batchStop" d
  have hfirst : Run B (.assign "batchFailed" (.lit 1)) σ σ₁ 2 := by
    simpa [σ₁] using (Run.assign (evalB_lit hone))
  have hcount₁ : σ₁.vars "drawCount" = d := by simp [σ₁, hcount]
  have hsecond : Run B (.assign "batchStop" (.var "drawCount")) σ₁ σ₂ 2 := by
    apply Run.assign
    simpa [σ₂, hcount₁] using (evalB_var (by rw [hcount₁]; exact hdB :
      σ₁.vars "drawCount" < B))
  have hseq : Run B (seqs [.assign "batchFailed" (.lit 1),
      .assign "batchStop" (.var "drawCount")]) σ σ₂ 4 := by
    simpa [seqs] using Run.seq hfirst hsecond
  have hcond : (Cond.eq (.var "drawFound") (.lit 0)).evalB B σ = some true := by
    rw [evalB_condEq (evalB_var (by rw [hfound]; omega :
      σ.vars "drawFound" < B)) (evalB_lit (by omega : 0 < B))]
    simp [hfound]
  refine ⟨σ₂, ?_, by simp [σ₂, σ₁], by simp [σ₂]⟩
  simpa using Run.ite_true hcond hseq

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

private lemma selector_used_eq {m t u : ℕ} (hm : 0 < m)
    (tape : BitTape m t) (result : Option (Fin m))
    (hsel : selectBitIndexWithCount m hm t tape = (result, u)) :
    bitTapeAttemptsUsed m t tape = u := by
  have h := selectBitIndexWithCount_eq m hm t tape
  rw [hsel] at h
  exact (congrArg Prod.snd h).symm

private lemma selector_failed_uses_cap {m t u : ℕ} (hm : 0 < m)
    (tape : BitTape m t)
    (hsel : selectBitIndexWithCount m hm t tape = (none, u)) : u = t := by
  have hnone : selectBitIndex m hm t tape = none := by
    have h := congrArg Prod.fst hsel
    simpa [selectBitIndexWithCount_eq m hm t tape] using h
  have hreject := (selectBitIndex_eq_none_iff m hm t tape).mp hnone
  have hcomplete := (selector_complete_rejection_iff m hm t tape).mpr hreject
  have h₁ := selector_used_eq hm tape none hsel
  have h₂ := selector_used_eq hm tape none hcomplete
  omega

/-- The total consumed prefix is inside the supplied tape, and each call
accounts for at most one requested draw. -/
lemma DrawTrace.used_and_calls (m : ℕ) (hm : 0 < m) (t : ℕ) :
    ∀ {r : ℕ} {blocks : List (Block m)} {values : List (Fin m)}
      {used : ℕ} {failed : Bool},
      DrawTrace m hm t r blocks values used failed →
        used ≤ blocks.length ∧
          values.length + (if failed then 1 else 0) ≤ r
  | _, _, _, _, _, .done _ => by simp
  | _, _, _, _, _, .failed tape tail u hsel => by
      have hu : u = t := selector_failed_uses_cap hm tape hsel
      simp [hu]
  | _, _, _, _, _, .accepted tape tail i u hsel hnext => by
      obtain ⟨hused, hcalls⟩ := DrawTrace.used_and_calls m hm t hnext
      have hu : u ≤ t := (stoppedEvent_bounds m hm t u i tape hsel).2
      constructor
      · simp only [List.length_append, List.length_ofFn] at hused ⊢
        simp only [List.length_drop, List.length_append, List.length_ofFn] at hused
        omega
      · simp only [List.length_cons]
        omega

/-- Execute a trace using the actual counted draw-and-append source at each
step. The initial buffer may contain arbitrary cells; exactly the occupied
prefix is overwritten. -/
lemma sequentialLoop_run_trace
    {B n v m domainCap t bufferCap target : ℕ}
    (hm : 0 < m) (domain : ℕ → ℕ)
    (hmCap : m ≤ domainCap) (hvalueB : ∀ i < m, domain i < B)
    (hvn : v < n) (hpowB : 2 ^ Nat.clog 2 m < B)
    (hnB : n < B) (htwoB : 2 < B) (htB : t < B)
    (hmB : m < B) (honeB : 1 < B)
    (hcapacity : target ≤ bufferCap) (htargetB : target < B) :
    ∀ (r d : ℕ) (blocks : List (Block m))
      (values : List (Fin m)) (used : ℕ) (failed : Bool)
      (σ : Env) (g draws : ℕ → ℕ) (rest : List ℕ),
      DrawTrace m hm t r blocks values used failed →
      d + r = target →
      σ.arrs "key0" = arrOf n g →
      σ.arrs "drawDomain" = arrOf domainCap domain →
      σ.arrs "sampleDraws" = arrOf bufferCap draws →
      σ.vars "drawCount" = d →
      σ.vars "batchStop" = target →
      σ.vars "batchFailed" = 0 →
      σ.vars "batchTarget" = target →
      σ.vars "v" = v →
      σ.vars "L" = Nat.clog 2 m →
      σ.vars "drawModulus" = m →
      σ.vars "drawCap" = t →
      σ.inp = flattenBitBlockList blocks ++ rest →
      ∃ σ' g',
        Run B (.while (.lt (.var "drawCount") (.var "batchStop"))
          sequentialDrawBody) σ σ'
          ((15 * Nat.clog 2 m + 30) * used +
            43 * (values.length + if failed then 1 else 0) + 4) ∧
        σ'.arrs "key0" = arrOf n g' ∧
        (∀ j < n, j ≠ v → g' j = g j) ∧
        σ'.arrs "drawDomain" = arrOf domainCap domain ∧
        σ'.arrs "sampleDraws" =
          arrOf bufferCap (writeDraws domain draws d values) ∧
        σ'.vars "drawCount" = d + values.length ∧
        σ'.vars "batchStop" =
          (if failed then d + values.length else target) ∧
        σ'.vars "batchFailed" = (if failed then 1 else 0) ∧
        σ'.vars "batchTarget" = target ∧
        σ'.inp = flattenBitBlockList (blocks.drop used) ++ rest ∧
        σ'.vars "v" = v ∧ σ'.vars "L" = Nat.clog 2 m ∧
        σ'.vars "drawModulus" = m ∧ σ'.vars "drawCap" = t := by
  intro r
  induction r with
  | zero =>
      intro d blocks values used failed σ g draws rest htrace hr hkey hdomain
        hdraws hcount hstop hbad htarget hv hL hmod hcap hinp
      cases htrace with
      | done =>
          have hd : d = target := by omega
          have hguard := batchGuard_false hcount hstop (by omega : target ≤ d)
            (by omega : d < B) htargetB
          refine ⟨σ, g, ?_, hkey, ?_, hdomain, ?_, ?_, ?_, hbad,
            htarget, ?_, hv, hL, hmod, hcap⟩
          · simpa [sequentialDrawBody] using Run.while_false hguard
          · intro j hj hneq; rfl
          · simpa [writeDraws] using hdraws
          · simpa using hcount
          · simpa using hstop
          · simpa using hinp
  | succ r ih =>
      intro d blocks values used failed σ g draws rest htrace hr hkey hdomain
        hdraws hcount hstop hbad htarget hv hL hmod hcap hinp
      cases htrace with
      | failed tape tail u hsel =>
          have hd : d < target := by omega
          have hcapBuf : d < bufferCap := by omega
          have hdB : d + 1 < B := by omega
          have hinput : σ.inp = flattenBitBlocks tape ++
              (flattenBitBlockList tail ++ rest) := by
            simpa [flattenBitBlocks, flattenBitBlockList_eq_flatMap,
              List.flatMap_append, List.append_assoc] using hinp
          obtain ⟨σ₁, g₁, hdraw, hkey₁, hframe₁, _, hfail₁,
            hused₁, hfound₁, hinp₁, hdomain₁, _, hv₁, hL₁, hmod₁, hcap₁⟩ :=
            countedIndexedDrawAppend_run_tape tape hm hkey hdomain hmCap hvalueB
              hdraws hcount hcapBuf hdB hv hvn hL hmod hcap hinput
              hpowB hnB htwoB htB hmB honeB
          obtain ⟨hdraws₁, hcount₁, _⟩ := hfail₁ (by simpa [hsel])
          have hu : bitTapeAttemptsUsed m t tape = used :=
            selector_used_eq hm tape none hsel
          have huCap : used = t := selector_failed_uses_cap hm tape hsel
          have hfoundZero : σ₁.vars "drawFound" = 0 := by
            simpa [hsel] using hfound₁
          obtain ⟨σ₂, hbranch, hbad₂, hstop₂⟩ :=
            batchBranch_failure hfoundZero hcount₁ (by omega : d < B) honeB
          have hbody : Run B sequentialDrawBody σ σ₂
              ((15 * Nat.clog 2 m + 30) * used + 39) := by
            have hseq := Run.seq hdraw hbranch
            simpa [sequentialDrawBody, seqs, hu, Nat.add_assoc] using hseq
          have hcount₂ : σ₂.vars "drawCount" = d :=
            (hbranch.frame_var "drawCount" (by decide)).trans hcount₁
          have hguard₂ := batchGuard_false hcount₂ hstop₂ (by omega : d ≤ d)
            (by omega : d < B) (by omega : d < B)
          have htailRun : Run B
              (.while (.lt (.var "drawCount") (.var "batchStop"))
                sequentialDrawBody) σ₂ σ₂ 4 := by
            simpa using Run.while_false hguard₂
          have hguard := batchGuard_true hcount hstop hd htargetB
          have hwhole : Run B
              (.while (.lt (.var "drawCount") (.var "batchStop"))
                sequentialDrawBody) σ σ₂
              ((15 * Nat.clog 2 m + 30) * used + 47) := by
            have h := runWhileTrue hguard hbody htailRun
            have hsz : (Cond.lt (.var "drawCount")
                (.var "batchStop")).size = 3 := by decide
            rw [hsz] at h
            exact h.mono (by omega)
          refine ⟨σ₂, g₁, ?_, ?_, hframe₁, ?_, ?_, ?_, ?_, hbad₂,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa using hwhole
          · exact (hbranch.frame_arr "key0" (by decide)).trans hkey₁
          · exact (hbranch.frame_arr "drawDomain" (by decide)).trans hdomain₁
          · simpa [writeDraws] using
              (hbranch.frame_arr "sampleDraws" (by decide)).trans hdraws₁
          · simpa using hcount₂
          · simpa using hstop₂
          · exact (hbranch.frame_var "batchTarget" (by decide)).trans
              ((hdraw.frame_var "batchTarget" (by decide)).trans htarget)
          · have hdrop : (List.ofFn tape ++ tail).drop used =
                (List.ofFn tape).drop used ++ tail :=
              drop_ofFn_append tape tail (by omega)
            simpa [hu, hdrop, flatten_append, List.append_assoc] using
              (hbranch.frame_inp (by decide)).trans hinp₁
          · exact (hbranch.frame_var "v" (by decide)).trans hv₁
          · exact (hbranch.frame_var "L" (by decide)).trans hL₁
          · exact (hbranch.frame_var "drawModulus" (by decide)).trans hmod₁
          · exact (hbranch.frame_var "drawCap" (by decide)).trans hcap₁
      | accepted tape tail i u hsel hnext =>
          rename_i valuesTail usedTail
          have hd : d < target := by omega
          have hcapBuf : d < bufferCap := by omega
          have hdB : d + 1 < B := by omega
          have hinput : σ.inp = flattenBitBlocks tape ++
              (flattenBitBlockList tail ++ rest) := by
            simpa [flattenBitBlocks, flattenBitBlockList_eq_flatMap,
              List.flatMap_append, List.append_assoc] using hinp
          obtain ⟨σ₁, g₁, hdraw, hkey₁, hframe₁, hsuccess₁, _,
            hused₁, hfound₁, hinp₁, hdomain₁, _, hv₁, hL₁, hmod₁, hcap₁⟩ :=
            countedIndexedDrawAppend_run_tape tape hm hkey hdomain hmCap hvalueB
              hdraws hcount hcapBuf hdB hv hvn hL hmod hcap hinput
              hpowB hnB htwoB htB hmB honeB
          obtain ⟨i', hi', hdraws₁, hcount₁⟩ := hsuccess₁ (by simp [hsel])
          have hii : i' = i := by
            have he : (some i' : Option (Fin m)) = some i :=
              hi'.symm.trans (by simp [hsel])
            exact Option.some.inj he
          subst i'
          have hu : bitTapeAttemptsUsed m t tape = u :=
            selector_used_eq hm tape (some i) hsel
          have huCap : u ≤ t := (stoppedEvent_bounds m hm t u i tape hsel).2
          have hfoundOne : σ₁.vars "drawFound" = 1 := by
            simpa [hsel] using hfound₁
          have hbranch : Run B (.ite (.eq (.var "drawFound") (.lit 0))
              (seqs [.assign "batchFailed" (.lit 1),
                .assign "batchStop" (.var "drawCount")]) .skip) σ₁ σ₁ 8 :=
            batchBranch_success hfoundOne honeB
          have hbody : Run B sequentialDrawBody σ σ₁
              ((15 * Nat.clog 2 m + 30) * u + 39) := by
            have hseq := Run.seq hdraw hbranch
            simpa [sequentialDrawBody, seqs, hu, Nat.add_assoc] using hseq
          have hstop₁ : σ₁.vars "batchStop" = target :=
            (hdraw.frame_var "batchStop" (by decide)).trans hstop
          have hbad₁ : σ₁.vars "batchFailed" = 0 :=
            (hdraw.frame_var "batchFailed" (by decide)).trans hbad
          have htarget₁ : σ₁.vars "batchTarget" = target :=
            (hdraw.frame_var "batchTarget" (by decide)).trans htarget
          have hinput₁ : σ₁.inp =
              flattenBitBlockList ((List.ofFn tape).drop u ++ tail) ++ rest := by
            simpa [hu, flatten_append, List.append_assoc] using hinp₁
          have hrTail : d + 1 + r = target := by omega
          obtain ⟨σ₂, g₂, hloop₂, hkey₂, hframe₂, hdomain₂,
            hdraws₂, hcount₂, hstop₂, hbad₂, htarget₂,
            hinp₂, hv₂, hL₂, hmod₂, hcap₂⟩ :=
            ih (d + 1) ((List.ofFn tape).drop u ++ tail) _ _ _
              σ₁ g₁ (upd draws d (domain i.val)) rest hnext hrTail
              hkey₁ hdomain₁ hdraws₁ hcount₁ hstop₁ hbad₁ htarget₁
              hv₁ hL₁ hmod₁ hcap₁ hinput₁
          have hguard := batchGuard_true hcount hstop hd htargetB
          have hwhole : Run B
              (.while (.lt (.var "drawCount") (.var "batchStop"))
                sequentialDrawBody) σ σ₂
              ((15 * Nat.clog 2 m + 30) * (u + usedTail) +
                43 * ((i :: valuesTail).length + if failed then 1 else 0) + 4) := by
            have h := runWhileTrue hguard hbody hloop₂
            have hsz : (Cond.lt (.var "drawCount")
                (.var "batchStop")).size = 3 := by decide
            rw [hsz] at h
            convert h using 1 <;> simp only [List.length_cons]
            ring
          refine ⟨σ₂, g₂, hwhole, hkey₂, ?_, hdomain₂, ?_, ?_, ?_,
            hbad₂, htarget₂, ?_, hv₂, hL₂, hmod₂, hcap₂⟩
          · intro j hj hneq
            exact (hframe₂ j hj hneq).trans (hframe₁ j hj hneq)
          · simpa [writeDraws] using hdraws₂
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount₂
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstop₂
          · have hdrop : (List.ofFn tape ++ tail).drop u =
                (List.ofFn tape).drop u ++ tail :=
              drop_ofFn_append tape tail huCap
            have hdrop₂ : ((List.ofFn tape).drop u ++ tail).drop usedTail =
                (List.ofFn tape ++ tail).drop (u + usedTail) := by
              rw [← hdrop, List.drop_drop]
            rw [hdrop₂] at hinp₂
            exact hinp₂

/-- Run the fixed source command on a finite block list. The caller supplies
enough blocks for the worst case of `r` capped draws, but each successful
draw consumes only its actual attempts. The reported cost charges the exact
number of read blocks plus a linear overhead per call. A failed call keeps
all completed values in the occupied prefix and stops further calls. -/
lemma sequentialDraws_run_list
    {B n v m domainCap t bufferCap r : ℕ} {σ : Env}
    {g domain draws : ℕ → ℕ} {blocks : List (Block m)} {rest : List ℕ}
    (hm : 0 < m) (hlen : r * t ≤ blocks.length)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hdomain : σ.arrs "drawDomain" = arrOf domainCap domain)
    (hmCap : m ≤ domainCap) (hvalueB : ∀ i < m, domain i < B)
    (hdraws : σ.arrs "sampleDraws" = arrOf bufferCap draws)
    (hbufferCap : r ≤ bufferCap)
    (htarget : σ.vars "batchTarget" = r)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = Nat.clog 2 m)
    (hmod : σ.vars "drawModulus" = m)
    (hcap : σ.vars "drawCap" = t)
    (hinp : σ.inp = flattenBitBlockList blocks ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B) (hnB : n < B)
    (htwoB : 2 < B) (htB : t < B) (hmB : m < B)
    (hrB : r < B) (honeB : 1 < B) :
    ∃ (values : List (Fin m)) (used : ℕ) (failed : Bool)
      (σ' : Env) (g' : ℕ → ℕ),
      DrawTrace m hm t r blocks values used failed ∧
      Run B sequentialDraws σ σ'
        ((15 * Nat.clog 2 m + 30) * used +
          43 * (values.length + if failed then 1 else 0) + 10) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ j < n, j ≠ v → g' j = g j) ∧
      σ'.arrs "drawDomain" = arrOf domainCap domain ∧
      σ'.arrs "sampleDraws" =
        arrOf bufferCap (writeDraws domain draws 0 values) ∧
      (∀ j (hj : j < values.length),
        (σ'.arrs "sampleDraws")[j]? = some (domain values[j].val)) ∧
      (∀ j (hj : j < bufferCap), values.length ≤ j →
        (σ'.arrs "sampleDraws")[j]? = some (draws j)) ∧
      σ'.vars "drawCount" = values.length ∧
      σ'.vars "batchStop" = (if failed then values.length else r) ∧
      σ'.vars "batchFailed" = (if failed then 1 else 0) ∧
      (failed = false ↔ σ'.vars "drawCount" = r) ∧
      used ≤ blocks.length ∧
      values.length + (if failed then 1 else 0) ≤ r ∧
      σ'.vars "batchTarget" = r ∧
      σ'.inp = flattenBitBlockList (blocks.drop used) ++ rest ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = Nat.clog 2 m ∧
      σ'.vars "drawModulus" = m ∧ σ'.vars "drawCap" = t := by
  obtain ⟨values, used, failed, htrace⟩ := drawTrace_exists m hm t r blocks hlen
  let σ₁ := σ.setVar "drawCount" 0
  let σ₂ := σ₁.setVar "batchStop" r
  let σ₃ := σ₂.setVar "batchFailed" 0
  have hinit₁ : Run B (.assign "drawCount" (.lit 0)) σ σ₁ 2 := by
    simpa [σ₁] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have htarget₁ : σ₁.vars "batchTarget" = r := by simp [σ₁, htarget]
  have hinit₂ : Run B (.assign "batchStop" (.var "batchTarget")) σ₁ σ₂ 2 := by
    apply Run.assign
    simpa [σ₂, htarget₁] using (evalB_var (by rw [htarget₁]; exact hrB :
      σ₁.vars "batchTarget" < B))
  have hinit₃ : Run B (.assign "batchFailed" (.lit 0)) σ₂ σ₃ 2 := by
    simpa [σ₃] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hkey₃ : σ₃.arrs "key0" = arrOf n g := by simp [σ₃, σ₂, σ₁, hkey]
  have hdomain₃ : σ₃.arrs "drawDomain" = arrOf domainCap domain := by
    simp [σ₃, σ₂, σ₁, hdomain]
  have hdraws₃ : σ₃.arrs "sampleDraws" = arrOf bufferCap draws := by
    simp [σ₃, σ₂, σ₁, hdraws]
  have hcount₃ : σ₃.vars "drawCount" = 0 := by simp [σ₃, σ₂, σ₁]
  have hstop₃ : σ₃.vars "batchStop" = r := by simp [σ₃, σ₂]
  have hbad₃ : σ₃.vars "batchFailed" = 0 := by simp [σ₃]
  have htarget₃ : σ₃.vars "batchTarget" = r := by simp [σ₃, σ₂, σ₁, htarget]
  have hv₃ : σ₃.vars "v" = v := by simp [σ₃, σ₂, σ₁, hv]
  have hL₃ : σ₃.vars "L" = Nat.clog 2 m := by simp [σ₃, σ₂, σ₁, hL]
  have hmod₃ : σ₃.vars "drawModulus" = m := by simp [σ₃, σ₂, σ₁, hmod]
  have hcap₃ : σ₃.vars "drawCap" = t := by simp [σ₃, σ₂, σ₁, hcap]
  have hinp₃ : σ₃.inp = flattenBitBlockList blocks ++ rest := by
    simpa [σ₃, σ₂, σ₁] using hinp
  obtain ⟨σ', g', hloop, hkey', hframe', hdomain', hdraws',
    hcount', hstop', hbad', htarget', hinp', hv', hL', hmod', hcap'⟩ :=
    sequentialLoop_run_trace hm domain hmCap hvalueB hvn hpowB hnB
      htwoB htB hmB honeB hbufferCap hrB r 0 blocks values used failed
      σ₃ g draws rest htrace (by simp) hkey₃ hdomain₃ hdraws₃
      hcount₃ hstop₃ hbad₃ htarget₃ hv₃ hL₃ hmod₃ hcap₃ hinp₃
  have hwhole : Run B sequentialDraws σ σ'
      ((15 * Nat.clog 2 m + 30) * used +
        43 * (values.length + if failed then 1 else 0) + 10) := by
    have hseq := Run.seq hinit₁ (Run.seq hinit₂ (Run.seq hinit₃ hloop))
    change Run B
      ((Com.assign "drawCount" (.lit 0)).seq
        ((Com.assign "batchStop" (.var "batchTarget")).seq
          ((Com.assign "batchFailed" (.lit 0)).seq
            (.while (.lt (.var "drawCount") (.var "batchStop"))
              sequentialDrawBody)))) σ σ' _
    exact hseq.mono (by omega)
  have hbounds := DrawTrace.used_and_calls m hm t htrace
  have hlenVals := (DrawTrace.length_and_status m hm t htrace).1
  have hcells := writeDraws_buffer_cells domain draws 0 values (by omega :
    0 + values.length ≤ bufferCap)
  refine ⟨values, used, failed, σ', g', htrace, hwhole, hkey', hframe',
    hdomain', hdraws', ?_, ?_, ?_, ?_, hbad', ?_, hbounds.1,
    hbounds.2, htarget', hinp', hv', hL', hmod', hcap'⟩
  · intro j hj
    rw [hdraws']
    simpa using hcells.1 j hj
  · intro j hj houtside
    rw [hdraws']
    exact hcells.2 j hj (Or.inr (by simpa using houtside))
  · simpa using hcount'
  · simpa using hstop'
  · have hstatus := (DrawTrace.length_and_status m hm t htrace).2
    simpa [hcount'] using hstatus

end Lax457868Proofs.SequentialDraws
