import Lax67.RamComputes
import Lax67Proofs.Lib.Basic

/-!
Semantic acceptance proofs for the input and time contract. The parity
program works on all raw finite lists at every word length at least one,
without any bound on the list length or entries. The last-entry program
has a constant instruction count, independent of the input length.
-/

namespace Lax67Proofs.InputSemantics

open Lax67.Ram Lax67.RamComputes Lax67Proofs.Machine
open Lax67Proofs.Reasoning.Lib

/-- The empty program executes no instruction. -/
theorem empty_runsTo (w : ℕ) (x : List ℕ) : RunsTo w [] x [] 0 := by
  exact (runOut_init_iff.mp (show runOut w 0 [] (initState x) 0 = some ([], 0) by
    simp [runOut_zero, initState])).1

/-- Explicit halt costs one, even as the first instruction. -/
theorem halt_runsTo (w : ℕ) (x : List ℕ) : RunsTo w [.halt] x [] 1 := by
  exact (runOut_init_iff.mp (show runOut w 1 [.halt] (initState x) 0 = some ([], 1) by
    simp [runOut_succ, step_eq, initState, effect_halt])).1

/-- Writing the initial zero and explicitly halting costs two. -/
theorem write_halt_runsTo (w : ℕ) (x : List ℕ) :
    RunsTo w [.write 0, .halt] x [0] 2 := by
  exact (runOut_init_iff.mp (show
    runOut w 2 [.write 0, .halt] (initState x) 0 = some ([0], 2) by
      simp [runOut_succ, step_eq, initState, effect_write_eq, effect_halt])).1

/-- An exhausted read is an executed instruction and costs one. -/
theorem exhausted_read_runsTo (w : ℕ) : RunsTo w [.read 0] [] [] 1 := by
  exact (runOut_init_iff.mp (show runOut w 1 [.read 0] (initState []) 0 = some ([], 1) by
    simp [runOut_succ, step_eq, initState, effect_read_eq])).1

/-- Fallthrough after a write incurs no terminal instruction. -/
theorem write_fallthrough_runsTo (w : ℕ) (x : List ℕ) :
    RunsTo w [.write 0] x [0] 1 := by
  exact (runOut_init_iff.mp (show runOut w 1 [.write 0] (initState x) 0 = some ([0], 1) by
    simp [runOut_succ, runOut_zero, step_eq, initState, effect_write_eq])).1

/-- Program addresses remain untruncated, including at word length one. -/
theorem jump_untruncated : RunsTo 1 [.jump 2, .write 0] [] [] 1 := by
  exact (runOut_init_iff.mp (show
    runOut 1 1 [.jump 2, .write 0] (initState []) 0 = some ([], 1) by
      simp [runOut_succ, runOut_zero, step_eq, initState, effect_jump])).1

/-- The audited zero-time explicit halt is impossible. -/
theorem halt_not_zero (w : ℕ) (x : List ℕ) : ¬ RunsTo w [.halt] x [] 0 := by
  intro h
  have := (runsTo_unique h (halt_runsTo w x)).2
  omega

/-- EOF parity uses program control to remember the parity and one data
cell for the consumed value and final answer. It has no length header. -/
def parityProgram : Program :=
  [.jeof 8, .read 0, .jump 4, .halt,
   .jeof 11, .read 0, .jump 0, .halt,
   .set 0 0, .write 0, .halt,
   .set 0 1, .write 0, .halt]

/-- One visit to either parity control location consumes one word and
switches parity in exactly three successful transitions. -/
private theorem parity_cons {w : ℕ} (s : State) (b : Bool) (v : ℕ) (xs : List ℕ)
    (hpc : s.pc = if b then 4 else 0) (hin : s.inp = v :: xs) :
    run w parityProgram 3 s = some { s with
      pc := if !b then 4 else 0
      mem := setCell w s.mem 0 v
      inp := xs } := by
  cases b <;> simp [run_succ, run_zero, step_eq, parityProgram, effect_jeof,
    effect_read_eq, effect_jump, hpc, hin]

/-- An empty remaining tape writes the control parity and reaches its
explicit halt after three successful transitions. -/
private theorem parity_nil {w : ℕ} (hw : 1 < 2 ^ w) (s : State) (b : Bool)
    (hpc : s.pc = if b then 4 else 0) (hin : s.inp = []) (hout : s.out = []) :
    ∃ u, run w parityProgram 3 s = some u ∧ step w parityProgram u = none ∧
      terminalCost parityProgram u = 1 ∧ u.out = [if b then 1 else 0] := by
  cases b
  · refine ⟨{ s with pc := 10, mem := setCell w s.mem 0 0, out := [0] }, ?_, ?_, ?_, rfl⟩
    · simp [run_succ, run_zero, step_eq, parityProgram, effect_jeof, effect_set,
        effect_write_eq, setCell_eq, hpc, hin, hout]
    · simp [step_eq, parityProgram, effect_halt]
    · simp [terminalCost_eq, parityProgram]
  · refine ⟨{ s with pc := 13, mem := setCell w s.mem 0 1, out := [1] }, ?_, ?_, ?_, rfl⟩
    · simp [run_succ, run_zero, step_eq, parityProgram, effect_jeof, effect_set,
        effect_write_eq, setCell_eq, hpc, hin, hout, Nat.mod_eq_of_lt hw]
    · simp [step_eq, parityProgram, effect_halt]
    · simp [terminalCost_eq, parityProgram]

private theorem parity_run {w : ℕ} (hw : 1 < 2 ^ w) (xs : List ℕ) (s : State)
    (b : Bool) (hpc : s.pc = if b then 4 else 0) (hin : s.inp = xs) (hout : s.out = []) :
    ∃ u, run w parityProgram (3 * xs.length + 3) s = some u ∧
      step w parityProgram u = none ∧ terminalCost parityProgram u = 1 ∧
      u.out = [(xs.length + if b then 1 else 0) % 2] := by
  induction xs generalizing s b with
  | nil =>
      cases b <;> simpa using parity_nil hw s _ hpc hin hout
  | cons v xs ih =>
      let s' : State := { s with
        pc := if !b then 4 else 0
        mem := setCell w s.mem 0 v
        inp := xs }
      obtain ⟨u, hr, ht, hc, ho⟩ := ih s' (!b) rfl rfl hout
      refine ⟨u, ?_, ht, hc, ?_⟩
      · have hfirst : run w parityProgram 3 s = some s' := parity_cons s b v xs hpc hin
        rw [show 3 * (v :: xs).length + 3 = 3 + (3 * xs.length + 3) by
          simp only [List.length_cons]; omega]
        exact run_trans hfirst hr
      · rw [ho]
        congr 1
        cases b <;> simp [Nat.add_mod, Nat.add_comm, Nat.add_left_comm]

/-- A fixed program computes raw-list length parity with exact linear
time for all finite inputs, even when their length does not fit a word. -/
theorem parity_runsTo {w : ℕ} (hw : 1 ≤ w) (x : List ℕ) :
    RunsTo w parityProgram x [x.length % 2] (3 * x.length + 4) := by
  have hw' : 1 < 2 ^ w := lt_of_lt_of_le (by norm_num : 1 < 2 ^ 1)
    (Nat.pow_le_pow_right (by norm_num) hw)
  obtain ⟨u, hr, ht, hc, ho⟩ := parity_run hw' x (initState x) false rfl rfl rfl
  refine ⟨3 * x.length + 3, u, hr, ht, ?_, ?_⟩
  · simpa using ho
  · rw [hc]

theorem parity_computesInTime {w : ℕ} (hw : 1 ≤ w) :
    ComputesInTime w parityProgram Set.univ (fun x => [x.length % 2])
      (fun x => 3 * x.length + 4) := by
  intro x _
  exact ⟨_, le_rfl, parity_runsTo hw x⟩

/-- Read the input's last entry using its length and indexed access.
Cell zero is both the index source and destination of `inputLoad`. -/
def lastProgram : Program :=
  [.inputLength 0, .set 1 1, .sub 0 0 1, .inputLoad 0 0, .write 0, .halt]

/-- Only the supplied length and returned entry need fit. Earlier input
entries are unconstrained because the program never reads them. -/
theorem last_runsTo {w : ℕ} (xs : List ℕ) (v : ℕ)
    (hlen : xs.length + 1 < 2 ^ w) (hv : v < 2 ^ w) :
    RunsTo w lastProgram (xs ++ [v]) [v] 6 := by
  have h1 : 1 < 2 ^ w := by omega
  have hn : xs.length < 2 ^ w := by omega
  apply (runOut_init_iff.mp (show
    runOut w 6 lastProgram (initState (xs ++ [v])) 0 = some ([v], 6) from ?_)).1
  simp [runOut_succ, step_eq, lastProgram, initState, effect_inputLength,
    effect_set, effect_sub_eq, effect_inputLoad_eq, effect_write_eq, effect_halt,
    setCell_eq, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hv]

/-- Indexed reads refer to the original input after a sequential read. -/
theorem indexed_after_read (w : ℕ) (v : ℕ) (xs : List ℕ) :
    RunsTo w [.read 0, .inputLoad 0 1, .write 0, .halt] (v :: xs) [v % 2 ^ w] 4 := by
  by_cases hw : w = 0
  · subst w
    apply (runOut_init_iff.mp (show
      runOut 0 4 [.read 0, .inputLoad 0 1, .write 0, .halt] (initState (v :: xs)) 0 =
        some ([v % 2 ^ 0], 4) from ?_)).1
    simp [runOut_succ, step_eq, initState, effect_read_eq, effect_inputLoad_eq,
      effect_write_eq, effect_halt, setCell_eq, Nat.mod_one]
  · have h1 : 1 < 2 ^ w := lt_of_lt_of_le (by norm_num : 1 < 2 ^ 1)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    apply (runOut_init_iff.mp (show
      runOut w 4 [.read 0, .inputLoad 0 1, .write 0, .halt] (initState (v :: xs)) 0 =
        some ([v % 2 ^ w], 4) from ?_)).1
    simp [runOut_succ, step_eq, initState, effect_read_eq, effect_inputLoad_eq,
      effect_write_eq, effect_halt, setCell_eq, Nat.mod_eq_of_lt h1]

/-- Empty indexed input returns zero. -/
example : RunsTo 2 [.inputLoad 0 0, .write 0, .halt] [] [0] 3 :=
  (runOut_init_iff.mp (by decide : runOut 2 3 [.inputLoad 0 0, .write 0, .halt]
    (initState []) 0 = some ([0], 3))).1

/-- Out-of-range indexed input returns zero, even with zero-valued data. -/
example : RunsTo 2 [.set 0 3, .inputLoad 0 0, .write 0, .halt] [0, 1] [0] 4 :=
  (runOut_init_iff.mp (by decide : runOut 2 4 [.set 0 3, .inputLoad 0 0, .write 0, .halt]
    (initState [0, 1]) 0 = some ([0], 4))).1

/-- Oversized indexed values are reduced. -/
example : RunsTo 2 [.inputLoad 0 0, .write 0, .halt] [7] [3] 3 :=
  (runOut_init_iff.mp (by decide : runOut 2 3 [.inputLoad 0 0, .write 0, .halt]
    (initState [7]) 0 = some ([3], 3))).1

/-- Length metadata wraps when the complete length does not fit. -/
example : RunsTo 1 [.inputLength 0, .write 0, .halt] [0, 0] [0] 3 :=
  (runOut_init_iff.mp (by decide : runOut 1 3 [.inputLength 0, .write 0, .halt]
    (initState [0, 0]) 0 = some ([0], 3))).1

/-- EOF testing distinguishes an exhausted tape from zero-valued input. -/
example : RunsTo 1 parityProgram [0] [1] 7 := parity_runsTo (by norm_num) [0]
example : RunsTo 1 parityProgram [0, 0] [0] 10 := parity_runsTo (by norm_num) [0, 0]

end Lax67Proofs.InputSemantics
