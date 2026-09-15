import Lax67Proofs.Tactic
import Lax67Proofs.Compile

/-!
The two pieces every module of the data-structure library needs, and
neither `Reasoning` nor `Spec` should carry.

`upd` is what a store does to a cell function: `arrOf n f` is the kit's
way of saying what is *at* each position of an array, a store changes
one position, so it changes `f` at one point. It is written as the very
`if` that `set_arrOf` produces, so that a store rewrites into it and no
`Function.update` cast has to be pushed around afterwards.

`runOut` is the driver the worked examples are checked with. Every `Lib`
module ships a small program built from its own operations, compiled and
run on the machine of the concept package, so that what its
specifications say is also *seen*; that is house discipline everywhere
else in this repo and there is no reason for the kit to be exempt.
-/

namespace Lax67Proofs.Reasoning.Lib

open Lax67Proofs.Imp

/-! ### Updating a cell function -/

/-- The cell function `f` with position `k` holding `v`. -/
def upd (f : ℕ → ℕ) (k v : ℕ) : ℕ → ℕ := fun i => if i = k then v else f i

theorem upd_apply (f : ℕ → ℕ) (k v i : ℕ) : upd f k v i = if i = k then v else f i := rfl

@[simp] theorem upd_self (f : ℕ → ℕ) (k v : ℕ) : upd f k v k = v := by simp [upd]

@[simp] theorem upd_of_ne {f : ℕ → ℕ} {k i : ℕ} (v : ℕ) (h : i ≠ k) : upd f k v i = f i := by
  simp [upd, h]

/-- A store into an `arrOf` array is an `upd` of its cell function. This
is `set_arrOf` with the anonymous function named, and it is the only
bridge an operation's specification needs between the list and the
function. -/
theorem set_arrOf_eq_upd {n : ℕ} (f : ℕ → ℕ) (k v : ℕ) :
    (arrOf n f).set k v = arrOf n (upd f k v) := set_arrOf f v

/-- `arrOf` at a position, in the `getElem` form `simp` normalizes a
`getD` into once it can see the length. `Reasoning`'s `getD_arrOf` is
stated on `getD`, so it stops firing exactly when `simp` has made most
progress; this is the companion that keeps going. -/
@[simp] theorem getElem_arrOf {n i : ℕ} (f : ℕ → ℕ) (h : i < (arrOf n f).length) :
    (arrOf n f)[i] = f i := by
  simp only [arrOf, List.getElem_map, List.getElem_range]

/-- An update stays within a pointwise bound. -/
theorem upd_le {f : ℕ → ℕ} {k v c i : ℕ} (hv : v ≤ c) (hf : f i ≤ c) : upd f k v i ≤ c := by
  rw [upd_apply]; split <;> assumption

/-! ### The worked-example driver -/

open Lax67.Ram Lax67Proofs.Machine

/-- Run `p` at word length `w` from `s` using at most `fuel` executed
instructions, and return its complete output and the accumulated count.
Fetched terminal instructions cost one. Falling outside the program
costs zero and is detected even when the available fuel is zero.
`none` means that no terminating execution fits the available fuel. -/
def runOut (w : ℕ) : ℕ → Program → State → ℕ → Option (List ℕ × ℕ)
  | 0, p, s, k => if s.pc < p.length then none else some (s.out, k)
  | fuel + 1, p, s, k =>
      if s.pc < p.length then
        match step w p s with
        | none => some (s.out, k + 1)
        | some s' => runOut w fuel p s' (k + 1)
      else some (s.out, k)

/-! Materialize defining equations here so downstream simplification
introduces no declarations in the proof package's namespace. -/

@[simp] theorem runOut_zero (w : ℕ) (p : Program) (s : State) (k : ℕ) :
    runOut w 0 p s k = if s.pc < p.length then none else some (s.out, k) := by
  simp [runOut]

theorem runOut_succ (w fuel : ℕ) (p : Program) (s : State) (k : ℕ) :
    runOut w (fuel + 1) p s k =
      if s.pc < p.length then
        match step w p s with
        | none => some (s.out, k + 1)
        | some s' => runOut w fuel p s' (k + 1)
      else some (s.out, k) := by
  simp [runOut]

/-- The execution driver returns only terminal states, with the exact
instruction charge bounded by its fuel. The initial count is an offset. -/
theorem runOut_sound {w fuel k t : ℕ} {p : Program} {s : State} {y : List ℕ}
    (h : runOut w fuel p s k = some (y, t)) :
    ∃ j u, run w p j s = some u ∧ step w p u = none ∧ u.out = y ∧
      t = k + (j + terminalCost p u) ∧ j + terminalCost p u ≤ fuel := by
  induction fuel generalizing s k with
  | zero =>
      rw [runOut_zero] at h
      split at h
      · contradiction
      · rename_i hpc
        have heq := Prod.mk.inj (Option.some.inj h)
        refine ⟨0, s, rfl, step_none_of_length_le (by omega), heq.1, ?_, ?_⟩
        · simpa [terminalCost_eq, hpc] using heq.2.symm
        · simp [terminalCost_eq, hpc]
  | succ fuel ih =>
      rw [runOut_succ] at h
      split at h
      · rename_i hpc
        cases hs : step w p s with
        | none =>
            simp only [hs] at h
            have heq := Prod.mk.inj (Option.some.inj h)
            refine ⟨0, s, rfl, hs, heq.1, ?_, ?_⟩
            · simpa [terminalCost_eq, hpc] using heq.2.symm
            · simp [terminalCost_eq, hpc]
        | some s' =>
            simp only [hs] at h
            obtain ⟨j, u, hr, hu, hy, ht, hf⟩ := ih h
            refine ⟨j + 1, u, ?_, hu, hy, ?_, ?_⟩
            · rw [run_succ, hs]; exact hr
            · omega
            · omega
      · rename_i hpc
        have heq := Prod.mk.inj (Option.some.inj h)
        refine ⟨0, s, rfl, step_none_of_length_le (by omega), heq.1, ?_, ?_⟩
        · simpa [terminalCost_eq, hpc] using heq.2.symm
        · simp [terminalCost_eq, hpc]

/-- Every charged terminating execution is found with sufficient fuel. -/
theorem runOut_complete {w j fuel : ℕ} {p : Program} {s u : State}
    (hr : run w p j s = some u) (hu : step w p u = none)
    (hf : j + terminalCost p u ≤ fuel) (k : ℕ) :
    runOut w fuel p s k = some (u.out, k + (j + terminalCost p u)) := by
  induction j generalizing s fuel k with
  | zero =>
      have heq : s = u := Option.some.inj hr
      subst u
      cases fuel with
      | zero =>
          have hpc : ¬ s.pc < p.length := by
            simpa [terminalCost_eq] using hf
          simp [runOut_zero, terminalCost_eq, hpc]
      | succ fuel =>
          by_cases hpc : s.pc < p.length <;>
            simp [runOut_succ, terminalCost_eq, hpc, hu]
  | succ j ih =>
      rw [run_succ] at hr
      cases hs : step w p s with
      | none => simp [hs] at hr
      | some s' =>
          have hpc : s.pc < p.length := by
            by_contra hn
            have := step_none_of_length_le (w := w) (p := p) (s := s) (by omega)
            rw [hs] at this
            contradiction
          obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
          rw [runOut_succ, if_pos hpc, hs]
          have hrec := ih (fuel := fuel) (by simpa [hs] using hr) (by omega) (k + 1)
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec

/-- The driver's reported count agrees with the public timed relation,
including its exact fuel boundary. -/
theorem runOut_init_iff {w fuel t : ℕ} {p : Program} {x y : List ℕ} :
    runOut w fuel p (initState x) 0 = some (y, t) ↔
      RunsTo w p x y t ∧ t ≤ fuel := by
  constructor
  · intro h
    obtain ⟨j, u, hr, hu, hy, ht, hf⟩ := runOut_sound h
    simp only [Nat.zero_add] at ht
    exact ⟨⟨j, u, hr, hu, hy, ht⟩, ht ▸ hf⟩
  · rintro ⟨⟨j, u, hr, hu, hy, ht⟩, hf⟩
    have := runOut_complete hr hu (ht ▸ hf) 0
    simpa only [Nat.zero_add, hy, ← ht] using this

end Lax67Proofs.Reasoning.Lib
