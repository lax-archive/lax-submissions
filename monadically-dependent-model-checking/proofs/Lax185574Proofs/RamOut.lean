import Lax185574Proofs.RamExec

/-!
The entries of the output of a run at word length `v` are below `2 ^ v`.
-/

namespace Lax185574Proofs.RamExec

open Lax808846.Ram Lax808846Proofs.Machine

theorem effect_out_lt {i : Instr} {v : ℕ} {s s' : State} (h : i.effect v s = some s')
    (hs : ∀ e ∈ s.out, e < 2 ^ v) : ∀ e ∈ s'.out, e < 2 ^ v := by
  cases i <;> simp only [effect_set, effect_load_eq, effect_store_eq, effect_add_eq,
    effect_sub_eq, effect_mul_eq, effect_div_eq, effect_and_eq, effect_shiftl_eq,
    effect_not_eq, effect_jump, effect_jzero_eq, effect_jeof, effect_inputLength,
    effect_inputLoad_eq, effect_halt, effect_read_eq, effect_write_eq] at h
  all_goals first
    | (cases h; exact hs)
    | skip
  · cases h
  · cases hh : s.inp.head? with
    | none => simp [hh] at h
    | some u => simp only [hh, Option.map_some, Option.some.injEq] at h; subst h; exact hs
  · cases h
    intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hs e he
    · exact Nat.mod_lt _ (by positivity)

theorem run_out_lt {v k : ℕ} {q : Program} {s s' : State} (h : run v q k s = some s')
    (hs : ∀ e ∈ s.out, e < 2 ^ v) : ∀ e ∈ s'.out, e < 2 ^ v := by
  induction k generalizing s with
  | zero => cases h; exact hs
  | succ k ih =>
      rw [run_succ] at h
      cases hst : step v q s with
      | none => simp [hst] at h
      | some t =>
          rw [hst] at h
          refine ih h ?_
          rw [step_eq] at hst
          cases hq : q[s.pc]? with
          | none => simp [hq] at hst
          | some i => exact effect_out_lt (by simpa [hq] using hst) hs

/-- The entries of an output at word length `v` are below `2 ^ v`. -/
theorem runsTo_out_lt {v t : ℕ} {q : Program} {x y : List ℕ} (h : RunsTo v q x y t) :
    ∀ e ∈ y, e < 2 ^ v := by
  obtain ⟨k, s, hr, -, hy, -⟩ := h
  rw [← hy]
  exact run_out_lt hr (by simp [initState])

end Lax185574Proofs.RamExec
