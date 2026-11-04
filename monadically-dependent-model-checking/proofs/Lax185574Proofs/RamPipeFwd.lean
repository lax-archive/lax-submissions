import Lax185574Proofs.RamPipe

/-!
The pipe forwards for the concrete program `pipeProg`, with its
constant, and the fact that the output of a halting run is no longer
than its time.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
/-- One instruction writes at most one entry. -/
theorem effect_out_length {i : Instr} {v : ℕ} {s s' : State} (h : i.effect v s = some s') :
    s'.out.length ≤ s.out.length + 1 := by
  cases i <;> simp only [effect_set, effect_load_eq, effect_store_eq, effect_add_eq,
    effect_sub_eq, effect_mul_eq, effect_div_eq, effect_and_eq, effect_shiftl_eq,
    effect_not_eq, effect_jump, effect_jzero_eq, effect_jeof, effect_inputLength,
    effect_inputLoad_eq, effect_halt, effect_read_eq, effect_write_eq] at h
  all_goals first
    | (cases h; simp)
    | skip
  · cases h
  · cases hs : s.inp.head? with
    | none => simp [hs] at h
    | some v => simp only [hs, Option.map_some, Option.some.injEq] at h; subst h; simp

/-- A run of `k` transitions writes at most `k` entries. -/
theorem run_out_length {v k : ℕ} {q : Program} {s s' : State} (h : run v q k s = some s') :
    s'.out.length ≤ s.out.length + k := by
  induction k generalizing s with
  | zero => cases h; omega
  | succ k ih =>
      rw [run_succ] at h
      cases hs : step v q s with
      | none => simp [hs] at h
      | some t =>
          rw [hs] at h
          have h1 := ih h
          rw [step_eq] at hs
          cases hq : q[s.pc]? with
          | none => simp [hq] at hs
          | some i =>
              have := effect_out_length (by simpa [hq] using hs)
              omega

/-- The output of a halting run is no longer than its time. -/
theorem runsTo_out_length {v t : ℕ} {q : Program} {x y : List ℕ} (h : RunsTo v q x y t) :
    y.length ≤ t := by
  obtain ⟨k, s, hk, -, hy, ht⟩ := h
  have := run_out_length hk
  simp only [initState, List.length_nil, Nat.zero_add] at this
  rw [← hy]; omega

/-- The constant of the pipe. -/
def pipeK (ρ : Rewrite 1) (ρ' : Rewrite 2) : ℕ :=
  pipeBase ρ ρ' + stepBound (pipeKs₁ ρ) + stepBound (pipeKs₂ ρ') + 24

/-- The pipe forwards, for the concrete program `pipeProg`. -/
theorem pipe_fwd (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2) (w : ℕ) (x y z : List ℕ)
    (t₁ t₂ : ℕ) (hK : pipeK ρ ρ' ≤ 2 ^ (w - 2)) (hy : y.length < 2 ^ (w - 2))
    (hfit : ρ.Fits w (fun _ => x)) (hfit' : ρ'.Fits w ![y, x])
    (h₁ : RunsTo (w - 2) P (ρ.apply fun _ => x) y t₁)
    (h₂ : RunsTo (w - 2) M (ρ'.apply ![y, x]) z t₂) :
    ∃ t ≤ pipeK ρ ρ' * (t₁ + t₂ + ρ.cost (fun _ => x) + ρ'.cost ![y, x]),
      RunsTo w (pipeProg P M ρ ρ') x z t := by
  obtain ⟨t, ht, hr⟩ := pipe_run P M ρ ρ' w x y z t₁ t₂ (by simp only [pipeK] at hK; omega) hy.le
    hfit hfit' h₁ h₂
  refine ⟨t, le_trans ht ?_, hr⟩
  have hc₁ : ρ.cost (fun _ => x) = (ρ.map (·.cost fun _ => x)).sum + 1 := rfl
  have hc₂ : ρ'.cost ![y, x] = (ρ'.map (·.cost ![y, x])).sum + 1 := rfl
  rw [hc₁, hc₂, pipeK]
  generalize (ρ.map (·.cost fun _ => x)).sum = C₁
  generalize (ρ'.map (·.cost ![y, x])).sum = C₂
  generalize stepBound (pipeKs₁ ρ) = B₁
  generalize stepBound (pipeKs₂ ρ') = B₂
  generalize pipeBase ρ ρ' = B₀
  set T := t₁ + t₂ + (C₁ + 1) + (C₂ + 1)
  have a1 : B₁ * (t₁ + 1) ≤ B₁ * T := Nat.mul_le_mul_left _ (by omega)
  have a2 : B₂ * (t₂ + 1) ≤ B₂ * T := Nat.mul_le_mul_left _ (by omega)
  have a3 : (B₀ + B₁ + B₂ + 24) * T = B₀ * T + B₁ * T + B₂ * T + 24 * T := by ring
  rw [a3]
  omega

theorem pipeBase_le_pipeK (ρ : Rewrite 1) (ρ' : Rewrite 2) : pipeBase ρ ρ' ≤ pipeK ρ ρ' := by
  simp only [pipeK]; omega

end Lax185574Proofs.RamSim
