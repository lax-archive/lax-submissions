import Lax808846Proofs.Machine

/-!
Execution of raw word-RAM code, in the form used by the simulators of
`RamSimulate`. `Exec w p n s s'` says that `n` successful transitions of
`p` lead from `s` to `s'`. Each instruction with word operands gets a
rule whose result is an explicit state, with memory written by
`Function.update`. A state whose cells all hold words stays so, which is
`WordMem`.
-/

namespace Lax185574Proofs.RamExec

open Lax808846.Ram Lax808846Proofs.Machine

/-- `n` successful transitions lead from `s` to `s'`. -/
def Exec (w : ℕ) (p : Program) (n : ℕ) (s s' : State) : Prop :=
  run w p n s = some s'

variable {w : ℕ} {p : Program}

theorem Exec.refl (s : State) : Exec w p 0 s s := rfl

theorem Exec.trans {n m : ℕ} {s s₁ s₂ : State} (h₁ : Exec w p n s s₁) (h₂ : Exec w p m s₁ s₂) :
    Exec w p (n + m) s s₂ := run_trans h₁ h₂

theorem Exec.one {s s' : State} {ins : Instr} (h : p[s.pc]? = some ins)
    (he : ins.effect w s = some s') : Exec w p 1 s s' := by
  unfold Exec; rw [run_one h, he]

/-- Every cell holds a word. -/
def WordMem (w : ℕ) (m : ℕ → ℕ) : Prop := ∀ a, m a < 2 ^ w

theorem setCell_lit {a : ℕ} (m : ℕ → ℕ) (v : ℕ) (ha : a < 2 ^ w) :
    setCell w m a v = Function.update m a (v % 2 ^ w) := by
  funext b
  rw [setCell_eq, Nat.mod_eq_of_lt ha, Function.update_apply]

theorem WordMem.update {m : ℕ → ℕ} (h : WordMem w m) (a : ℕ) {v : ℕ} (hv : v < 2 ^ w) :
    WordMem w (Function.update m a v) := by
  intro b
  rw [Function.update_apply]
  split_ifs
  · exact hv
  · exact h b

theorem WordMem.setCell {m : ℕ → ℕ} (h : WordMem w m) (a v : ℕ) :
    WordMem w (Lax808846.Ram.setCell w m a v) := by
  intro b
  rw [setCell_eq]
  split_ifs
  · exact Nat.mod_lt _ (two_pow_pos w)
  · exact h b

/-! ### One instruction

Each rule takes the instruction at the program counter and the facts
that its operand cells are words, and gives the next state. -/

section rules

variable {s : State}

theorem x_set {a n : ℕ} (h : p[s.pc]? = some (.set a n)) (ha : a < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (n % 2 ^ w) } :=
  Exec.one h (by rw [effect_set, setCell_lit _ _ ha])

theorem x_load {a b : ℕ} (h : p[s.pc]? = some (.load a b)) (hm : WordMem w s.mem)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (s.mem (s.mem b)) } :=
  Exec.one h (by
    rw [effect_load hb (hm b), setCell_lit _ _ ha, Nat.mod_eq_of_lt (hm _)])

theorem x_store {a b : ℕ} (h : p[s.pc]? = some (.store a b)) (hm : WordMem w s.mem)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem (s.mem a) (s.mem b) } :=
  Exec.one h (by
    rw [effect_store ha hb, setCell_lit _ _ (hm a), Nat.mod_eq_of_lt (hm _)])

theorem x_add {a b c : ℕ} (h : p[s.pc]? = some (.add a b c))
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a ((s.mem b + s.mem c) % 2 ^ w) } :=
  Exec.one h (by rw [effect_add hb hc, setCell_lit _ _ ha])

theorem x_sub {a b c : ℕ} (h : p[s.pc]? = some (.sub a b c)) (hm : WordMem w s.mem)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (s.mem b - s.mem c) } :=
  Exec.one h (by
    rw [effect_sub hb hc, setCell_lit _ _ ha,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (hm b))])

theorem x_mul {a b c : ℕ} (h : p[s.pc]? = some (.mul a b c))
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a ((s.mem b * s.mem c) % 2 ^ w) } :=
  Exec.one h (by rw [effect_mul hb hc, setCell_lit _ _ ha])

theorem x_div {a b c : ℕ} (h : p[s.pc]? = some (.div a b c)) (hm : WordMem w s.mem)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (s.mem b / s.mem c) } :=
  Exec.one h (by
    rw [effect_div hb hc, setCell_lit _ _ ha,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (hm b))])

theorem x_and {a b c : ℕ} (h : p[s.pc]? = some (.and a b c)) (hm : WordMem w s.mem)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (Nat.land (s.mem b) (s.mem c)) } :=
  Exec.one h (by
    rw [effect_and hb hc, setCell_lit _ _ ha,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (land_le_left _ _) (hm b))])

theorem x_shiftl {a b c : ℕ} (h : p[s.pc]? = some (.shiftl a b c))
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a ((s.mem b * 2 ^ s.mem c) % 2 ^ w) } :=
  Exec.one h (by rw [effect_shiftl hb hc, setCell_lit _ _ ha])

theorem x_not {a b : ℕ} (h : p[s.pc]? = some (.not a b))
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (2 ^ w - 1 - s.mem b) } :=
  Exec.one h (by
    rw [effect_not hb, setCell_lit _ _ ha,
      Nat.mod_eq_of_lt (by have := two_pow_pos w; omega)])

theorem x_jump {l : ℕ} (h : p[s.pc]? = some (.jump l)) :
    Exec w p 1 s { s with pc := l } :=
  Exec.one h (effect_jump w l s)

theorem x_jzero {a l : ℕ} (h : p[s.pc]? = some (.jzero a l)) (ha : a < 2 ^ w) :
    Exec w p 1 s { s with pc := if s.mem a = 0 then l else s.pc + 1 } :=
  Exec.one h (effect_jzero ha)

theorem x_jzero_pos {a l : ℕ} (h : p[s.pc]? = some (.jzero a l)) (ha : a < 2 ^ w)
    (h0 : s.mem a = 0) : Exec w p 1 s { s with pc := l } := by
  have := x_jzero h ha; rwa [if_pos h0] at this

theorem x_jzero_neg {a l : ℕ} (h : p[s.pc]? = some (.jzero a l)) (ha : a < 2 ^ w)
    (h0 : s.mem a ≠ 0) : Exec w p 1 s { s with pc := s.pc + 1 } := by
  have := x_jzero h ha; rwa [if_neg h0] at this

theorem x_inputLength {a : ℕ} (h : p[s.pc]? = some (.inputLength a)) (ha : a < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (s.input.length % 2 ^ w) } :=
  Exec.one h (by rw [effect_inputLength, setCell_lit _ _ ha])

theorem x_inputLoad {a b : ℕ} (h : p[s.pc]? = some (.inputLoad a b)) (hm : WordMem w s.mem)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (s.input[s.mem b]?.getD 0 % 2 ^ w) } :=
  Exec.one h (by rw [effect_inputLoad hb (hm b), setCell_lit _ _ ha])

theorem x_write {a : ℕ} (h : p[s.pc]? = some (.write a)) (hm : WordMem w s.mem)
    (ha : a < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, out := s.out ++ [s.mem a] } :=
  Exec.one h (effect_write ha (hm a))

end rules

/-! ### Termination -/

/-- A run of `n` transitions that ends where the program halts, with its
charged time. -/
theorem runsTo_of_exec {x y : List ℕ} {n : ℕ} {s : State}
    (h : Exec w p n (initState x) s) (hs : step w p s = none) (hy : s.out = y) :
    RunsTo w p x y (n + terminalCost p s) :=
  ⟨n, s, h, hs, hy, rfl⟩

theorem terminalCost_le_one (p : Program) (s : State) : terminalCost p s ≤ 1 := by
  rw [terminalCost_eq]; split_ifs <;> omega

theorem step_halt {s : State} (h : p[s.pc]? = some .halt) : step w p s = none := by
  rw [step_eq, h]; rfl

end Lax185574Proofs.RamExec

namespace Lax185574Proofs.RamExec
open Lax808846.Ram Lax808846Proofs.Machine
variable {w : ℕ} {p : Program}

theorem WordMem.effect {i : Instr} {s s' : State} (hm : WordMem w s.mem)
    (h : i.effect w s = some s') : WordMem w s'.mem := by
  cases i <;> simp only [effect_set, effect_load_eq, effect_store_eq, effect_add_eq,
    effect_sub_eq, effect_mul_eq, effect_div_eq, effect_and_eq, effect_shiftl_eq,
    effect_not_eq, effect_jump, effect_jzero_eq, effect_jeof, effect_inputLength,
    effect_inputLoad_eq, effect_halt, effect_read_eq, effect_write_eq] at h
  all_goals first
    | (cases h; exact hm.setCell _ _)
    | (cases h; exact hm)
    | skip
  · cases h
  · cases hs : s.inp.head? with
    | none => simp [hs] at h
    | some v => simp only [hs, Option.map_some, Option.some.injEq] at h; subst h; exact hm.setCell _ _

theorem WordMem.exec {n : ℕ} {s s' : State} (hm : WordMem w s.mem) (h : Exec w p n s s') :
    WordMem w s'.mem := by
  induction n generalizing s with
  | zero => cases h; exact hm
  | succ n ih =>
      unfold Exec at h
      rw [run_succ] at h
      cases hs : step w p s with
      | none => simp [hs] at h
      | some t =>
          rw [hs] at h
          refine ih ?_ h
          rw [step_eq] at hs
          cases hp : p[s.pc]? with
          | none => simp [hp] at hs
          | some i => exact hm.effect (by simpa [hp] using hs)

/-- Instruction fetch inside a placed block. -/
theorem fetch {A i : ℕ} {c : Program} {s : State} {ins : Instr} (hf : Fits p A c)
    (hpc : s.pc = A + i) (hi : c[i]? = some ins) : p[s.pc]? = some ins := by
  rw [hpc, hf i (List.getElem?_eq_some_iff.mp hi).1, hi]

theorem Exec.of_eq {n : ℕ} {s s₁ s₂ : State} (h : Exec w p n s s₁) (he : s₁ = s₂) :
    Exec w p n s s₂ := he ▸ h

theorem Exec.cast {n m : ℕ} {s s' : State} (h : Exec w p n s s') (he : n = m) :
    Exec w p m s s' := he ▸ h

theorem Exec.at_pc {n A : ℕ} {s s' : State} (h : Exec w p n s s') (hpc : s'.pc = A) :
    Exec w p n s { s' with pc := A } := by
  cases s'; cases hpc; exact h

/-- Name the state after one step that writes one cell. -/
theorem Exec.upd {n a v : ℕ} {s : State} {pc : ℕ}
    (h : Exec w p n s { s with pc := pc, mem := Function.update s.mem a v }) :
    ∃ s', Exec w p n s s' ∧ s'.pc = pc ∧ (∀ c, s'.mem c = if c = a then v else s.mem c) ∧
      s'.input = s.input ∧ s'.inp = s.inp ∧ s'.out = s.out :=
  ⟨_, h, rfl, fun c => Function.update_apply _ _ _ _, rfl, rfl, rfl⟩

theorem fits_cons {A : ℕ} {ins : Instr} {c : Program} :
    Fits p A (ins :: c) ↔ p[A]? = some ins ∧ Fits p (A + 1) c := by
  rw [show ins :: c = [ins] ++ c from rfl, fits_append, fits_singleton]; simp

end Lax185574Proofs.RamExec
