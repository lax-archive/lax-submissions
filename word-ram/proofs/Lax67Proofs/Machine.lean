import Lax67.Ram
import Mathlib.Tactic

/-!
Reasoning kit for the word machine: the equations of the concept's
definitions, composition of runs, the placement predicate `Fits`, and
the three bitwise identities the compiler's lowered operators need.

The raw defining equations are proved by `rfl`. The concept's `step` and
`Instr.effect` are defined by pattern matching, and `simp`-unfolding
such a definition creates an auxiliary declaration named after it — in
the concept's namespace, which this package is not allowed to declare
into. So the equations are restated here, in this package's namespace,
and only these are ever used.

The word length appears in two places: every value the machine produces
carries a `% 2 ^ w`, and every data-memory address or input index
carries one. Program addresses are untruncated. The lemmas
below come in two flavours accordingly — the raw equation, with the
`_eq` suffix, and the version whose hypothesis is that the addresses are
words, in which case `Nat.mod_eq_of_lt` removes the reduction.
Everything above this file uses only the second flavour, which is what
makes the simulation an equality with the unbounded reference semantics
rather than a congruence modulo `2 ^ w`. The value a machine
instruction writes keeps its `% 2 ^ w`, because that reduction lives
inside `setCell` and is removed at the point where the value is read
back out, by `setCell_self`.

The bitwise identities are here because they are facts about `Nat`, not
about the machine, and because they are what makes the instruction set
of the concept a generating set: `∨`, `⊕` and `≫` are not instructions,
and the compiler emits the three-and-four instruction blocks the
concept's notes tabulate. Each is `#guard`ed on small cases before it is
proved.
-/

namespace Lax67Proofs.Machine

open Lax67.Ram

/-- There is at least one word. -/
theorem two_pow_pos (w : ℕ) : 0 < 2 ^ w := by positivity

/-! ### Memory -/

theorem setCell_eq (w : ℕ) (m : ℕ → ℕ) (a v b : ℕ) :
    setCell w m a v b = if b = a % 2 ^ w then v % 2 ^ w else m b := rfl

/-- Writing a word to a cell whose address is a word is an ordinary
update. -/
theorem setCell_self {w a v : ℕ} (m : ℕ → ℕ) (ha : a < 2 ^ w) (hv : v < 2 ^ w) :
    setCell w m a v a = v := by
  rw [setCell_eq, Nat.mod_eq_of_lt ha, if_pos rfl, Nat.mod_eq_of_lt hv]

/-- Reading back a cell just written, without a bound on the value: the
truncation is what remains. -/
theorem setCell_self_mod {w a : ℕ} (m : ℕ → ℕ) (v : ℕ) (ha : a < 2 ^ w) :
    setCell w m a v a = v % 2 ^ w := by
  rw [setCell_eq, Nat.mod_eq_of_lt ha, if_pos rfl]

/-- A write to a word address leaves every other cell alone. -/
theorem setCell_of_ne {w a b : ℕ} (m : ℕ → ℕ) (v : ℕ) (ha : a < 2 ^ w) (hb : b ≠ a) :
    setCell w m a v b = m b := by
  rw [setCell_eq, Nat.mod_eq_of_lt ha, if_neg hb]

/-! ### Instructions

An instruction that writes memory uses one `setCell`. Control and
output instructions preserve memory, and every instruction preserves
the original input array. -/

theorem effect_set (w a n : ℕ) (s : State) :
    (Instr.set a n).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a n } := rfl

theorem effect_load_eq (w a b : ℕ) (s : State) :
    (Instr.load a b).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) } := rfl

/-- Indirect read through a cell whose address, and whose contents, are
words. -/
theorem effect_load {w a b : ℕ} {s : State} (hb : b < 2 ^ w) (hm : s.mem b < 2 ^ w) :
    (Instr.load a b).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a (s.mem (s.mem b)) } := by
  rw [effect_load_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hm]

theorem effect_store_eq (w a b : ℕ) (s : State) :
    (Instr.store a b).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) } := rfl

/-- Indirect write through a cell whose address is a word. -/
theorem effect_store {w a b : ℕ} {s : State} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (Instr.store a b).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem (s.mem a) (s.mem b) } := by
  rw [effect_store_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem effect_add_eq (w a b c : ℕ) (s : State) :
    (Instr.add a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) } := rfl

theorem effect_add {w a b c : ℕ} {s : State} (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    (Instr.add a b c).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a (s.mem b + s.mem c) } := by
  rw [effect_add_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem effect_sub_eq (w a b c : ℕ) (s : State) :
    (Instr.sub a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) } := rfl

theorem effect_sub {w a b c : ℕ} {s : State} (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    (Instr.sub a b c).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a (s.mem b - s.mem c) } := by
  rw [effect_sub_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem effect_mul_eq (w a b c : ℕ) (s : State) :
    (Instr.mul a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) } := rfl

theorem effect_mul {w a b c : ℕ} {s : State} (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    (Instr.mul a b c).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a (s.mem b * s.mem c) } := by
  rw [effect_mul_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem effect_div_eq (w a b c : ℕ) (s : State) :
    (Instr.div a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) } := rfl

theorem effect_div {w a b c : ℕ} {s : State} (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    (Instr.div a b c).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a (s.mem b / s.mem c) } := by
  rw [effect_div_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem effect_and_eq (w a b c : ℕ) (s : State) :
    (Instr.and a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) } := rfl

theorem effect_and {w a b c : ℕ} {s : State} (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    (Instr.and a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem b) (s.mem c)) } := by
  rw [effect_and_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem effect_shiftl_eq (w a b c : ℕ) (s : State) :
    (Instr.shiftl a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) } := rfl

theorem effect_shiftl {w a b c : ℕ} {s : State} (hb : b < 2 ^ w) (hc : c < 2 ^ w) :
    (Instr.shiftl a b c).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem b * 2 ^ s.mem c) } := by
  rw [effect_shiftl_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem effect_not_eq (w a b : ℕ) (s : State) :
    (Instr.not a b).effect w s =
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (2 ^ w - 1 - s.mem (b % 2 ^ w)) } := rfl

theorem effect_not {w a b : ℕ} {s : State} (hb : b < 2 ^ w) :
    (Instr.not a b).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a (2 ^ w - 1 - s.mem b) } := by
  rw [effect_not_eq, Nat.mod_eq_of_lt hb]

theorem effect_jump (w l : ℕ) (s : State) :
    (Instr.jump l).effect w s = some { s with pc := l } := rfl

theorem effect_jzero_eq (w a l : ℕ) (s : State) :
    (Instr.jzero a l).effect w s =
      some { s with pc := if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1 } := rfl

theorem effect_jzero {w a l : ℕ} {s : State} (ha : a < 2 ^ w) :
    (Instr.jzero a l).effect w s =
      some { s with pc := if s.mem a = 0 then l else s.pc + 1 } := by
  rw [effect_jzero_eq, Nat.mod_eq_of_lt ha]

theorem effect_jeof (w l : ℕ) (s : State) :
    (Instr.jeof l).effect w s =
      some { s with pc := if s.inp.isEmpty then l else s.pc + 1 } := rfl

theorem effect_inputLength (w a : ℕ) (s : State) :
    (Instr.inputLength a).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a s.input.length } := rfl

theorem effect_inputLoad_eq (w a b : ℕ) (s : State) :
    (Instr.inputLoad a b).effect w s =
      some { s with
        pc := s.pc + 1
        mem := setCell w s.mem a (s.input[s.mem (b % 2 ^ w) % 2 ^ w]?.getD 0) } := rfl

theorem effect_inputLoad {w a b : ℕ} {s : State}
    (hb : b < 2 ^ w) (hm : s.mem b < 2 ^ w) :
    (Instr.inputLoad a b).effect w s =
      some { s with
        pc := s.pc + 1
        mem := setCell w s.mem a (s.input[s.mem b]?.getD 0) } := by
  rw [effect_inputLoad_eq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hm]

theorem effect_halt (w : ℕ) (s : State) : Instr.halt.effect w s = none := rfl

theorem effect_write_eq (w a : ℕ) (s : State) :
    (Instr.write a).effect w s =
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] } := rfl

theorem effect_write {w a : ℕ} {s : State} (ha : a < 2 ^ w) (hv : s.mem a < 2 ^ w) :
    (Instr.write a).effect w s =
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem a] } := by
  rw [effect_write_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hv]

theorem effect_read_eq (w a : ℕ) (s : State) :
    (Instr.read a).effect w s =
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail } := rfl

theorem effect_read {w : ℕ} {s : State} {v : ℕ} {rest : List ℕ} (a : ℕ)
    (h : s.inp = v :: rest) :
    (Instr.read a).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := rest } := by
  rw [effect_read_eq, h]; rfl

/-! ### Running -/

theorem step_eq (w : ℕ) (p : Program) (s : State) :
    step w p s = p[s.pc]?.bind fun i => i.effect w s := rfl

@[simp] theorem run_zero (w : ℕ) (p : Program) (s : State) : run w p 0 s = some s := rfl

theorem run_succ (w : ℕ) (p : Program) (t : ℕ) (s : State) :
    run w p (t + 1) s = (step w p s).bind (run w p t) := rfl

theorem run_add (w : ℕ) (p : Program) (t t' : ℕ) (s : State) :
    run w p (t + t') s = (run w p t s).bind (run w p t') := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_add, run_succ, run_succ]
      cases h : step w p s with
      | none => simp
      | some s₁ => simpa using ih s₁

/-- Runs compose: `t₁` steps to `s₁` and then `t₂` steps to `s₂`. -/
theorem run_trans {w : ℕ} {p : Program} {t₁ t₂ : ℕ} {s s₁ s₂ : State}
    (h₁ : run w p t₁ s = some s₁) (h₂ : run w p t₂ s₁ = some s₂) :
    run w p (t₁ + t₂) s = some s₂ := by
  rw [run_add, h₁]; exact h₂

/-- One step, when the instruction at the program counter is known. -/
theorem run_one {w : ℕ} {p : Program} {s : State} {ins : Instr} (h : p[s.pc]? = some ins) :
    run w p 1 s = ins.effect w s := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_eq, h]
  show (ins.effect w s).bind (run w p 0) = ins.effect w s
  cases ins.effect w s <;> rfl

/-- The original instruction subset, also allowing `jeof`: these
instructions can inspect the remaining tape but never the input array. -/
def IgnoresInputArray : Instr → Prop
  | .inputLength _ => False
  | .inputLoad _ _ => False
  | _ => True

/-- For every instruction in the original subset, replacing only the
new input-array field commutes with instruction execution. -/
theorem effect_replace_input {w : ℕ} {i : Instr} (h : IgnoresInputArray i)
    (s : State) (x : List ℕ) :
    i.effect w { s with input := x } =
      (i.effect w s).map (fun t => { t with input := x }) := by
  cases i <;> simp only [IgnoresInputArray] at h
  all_goals first
  | contradiction
  | rfl
  | simp only [effect_read_eq, Option.map_map]; rfl

/-- A program without `inputLength` and `inputLoad` has exactly the
same transition behavior after replacing the original input array. -/
theorem step_replace_input {w : ℕ} {p : Program}
    (hp : ∀ i ∈ p, IgnoresInputArray i) (s : State) (x : List ℕ) :
    step w p { s with input := x } =
      (step w p s).map (fun t => { t with input := x }) := by
  rw [step_eq, step_eq]
  cases hi : p[s.pc]? with
  | none => rfl
  | some i =>
      simpa [hi] using effect_replace_input (w := w) (hp i (List.mem_of_getElem? hi)) s x

/-- The added input-array field is a conservative extension for the
original instruction subset: every successful-transition count gives
the same counter, memory, remaining tape, output, and termination result. -/
theorem run_replace_input {w : ℕ} {p : Program}
    (hp : ∀ i ∈ p, IgnoresInputArray i) (k : ℕ) (s : State) (x : List ℕ) :
    run w p k { s with input := x } =
      (run w p k s).map (fun t => { t with input := x }) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [run_succ, run_succ, step_replace_input hp]
      cases hs : step w p s with
      | none => rfl
      | some t => simpa [hs] using ih t

/-- A successful instruction preserves the original read-only input. -/
theorem effect_input {w : ℕ} {i : Instr} {s s' : State}
    (h : i.effect w s = some s') : s'.input = s.input := by
  cases i <;> simp only [effect_set, effect_load_eq, effect_store_eq, effect_add_eq,
    effect_sub_eq, effect_mul_eq, effect_div_eq, effect_and_eq, effect_shiftl_eq,
    effect_not_eq, effect_jump, effect_jzero_eq, effect_jeof, effect_inputLength,
    effect_inputLoad_eq, effect_halt, effect_read_eq, effect_write_eq] at h
  all_goals try { cases h <;> rfl }
  cases hs : s.inp.head? with
  | none => simp [hs] at h
  | some v =>
      simp only [hs, Option.map_some] at h
      cases h
      rfl

/-- Every successful transition preserves the original read-only input. -/
theorem step_input {w : ℕ} {p : Program} {s s' : State}
    (h : step w p s = some s') : s'.input = s.input := by
  rw [step_eq] at h
  cases hp : p[s.pc]? with
  | none => simp [hp] at h
  | some i => exact effect_input (by simpa [hp] using h)

/-- Sequential reads, jumps, and writes cannot change indexed input. -/
theorem run_input {w k : ℕ} {p : Program} {s s' : State}
    (h : run w p k s = some s') : s'.input = s.input := by
  induction k generalizing s with
  | zero => cases h; rfl
  | succ k ih =>
      rw [run_succ] at h
      cases hs : step w p s with
      | none => simp [hs] at h
      | some t => exact (ih (by simpa [hs] using h)).trans (step_input hs)

/-- Out-of-range instruction fetch terminates without a charge. -/
theorem step_none_of_length_le {w : ℕ} {p : Program} {s : State}
    (h : p.length ≤ s.pc) : step w p s = none := by
  rw [step_eq, List.getElem?_eq_none (by omega)]
  rfl

theorem terminalCost_eq (p : Program) (s : State) :
    terminalCost p s = if s.pc < p.length then 1 else 0 := rfl

/-- A fetched instruction costs one when it terminates. -/
theorem terminalCost_of_getElem? {p : Program} {s : State} {i : Instr}
    (h : p[s.pc]? = some i) : terminalCost p s = 1 := by
  rw [terminalCost_eq, if_pos]
  exact List.getElem?_eq_some_iff.mp h |>.1

/-- A terminal state cannot make any further successful transition. -/
theorem run_succ_of_terminal {w : ℕ} {p : Program} {s : State}
    (h : step w p s = none) (k : ℕ) : run w p (k + 1) s = none := by
  rw [run_succ, h]; rfl

/-- Determinism fixes both the terminal state and successful-transition
count, regardless of the proposed bounds. -/
theorem terminal_run_unique {w k k' : ℕ} {p : Program} {s t t' : State}
    (h : run w p k s = some t) (ht : step w p t = none)
    (h' : run w p k' s = some t') (ht' : step w p t' = none) :
    k = k' ∧ t = t' := by
  induction k generalizing s k' with
  | zero =>
      have heq : s = t := Option.some.inj h
      subst t
      cases k' with
      | zero => exact ⟨rfl, Option.some.inj h'⟩
      | succ k' => rw [run_succ_of_terminal ht] at h'; contradiction
  | succ k ih =>
      cases k' with
      | zero =>
          have heq : s = t' := Option.some.inj h'
          subst t'
          rw [run_succ_of_terminal ht'] at h
          contradiction
      | succ k' =>
          rw [run_succ] at h h'
          cases hs : step w p s with
          | none => simp [hs] at h
          | some u =>
              obtain ⟨hk, heq⟩ := ih (by simpa [hs] using h) (by simpa [hs] using h')
              exact ⟨congrArg Nat.succ hk, heq⟩

/-- A terminating program has a unique complete output and exact charged time. -/
theorem runsTo_unique {w t t' : ℕ} {p : Program} {x y y' : List ℕ}
    (h : RunsTo w p x y t) (h' : RunsTo w p x y' t') : y = y' ∧ t = t' := by
  obtain ⟨k, s, hr, hs, hy, ht⟩ := h
  obtain ⟨k', s', hr', hs', hy', ht'⟩ := h'
  obtain ⟨rfl, rfl⟩ := terminal_run_unique hr hs hr' hs'
  exact ⟨hy.symm.trans hy', ht.trans ht'.symm⟩

/-! ### Bitwise identities

The three operations of the reference language that are not
instructions — disjunction, exclusive or, and the right shift — are
compiled to the blocks the concept's notes tabulate, and these are the
three facts that make those blocks compute what they claim to. None of
them is in mathlib in this form. Each is falsifiable on small numbers,
so each is `#guard`ed on small numbers before it is proved. -/

#guard (List.range 40).all fun a => (List.range 40).all fun b =>
  (a ||| b) = a + (b - (a &&& b))

#guard (List.range 40).all fun a => (List.range 40).all fun b =>
  (a ^^^ b) = (a + (b - (a &&& b))) - (a &&& b)

#guard (List.range 12).all fun w => (List.range 24).all fun n =>
  (List.range 40).all fun a => decide (2 ^ w ≤ a) || (a / (2 ^ n % 2 ^ w) = a / 2 ^ n)

/-- Addition splits into the disjunction and the conjunction: a bit
present in both operands is carried by exactly one of them. -/
theorem add_eq_lor_add_land (a b : ℕ) : a + b = (a ||| b) + (a &&& b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · have ihh := ih (a / 2) (Nat.div_lt_self ha (by norm_num)) (b / 2)
        have hor : 2 * (a / 2 ||| b / 2) + (a ||| b) % 2 = a ||| b := by
          rw [← Nat.or_div_two]; exact Nat.div_add_mod _ 2
        have hand : 2 * (a / 2 &&& b / 2) + (a &&& b) % 2 = a &&& b := by
          rw [← Nat.and_div_two]; exact Nat.div_add_mod _ 2
        have ha2 := Nat.div_add_mod a 2
        have hb2 := Nat.div_add_mod b 2
        have h1 : ((a ||| b) % 2 = 1) ↔ (a % 2 = 1 ∨ b % 2 = 1) := Nat.or_mod_two_eq_one
        have h2 : ((a &&& b) % 2 = 1) ↔ (a % 2 = 1 ∧ b % 2 = 1) := Nat.and_mod_two_eq_one
        have h3 := Nat.mod_two_eq_zero_or_one (a ||| b)
        have h4 := Nat.mod_two_eq_zero_or_one (a &&& b)
        have h5 := Nat.mod_two_eq_zero_or_one a
        have h6 := Nat.mod_two_eq_zero_or_one b
        omega

/-! The compiler works with `Nat.land`, `Nat.lor` and `Nat.xor`, which
is what the concept's `Instr.effect` and the reference language's
`Bop.apply` are written with, so the identities are stated in that form;
the bit-level proofs above are in the notation `Nat.testBit`'s simp set
speaks. -/

theorem land_le_left (a b : ℕ) : Nat.land a b ≤ a := Nat.and_le_left

theorem land_le_right (a b : ℕ) : Nat.land a b ≤ b := Nat.and_le_right

theorem lor_lt_two_pow {a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    Nat.lor a b < 2 ^ n := Nat.or_lt_two_pow ha hb

/-- **Disjunction from `and`, `sub` and `add`.** This is the three
instruction block `and t b c; sub t c t; add a b t` of the concept's
notes, read as an equation. -/
theorem lor_eq_add_sub_land (a b : ℕ) : Nat.lor a b = a + (b - Nat.land a b) := by
  have hland : (a &&& b) = Nat.land a b := rfl
  have hlor : (a ||| b) = Nat.lor a b := rfl
  have h := add_eq_lor_add_land a b
  have hb : a &&& b ≤ b := Nat.and_le_right
  rw [hland, hlor] at h
  rw [hland] at hb
  omega

/-- Exclusive or is the disjunction minus the conjunction. -/
theorem xor_add_land (a b : ℕ) : (a ^^^ b) + (a &&& b) = a ||| b := by
  have hdisj : (a ^^^ b) &&& (a &&& b) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp
  have hor : ((a ^^^ b) ||| (a &&& b)) = a ||| b := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
    cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp
  rw [add_eq_lor_add_land, hdisj, hor, Nat.add_zero]

/-- **Exclusive or from `and`, `sub` and `add`.** This is the four
instruction block `and t b c; sub u c t; add u b u; sub a u t` of the
concept's notes, read as an equation. -/
theorem xor_eq_sub_add_sub_land (a b : ℕ) :
    Nat.xor a b = (a + (b - Nat.land a b)) - Nat.land a b := by
  have hland : (a &&& b) = Nat.land a b := rfl
  have hlor : (a ||| b) = Nat.lor a b := rfl
  have hxor : (a ^^^ b) = Nat.xor a b := rfl
  have h := xor_add_land a b
  rw [hland, hlor, hxor] at h
  have h' := lor_eq_add_sub_land a b
  omega

/-- **The right shift from `set`, `shiftl` and `div`.** A shift
distance of `w` or more truncates the shifted power of two to zero, and
division by zero is zero — which is what the shift of a word by that
distance is anyway, so the block `set t 1; shiftl t t c; div a b t`
computes the right shift at every distance, not only the ones below the
word length. -/
theorem div_two_pow_mod_two_pow {a w : ℕ} (n : ℕ) (ha : a < 2 ^ w) :
    a / (2 ^ n % 2 ^ w) = a / 2 ^ n := by
  rcases lt_or_ge n w with hn | hn
  · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hn)]
  · obtain ⟨k, hk⟩ := pow_dvd_pow 2 hn
    have hle : 2 ^ w ≤ 2 ^ w * k := by
      rw [← hk]; exact Nat.pow_le_pow_right (by norm_num) hn
    rw [hk, Nat.mul_mod_right, Nat.div_zero, Nat.div_eq_of_lt (lt_of_lt_of_le ha hle)]

/-! ### Placement -/

/-- The program `p` contains the block `q` at address `a`. -/
def Fits (p : Program) (a : ℕ) (q : Program) : Prop :=
  ∀ i, i < q.length → p[a + i]? = q[i]?

theorem Fits.head {p : Program} {a : ℕ} {ins : Instr} {q : Program}
    (h : Fits p a (ins :: q)) : p[a]? = some ins := by
  simpa using h 0 (by simp)

theorem fits_append {p : Program} {a : ℕ} {q r : Program} :
    Fits p a (q ++ r) ↔ Fits p a q ∧ Fits p (a + q.length) r := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega)
      rwa [List.getElem?_append_left hi] at this
    · have := h (q.length + i) (by simp; omega)
      rw [List.getElem?_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    rcases lt_or_ge i q.length with hlt | hge
    · rw [List.getElem?_append_left hlt]; exact h₁ i hlt
    · rw [List.getElem?_append_right hge]
      have := h₂ (i - q.length) (by simp at hi; omega)
      rwa [Nat.add_assoc, Nat.add_sub_cancel' hge] at this

theorem Fits.congr {p : Program} {a a' : ℕ} {q : Program} (h : Fits p a q) (ha : a = a') :
    Fits p a' q := ha ▸ h

theorem fits_singleton {p : Program} {a : ℕ} {ins : Instr} :
    Fits p a [ins] ↔ p[a]? = some ins := by
  constructor
  · exact fun h => h.head
  · intro h i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simpa using h

theorem fits_self (q r : Program) : Fits (q ++ r) 0 q := by
  intro i hi
  simpa using List.getElem?_append_left (l₂ := r) hi

end Lax67Proofs.Machine
