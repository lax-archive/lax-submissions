import Lax185574Proofs.Words.Guarded

/-!
A bounded copy program.

`catProg E` copies its input to its output, one entry at a time, until
the input tape is empty, and then halts. Before every entry it checks
that fewer than `catLim w E = (2^w - 1) / 2^E` entries have been
copied, and otherwise loops forever. So it halts exactly on the inputs
of length at most `catLim w E`, and then outputs the input with every entry reduced
modulo `2^w`. A composite ends a stage with this program to bound the
length of the words it passes on, without having to know their format.
-/

namespace Lax185574Proofs.RamCat

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.Words

/-- The bounded copy program. Cells: `0` the count, `1` the limit, `2`
the entry, `3` the constant one, `4` the constant `2^E`, `5` scratch. -/
def catProg (E : ℕ) : Program :=
  [.not 1 1, .set 4 (2 ^ E), .div 1 1 4, .set 3 1,
    .jeof 11, .sub 5 1 0, .jzero 5 12, .read 2, .write 2, .add 0 0 3, .jump 4,
    .halt, .jump 12]

/-- The largest input length copied. -/
def catLim (w E : ℕ) : ℕ := (2 ^ w - 1) / 2 ^ E

/-- The state at the head of the loop after `j` entries. -/
structure CatInv (w E : ℕ) (x : List ℕ) (j : ℕ) (s : State) : Prop where
  pc : s.pc = 4
  cnt : s.mem 0 = j
  lim : s.mem 1 = catLim w E
  one : s.mem 3 = 1
  input : s.input = x
  inp : s.inp = x.drop j
  out : s.out = (x.take j).map (· % 2 ^ w)

variable {w E : ℕ}

theorem two_pow_ge (hw : 4 ≤ w) : 16 ≤ 2 ^ w :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)

theorem catLim_lt (w E : ℕ) : catLim w E < 2 ^ w := by
  have := two_pow_pos w
  have : (2 ^ w - 1) / 2 ^ E ≤ 2 ^ w - 1 := Nat.div_le_self _ _
  simp only [catLim]; omega

/-- The memory after the four instructions of the prelude. -/
def catMem (w E : ℕ) : ℕ → ℕ :=
  let m₂ := setCell w (setCell w (fun _ => 0) 1 (2 ^ w - 1 - 0)) 4 (2 ^ E)
  setCell w (setCell w m₂ 1 (m₂ 1 / m₂ 4)) 3 1

theorem cat_init (hw : 4 ≤ w) (hE : E < w) (x : List ℕ) :
    ∃ s, run w (catProg E) 4 (initState x) = some s ∧ CatInv w E x 0 s := by
  have h16 := two_pow_ge hw
  have hEw : 2 ^ E < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) hE
  refine ⟨{ (initState x) with pc := 4, mem := catMem w E }, ?_, ?_⟩
  · rw [show (4 : ℕ) = 1 + (1 + (1 + 1)) from rfl, run_add,
      run_one (ins := .not 1 1) (by simp [catProg, initState]), effect_not (by omega)]
    simp only [Option.bind_some]
    rw [run_add, run_one (ins := .set 4 (2 ^ E)) (by simp [catProg, initState]), effect_set]
    simp only [Option.bind_some]
    rw [run_add, run_one (ins := .div 1 1 4) (by simp [catProg, initState]),
      effect_div (by omega) (by omega)]
    simp only [Option.bind_some]
    rw [run_one (ins := .set 3 1) (by simp [catProg, initState]), effect_set]
    rfl
  · have e1 : setCell w (setCell w (fun _ => 0) 1 (2 ^ w - 1 - 0)) 4 (2 ^ E) 1 = 2 ^ w - 1 := by
      rw [setCell_of_ne _ _ (by omega) (by omega), setCell_self _ (by omega) (by omega)]; rfl
    have e4 : setCell w (setCell w (fun _ => 0) 1 (2 ^ w - 1 - 0)) 4 (2 ^ E) 4 = 2 ^ E :=
      setCell_self _ (by omega) hEw
    refine ⟨rfl, ?_, ?_, ?_, rfl, by simp [initState], by simp [initState]⟩
    · simp only [catMem]
      rw [setCell_of_ne _ _ (by omega) (by omega), setCell_of_ne _ _ (by omega) (by omega),
        setCell_of_ne _ _ (by omega) (by omega), setCell_of_ne _ _ (by omega) (by omega)]
    · simp only [catMem]
      rw [setCell_of_ne _ _ (by omega) (by omega), e1, e4,
        setCell_self _ (by omega) (by have := catLim_lt w E; simpa [catLim] using this)]
      rfl
    · simp only [catMem]
      rw [setCell_self _ (by omega) (by omega)]

theorem cat_body (hw : 4 ≤ w) {x : List ℕ} {j : ℕ} {s : State} (I : CatInv w E x j s)
    (hj : j < catLim w E) {v : ℕ} {rest : List ℕ} (hv : x.drop j = v :: rest) :
    ∃ s', run w (catProg E) 7 s = some s' ∧ CatInv w E x (j + 1) s' := by
  have h16 := two_pow_ge hw
  have hM := catLim_lt w E
  obtain ⟨pc, mem, input, inp, out⟩ := s
  obtain ⟨hpc, hc, hl, h1, hin, hinp, hout⟩ := I
  simp only at hpc hc hl h1 hin hinp hout
  subst hpc hinp hout
  have e5 : setCell w mem 5 (mem 1 - mem 0) 5 = catLim w E - j := by
    rw [setCell_self _ (by omega) (by omega), hl, hc]
  have e5' : setCell w mem 5 (mem 1 - mem 0) 5 ≠ 0 := by rw [e5]; omega
  generalize hm₁ : setCell w mem 5 (mem 1 - mem 0) = m₁ at e5'
  generalize hm₂ : setCell w m₁ 2 v = m₂
  refine ⟨⟨4, setCell w m₂ 0 (m₂ 0 + m₂ 3), input, rest,
    (x.take j).map (· % 2 ^ w) ++ [v % 2 ^ w]⟩, ?_, ?_⟩
  · have hv' := hv
    rw [← hin] at hv'
    rw [show (7 : ℕ) = 1 + (1 + (1 + (1 + (1 + (1 + 1))))) from rfl, run_add,
      run_one (ins := .jeof 11) (by simp [catProg]), effect_jeof]
    simp only [hv, List.isEmpty_cons, Bool.false_eq_true, if_false, Option.bind_some]
    rw [run_add, run_one (ins := .sub 5 1 0) (by simp [catProg]), effect_sub (by omega) (by omega)]
    simp only [Option.bind_some, hm₁]
    rw [run_add, run_one (ins := .jzero 5 12) (by simp [catProg]), effect_jzero (by omega)]
    simp only [e5', if_false, Option.bind_some]
    rw [run_add, run_one (ins := .read 2) (by simp [catProg]), effect_read 2 rfl]
    simp only [Option.bind_some]
    rw [run_add, run_one (ins := .write 2) (by simp [catProg]), effect_write_eq]
    simp only [Option.bind_some]
    rw [run_add, run_one (ins := .add 0 0 3) (by simp [catProg]), effect_add (by omega) (by omega)]
    simp only [Option.bind_some]
    rw [run_one (ins := .jump 4) (by simp [catProg]), effect_jump]
    simp only [hm₂]
    congr 3
    rw [← hm₂, setCell_eq, Nat.mod_eq_of_lt (a := 2) (by omega), if_pos rfl, Nat.mod_mod]
  · have e0 : m₂ 0 = j := by
      rw [← hm₂, ← hm₁, setCell_of_ne _ _ (by omega) (by omega),
        setCell_of_ne _ _ (by omega) (by omega), hc]
    have e3 : m₂ 3 = 1 := by
      rw [← hm₂, ← hm₁, setCell_of_ne _ _ (by omega) (by omega),
        setCell_of_ne _ _ (by omega) (by omega), h1]
    refine ⟨rfl, ?_, ?_, ?_, hin, ?_, ?_⟩
    · show setCell w m₂ 0 (m₂ 0 + m₂ 3) 0 = j + 1
      rw [e0, e3, setCell_self _ (by omega) (by omega)]
    · show setCell w m₂ 0 (m₂ 0 + m₂ 3) 1 = catLim w E
      rw [setCell_of_ne _ _ (by omega) (by omega), ← hm₂, ← hm₁,
        setCell_of_ne _ _ (by omega) (by omega), setCell_of_ne _ _ (by omega) (by omega), hl]
    · show setCell w m₂ 0 (m₂ 0 + m₂ 3) 3 = 1
      rw [setCell_of_ne _ _ (by omega) (by omega), e3]
    · show rest = x.drop (j + 1)
      rw [← List.drop_drop, hv]; rfl
    · show (x.take j).map (· % 2 ^ w) ++ [v % 2 ^ w] = (x.take (j + 1)).map (· % 2 ^ w)
      have hj' : j < x.length := by
        by_contra h; rw [List.drop_eq_nil_of_le (by omega)] at hv; cases hv
      rw [List.take_add_one, List.map_append]
      congr
      rw [List.getElem?_eq_getElem hj']
      have : x[j] = v := by
        have := congrArg List.head? hv
        rw [List.head?_drop, List.getElem?_eq_getElem hj'] at this
        simpa using this
      simp [this]

theorem cat_loop (hw : 4 ≤ w) (hE : E < w) (x : List ℕ) :
    ∀ j, j ≤ x.length → j ≤ catLim w E →
      ∃ s, run w (catProg E) (4 + 7 * j) (initState x) = some s ∧ CatInv w E x j s
  | 0, _, _ => by simpa using cat_init hw hE x
  | j + 1, h₁, h₂ => by
      obtain ⟨s, hs, I⟩ := cat_loop hw hE x j (by omega) (by omega)
      obtain ⟨v, rest, hv⟩ : ∃ v rest, x.drop j = v :: rest := by
        cases h : x.drop j with
        | nil => rw [List.drop_eq_nil_iff] at h; omega
        | cons v rest => exact ⟨v, rest, rfl⟩
      obtain ⟨s', hs', I'⟩ := cat_body hw I (by omega) hv
      exact ⟨s', by rw [show 4 + 7 * (j + 1) = 4 + 7 * j + 7 by ring]; exact run_trans hs hs', I'⟩

/-- **Bounded copy, forward.** -/
theorem cat_fwd (hw : 4 ≤ w) (hE : E < w) {x : List ℕ} (hx : x.length ≤ catLim w E) :
    RunsTo w (catProg E) x (x.map (· % 2 ^ w)) (4 + 7 * x.length + 2) := by
  obtain ⟨s, hs, I⟩ := cat_loop hw hE x x.length le_rfl hx
  have hinp : s.inp = [] := by rw [I.inp]; simp
  set s' : State := { s with pc := 11 }
  have h1 : run w (catProg E) 1 s = some s' := by
    rw [run_one (ins := .jeof 11) (by simp [catProg, I.pc]), effect_jeof, hinp]
    simp [s', hinp]
  refine ⟨4 + 7 * x.length + 1, s', run_trans hs h1, ?_, ?_, ?_⟩
  · rw [step_eq]; simp [s', catProg]; rfl
  · show s.out = _; rw [I.out, List.take_length]
  · rw [terminalCost_of_getElem? (i := .halt) (by simp [s', catProg])]

/-- **Bounded copy, backward.** Every halting run copies an input of
length at most `catLim w E`. -/
theorem cat_back (hw : 4 ≤ w) (hE : E < w) {x y : List ℕ} {t : ℕ} (h : RunsTo w (catProg E) x y t) :
    x.length ≤ catLim w E ∧ y = x.map (· % 2 ^ w) := by
  have h16 := two_pow_ge hw
  by_cases hx : x.length ≤ catLim w E
  · exact ⟨hx, (runsTo_unique h (cat_fwd hw hE hx)).1⟩
  · exfalso
    obtain ⟨s, hs, I⟩ := cat_loop hw hE x (catLim w E) (by omega) le_rfl
    obtain ⟨v, rest, hv⟩ : ∃ v rest, x.drop (catLim w E) = v :: rest := by
      cases h : x.drop (catLim w E) with
      | nil => rw [List.drop_eq_nil_iff] at h; omega
      | cons v rest => exact ⟨v, rest, rfl⟩
    obtain ⟨pc, mem, input, inp, out⟩ := s
    obtain ⟨hpc, hc, hl, -, -, hinp, -⟩ := I
    simp only at hpc hc hl hinp
    subst hpc hinp
    have hM := catLim_lt w E
    have h3 : run w (catProg E) 3 ⟨4, mem, input, x.drop (catLim w E), out⟩ =
        some ⟨12, setCell w mem 5 (mem 1 - mem 0), input, x.drop (catLim w E), out⟩ := by
      rw [show (3 : ℕ) = 1 + (1 + 1) from rfl, run_add,
        run_one (ins := .jeof 11) (by simp [catProg]), effect_jeof]
      simp only [hv, List.isEmpty_cons, Bool.false_eq_true, if_false, Option.bind_some]
      rw [run_add, run_one (ins := .sub 5 1 0) (by simp [catProg]),
        effect_sub (by omega) (by omega)]
      simp only [Option.bind_some]
      rw [run_one (ins := .jzero 5 12) (by simp [catProg]), effect_jzero (by omega)]
      simp only [hl, hc, Nat.sub_self]
      rw [setCell_self _ (by omega) (by omega), if_pos rfl]
    exact not_runsTo_of_loop (run_trans hs h3) (by simp [catProg]) h

end Lax185574Proofs.RamCat
