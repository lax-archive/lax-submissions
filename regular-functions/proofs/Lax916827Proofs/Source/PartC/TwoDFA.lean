/-
Deterministic two-way automata and the fact that they recognise only regular
languages (Shepherdson's Theorem).  This is the combinatorial core of the proof
that two-way transducers compute continuous functions (Theorem `thm:continuity-2dfas` of
*Transducers*, M. Bojańczyk): running a deterministic automaton on the output
of a two-way transducer turns the transducer into a two-way automaton.

The proof is by the Myhill-Nerode theorem.  With a prefix `x` of the input one
associates its *profile*: the last letter of `x`, together with the outcome of
the run of the automaton inside `x` -- started either at the left end of `x` in
the initial state, or at the right end of `x` in an arbitrary state.  Such a run
either halts inside `x`, or leaves `x` to the right in some state, or never
leaves `x`.  The profile takes finitely many values, and two prefixes with the
same profile have the same left quotient, because the run on `x ++ y` can be
decomposed into phases that alternate between `x` and `y`.
-/
import Lax916827Proofs.Source.PartC.ContAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Deterministic two-way automata -/

/-- A deterministic two-way automaton: based on the letters adjacent to the
head and the current state, it either halts and answers (`Sum.inl`), or changes
state and moves the head left (`false`) or right (`true`). -/
structure TwoDFA (A R : Type) where
  /-- The initial state. -/
  init : R
  /-- The transition function. -/
  step : Option A → R → Option A → Bool ⊕ (R × Bool)

/-- A configuration of a two-way automaton over a fixed input: either the
position of the head together with the state, or the answer of a run that has
already terminated. -/
abbrev TwoCfg (R : Type) := (ℕ × R) ⊕ Bool

namespace TwoDFA

variable {A R : Type}

/-- One step of the computation on the input `w`.  A head that would leave the
input string terminates the run with the answer `false`. -/
def next (N : TwoDFA A R) (w : List A) : TwoCfg R → TwoCfg R
  | Sum.inr b => Sum.inr b
  | Sum.inl (p, r) =>
      match N.step (if p = 0 then none else w[p - 1]?) r w[p]? with
      | Sum.inl b => Sum.inr b
      | Sum.inr (r', true) => if p < w.length then Sum.inl (p + 1, r') else Sum.inr false
      | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false

@[simp] lemma next_inr (N : TwoDFA A R) (w : List A) (b : Bool) :
    N.next w (Sum.inr b) = Sum.inr b := rfl

@[simp] lemma iterate_next_inr (N : TwoDFA A R) (w : List A) (b : Bool) (n : ℕ) :
    (N.next w)^[n] (Sum.inr b) = Sum.inr b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, next_inr, ih]

/-- The automaton accepts the input if the run started at the left end in the
initial state terminates with the answer `true`. -/
def Accepts (N : TwoDFA A R) (w : List A) : Prop :=
  ∃ n, (N.next w)^[n] (Sum.inl (0, N.init)) = Sum.inr true

/-- The answer of a terminated run does not depend on when it is read off. -/
lemma answer_unique {N : TwoDFA A R} {w : List A} {c : TwoCfg R} {m n : ℕ} {b b' : Bool}
    (hm : (N.next w)^[m] c = Sum.inr b) (hn : (N.next w)^[n] c = Sum.inr b') : b = b' := by
  rcases le_total m n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show m + d = d + m by omega, Function.iterate_add_apply, hm, iterate_next_inr] at hn
    exact Sum.inr_injective hn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show n + d = d + n by omega, Function.iterate_add_apply, hn, iterate_next_inr] at hm
    exact (Sum.inr_injective hm).symm

/-! ## Iterating two functions in lockstep -/

/-- If `φ` intertwines `F` and `G` on all configurations satisfying `P`, then it
intertwines their iterates, as long as the `F`-run satisfies `P`. -/
lemma iterate_simul {X Y : Type} (F : X → X) (G : Y → Y) (φ : X → Y) (P : X → Prop) (c : X)
    (h : ∀ z, P z → φ (F z) = G (φ z)) :
    ∀ k, (∀ j < k, P (F^[j] c)) → φ (F^[k] c) = G^[k] (φ c) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have h1 := ih (fun j hj => hk j (by omega))
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h (F^[k] c) (hk k (by omega)),
        h1]

/-! ## The run inside a prefix -/

/-- The run has not left the prefix `x` yet. -/
def insideL (x : List A) : TwoCfg R → Prop
  | Sum.inr _ => False
  | Sum.inl (p, _) => p < x.length

variable (N : TwoDFA A R)

/-- Inside the prefix `x`, the run does not depend on what follows. -/
lemma next_append_of_insideL (x y : List A) (c : TwoCfg R) (hc : insideL x c) :
    N.next (x ++ y) c = N.next x c := by
  rcases c with ⟨p, r⟩ | b
  · have hp : p < x.length := hc
    have hlen : (x ++ y).length = x.length + y.length := by simp
    have h1 : (x ++ y)[p]? = x[p]? := List.getElem?_append_left hp
    have h2 : (x ++ y)[p - 1]? = x[p - 1]? := List.getElem?_append_left (by omega)
    have h3 : (p < (x ++ y).length) = (p < x.length) := by
      simp only [List.length_append, eq_iff_iff]
      constructor
      · intro _; exact hp
      · intro _; omega
    simp only [next, h1, h2]
    cases N.step (if p = 0 then none else x[p - 1]?) r x[p]? with
    | inl b => rfl
    | inr rd =>
        rcases rd with ⟨r', dir⟩
        cases dir with
        | true => simp only [if_pos hp, if_pos (show p < (x ++ y).length by omega)]
        | false => rfl
  · exact absurd hc not_false

open scoped Classical

/-- The outcome recorded by a configuration in which the run inside a prefix
stops: the answer if it has halted, the state if it has left the prefix. -/
def outOf : TwoCfg R → Bool ⊕ R
  | Sum.inr b => Sum.inl b
  | Sum.inl (_, r) => Sum.inr r

/-- The outcome of the run inside the prefix `x`, started in the configuration
`c`: it either halts with an answer (`Sum.inl`), or leaves `x` to the right in
some state (`Sum.inr`), or never leaves `x` (`none`). -/
noncomputable def leftOutcome (x : List A) (c : TwoCfg R) : Option (Bool ⊕ R) :=
  if h : ∃ k, ¬ insideL x ((N.next x)^[k] c) then
    some (outOf ((N.next x)^[Nat.find h] c))
  else none

/-- The profile of a prefix: its last letter, the outcomes of the runs entering
it from the right, and the outcome of the initial run. -/
noncomputable def prof (x : List A) : Option A × (R → Option (Bool ⊕ R)) × Option (Bool ⊕ R) :=
  (x.getLast?, fun r => N.leftOutcome x (Sum.inl (x.length - 1, r)),
    N.leftOutcome x (Sum.inl (0, N.init)))

/-- Splitting a run at an intermediate configuration. -/
lemma split_run {w : List A} {S Z : TwoCfg R} {n k : ℕ}
    (hacc : (N.next w)^[n] S = Sum.inr true) (hk : (N.next w)^[k] S = Z)
    (hZ : ∀ b, Z ≠ Sum.inr b) : k ≤ n ∧ (N.next w)^[n - k] Z = Sum.inr true := by
  have hkn : k ≤ n := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hcon.le
    apply hZ true
    rw [← hk, hd, show n + d = d + n by omega, Function.iterate_add_apply, hacc,
      iterate_next_inr]
  refine ⟨hkn, ?_⟩
  have : (N.next w)^[n - k + k] S = (N.next w)^[n - k] ((N.next w)^[k] S) :=
    Function.iterate_add_apply _ _ _ _
  rw [show n - k + k = n by omega, hacc, hk] at this
  exact this.symm

/-- Inside a prefix the run does not depend on what follows (iterated form). -/
lemma left_iterate_agree (x y : List A) (c : TwoCfg R) (k : ℕ)
    (hk : ∀ j < k, insideL x ((N.next x)^[j] c)) :
    (N.next (x ++ y))^[k] c = (N.next x)^[k] c := by
  have h := iterate_simul (N.next x) (N.next (x ++ y)) id (insideL x) c
    (fun z hz => by simpa using (N.next_append_of_insideL x y z hz).symm) k hk
  simpa using h.symm

/-- When the run leaves the prefix `x`, it is either halted or exactly at the
right end of `x`. -/
lemma exit_config (x : List A) (c : TwoCfg R) (hc : insideL x c)
    (h : ∃ k, ¬ insideL x ((N.next x)^[k] c)) :
    0 < Nat.find h ∧
      ((∃ b, (N.next x)^[Nat.find h] c = Sum.inr b) ∨
        (∃ r, (N.next x)^[Nat.find h] c = Sum.inl (x.length, r))) := by
  have hpos : 0 < Nat.find h := by
    rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
    · exact absurd (h0 ▸ Nat.find_spec h) (by simpa using hc)
    · exact h0
  refine ⟨hpos, ?_⟩
  have hprev : insideL x ((N.next x)^[Nat.find h - 1] c) :=
    not_not.mp (Nat.find_min h (by omega))
  have hstep : (N.next x)^[Nat.find h] c = N.next x ((N.next x)^[Nat.find h - 1] c) := by
    conv_lhs => rw [show Nat.find h = (Nat.find h - 1) + 1 by omega]
    rw [Function.iterate_succ_apply']
  have hnot := Nat.find_spec h
  rcases hz : (N.next x)^[Nat.find h - 1] c with ⟨p, r⟩ | b
  · have hp : p < x.length := by rw [hz] at hprev; exact hprev
    rw [hz] at hstep
    rw [hstep] at hnot ⊢
    rcases hstepval : N.step (if p = 0 then none else x[p - 1]?) r x[p]? with b | ⟨r', dir⟩
    · exact Or.inl ⟨b, by simp only [next, hstepval]⟩
    · cases dir with
      | true =>
          have hval : N.next x (Sum.inl (p, r)) = Sum.inl (p + 1, r') := by
            simp only [next, hstepval, if_pos hp]
          rw [hval] at hnot ⊢
          have : ¬ (p + 1 < x.length) := hnot
          exact Or.inr ⟨r', by rw [show p + 1 = x.length by omega]⟩
      | false =>
          by_cases hp0 : 0 < p
          · have hval : N.next x (Sum.inl (p, r)) = Sum.inl (p - 1, r') := by
              simp [next, hstepval, hp0]
            rw [hval] at hnot
            exact absurd (show p - 1 < x.length by omega) hnot
          · refine Or.inl ⟨false, ?_⟩
            simp only [next, hstepval, if_neg hp0]
  · rw [hz] at hprev
    exact absurd hprev not_false

lemma leftOutcome_none (x y : List A) (c : TwoCfg R)
    (hnone : N.leftOutcome x c = none) (k : ℕ) :
    insideL x ((N.next (x ++ y))^[k] c) := by
  have h : ¬ ∃ k, ¬ insideL x ((N.next x)^[k] c) := by
    intro hcon
    rw [leftOutcome, dif_pos hcon] at hnone
    simp at hnone
  push_neg at h
  have hall : ∀ j, insideL x ((N.next x)^[j] c) := h
  rw [left_iterate_agree N x y c k (fun j _ => hall j)]
  exact hall k

lemma leftOutcome_halt (x y : List A) (c : TwoCfg R) (hc : insideL x c) {b : Bool}
    (hb : N.leftOutcome x c = some (Sum.inl b)) :
    ∃ k, 0 < k ∧ (N.next (x ++ y))^[k] c = Sum.inr b := by
  have h : ∃ k, ¬ insideL x ((N.next x)^[k] c) := by
    by_contra hcon
    rw [leftOutcome, dif_neg hcon] at hb
    simp at hb
  rw [leftOutcome, dif_pos h] at hb
  have hoZ : outOf ((N.next x)^[Nat.find h] c) = Sum.inl b := Option.some_injective _ hb
  obtain ⟨hpos, hcase⟩ := exit_config N x c hc h
  have hagree : (N.next (x ++ y))^[Nat.find h] c = (N.next x)^[Nat.find h] c :=
    left_iterate_agree N x y c _ (fun j hj => not_not.mp (Nat.find_min h hj))
  rcases hcase with ⟨b', hb'⟩ | ⟨r, hr⟩
  · rw [hb'] at hoZ
    have : b' = b := by simpa [outOf] using hoZ
    exact ⟨Nat.find h, hpos, by rw [hagree, hb', this]⟩
  · rw [hr] at hoZ
    simp [outOf] at hoZ

lemma leftOutcome_exit (x y : List A) (c : TwoCfg R) (hc : insideL x c) {r : R}
    (hr : N.leftOutcome x c = some (Sum.inr r)) :
    ∃ k, 0 < k ∧ (N.next (x ++ y))^[k] c = Sum.inl (x.length, r) := by
  have h : ∃ k, ¬ insideL x ((N.next x)^[k] c) := by
    by_contra hcon
    rw [leftOutcome, dif_neg hcon] at hr
    simp at hr
  rw [leftOutcome, dif_pos h] at hr
  have hoZ : outOf ((N.next x)^[Nat.find h] c) = Sum.inr r := Option.some_injective _ hr
  obtain ⟨hpos, hcase⟩ := exit_config N x c hc h
  have hagree : (N.next (x ++ y))^[Nat.find h] c = (N.next x)^[Nat.find h] c :=
    left_iterate_agree N x y c _ (fun j hj => not_not.mp (Nat.find_min h hj))
  rcases hcase with ⟨b', hb'⟩ | ⟨r', hr'⟩
  · rw [hb'] at hoZ
    simp [outOf] at hoZ
  · rw [hr'] at hoZ
    have : r' = r := by simpa [outOf] using hoZ
    exact ⟨Nat.find h, hpos, by rw [hagree, hr', this]⟩

/-! ## The run to the right of a prefix -/

/-- Translating a configuration to the right of the prefix `x` into the
corresponding configuration to the right of the prefix `x'`. -/
def shiftCfg (m m' : ℕ) : TwoCfg R → TwoCfg R
  | Sum.inl (p, r) => Sum.inl (p - m + m', r)
  | Sum.inr b => Sum.inr b

/-- Strictly to the right of the prefix, the run only depends on the suffix. -/
lemma next_shift (x x' y : List A) (p : ℕ) (r : R) (hp : x.length < p) :
    shiftCfg x.length x'.length (N.next (x ++ y) (Sum.inl (p, r)))
      = N.next (x' ++ y) (shiftCfg x.length x'.length (Sum.inl (p, r))) := by
  set m := x.length with hm
  set m' := x'.length with hm'
  have hy1 : (x ++ y)[p]? = y[p - m]? := List.getElem?_append_right (by omega)
  have hy2 : (x ++ y)[p - 1]? = y[p - 1 - m]? := List.getElem?_append_right (by omega)
  have hy1' : (x' ++ y)[p - m + m']? = y[p - m]? := by
    rw [List.getElem?_append_right (by omega)]
    congr 1
    omega
  have hy2' : (x' ++ y)[p - m + m' - 1]? = y[p - 1 - m]? := by
    rw [List.getElem?_append_right (by omega)]
    congr 1
    omega
  have hne : ¬ (p = 0) := by omega
  have hne' : ¬ (p - m + m' = 0) := by omega
  have hlen : (x ++ y).length = m + y.length := by simp [hm]
  have hlen' : (x' ++ y).length = m' + y.length := by simp [hm']
  simp only [next, shiftCfg, hy1, hy2, hy1', hy2', if_neg hne, if_neg hne']
  rcases hstep : N.step y[p - 1 - m]? r y[p - m]? with b | ⟨r', dir⟩
  · rfl
  · cases dir with
    | true =>
        by_cases hb : p < (x ++ y).length
        · have hb' : p - m + m' < (x' ++ y).length := by omega
          simp only [if_pos hb, if_pos hb']
          congr 2
          omega
        · have hb' : ¬ (p - m + m' < (x' ++ y).length) := by omega
          simp only [if_neg hb, if_neg hb']
    | false =>
        have h0 : 0 < p := by omega
        have h0' : 0 < p - m + m' := by omega
        simp only [if_pos h0, if_pos h0']
        congr 2
        omega


/-- In one step the head moves by one position. -/
lemma next_pos (w : List A) (p : ℕ) (rr : R) {q : ℕ} {rr' : R}
    (h : N.next w (Sum.inl (p, rr)) = Sum.inl (q, rr')) : q = p + 1 ∨ (0 < p ∧ q = p - 1) := by
  rcases hstep : N.step (if p = 0 then none else w[p - 1]?) rr w[p]? with b | ⟨r'', dir⟩
  · rw [show N.next w (Sum.inl (p, rr)) = Sum.inr b from by simp only [next, hstep]] at h
    exact absurd h (by simp)
  · cases dir with
    | true =>
        by_cases hb : p < w.length
        · rw [show N.next w (Sum.inl (p, rr)) = Sum.inl (p + 1, r'') from by
            simp only [next, hstep, if_pos hb]] at h
          exact Or.inl (congrArg Prod.fst (Sum.inl_injective h)).symm
        · rw [show N.next w (Sum.inl (p, rr)) = Sum.inr false from by
            simp only [next, hstep, if_neg hb]] at h
          exact absurd h (by simp)
    | false =>
        by_cases h0 : 0 < p
        · rw [show N.next w (Sum.inl (p, rr)) = Sum.inl (p - 1, r'') from by
            simp only [next, hstep, if_pos h0]] at h
          refine Or.inr ⟨h0, ?_⟩
          have := Sum.inl_injective h
          exact (congrArg Prod.fst this).symm
        · rw [show N.next w (Sum.inl (p, rr)) = Sum.inr false from by
            simp only [next, hstep, if_neg h0]] at h
          exact absurd h (by simp)

/-! ## Prefixes with the same profile have the same left quotient -/

/-- The heart of the argument: if two nonempty prefixes have the same last
letter and the same left outcomes, then an accepting run started at the right
end of one of them is matched by an accepting run started at the right end of
the other. -/
lemma accept_transfer {N : TwoDFA A R} {x x' y : List A} (hlast : x.getLast? = x'.getLast?)
    (hleft : ∀ r, N.leftOutcome x (Sum.inl (x.length - 1, r))
      = N.leftOutcome x' (Sum.inl (x'.length - 1, r)))
    (hx : x ≠ []) (hx' : x' ≠ []) :
    ∀ (n : ℕ) (r : R),
      (N.next (x ++ y))^[n] (Sum.inl (x.length, r)) = Sum.inr true →
      ∃ n', (N.next (x' ++ y))^[n'] (Sum.inl (x'.length, r)) = Sum.inr true := by
  have hm : 0 < x.length := List.length_pos_iff.mpr hx
  have hm' : 0 < x'.length := List.length_pos_iff.mpr hx'
  have hm0 : ¬ (x.length = 0) := by omega
  have hm0' : ¬ (x'.length = 0) := by omega
  have hlab : (x ++ y)[x.length - 1]? = x.getLast? := by
    rw [List.getElem?_append_left (by omega), List.getLast?_eq_getElem?]
  have hlab' : (x' ++ y)[x'.length - 1]? = x'.getLast? := by
    rw [List.getElem?_append_left (by omega), List.getLast?_eq_getElem?]
  have hhead : (x ++ y)[x.length]? = y[0]? := by
    rw [List.getElem?_append_right (le_refl _)]
    simp
  have hhead' : (x' ++ y)[x'.length]? = y[0]? := by
    rw [List.getElem?_append_right (le_refl _)]
    simp
  have hlenw : (x ++ y).length = x.length + y.length := by simp
  have hlenw' : (x' ++ y).length = x'.length + y.length := by simp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro r hacc
  have hn1 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hacc
    · exact h
  have hsplit1 : (N.next (x ++ y))^[n] (Sum.inl (x.length, r))
      = (N.next (x ++ y))^[n - 1] (N.next (x ++ y) (Sum.inl (x.length, r))) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Function.iterate_succ_apply]
  rcases hstep : N.step x.getLast? r y[0]? with b | ⟨r', dir⟩
  · -- the machine halts at the interface
    have e : N.next (x ++ y) (Sum.inl (x.length, r)) = Sum.inr b := by
      simp only [next, if_neg hm0, hlab, hhead, hstep]
    have e' : N.next (x' ++ y) (Sum.inl (x'.length, r)) = Sum.inr b := by
      simp only [next, if_neg hm0', hlab', ← hlast, hhead', hstep]
    rw [hsplit1, e, iterate_next_inr] at hacc
    have hb : b = true := Sum.inr_injective hacc
    exact ⟨1, by rw [Function.iterate_one, e', hb]⟩
  · cases dir with
    | true =>
        -- the machine moves into the suffix
        by_cases hy : y = []
        · subst hy
          have e : N.next (x ++ []) (Sum.inl (x.length, r)) = Sum.inr false := by
            simp only [next, if_neg hm0, hlab, hhead, hstep]
            rw [if_neg (by simp)]
          rw [hsplit1, e, iterate_next_inr] at hacc
          exact absurd (Sum.inr_injective hacc) (by simp)
        · have hylen : 0 < y.length := List.length_pos_iff.mpr hy
          have e : N.next (x ++ y) (Sum.inl (x.length, r)) = Sum.inl (x.length + 1, r') := by
            simp only [next, if_neg hm0, hlab, hhead, hstep]
            rw [if_pos (by omega)]
          have e' : N.next (x' ++ y) (Sum.inl (x'.length, r)) = Sum.inl (x'.length + 1, r') := by
            simp only [next, if_neg hm0', hlab', ← hlast, hhead', hstep]
            rw [if_pos (by omega)]
          set S : TwoCfg R := Sum.inl (x.length + 1, r') with hS
          set S' : TwoCfg R := Sum.inl (x'.length + 1, r') with hS'
          have hacc1 : (N.next (x ++ y))^[n - 1] S = Sum.inr true := by
            rw [hsplit1, e] at hacc; exact hacc
          -- the run stays strictly to the right of `x` until it returns
          have hPex : ∃ k, ¬ (∃ p rr, (N.next (x ++ y))^[k] S = Sum.inl (p, rr) ∧ x.length < p) := by
            refine ⟨n - 1, ?_⟩
            rw [hacc1]
            rintro ⟨p, rr, hpr, -⟩
            exact absurd hpr (by simp)
          set k₀ := Nat.find hPex with hk₀
          have hk₀lt : ∀ j < k₀, ∃ p rr, (N.next (x ++ y))^[j] S = Sum.inl (p, rr) ∧ x.length < p :=
            fun j hj => not_not.mp (Nat.find_min hPex hj)
          have hk₀spec := Nat.find_spec hPex
          have hk₀pos : 0 < k₀ := by
            rcases Nat.eq_zero_or_pos k₀ with h0 | h0
            · exfalso
              apply hk₀spec
              rw [← hk₀, h0]
              exact ⟨x.length + 1, r', rfl, by omega⟩
            · exact h0
          -- lockstep on the right of the prefix
          have hstepshift : ∀ z : TwoCfg R,
              (∃ p rr, z = Sum.inl (p, rr) ∧ x.length < p) →
              shiftCfg x.length x'.length (N.next (x ++ y) z)
                = N.next (x' ++ y) (shiftCfg x.length x'.length z) := by
            rintro z ⟨p, rr, rfl, hp⟩
            exact next_shift N x x' y p rr hp
          have hlock := iterate_simul (N.next (x ++ y)) (N.next (x' ++ y))
            (shiftCfg x.length x'.length)
            (fun z => ∃ p rr, z = Sum.inl (p, rr) ∧ x.length < p) S hstepshift k₀ hk₀lt
          have hSshift : shiftCfg x.length x'.length S = S' := by
            simp only [hS, hS', shiftCfg]
            congr 2
            omega
          rw [hSshift] at hlock
          -- the configuration in which the run comes back
          have hZ : (∃ b, (N.next (x ++ y))^[k₀] S = Sum.inr b) ∨
              (∃ rr, (N.next (x ++ y))^[k₀] S = Sum.inl (x.length, rr)) := by
            obtain ⟨p, rr, hp, hplt⟩ := hk₀lt (k₀ - 1) (by omega)
            have hstepk : (N.next (x ++ y))^[k₀] S
                = N.next (x ++ y) ((N.next (x ++ y))^[k₀ - 1] S) := by
              conv_lhs => rw [show k₀ = (k₀ - 1) + 1 by omega]
              rw [Function.iterate_succ_apply']
            rw [hp] at hstepk
            rcases hcfg : N.next (x ++ y) (Sum.inl (p, rr)) with ⟨q, rr'⟩ | b
            · refine Or.inr ⟨rr', ?_⟩
              rw [hstepk, hcfg]
              have hq := next_pos N (x ++ y) p rr hcfg
              have hqle : ¬ (x.length < q) := by
                intro hlt
                exact hk₀spec ⟨q, rr', by rw [hstepk, hcfg], hlt⟩
              have : q = x.length := by omega
              rw [this]
            · exact Or.inl ⟨b, by rw [hstepk, hcfg]⟩
          rcases hZ with ⟨b, hb⟩ | ⟨rr, hrr⟩
          · have hbtrue : b = true := answer_unique hb hacc1
            refine ⟨k₀ + 1, ?_⟩
            rw [Function.iterate_add_apply, Function.iterate_one, e', ← hlock, hb, hbtrue]
            rfl
          · obtain ⟨hk₀le, hrest⟩ := split_run N hacc1 hrr (by simp)
            obtain ⟨n'', hn''⟩ := IH (n - 1 - k₀) (by omega) rr hrest
            refine ⟨n'' + k₀ + 1, ?_⟩
            rw [Function.iterate_add_apply, Function.iterate_one, e',
              Function.iterate_add_apply, ← hlock, hrr]
            simpa only [shiftCfg, Nat.sub_self, Nat.zero_add] using hn''
    | false =>
        -- the machine moves into the prefix
        have e : N.next (x ++ y) (Sum.inl (x.length, r)) = Sum.inl (x.length - 1, r') := by
          simp only [next, if_neg hm0, hlab, hhead, hstep]
          rw [if_pos hm]
        have e' : N.next (x' ++ y) (Sum.inl (x'.length, r)) = Sum.inl (x'.length - 1, r') := by
          simp only [next, if_neg hm0', hlab', ← hlast, hhead', hstep]
          rw [if_pos hm']
        have hacc1 : (N.next (x ++ y))^[n - 1] (Sum.inl (x.length - 1, r')) = Sum.inr true := by
          rw [hsplit1, e] at hacc; exact hacc
        have hin : insideL x (Sum.inl (x.length - 1, r')) := by
          show x.length - 1 < x.length
          omega
        have hin' : insideL x' (Sum.inl (x'.length - 1, r')) := by
          show x'.length - 1 < x'.length
          omega
        rcases ho : N.leftOutcome x (Sum.inl (x.length - 1, r')) with _ | o
        · exfalso
          have := leftOutcome_none N x y _ ho (n - 1)
          rw [hacc1] at this
          exact this
        · have ho' : N.leftOutcome x' (Sum.inl (x'.length - 1, r')) = some o := by
            rw [← hleft r', ho]
          rcases o with b | rr
          · obtain ⟨k, -, hk⟩ := leftOutcome_halt N x y _ hin ho
            have hbtrue : b = true := answer_unique hk hacc1
            obtain ⟨k', -, hk'⟩ := leftOutcome_halt N x' y _ hin' ho'
            refine ⟨k' + 1, ?_⟩
            rw [Function.iterate_add_apply, Function.iterate_one, e', hk', hbtrue]
          · obtain ⟨k, hkpos, hk⟩ := leftOutcome_exit N x y _ hin ho
            obtain ⟨k', -, hk'⟩ := leftOutcome_exit N x' y _ hin' ho'
            obtain ⟨hkle, hrest⟩ := split_run N hacc1 hk (by simp)
            obtain ⟨n'', hn''⟩ := IH (n - 1 - k) (by omega) rr hrest
            refine ⟨n'' + k' + 1, ?_⟩
            rw [Function.iterate_add_apply, Function.iterate_one, e',
              Function.iterate_add_apply, hk']
            exact hn''


/-- Prefixes with the same profile have the same left quotient. -/
lemma accepts_transfer {N : TwoDFA A R} {x x' y : List A} (hprof : N.prof x = N.prof x')
    (h : N.Accepts (x ++ y)) : N.Accepts (x' ++ y) := by
  simp only [prof, Prod.mk.injEq] at hprof
  obtain ⟨hlast, hleftf, hinit⟩ := hprof
  have hleft : ∀ r, N.leftOutcome x (Sum.inl (x.length - 1, r))
      = N.leftOutcome x' (Sum.inl (x'.length - 1, r)) := fun r => congrFun hleftf r
  by_cases hx : x = []
  · have hx' : x' = [] := by
      rw [hx] at hlast
      simpa [List.getLast?_eq_none_iff] using hlast.symm
    rw [hx'] at *
    rw [hx] at h
    exact h
  · have hx' : x' ≠ [] := by
      intro h0
      rw [h0] at hlast
      simp [List.getLast?_eq_none_iff, hx] at hlast
    obtain ⟨n, hn⟩ := h
    have hm : 0 < x.length := List.length_pos_iff.mpr hx
    have hm' : 0 < x'.length := List.length_pos_iff.mpr hx'
    have hin : insideL x (Sum.inl (0, N.init)) := hm
    have hin' : insideL x' (Sum.inl (0, N.init)) := hm'
    rcases ho : N.leftOutcome x (Sum.inl (0, N.init)) with _ | o
    · exfalso
      have := leftOutcome_none N x y _ ho n
      rw [hn] at this
      exact this
    · have ho' : N.leftOutcome x' (Sum.inl (0, N.init)) = some o := by rw [← hinit, ho]
      rcases o with b | rr
      · obtain ⟨k, -, hk⟩ := leftOutcome_halt N x y _ hin ho
        have hbtrue : b = true := answer_unique hk hn
        obtain ⟨k', -, hk'⟩ := leftOutcome_halt N x' y _ hin' ho'
        exact ⟨k', by rw [hk', hbtrue]⟩
      · obtain ⟨k, hkpos, hk⟩ := leftOutcome_exit N x y _ hin ho
        obtain ⟨k', -, hk'⟩ := leftOutcome_exit N x' y _ hin' ho'
        obtain ⟨hkle, hrest⟩ := split_run N hn hk (by simp)
        obtain ⟨n'', hn''⟩ := accept_transfer hlast hleft hx hx' (n - k) rr hrest
        refine ⟨n'' + k', ?_⟩
        rw [Function.iterate_add_apply, hk']
        exact hn''

/-- **Shepherdson's Theorem.**  A deterministic two-way automaton recognises a
regular language. -/
theorem accepts_isRegular [Finite A] [Finite R] (N : TwoDFA A R) :
    Language.IsRegular {w : List A | N.Accepts w} := by
  classical
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  refine finite_range_of_factors _ N.prof (Set.toFinite _) ?_
  intro x x' hxx'
  ext y
  show N.Accepts (x ++ y) ↔ N.Accepts (x' ++ y)
  exact ⟨fun hy => accepts_transfer hxx' hy, fun hy => accepts_transfer hxx'.symm hy⟩

end TwoDFA

end Lax916827Proofs.Transducers


