/-
Pebble automata: the variant of pebble transducers that computes an answer instead of a string.

This is the model used in the book's proof of Theorem `thm:pebble-are-continuous`: the composition
of a pebble transducer with a deterministic automaton for the target language is a pebble
automaton, so the theorem reduces to the statement that pebble automata recognise regular
languages.

Two differences with `Transducers.Pebble`, both of them conveniences of the formalisation and
neither of them a change of the model:

* the machine is allowed to *stay* in place (this is what the `out` action of a pebble transducer
  does once the output letter has been fed to the automaton for the target language), and
* the answer is an element of an arbitrary finite type `O` rather than a Boolean.  The extra
  generality is what makes the induction of `RequestProject/PartD/PebbleReg.lean` go through: the
  sub-machine that describes what happens above the bottom pebble answers either "the whole
  machine halted with the answer `o`" or "the bottom pebble was popped in the state `r`".

The semantics is given by a *function* on configurations (a run that would leave the input string,
exceed the stack bound or pop from an empty stack dies), so a run is an iteration of that function
and the answer of a configuration is unique.
-/
import Lax194892Proofs.Source.PartD.PebbleDef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-! ## Resolving a sequence of stationary steps -/

section Resolve

variable {R X : Type}

/-- One step of the iteration of a map `g : R → X ⊕ R`, with the outcomes in `X` absorbing. -/
def stayStep (g : R → X ⊕ R) : X ⊕ R → X ⊕ R
  | Sum.inl x => Sum.inl x
  | Sum.inr r => g r

@[simp] lemma stayStep_inl (g : R → X ⊕ R) (x : X) : stayStep g (Sum.inl x) = Sum.inl x := rfl

lemma stayStep_iterate_inl (g : R → X ⊕ R) (x : X) (n : ℕ) :
    (stayStep g)^[n] (Sum.inl x) = Sum.inl x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, stayStep_inl, ih]

/-- The outcome of iterating `g` from `r` is unique. -/
lemma stayStep_unique {g : R → X ⊕ R} {r : R} {m n : ℕ} {x y : X}
    (hm : (stayStep g)^[m] (Sum.inr r) = Sum.inl x)
    (hn : (stayStep g)^[n] (Sum.inr r) = Sum.inl y) : x = y := by
  rcases le_total m n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show m + d = d + m by omega, Function.iterate_add_apply, hm,
      stayStep_iterate_inl] at hn
    exact Sum.inl_injective hn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show n + d = d + n by omega, Function.iterate_add_apply, hn,
      stayStep_iterate_inl] at hm
    exact (Sum.inl_injective hm).symm

open Classical in
/-- The eventual outcome of iterating `g` from `r`, if there is one. -/
noncomputable def resolve (g : R → X ⊕ R) (r : R) : Option X :=
  if h : ∃ n x, (stayStep g)^[n] (Sum.inr r) = Sum.inl x then some h.choose_spec.choose else none

lemma resolve_eq_some_iff {g : R → X ⊕ R} {r : R} {x : X} :
    resolve g r = some x ↔ ∃ n, (stayStep g)^[n] (Sum.inr r) = Sum.inl x := by
  classical
  unfold resolve
  split_ifs with h
  · have hx := h.choose_spec.choose_spec
    constructor
    · intro he
      exact ⟨h.choose, by rw [← Option.some_injective _ he]; exact hx⟩
    · rintro ⟨n, hn⟩
      rw [stayStep_unique hx hn]
  · simp only [false_iff]
    rintro ⟨n, hn⟩
    exact h ⟨n, x, hn⟩

lemma resolve_eq_none_iff {g : R → X ⊕ R} {r : R} :
    resolve g r = none ↔ ∀ n x, (stayStep g)^[n] (Sum.inr r) ≠ Sum.inl x := by
  classical
  constructor
  · intro h n x hn
    rw [Option.eq_none_iff_forall_ne_some] at h
    exact h x (resolve_eq_some_iff.2 ⟨n, hn⟩)
  · intro h
    rcases hr : resolve g r with _ | x
    · rfl
    · obtain ⟨n, hn⟩ := resolve_eq_some_iff.1 hr
      exact absurd hn (h n x)

end Resolve

/-! ## Pebble automata -/

/-- The actions of a pebble automaton: stay in place, move the head, push a new pebble on the
first input position, pop the topmost pebble, or halt with an answer. -/
inductive PebAutAction (O : Type) : Type
  /-- Stay in place, only changing the state. -/
  | stay : PebAutAction O
  /-- Move the head one position to the right (`true`) or left (`false`). -/
  | move : Bool → PebAutAction O
  /-- Push the first input position onto the pebble stack. -/
  | push : PebAutAction O
  /-- Pop the topmost pebble. -/
  | pop : PebAutAction O
  /-- Halt with an answer. -/
  | halt : O → PebAutAction O

/-- A `k`-pebble automaton over the input alphabet `A`, with states `R` and answers in `O`. -/
structure PebbleAut (A R O : Type) (k : ℕ) where
  /-- The transition function. -/
  step : R → PebbleView A → R × PebAutAction O

/-- A configuration of a pebble automaton: a state together with the stack of pebbles (listed
from the bottom), or a terminated run, which either has an answer (`some o`) or has died
(`none`). -/
abbrev PebAutCfg (R O : Type) := (R × List ℕ) ⊕ Option O

namespace PebbleAut

variable {A R O : Type} {k : ℕ}

/-- One step of the computation on the input `w`.  A run that would move the head out of the
input string, exceed the stack bound, or pop from an empty stack, dies. -/
def next (N : PebbleAut A R O k) (w : List A) : PebAutCfg R O → PebAutCfg R O
  | Sum.inr x => Sum.inr x
  | Sum.inl (r, st) =>
      let t := N.step r (viewOf w st)
      match t.2 with
      | PebAutAction.stay => Sum.inl (t.1, st)
      | PebAutAction.halt o => Sum.inr (some o)
      | PebAutAction.push =>
          if st.length < k then Sum.inl (t.1, st ++ [0]) else Sum.inr none
      | PebAutAction.pop =>
          if st = [] then Sum.inr none else Sum.inl (t.1, st.dropLast)
      | PebAutAction.move d =>
          match st.getLast? with
          | none => Sum.inr none
          | some p =>
              if d then
                (if p < w.length then Sum.inl (t.1, st.dropLast ++ [p + 1]) else Sum.inr none)
              else
                (if 0 < p then Sum.inl (t.1, st.dropLast ++ [p - 1]) else Sum.inr none)

@[simp] lemma next_inr (N : PebbleAut A R O k) (w : List A) (x : Option O) :
    N.next w (Sum.inr x) = Sum.inr x := rfl

@[simp] lemma iterate_next_inr (N : PebbleAut A R O k) (w : List A) (x : Option O) (n : ℕ) :
    (N.next w)^[n] (Sum.inr x) = Sum.inr x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, next_inr, ih]

/-- The run of `N` on `w` started in the configuration `c` answers `o`. -/
def Answers (N : PebbleAut A R O k) (w : List A) (c : PebAutCfg R O) (o : O) : Prop :=
  ∃ n, (N.next w)^[n] c = Sum.inr (some o)

/-- The answer of a run is unique. -/
lemma answers_unique {N : PebbleAut A R O k} {w : List A} {c : PebAutCfg R O} {o o' : O}
    (h : N.Answers w c o) (h' : N.Answers w c o') : o = o' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨n, hn⟩ := h'
  rcases le_total m n with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show m + d = d + m by omega, Function.iterate_add_apply, hm, iterate_next_inr] at hn
    exact Option.some_injective _ (Sum.inr_injective hn)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show n + d = d + n by omega, Function.iterate_add_apply, hn, iterate_next_inr] at hm
    exact (Option.some_injective _ (Sum.inr_injective hm)).symm

/-- A run that has died has no answer. -/
lemma not_answers_of_dead {N : PebbleAut A R O k} {w : List A} {c : PebAutCfg R O} {m : ℕ}
    (h : (N.next w)^[m] c = Sum.inr none) (o : O) : ¬ N.Answers w c o := by
  rintro ⟨n, hn⟩
  rcases le_total m n with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show m + d = d + m by omega, Function.iterate_add_apply, h, iterate_next_inr] at hn
    exact absurd hn (by simp)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show n + d = d + n by omega, Function.iterate_add_apply, hn, iterate_next_inr] at h
    exact absurd h (by simp)

/-- Reading the answer of a run off a configuration in which it has already terminated. -/
lemma exists_iterate_iff_of_halt {N : PebbleAut A R O k} {w : List A} {c : PebAutCfg R O}
    {z : Option O} {m : ℕ} (hm : (N.next w)^[m] c = Sum.inr z) (o₀ : O) :
    (∃ n, (N.next w)^[n] c = Sum.inr (some o₀)) ↔ z = some o₀ := by
  constructor
  · rintro ⟨n, hn⟩
    rcases le_total m n with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [show m + d = d + m by omega, Function.iterate_add_apply, hm, iterate_next_inr] at hn
      exact Sum.inr_injective hn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [show n + d = d + n by omega, Function.iterate_add_apply, hn, iterate_next_inr] at hm
      exact (Sum.inr_injective hm).symm
  · rintro rfl
    exact ⟨m, hm⟩

/-- One step from a configuration with an empty stack. -/
lemma next_nil (N : PebbleAut A R O k) (w : List A) (r : R) :
    N.next w (Sum.inl (r, [])) =
      (match (N.step r []).2 with
       | PebAutAction.stay => Sum.inl ((N.step r []).1, [])
       | PebAutAction.halt o => Sum.inr (some o)
       | PebAutAction.push => if 0 < k then Sum.inl ((N.step r []).1, [0]) else Sum.inr none
       | PebAutAction.pop => Sum.inr none
       | PebAutAction.move _ => Sum.inr none) := by
  simp only [next, show viewOf w ([] : List ℕ) = [] from rfl]
  cases (N.step r []).2 <;> simp

/-- One step from a configuration with a single pebble on the stack. -/
lemma next_single (N : PebbleAut A R O k) (w : List A) (q : ℕ) (r : R) :
    N.next w (Sum.inl (r, [q])) =
      (match (N.step r (viewOf w [q])).2 with
       | PebAutAction.stay => Sum.inl ((N.step r (viewOf w [q])).1, [q])
       | PebAutAction.halt o => Sum.inr (some o)
       | PebAutAction.push =>
           if 1 < k then Sum.inl ((N.step r (viewOf w [q])).1, [q, 0]) else Sum.inr none
       | PebAutAction.pop => Sum.inl ((N.step r (viewOf w [q])).1, [])
       | PebAutAction.move d =>
           if d then
             (if q < w.length then Sum.inl ((N.step r (viewOf w [q])).1, [q + 1])
              else Sum.inr none)
           else
             (if 0 < q then Sum.inl ((N.step r (viewOf w [q])).1, [q - 1])
              else Sum.inr none)) := by
  simp only [next]
  cases (N.step r (viewOf w [q])).2 with
  | stay => rfl
  | halt o => rfl
  | push => simp
  | pop => simp
  | move d => cases d <;> simp

lemma answers_of_next {N : PebbleAut A R O k} {w : List A} {c : PebAutCfg R O} {o : O}
    (h : N.Answers w (N.next w c) o) : N.Answers w c o := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply, hn]⟩

lemma answers_iff_next {N : PebbleAut A R O k} {w : List A} {r : R} {st : List ℕ} {o : O} :
    N.Answers w (Sum.inl (r, st)) o ↔ N.Answers w (N.next w (Sum.inl (r, st))) o := by
  refine ⟨?_, answers_of_next⟩
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp at hn
  | succ n => exact ⟨n, by rwa [Function.iterate_succ_apply] at hn⟩


lemma answers_iterate {N : PebbleAut A R O k} {w : List A} {c : PebAutCfg R O} {o : O} (m : ℕ) :
    N.Answers w ((N.next w)^[m] c) o ↔ N.Answers w c o := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + m, by rw [Function.iterate_add_apply]; exact hn⟩
  · rintro ⟨n, hn⟩
    rcases le_total n m with h | h
    · refine ⟨0, ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      simp only [Function.iterate_zero_apply]
      rw [show n + d = d + n by omega, Function.iterate_add_apply, hn, iterate_next_inr]
    · refine ⟨n - m, ?_⟩
      rw [← Function.iterate_add_apply, show n - m + m = n by omega]
      exact hn

/-- The pebbles of a run never leave the input string. -/
lemma next_stack_le {N : PebbleAut A R O k} {w : List A} {r r' : R} {st st' : List ℕ}
    (h : ∀ q ∈ st, q ≤ w.length)
    (he : N.next w (Sum.inl (r, st)) = Sum.inl (r', st')) : ∀ q ∈ st', q ≤ w.length := by
  cases hact : (N.step r (viewOf w st)).2 with
  | stay =>
      simp only [next, hact, Sum.inl.injEq, Prod.mk.injEq] at he
      rw [← he.2]; exact h
  | halt o => simp only [next, hact] at he; exact absurd he (by simp)
  | push =>
      simp only [next, hact] at he
      split_ifs at he with hlt
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at he
        rw [← he.2]
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact h q hq
        · simp only [List.mem_singleton] at hq
          omega
  | pop =>
      simp only [next, hact] at he
      split_ifs at he with hnil
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at he
        rw [← he.2]
        exact fun q hq => h q (List.dropLast_subset _ hq)
  | move d =>
      simp only [next, hact] at he
      cases hlast : st.getLast? with
      | none => simp only [hlast] at he; exact absurd he (by simp)
      | some x =>
          have hxmem : x ∈ st := List.mem_of_getLast? hlast
          have hxle : x ≤ w.length := h x hxmem
          simp only [hlast] at he
          split_ifs at he with h1 h2 h3
          all_goals
            first
              | exact Sum.noConfusion he
              | (simp only [Sum.inl.injEq, Prod.mk.injEq] at he
                 rw [← he.2]
                 intro q hq
                 rcases List.mem_append.1 hq with hq | hq
                 · exact h q (List.dropLast_subset _ hq)
                 · simp only [List.mem_singleton] at hq
                   omega)

/-- The state reached in one step is the state produced by the transition function. -/
lemma next_state {N : PebbleAut A R O k} {w : List A} {r r' : R} {st st' : List ℕ}
    (he : N.next w (Sum.inl (r, st)) = Sum.inl (r', st')) :
    r' = (N.step r (viewOf w st)).1 := by
  cases hact : (N.step r (viewOf w st)).2 with
  | stay =>
      simp only [next, hact, Sum.inl.injEq, Prod.mk.injEq] at he
      exact he.1.symm
  | halt o => simp only [next, hact] at he; simp at he
  | push =>
      simp only [next, hact] at he
      split_ifs at he
      simp only [Sum.inl.injEq, Prod.mk.injEq] at he
      exact he.1.symm
  | pop =>
      simp only [next, hact] at he
      split_ifs at he
      simp only [Sum.inl.injEq, Prod.mk.injEq] at he
      exact he.1.symm
  | move d =>
      simp only [next, hact] at he
      cases hlast : st.getLast? with
      | none => simp only [hlast] at he; simp at he
      | some x =>
          simp only [hlast] at he
          split_ifs at he <;>
            first
              | exact Sum.noConfusion he
              | (simp only [Sum.inl.injEq, Prod.mk.injEq] at he; exact he.1.symm)

/-- The pebbles of a run never leave the input string. -/
lemma iterate_stack_le {N : PebbleAut A R O k} {w : List A} {r : R} {st : List ℕ}
    (h : ∀ q ∈ st, q ≤ w.length) (n : ℕ) {r' : R} {st' : List ℕ}
    (he : (N.next w)^[n] (Sum.inl (r, st)) = Sum.inl (r', st')) : ∀ q ∈ st', q ≤ w.length := by
  induction n generalizing r st with
  | zero => cases he; exact h
  | succ n ih =>
      rw [Function.iterate_succ_apply] at he
      cases hc : N.next w (Sum.inl (r, st)) with
      | inr x => rw [hc, iterate_next_inr] at he; exact absurd he (by simp)
      | inl rs =>
          obtain ⟨r2, st2⟩ := rs
          exact ih (next_stack_le h hc) (by rw [← hc]; exact he)

open Classical in
/-- The answer of the run started in a configuration, if there is one. -/
noncomputable def answerOf (N : PebbleAut A R O k) (w : List A) (c : PebAutCfg R O) : Option O :=
  if h : ∃ o, N.Answers w c o then some h.choose else none

lemma answerOf_eq_some_iff {N : PebbleAut A R O k} {w : List A} {c : PebAutCfg R O} {o : O} :
    N.answerOf w c = some o ↔ N.Answers w c o := by
  classical
  unfold answerOf
  split_ifs with h
  · have hx := h.choose_spec
    exact ⟨fun he => by rwa [← Option.some_injective _ he], fun ho => by rw [answers_unique hx ho]⟩
  · simp only [false_iff]
    exact fun ho => h ⟨o, ho⟩

lemma answerOf_eq_none_iff {N : PebbleAut A R O k} {w : List A} {c : PebAutCfg R O} :
    N.answerOf w c = none ↔ ∀ o, ¬ N.Answers w c o := by
  classical
  constructor
  · intro h o ho
    rw [← answerOf_eq_some_iff] at ho
    rw [h] at ho
    exact absurd ho (by simp)
  · intro h
    rcases hc : N.answerOf w c with _ | o
    · rfl
    · exact absurd (answerOf_eq_some_iff.1 hc) (h o)

end PebbleAut

end Lax194892Proofs.Transducers
