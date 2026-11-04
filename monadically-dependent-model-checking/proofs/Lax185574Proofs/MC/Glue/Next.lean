import Lax185574Proofs.MC.Glue.Skip

/-!
The order of the calls of the pipeline of thm:mc.

`nextCall` gives the call after a call: the call of the next step, or
the evaluation after the last step. `pcalls_succ`: in `pcalls`, the entry
after a call is its `nextCall`. `pcalls_valid`: every call matches the
step it belongs to.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs

variable {n : ℕ}

/-- The first call of step `t`. -/
def stepFirst (hn : 0 < n) (t : ℕ) : Step → PCall n
  | .merge P Q => .merge t P Q
  | .resolvePos P Q => .resolve t true P Q
  | .resolveNeg P Q => .resolve t false P Q

/-- The call after the last call of step `t`. -/
def afterStep (hn : 0 < n) (steps : List Step) (t : ℕ) : PCall n :=
  if h : t + 1 < steps.length then stepFirst hn (t + 1) steps[t + 1] else .eval ⟨0, hn⟩

/-- The call after a call. -/
def nextCall (hn : 0 < n) (steps : List Step) : PCall n → Option (PCall n)
  | .merge t _ _ => some (afterStep hn steps t)
  | .resolve t _ _ _ => some (afterStep hn steps t)
  | .eval _ => none

/-! ### Linked lists -/

/-- Consecutive entries of `l` stand in relation `R`. -/
def Linked {α : Type*} (R : α → α → Prop) (l : List α) : Prop :=
  ∀ j a b, l[j]? = some a → l[j + 1]? = some b → R a b

theorem linked_append {α : Type*} {R : α → α → Prop} {A B : List α} (hA : Linked R A)
    (hB : Linked R B) (hAB : ∀ a b, A.getLast? = some a → B.head? = some b → R a b) :
    Linked R (A ++ B) := by
  intro j a b ha hb
  by_cases h1 : j + 1 < A.length
  · rw [List.getElem?_append_left (by omega)] at ha
    rw [List.getElem?_append_left h1] at hb
    exact hA j a b ha hb
  by_cases h2 : j + 1 = A.length
  · rw [List.getElem?_append_left (by omega)] at ha
    rw [List.getElem?_append_right (by omega), show j + 1 - A.length = 0 by omega] at hb
    refine hAB a b ?_ (by rw [List.head?_eq_getElem?]; exact hb)
    rw [List.getLast?_eq_getElem?, show A.length - 1 = j by omega]; exact ha
  · rw [List.getElem?_append_right (by omega)] at ha hb
    exact hB (j - A.length) a b ha (by rw [show j - A.length + 1 = j + 1 - A.length by omega]; exact hb)

theorem linked_single {α : Type*} {R : α → α → Prop} (a : α) : Linked R [a] := by
  intro j x y _ hy
  simp at hy

/-! ### The calls of a step -/

theorem stepCalls_eq (hn : 0 < n) (t : ℕ) (st : Step) : stepCalls n t st = [stepFirst hn t st] := by
  cases st <;> rfl

theorem linked_stepCalls (hn : 0 < n) (steps : List Step) (t : ℕ) (st : Step) :
    Linked (fun c c' => nextCall hn steps c = some c') (stepCalls n t st) := by
  rw [stepCalls_eq hn]; exact linked_single _

theorem stepCalls_head (hn : 0 < n) (t : ℕ) (st : Step) :
    (stepCalls n t st).head? = some (stepFirst hn t st) := by
  rw [stepCalls_eq hn]; rfl

theorem stepCalls_last (hn : 0 < n) (steps : List Step) (t : ℕ) (st : Step) :
    ∃ c, (stepCalls n t st).getLast? = some c ∧ nextCall hn steps c = some (afterStep hn steps t) := by
  refine ⟨stepFirst hn t st, by rw [stepCalls_eq hn]; rfl, ?_⟩
  cases st <;> rfl

theorem stepCalls_ne_nil (hn : 0 < n) (t : ℕ) (st : Step) : stepCalls n t st ≠ [] := by
  rw [stepCalls_eq hn]; simp

/-! ### All calls -/

theorem linked_callsFrom (hn : 0 < n) (steps : List Step) :
    ∀ k t, t + k = steps.length →
      Linked (fun c c' => nextCall hn steps c = some c')
        (callsFrom n t (steps.drop t) ++ [.eval ⟨0, hn⟩]) := by
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [List.drop_of_length_le (by omega)]
    simp only [callsFrom, List.nil_append]; exact linked_single _
  | succ k ih =>
    intro t ht
    rw [List.drop_eq_getElem_cons (by omega)]
    simp only [callsFrom, List.append_assoc]
    refine linked_append (linked_stepCalls hn steps t _) (ih (t + 1) (by omega)) ?_
    intro a b ha hb
    obtain ⟨c, hc, hcn⟩ := stepCalls_last hn steps t steps[t]
    rw [ha] at hc; cases hc
    rw [hcn]
    congr 1
    unfold afterStep
    by_cases h : t + 1 < steps.length
    · rw [dif_pos h, List.drop_eq_getElem_cons h] at *
      simp only [callsFrom, List.append_assoc, List.head?_append, stepCalls_head hn] at hb
      simpa using hb
    · rw [dif_neg h, List.drop_of_length_le (by omega)] at *
      simp only [callsFrom, List.nil_append, List.head?_cons, Option.some.injEq] at hb
      exact hb

/-- **The order of the calls.** -/
theorem pcalls_succ (hn : 0 < n) (steps : List Step) {j : ℕ} {c : PCall n}
    (h : (pcalls n steps)[j]? = some c) : (pcalls n steps)[j + 1]? = nextCall hn steps c := by
  have hL := linked_callsFrom hn steps steps.length 0 (by simp)
  simp only [List.drop_zero] at hL
  have hp : pcalls n steps = callsFrom n 0 steps ++ [.eval ⟨0, hn⟩] := by simp [pcalls, hn]
  rw [hp] at h ⊢
  cases hb : (callsFrom n 0 steps ++ [PCall.eval ⟨0, hn⟩])[j + 1]? with
  | some b => exact (hL j c b h hb).symm
  | none =>
    -- `c` is the last call, the evaluation
    have hlen : j + 1 = (callsFrom n 0 steps ++ [PCall.eval ⟨0, hn⟩]).length := by
      have h1 : j < (callsFrom n 0 steps ++ [PCall.eval ⟨0, hn⟩]).length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h
      have h2 : ¬ j + 1 < (callsFrom n 0 steps ++ [PCall.eval ⟨0, hn⟩]).length := by
        intro hc; rw [List.getElem?_eq_getElem hc] at hb; simp at hb
      omega
    rw [List.getElem?_append_right (by simp at hlen ⊢; omega)] at h
    simp at hlen
    rw [show j - (callsFrom n 0 steps).length = 0 by omega] at h
    simp at h; subst h; rfl

/-! ### Calls match their steps -/

/-- A call matches the script: its step exists and is of its kind, and
the evaluation is on vertex `0`. -/
def Valid (steps : List Step) : PCall n → Prop
  | .merge t P Q => steps[t]? = some (.merge P Q)
  | .resolve t sg P Q => steps[t]? = some (if sg then .resolvePos P Q else .resolveNeg P Q)
  | .eval a => a.val = 0

theorem valid_callsFrom (steps : List Step) :
    ∀ k t, t + k = steps.length → ∀ c ∈ callsFrom n t (steps.drop t), Valid steps c := by
  intro k
  induction k with
  | zero =>
    intro t ht c hc
    rw [List.drop_of_length_le (by omega)] at hc; simp [callsFrom] at hc
  | succ k ih =>
    intro t ht c hc
    rw [List.drop_eq_getElem_cons (by omega)] at hc
    simp only [callsFrom, List.mem_append] at hc
    rcases hc with hc | hc
    · have hs : steps[t]? = some steps[t] := List.getElem?_eq_getElem (by omega)
      generalize steps[t] = st at hs hc
      cases st with
      | merge P Q => simp [stepCalls] at hc; subst hc; exact hs
      | resolvePos P Q => simp [stepCalls] at hc; subst hc; exact hs
      | resolveNeg P Q => simp [stepCalls] at hc; subst hc; exact hs
    · exact ih (t + 1) (by omega) c hc

theorem pcalls_valid (steps : List Step) {c : PCall n} (h : c ∈ pcalls n steps) :
    Valid steps c := by
  simp only [pcalls, List.mem_append] at h
  rcases h with h | h
  · exact valid_callsFrom steps steps.length 0 (by simp) c (by simpa using h)
  · split_ifs at h <;> simp at h; subst h; rfl

end Lax185574Proofs.MC.Glue
