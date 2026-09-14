/-
Auxiliary facts about regular languages that are used in Part B.

Mathlib provides regularity of finite unions, intersections and complements,
together with the Myhill-Nerode theorem, but not the closure properties that we
need for the automata constructions of Part B.  The facts collected here are the
ones used in the characterisation theorems of Section *Machine independent characterisations*.
-/
import Lax765601Proofs.Source.Common.Basic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-! ## The language of strings with a prescribed last letter -/

/-- The language of strings whose last letter is `b`. -/
def lastLang {B : Type} (b : B) : Language B := {v | v.getLast? = some b}

/-- The dfa recognising `lastLang b`: it remembers the last letter read. -/
def lastDFA {B : Type} (b : B) : DFA B (Option B) where
  step := fun _ c => some c
  start := none
  accept := {some b}

lemma lastDFA_evalFrom {B : Type} (b : B) (s : Option B) (v : List B) :
    (lastDFA b).evalFrom s v = v.getLast?.orElse (fun _ => s) := by
  induction v generalizing s with
  | nil => simp [lastDFA]
  | cons a v ih =>
    rw [DFA.evalFrom_cons, show (lastDFA b).step s a = some a by simp [lastDFA]]
    rw [ih (some a)]
    cases v with
    | nil => simp
    | cons a' v' => simp [List.getLast?]

lemma lastDFA_accepts {B : Type} (b : B) : (lastDFA b).accepts = lastLang b := by
  funext w
  simp [lastLang, DFA.accepts, DFA.acceptsFrom, lastDFA]
  unfold DFA.evalFrom
  simp only []
  have h : ∀ (s : Option B) (w : List B), List.foldl (fun _ c => some c) s w = w.getLast?.orElse (fun _ => s) := by
    intro s w
    induction w generalizing s with
    | nil => rfl
    | cons a w ih =>
      rw [List.foldl_cons, ih]
      have hl : (a :: w).getLast? = w.getLast?.orElse (fun _ => some a) := by
        induction w with
        | nil => rfl
        | cons b w' ih => rfl
      rw [hl]
      cases w.getLast? with
      | none => rfl
      | some x => rfl
  simp [h]

lemma lastLang_isRegular {B : Type} [Finite B] (b : B) : (lastLang b).IsRegular := by
  rw [← lastDFA_accepts]
  -- Use the fact that DFA.accepts is regular
  -- We construct an εNFA from the DFA
  letI : Fintype (Option B) := Fintype.ofFinite (Option B)
  refine ⟨Option B, inferInstance, ?_⟩
  -- Convert DFA to εNFA
  use { step := fun s a => (lastDFA b).step s a
        start := (lastDFA b).start
        accept := (lastDFA b).accept }

end Lax132576Proofs.Transducers
