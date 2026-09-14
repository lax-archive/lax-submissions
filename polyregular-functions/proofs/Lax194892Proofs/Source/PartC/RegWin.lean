/-
**Regular languages and windows of three consecutive letters.**

Several of the automata constructions of Part D have to look, in every position of the input, at
the letter of that position *and at its two neighbours*.  This file adds the corresponding closure
property to the toolkit of `RequestProject/PartC/RegAut.lean`:

* `Transducers.RegAut.winMap` replaces every letter of a string by the triple consisting of the
  letter, its predecessor and its successor (the predecessor of the first letter and the successor
  of the last one being absent);
* `Transducers.RegAut.isRegular_comapWin` -- the inverse image of a regular language under a map
  that is letter-to-letter *on windows* is regular.  The automaton is the automaton of the language
  run with a delay of one letter: it keeps the last two letters read in its state and feeds the
  window of the earlier one to the original automaton, the last window being fed at the moment of
  acceptance.
* `Transducers.RegAut.isRegular_all_win` -- the strings all of whose windows satisfy a fixed
  condition form a regular language.
-/
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers
namespace RegAut
open Lax916827Proofs.Transducers.RegAut

variable {Γ Δ : Type}

/-- A **window**: a letter together with its predecessor and its successor. -/
abbrev Win (Γ : Type) : Type := Option Γ × Γ × Option Γ

/-- The windows of the letters of `p :: r`, the predecessor of `p` being `pp`. -/
def winFrom (pp : Option Γ) (p : Γ) : List Γ → List (Win Γ)
  | [] => [(pp, p, none)]
  | c :: r => (pp, p, some c) :: winFrom (some p) c r

/-- **The word of windows** of a string: every letter together with its two neighbours. -/
def winMap : List Γ → List (Win Γ)
  | [] => []
  | p :: r => winFrom none p r

@[simp] lemma winFrom_length (pp : Option Γ) (p : Γ) (r : List Γ) :
    (winFrom pp p r).length = r.length + 1 := by
  induction r generalizing pp p with
  | nil => rfl
  | cons c r ih => simp [winFrom, ih]

@[simp] lemma winMap_length (u : List Γ) : (winMap u).length = u.length := by
  cases u with
  | nil => rfl
  | cons p r => simp [winMap]

@[simp] lemma winMap_nil : winMap ([] : List Γ) = [] := rfl

lemma winFrom_getElem? (r : List Γ) (pp : Option Γ) (p : Γ) (j : ℕ) :
    (winFrom pp p r)[j]? =
      ((p :: r)[j]?).map fun c => ((if j = 0 then pp else (p :: r)[j - 1]?), c, (p :: r)[j + 1]?) := by
  induction r generalizing pp p j with
  | nil =>
      cases j with
      | zero => simp [winFrom]
      | succ j => simp [winFrom]
  | cons c r ih =>
      cases j with
      | zero => simp [winFrom]
      | succ j =>
          rw [show (winFrom pp p (c :: r)) = (pp, p, some c) :: winFrom (some p) c r from rfl]
          rw [List.getElem?_cons_succ, ih]
          cases j with
          | zero => simp
          | succ j => simp

/-- The window of the position `j`: the letter `u[j]`, its predecessor and its successor. -/
lemma winMap_getElem? (u : List Γ) (j : ℕ) :
    (winMap u)[j]? =
      (u[j]?).map fun c => ((if j = 0 then none else u[j - 1]?), c, u[j + 1]?) := by
  cases u with
  | nil => simp
  | cons p r =>
      rw [show winMap (p :: r) = winFrom none p r from rfl, winFrom_getElem?]

variable [Finite Γ]

/-- **The inverse image of a regular language under a map that is letter-to-letter on windows is
regular.** -/
lemma isRegular_comapWin (f : Win Γ → Δ) {L : Language Δ} (hL : L.IsRegular) :
    Language.IsRegular {u : List Γ | (winMap u).map f ∈ L} := by
  classical
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  haveI : Finite σ := hσ.finite
  set step : σ × Option (Option Γ × Γ) → Γ → σ × Option (Option Γ × Γ) := fun s c =>
    match s.2 with
    | none => (s.1, some (none, c))
    | some (pp, p) => (D.step s.1 (f (pp, p, some c)), some (some p, c)) with hstep
  set flush : σ × Option (Option Γ × Γ) → σ := fun s =>
    match s.2 with
    | none => s.1
    | some (pp, p) => D.step s.1 (f (pp, p, none)) with hflush
  have hkey : ∀ (r : List Γ) (pp : Option Γ) (p : Γ) (s : σ),
      flush (List.foldl step (s, some (pp, p)) r) =
        List.foldl D.step s ((winFrom pp p r).map f) := by
    intro r
    induction r with
    | nil => intro pp p s; simp [hflush, winFrom]
    | cons c r ih =>
        intro pp p s
        rw [List.foldl_cons, show step (s, some (pp, p)) c
            = (D.step s (f (pp, p, some c)), some (some p, c)) from rfl, ih]
        simp [winFrom]
  have hreg := isRegular_foldl step (D.start, (none : Option (Option Γ × Γ)))
    {s | flush s ∈ D.accept}
  refine isRegular_of_eq hreg (fun u => ?_)
  show (winMap u).map f ∈ D.accepts ↔ flush (List.foldl step (D.start, none) u) ∈ D.accept
  cases u with
  | nil =>
      simp only [winMap_nil, List.map_nil, List.foldl_nil]
      rw [DFA.mem_accepts]
      simp [hflush, DFA.eval, DFA.evalFrom]
  | cons p r =>
      rw [DFA.mem_accepts]
      rw [List.foldl_cons, show step (D.start, (none : Option (Option Γ × Γ))) p
        = (D.start, some (none, p)) from rfl, hkey r none p D.start]
      rw [show winMap (p :: r) = winFrom none p r from rfl]
      rfl

/-- **The strings all of whose windows satisfy a fixed condition form a regular language.** -/
lemma isRegular_all_win (P : Win Γ → Bool) :
    Language.IsRegular {u : List Γ | ∀ t ∈ winMap u, P t = true} := by
  have h := isRegular_comapWin (id : Win Γ → Win Γ) (isRegular_all P)
  refine isRegular_of_eq h (fun u => ?_)
  simp only [List.map_id]
  exact Iff.rfl

end RegAut
end Lax194892Proofs.Transducers
