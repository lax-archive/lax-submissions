import Lax765601.Continuity
import Lax765601.ElementaryProperties
import Lax765601.CompositionClosure
import Lax765601.MealyMachine
import Lax765601.StateTransformations
import Lax765601.PrimeMealyMachines
import Lax765601.MapLifting
import Lax765601.Aperiodicity
import Lax765601.Derivatives
import Lax765601Proofs.Source.PartA.Statements

/-!
The bridge between the concept package and the ported source development
(`Lax765601Proofs.Source`, the Part A files of `transducer-lean` under a new
namespace). Every concept definition is shown equal, or equivalent, to its
counterpart in the source, so that the source theorems transport to the
submitted statements in `Lax765601Proofs.Results`.
-/

namespace Lax765601Proofs.Bridge

open Lax765601.CompositionClosure Lax765601.MealyMachine Lax765601.StateTransformations
  Lax765601.PrimeMealyMachines Lax765601.MapLifting Lax765601.Aperiodicity Lax765601.Derivatives

variable {A B C Q : Type}

/-- A concept machine as a source machine. -/
def toSrc (M : Mealy A B Q) : Transducers.Mealy A B Q := ⟨M.init, M.step⟩

/-- A source machine as a concept machine. -/
def ofSrc (M : Transducers.Mealy A B Q) : Mealy A B Q := ⟨M.init, M.step⟩

lemma run_toSrc (M : Mealy A B Q) (q : Q) (w : List A) : (toSrc M).run q w = M.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      show (M.step q a).2 :: (toSrc M).run (M.step q a).1 w = (M.step q a).2 :: M.run _ w
      rw [ih]

lemma eval_toSrc (M : Mealy A B Q) : (toSrc M).eval = M.eval := by
  funext w
  exact run_toSrc M M.init w

lemma eval_ofSrc (M : Transducers.Mealy A B Q) : (ofSrc M).eval = M.eval :=
  (eval_toSrc (ofSrc M)).symm

lemma isMealy_iff (f : List A → List B) : IsMealy f ↔ Transducers.IsMealy f := by
  constructor
  · rintro ⟨Q, hQ, M, hM⟩
    exact ⟨Q, hQ, toSrc M, by rw [eval_toSrc, hM]⟩
  · rintro ⟨Q, hQ, M, hM⟩
    exact ⟨Q, hQ, ofSrc M, by rw [eval_ofSrc, hM]⟩

lemma isReversibleMealy_iff (f : List A → List B) :
    IsReversibleMealy f ↔ Transducers.IsReversibleMealy f := by
  constructor
  · rintro ⟨Q, hQ, M, hM, hr⟩
    exact ⟨Q, hQ, toSrc M, by rw [eval_toSrc, hM], hr⟩
  · rintro ⟨Q, hQ, M, hM, hr⟩
    exact ⟨Q, hQ, ofSrc M, by rw [eval_ofSrc, hM], hr⟩

lemma isFlipFlopMealy_iff (f : List A → List B) :
    IsFlipFlopMealy f ↔ Transducers.IsFlipFlopMealy f := by
  constructor
  · rintro ⟨Q, hQ, M, hM, hr⟩
    exact ⟨Q, hQ, toSrc M, by rw [eval_toSrc, hM], hr⟩
  · rintro ⟨Q, hQ, M, hM, hr⟩
    exact ⟨Q, hQ, ofSrc M, by rw [eval_ofSrc, hM], hr⟩

lemma primeMealyFam_iff (A B : Type) (f : List A → List B) :
    PrimeMealyFam A B f ↔ Transducers.PrimeMealyFam A B f :=
  or_congr (isReversibleMealy_iff f) (isFlipFlopMealy_iff f)

lemma flipFlopFam_iff (A B : Type) (f : List A → List B) :
    FlipFlopFam A B f ↔ Transducers.FlipFlopFam A B f :=
  isFlipFlopMealy_iff f

/-- The two composition closures agree as soon as the families do. -/
lemma compClosure_iff {P : Family} {P' : ∀ (A B : Type), (List A → List B) → Prop}
    (h : ∀ (A B : Type) (f : List A → List B), P A B f ↔ P' A B f)
    {A B : Type} {f : List A → List B} :
    CompClosure P A B f ↔ Transducers.CompClosure P' A B f := by
  constructor
  · intro hf
    induction hf with
    | base hb => exact Transducers.CompClosure.base ((h _ _ _).1 hb)
    | id A => exact Transducers.CompClosure.id A
    | comp _ _ ihf ihg => exact Transducers.CompClosure.comp ihf ihg
  · intro hf
    induction hf with
    | base hb => exact CompClosure.base ((h _ _ _).2 hb)
    | id A => exact CompClosure.id A
    | comp _ _ ihf ihg => exact CompClosure.comp ihf ihg

lemma splitSep_eq : ∀ w : List (Option A), splitSep w = Transducers.splitSep w
  | [] => rfl
  | none :: w => by simp [splitSep, Transducers.splitSep, splitSep_eq w]
  | some a :: w => by
      simp only [splitSep, Transducers.splitSep, splitSep_eq w]
      cases Transducers.splitSep w <;> rfl

lemma mapLift_eq (f : List A → List B) : mapLift f = Transducers.mapLift f := by
  funext w
  simp [mapLift, Transducers.mapLift, splitSep_eq]

lemma npow_eq (v : List A) : ∀ n : ℕ, npow v n = Transducers.npow v n
  | 0 => rfl
  | n + 1 => by simp [npow, Transducers.npow, npow_eq v n]

lemma aperiodic_iff (f : List A → List B) : Aperiodic f ↔ Transducers.Aperiodic f := by
  simp only [Aperiodic, Transducers.Aperiodic, npow_eq]

lemma range_deriv_eq (f : List A → List B) :
    Set.range (deriv f) = {g | ∃ w, g = Transducers.deriv f w} := by
  ext g
  exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩

end Lax765601Proofs.Bridge
