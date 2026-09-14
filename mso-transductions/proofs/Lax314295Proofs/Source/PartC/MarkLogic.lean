/-
From automata back to logic, with a free first-order variable.

Theorem `thm:mso-logic-languages` (`RequestProject/PartC/MSOBuchi.lean`) turns a regular language
into an mso *sentence*.  For the inclusion "rational ⊆ mso relabellings" of Theorem
`thm:logic-rational-functions` one needs the version with one free variable: a regular language `K`
of strings marked at one position gives a formula `φ(x₀)` such that

  `w ⊨ φ(x)` iff the string `w` with the position `x` marked belongs to `K`.

The formula is obtained from the sentence for `K` by a syntactic translation
`tr`: every variable of the sentence is shifted by one, so that the variable
`x₀` becomes free, and a test for the letter `(a, b₁, b₂)` becomes a test for
the letter `a` together with the test that the position is (or is not) the
distinguished position `x₀`.  Only strings marked twice at the same position
(`markAt2 w x x`) are used, which is why the two marks of `MarkStr.Mark2` are
translated in the same way; using the doubly marked alphabet here avoids a
second family of marked strings, since the doubly marked alphabet is the one
needed for Lemma `lem:logic-precomputation`.
-/
import Lax916827Proofs.Source.PartC.MSOBuchi
import Lax916827Proofs.Source.PartC.MarkStr
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MarkLogic

open MSO MarkStr

variable {A : Type}

/-! ## The syntactic translation -/

/-- Equality of two first-order variables. -/
def eqF (i j : ℕ) : MSO A := MSO.and (MSO.le i j) (MSO.le j i)

/-- The test that the position `x_i` is (if `b`) or is not (if `¬ b`) the
distinguished position `x₀`. -/
def markF : Bool → ℕ → MSO A
  | true, i => eqF i 0
  | false, i => MSO.not (eqF i 0)

/-- The translation of a formula over the doubly marked alphabet into a formula
over `A` with the free variable `x₀` for the marked position. -/
def tr : MSO (Mark2 A) → MSO A
  | MSO.le i j => MSO.le (i + 1) (j + 1)
  | MSO.lab z i => MSO.and (MSO.lab z.1 (i + 1)) (MSO.and (markF z.2.1 (i + 1)) (markF z.2.2 (i + 1)))
  | MSO.mem i j => MSO.mem (i + 1) j
  | MSO.not φ => MSO.not (tr φ)
  | MSO.and φ ψ => MSO.and (tr φ) (tr ψ)
  | MSO.or φ ψ => MSO.or (tr φ) (tr ψ)
  | MSO.exFO i φ => MSO.exFO (i + 1) (tr φ)
  | MSO.exSO j φ => MSO.exSO j (tr φ)

/-- The valuation in which the variable `x₀` is the marked position and every
other variable is shifted by one. -/
def shiftFO (x : ℕ) (fo : ℕ → ℕ) : ℕ → ℕ := fun i => if i = 0 then x else fo (i - 1)

lemma shiftFO_zero (x : ℕ) (fo : ℕ → ℕ) : shiftFO x fo 0 = x := rfl

lemma shiftFO_succ (x : ℕ) (fo : ℕ → ℕ) (i : ℕ) : shiftFO x fo (i + 1) = fo i := rfl

lemma shiftFO_const (x : ℕ) : shiftFO x (fun _ => x) = (fun _ => x) := by
  funext i
  rw [shiftFO]
  split <;> rfl

lemma shiftFO_update (x : ℕ) (fo : ℕ → ℕ) (i p : ℕ) :
    Function.update (shiftFO x fo) (i + 1) p = shiftFO x (Function.update fo i p) := by
  funext j
  rcases j with - | j
  · rw [Function.update_of_ne (by omega), shiftFO_zero, shiftFO_zero]
  · rw [shiftFO_succ]
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hj, shiftFO_succ]

lemma sat_markF (w : List A) (x : ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (b : Bool) (i : ℕ) :
    MSO.Sat w (shiftFO x fo) so (markF b (i + 1)) ↔ (decide (fo i = x) = b) := by
  have key : MSO.Sat w (shiftFO x fo) so (eqF (i + 1) 0) ↔ fo i = x := by
    simp only [eqF, MSO.Sat, shiftFO_succ, shiftFO_zero]
    omega
  rcases b with - | -
  · show ¬ MSO.Sat w (shiftFO x fo) so (eqF (i + 1) 0) ↔ _
    rw [key]
    simp
  · rw [show markF (A := A) true (i + 1) = eqF (i + 1) 0 from rfl, key]
    simp

/-- The translation is correct: a formula over the doubly marked alphabet holds
in `markAt2 w x x` if and only if its translation holds in `w`, with the
variable `x₀` interpreted as `x`. -/
lemma sat_tr (w : List A) (x : ℕ) :
    ∀ (φ : MSO (Mark2 A)) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      MSO.Sat w (shiftFO x fo) so (tr φ) ↔ MSO.Sat (markAt2 w x x) fo so φ := by
  intro φ
  induction φ with
  | le i j => intro fo so; simp [tr, MSO.Sat, shiftFO_succ]
  | lab z i =>
      intro fo so
      obtain ⟨a₀, b₁, b₂⟩ := z
      rw [tr]
      simp only [MSO.Sat]
      rw [sat_markF, sat_markF, markAt2_getElem?, shiftFO_succ]
      rcases hw : w[fo i]? with - | a
      · simp
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  | mem i j => intro fo so; simp [tr, MSO.Sat, shiftFO_succ]
  | not φ ih => intro fo so; simp [tr, MSO.Sat, ih]
  | and φ ψ ihφ ihψ => intro fo so; simp [tr, MSO.Sat, ihφ, ihψ]
  | or φ ψ ihφ ihψ => intro fo so; simp [tr, MSO.Sat, ihφ, ihψ]
  | exFO i φ ih =>
      intro fo so
      simp only [tr, MSO.Sat, markAt2_length]
      refine exists_congr (fun p => and_congr_right (fun _ => ?_))
      rw [shiftFO_update, ih]
  | exSO j φ ih =>
      intro fo so
      simp only [tr, MSO.Sat, markAt2_length]
      exact exists_congr (fun S => and_congr_right (fun _ => ih fo (Function.update so j S)))

/-! ## From a regular language of marked strings to a formula -/

/-- A regular language of strings marked at one position is defined by an mso
formula with one free first-order variable. -/
theorem exists_form_of_regular [Finite A] (K : Language (Mark2 A)) (hK : K.IsRegular) :
    ∃ φ : MSO A, ∀ (w : List A) (x : ℕ),
      (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ markAt2 w x x ∈ K) := by
  obtain ⟨ψ, hψ⟩ := MSOBuchi.msoDefinable_of_isRegular hK
  refine ⟨tr ψ, fun w x => ?_⟩
  rw [← shiftFO_const x, sat_tr w x ψ (fun _ => x) (fun _ => ∅)]
  exact hψ _ _ _

end MarkLogic
end Lax314295Proofs.Transducers
