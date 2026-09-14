/-
From automata back to logic, with *two* free first-order variables.

`RequestProject/PartC/MarkLogic.lean` turns a regular language of strings marked at one position
into an mso formula with one free variable.  The proof of Theorem `thm:logic-regular-functions`
needs the version with two free variables: a regular language `K` of doubly marked strings gives a
formula `φ(x₀, x₁)` such that

  `w ⊨ φ(x, y)` iff the string `w`, with the position `x` carrying the first
  mark and the position `y` the second one, belongs to `K`.

The translation is the one of `MarkLogic.tr`, except that the variables of the
sentence are shifted by two instead of one, the first mark becoming the free
variable `x₀` and the second one the free variable `x₁`.
-/
import Lax916827Proofs.Source.PartC.MSOBuchi
import Lax916827Proofs.Source.PartC.MarkStr
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace MarkLogic2

open MSO MarkStr

variable {A : Type}

/-! ## The syntactic translation -/

/-- Equality of two first-order variables. -/
def eqF (i j : ℕ) : MSO A := MSO.and (MSO.le i j) (MSO.le j i)

/-- The test that the position `x_i` is (if `b`) or is not (if `¬ b`) the
position `x_v`. -/
def markFv : Bool → ℕ → ℕ → MSO A
  | true, i, v => eqF i v
  | false, i, v => MSO.not (eqF i v)

/-- The translation of a formula over the doubly marked alphabet into a formula
over `A` with the free variables `x₀` (first mark) and `x₁` (second mark). -/
def tr2 : MSO (Mark2 A) → MSO A
  | MSO.le i j => MSO.le (i + 2) (j + 2)
  | MSO.lab z i =>
      MSO.and (MSO.lab z.1 (i + 2))
        (MSO.and (markFv z.2.1 (i + 2) 0) (markFv z.2.2 (i + 2) 1))
  | MSO.mem i j => MSO.mem (i + 2) j
  | MSO.not φ => MSO.not (tr2 φ)
  | MSO.and φ ψ => MSO.and (tr2 φ) (tr2 ψ)
  | MSO.or φ ψ => MSO.or (tr2 φ) (tr2 ψ)
  | MSO.exFO i φ => MSO.exFO (i + 2) (tr2 φ)
  | MSO.exSO j φ => MSO.exSO j (tr2 φ)

/-- The valuation in which `x₀` and `x₁` are the two marked positions and every
other variable is shifted by two. -/
def shiftFO2 (x y : ℕ) (fo : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i = 0 then x else if i = 1 then y else fo (i - 2)

lemma shiftFO2_zero (x y : ℕ) (fo : ℕ → ℕ) : shiftFO2 x y fo 0 = x := rfl

lemma shiftFO2_one (x y : ℕ) (fo : ℕ → ℕ) : shiftFO2 x y fo 1 = y := rfl

lemma shiftFO2_add (x y : ℕ) (fo : ℕ → ℕ) (i : ℕ) : shiftFO2 x y fo (i + 2) = fo i := by
  simp [shiftFO2]

lemma shiftFO2_const (x y : ℕ) :
    shiftFO2 x y (fun _ => y) = (fun i => if i = 0 then x else y) := by
  funext i
  rw [shiftFO2]
  split <;> [rfl; (split <;> rfl)]

lemma shiftFO2_update (x y : ℕ) (fo : ℕ → ℕ) (i p : ℕ) :
    Function.update (shiftFO2 x y fo) (i + 2) p = shiftFO2 x y (Function.update fo i p) := by
  funext j
  match j with
  | 0 => rw [Function.update_of_ne (by omega), shiftFO2_zero, shiftFO2_zero]
  | 1 => rw [Function.update_of_ne (by omega), shiftFO2_one, shiftFO2_one]
  | (j + 2) =>
      rw [shiftFO2_add]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne hj, shiftFO2_add]

lemma sat_markFv_zero (w : List A) (x y : ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (b : Bool) (i : ℕ) :
    MSO.Sat w (shiftFO2 x y fo) so (markFv b (i + 2) 0) ↔ (decide (fo i = x) = b) := by
  have key : MSO.Sat w (shiftFO2 x y fo) so (eqF (A := A) (i + 2) 0) ↔ fo i = x := by
    simp only [eqF, MSO.Sat, shiftFO2_add, shiftFO2_zero]
    omega
  rcases b with - | -
  · show ¬ MSO.Sat w (shiftFO2 x y fo) so (eqF (i + 2) 0) ↔ _
    rw [key]
    simp
  · rw [show markFv (A := A) true (i + 2) 0 = eqF (i + 2) 0 from rfl, key]
    simp

lemma sat_markFv_one (w : List A) (x y : ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (b : Bool) (i : ℕ) :
    MSO.Sat w (shiftFO2 x y fo) so (markFv b (i + 2) 1) ↔ (decide (fo i = y) = b) := by
  have key : MSO.Sat w (shiftFO2 x y fo) so (eqF (A := A) (i + 2) 1) ↔ fo i = y := by
    simp only [eqF, MSO.Sat, shiftFO2_add, shiftFO2_one]
    omega
  rcases b with - | -
  · show ¬ MSO.Sat w (shiftFO2 x y fo) so (eqF (i + 2) 1) ↔ _
    rw [key]
    simp
  · rw [show markFv (A := A) true (i + 2) 1 = eqF (i + 2) 1 from rfl, key]
    simp

/-- The translation is correct: a formula over the doubly marked alphabet holds
in `markAt2 w x y` if and only if its translation holds in `w`, with `x₀`
interpreted as `x` and `x₁` as `y`. -/
lemma sat_tr2 (w : List A) (x y : ℕ) :
    ∀ (φ : MSO (Mark2 A)) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      MSO.Sat w (shiftFO2 x y fo) so (tr2 φ) ↔ MSO.Sat (markAt2 w x y) fo so φ := by
  intro φ
  induction φ with
  | le i j => intro fo so; simp [tr2, MSO.Sat, shiftFO2_add]
  | lab z i =>
      intro fo so
      obtain ⟨a₀, b₁, b₂⟩ := z
      rw [tr2]
      simp only [MSO.Sat]
      rw [sat_markFv_zero, sat_markFv_one, markAt2_getElem?, shiftFO2_add]
      rcases hw : w[fo i]? with - | a
      · simp
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  | mem i j => intro fo so; simp [tr2, MSO.Sat, shiftFO2_add]
  | not φ ih => intro fo so; simp [tr2, MSO.Sat, ih]
  | and φ ψ ihφ ihψ => intro fo so; simp [tr2, MSO.Sat, ihφ, ihψ]
  | or φ ψ ihφ ihψ => intro fo so; simp [tr2, MSO.Sat, ihφ, ihψ]
  | exFO i φ ih =>
      intro fo so
      simp only [tr2, MSO.Sat, markAt2_length]
      refine exists_congr (fun p => and_congr_right (fun _ => ?_))
      rw [shiftFO2_update, ih]
  | exSO j φ ih =>
      intro fo so
      simp only [tr2, MSO.Sat, markAt2_length]
      exact exists_congr (fun S => and_congr_right (fun _ => ih fo (Function.update so j S)))

/-! ## From a regular language of doubly marked strings to a formula -/

/-- A regular language of strings marked at two positions is defined by an mso
formula with two free first-order variables. -/
theorem exists_form2_of_regular [Finite A] (K : Language (Mark2 A)) (hK : K.IsRegular) :
    ∃ φ : MSO A, ∀ (w : List A) (x y : ℕ),
      (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) φ ↔ markAt2 w x y ∈ K) := by
  obtain ⟨ψ, hψ⟩ := MSOBuchi.msoDefinable_of_isRegular hK
  refine ⟨tr2 ψ, fun w x y => ?_⟩
  rw [← shiftFO2_const x y, sat_tr2 w x y ψ (fun _ => y) (fun _ => ∅)]
  exact hψ _ _ _

end MarkLogic2
end Lax916827Proofs.Transducers
