/-
**Universal closure of a regular relation on two marked positions.**

This is the logical tool used by the book's first stage in the proof of the
snake lemma (`RequestProject/PartC/SnakeStage1.lean`).  A *checking automaton*
has to verify a condition that relates every marked position of a string to the
next marked one.  Such a condition is a regular property of the string marked at
the two positions, and the conjunction of all its instances is regular as well,
because it is expressed by the mso sentence

  `∀ x₀ ∀ x₁  φ (x₀, x₁)`,

where `φ` is the formula of `MarkLogic2.exists_form2_of_regular` and mso
sentences define regular languages (Theorem `thm:mso-logic-languages`,
`Transducers.isRegular_of_msoDefinable`).

The guards -- that the two positions are marked, that they are consecutive
marked positions, that one is to the left of the other -- are not part of the
statement: they are folded into the regular relation itself, which is closed
under Boolean combinations.
-/
import Lax916827Proofs.Source.PartC.MarkLogic2
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace SnakeMSO

open MSO MarkStr

variable {A : Type}

/-- The formula of `MarkLogic2.exists_form2_of_regular`, stated for an arbitrary
valuation: only the values of the two free variables `x₀` and `x₁` matter. -/
theorem exists_form2_of_regular' [Finite A] (K : Language (Mark2 A)) (hK : K.IsRegular) :
    ∃ φ : MSO A, ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      (MSO.Sat w fo so φ ↔ markAt2 w (fo 0) (fo 1) ∈ K) := by
  obtain ⟨ψ, hψ⟩ := MSOBuchi.msoDefinable_of_isRegular hK
  refine ⟨MarkLogic2.tr2 ψ, fun w fo so => ?_⟩
  have hfo : fo = MarkLogic2.shiftFO2 (fo 0) (fo 1) (fun i => fo (i + 2)) := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | (i + 2) => rw [MarkLogic2.shiftFO2_add]
  rw [hfo, MarkLogic2.sat_tr2 w (fo 0) (fo 1) ψ (fun i => fo (i + 2)) so]
  exact hψ _ _ _

/-- **The universal closure of a regular relation on two marked positions is a
regular language.** -/
theorem isRegular_forall2 [Finite A] {K : Language (Mark2 A)} (hK : K.IsRegular) :
    Language.IsRegular {u : List A | ∀ x < u.length, ∀ y < u.length, markAt2 u x y ∈ K} := by
  obtain ⟨φ, hφ⟩ := exists_form2_of_regular' K hK
  refine MSOBuchi.isRegular_of_msoDefinable ⟨MSO.not (MSO.exFO 0 (MSO.exFO 1 (MSO.not φ))), ?_⟩
  intro w fo so
  simp only [MSO.Sat, not_exists, not_and, not_not]
  constructor
  · intro h x hx y hy
    have := h x hx y hy
    rw [hφ w (Function.update (Function.update fo 0 x) 1 y) so] at this
    simpa [Function.update_of_ne, Function.update_self] using this
  · intro h x hx y hy
    rw [hφ w (Function.update (Function.update fo 0 x) 1 y) so]
    simpa [Function.update_of_ne, Function.update_self] using h x hx y hy

/-! ## Universal closure of a regular property of one marked position

A condition on a *single* marked position is a condition on the doubly marked
string in which the two marks sit at the same position; its universal closure is
obtained from `isRegular_forall2` by relaxing the relation on all the doubly
marked strings whose two marks are distinct. -/

/-- The step of the automaton that looks for a letter carrying both marks. -/
private def bothStep (s : Bool) (c : Mark2 A) : Bool := s || (c.2.1 && c.2.2)

private lemma bothStep_eval :
    ∀ (v : List (Mark2 A)) (s : Bool),
      v.foldl bothStep s = (s || v.any fun c => c.2.1 && c.2.2)
  | [], s => by simp
  | c :: v, s => by
      rw [List.foldl_cons, bothStep_eval v, List.any_cons]
      simp [bothStep, Bool.or_assoc]

/-- The strings carrying a letter with both marks form a regular language. -/
lemma isRegular_hasBoth [Finite A] :
    Language.IsRegular {v : List (Mark2 A) | (v.any fun c => c.2.1 && c.2.2) = true} := by
  refine RegAut.isRegular_of_eq
    (RegAut.isRegular_foldl (Γ := Mark2 A) bothStep false {b | b = true}) ?_
  intro v
  change ((v.any fun c => c.2.1 && c.2.2) = true) ↔ List.foldl bothStep false v ∈ ({b | b = true} : Set Bool)
  rw [bothStep_eval v false, Bool.false_or]
  exact Iff.rfl

/-- A string marked twice at the same position carries a letter with both
marks. -/
lemma any_markAt2_diag (w : List A) {x : ℕ} (hx : x < w.length) :
    ((markAt2 w x x).any fun c => c.2.1 && c.2.2) = true := by
  obtain ⟨a, ha⟩ : ∃ a, w[x]? = some a := ⟨w[x], List.getElem?_eq_getElem hx⟩
  have hmem : (a, true, true) ∈ markAt2 w x x := by
    refine List.mem_iff_getElem?.2 ⟨x, ?_⟩
    rw [markAt2_getElem?, ha]
    simp
  exact List.any_eq_true.2 ⟨_, hmem, by simp⟩

/-- A string whose two marks sit at different positions carries no letter with
both marks. -/
lemma any_markAt2_ne (w : List A) {x y : ℕ} (hxy : x ≠ y) :
    ((markAt2 w x y).any fun c => c.2.1 && c.2.2) = false := by
  by_contra hcon
  have hany : ((markAt2 w x y).any fun c => c.2.1 && c.2.2) = true := by
    cases h : ((markAt2 w x y).any fun c => c.2.1 && c.2.2) with
    | false => exact absurd h hcon
    | true => rfl
  obtain ⟨c, hmem, hc⟩ := List.any_eq_true.1 hany
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
  rw [markAt2_getElem?] at hj
  rcases hw : w[j]? with _ | a
  · rw [hw] at hj; simp at hj
  · rw [hw] at hj
    simp only [Option.map_some, Option.some.injEq] at hj
    subst hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hxy (hc.1 ▸ hc.2 ▸ rfl)

/-- **The universal closure of a regular property of one marked position is a
regular language.** -/
theorem isRegular_forall1 [Finite A] {K : Language (Mark2 A)} (hK : K.IsRegular) :
    Language.IsRegular {u : List A | ∀ x < u.length, markAt2 u x x ∈ K} := by
  classical
  have hK' : Language.IsRegular
      {v : List (Mark2 A) | v ∈ K ∨ (v.any fun c => c.2.1 && c.2.2) = false} := by
    refine RegAut.isRegular_or hK ?_
    refine RegAut.isRegular_of_eq (RegAut.isRegular_not (isRegular_hasBoth (A := A))) ?_
    intro v
    exact (Bool.not_eq_true _).to_iff.symm
  refine RegAut.isRegular_of_eq (isRegular_forall2 hK') ?_
  intro u
  constructor
  · intro h x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · exact Or.inl (h x hx)
    · exact Or.inr (any_markAt2_ne u hxy)
  · intro h x hx
    rcases h x hx x hx with hmem | hno
    · exact hmem
    · rw [any_markAt2_diag u hx] at hno
      exact absurd hno (by decide)

end SnakeMSO
end Lax916827Proofs.Transducers
