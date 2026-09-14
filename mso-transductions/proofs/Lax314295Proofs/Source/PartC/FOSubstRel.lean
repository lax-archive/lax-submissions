/-
Substitution of formulas for the label tests of a first-order formula, used for
the implication "aperiodic ⇒ first-order definable" of Theorem `thm:logic-aperiodic` of
*Transducers* (M. Bojańczyk): "it is also easy to see -- using substitution of
formulas -- that first-order definable Mealy machines are closed under
composition".

If `f : A* → B*` is length preserving and prefix determined, then the `p`-th
letter of `f w` is determined by the prefix `w` of length `p + 1`; so if, for
every letter `b` of `B`, the language of inputs whose output *ends* with `b` is
defined by a first-order sentence `χ b`, then the label test `b (x_i)` of a
formula over `B` can be replaced by the relativisation `relLe i (χ b)` of
`RequestProject/PartC/FORel.lean`, which says that `χ b` holds in the prefix
that ends at the position `x_i`.  No capture-avoiding machinery is needed: the
formulas `χ b` are sentences, and the only requirement is that the variable `i`
does not occur in them, which is arranged by shifting their variables up.
-/
import Lax314295Proofs.Source.PartC.FORename
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MSO

variable {A B : Type}

/-- Replace every label test `b (x_i)` of a formula over `B` by the statement
that the sentence `χ b` holds in the prefix ending at the position `x_i`. -/
def substRel (χ : B → MSO A) : MSO B → MSO A
  | le i j => le i j
  | lab b i => relLe i (χ b)
  | mem i j => mem i j
  | not φ => not (substRel χ φ)
  | and φ ψ => and (substRel χ φ) (substRel χ ψ)
  | or φ ψ => or (substRel χ φ) (substRel χ ψ)
  | exFO i φ => exFO i (substRel χ φ)
  | exSO i φ => exSO i (substRel χ φ)

lemma isFO_substRel {χ : B → MSO A} (hχ : ∀ b, (χ b).IsFO) :
    ∀ φ : MSO B, φ.IsFO → (substRel χ φ).IsFO := by
  intro φ
  induction φ with
  | le i j => exact fun _ => trivial
  | lab b i => exact fun _ => isFO_relLe i (hχ b)
  | mem i j => exact fun h => h.elim
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | exFO i φ ih => exact ih
  | exSO i φ _ => exact fun h => h.elim

lemma freeFO_substRel {χ : B → MSO A} (hχ : ∀ b, (χ b).freeFO = ∅) :
    ∀ φ : MSO B, (substRel χ φ).freeFO ⊆ φ.freeFO := by
  intro φ
  induction φ with
  | le i j => exact subset_rfl
  | lab b i =>
      refine subset_trans (freeFO_relLe i (χ b)) ?_
      rw [hχ b, Set.empty_union]
      exact subset_rfl
  | mem i j => exact subset_rfl
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => exact Set.union_subset_union ihφ ihψ
  | or φ ψ ihφ ihψ => exact Set.union_subset_union ihφ ihψ
  | exFO i φ ih => exact Set.diff_subset_diff_left ih
  | exSO i φ ih => exact ih

/-- Correctness of the substitution: if the sentence `χ b` defines, on the
prefixes of the input, the fact that the last letter produced by `f` is `b`,
then a formula holds in `f w` if and only if its substitution holds in `w`. -/
lemma sat_substRel {χ : B → MSO A} (hχfo : ∀ b, (χ b).IsFO) (hχfree : ∀ b, (χ b).freeFO = ∅)
    {f : List A → List B} (hlen : ∀ w : List A, (f w).length = w.length)
    (hχsat : ∀ (b : B) (w : List A) (p : ℕ), p < w.length →
      (Sat (w.take (p + 1)) (fun _ => 0) (fun _ => ∅) (χ b) ↔ (f w)[p]? = some b)) :
    ∀ (φ : MSO B), φ.IsFO → (∀ i ∈ φ.foVars, ∀ b, i ∉ (χ b).foVars) →
      ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), (∀ i ∈ φ.freeFO, fo i < w.length) →
        (Sat (f w) fo so φ ↔ Sat w fo so (substRel χ φ)) := by
  intro φ
  induction φ with
  | le i j => intro _ _ w fo so _; exact Iff.rfl
  | lab b i =>
      intro _ hfresh w fo so hpos
      have hi : fo i < w.length := hpos i rfl
      have hnotin : i ∉ (χ b).foVars := hfresh i (by simp [foVars]) b
      have hcond : ∀ j ∈ (χ b).freeFO, fo j ≤ fo i := by
        intro j hj
        rw [hχfree b] at hj
        exact hj.elim
      show (f w)[fo i]? = some b ↔ Sat w fo so (relLe i (χ b))
      rw [sat_relLe w i (χ b) (hχfo b) hnotin fo so hcond,
        sat_sentence_congr (hχfo b) (hχfree b) (w.take (fo i + 1)) fo (fun _ => 0)
          so (fun _ => ∅)]
      exact (hχsat b w (fo i) hi).symm
  | mem i j => intro h; exact h.elim
  | not φ ih =>
      intro hfo hfresh w fo so hpos
      show ¬ Sat (f w) fo so φ ↔ ¬ Sat w fo so (substRel χ φ)
      rw [ih hfo hfresh w fo so hpos]
  | and φ ψ ihφ ihψ =>
      intro hfo hfresh w fo so hpos
      show (Sat (f w) fo so φ ∧ Sat (f w) fo so ψ) ↔ _
      rw [ihφ hfo.1 (fun i hi => hfresh i (by simp [foVars, hi])) w fo so
          (fun i hi => hpos i (Or.inl hi)),
        ihψ hfo.2 (fun i hi => hfresh i (by simp [foVars, hi])) w fo so
          (fun i hi => hpos i (Or.inr hi))]
      exact Iff.rfl
  | or φ ψ ihφ ihψ =>
      intro hfo hfresh w fo so hpos
      show (Sat (f w) fo so φ ∨ Sat (f w) fo so ψ) ↔ _
      rw [ihφ hfo.1 (fun i hi => hfresh i (by simp [foVars, hi])) w fo so
          (fun i hi => hpos i (Or.inl hi)),
        ihψ hfo.2 (fun i hi => hfresh i (by simp [foVars, hi])) w fo so
          (fun i hi => hpos i (Or.inr hi))]
      exact Iff.rfl
  | exFO i φ ih =>
      intro hfo hfresh w fo so hpos
      have hfresh' : ∀ j ∈ φ.foVars, ∀ b, j ∉ (χ b).foVars :=
        fun j hj => hfresh j (by simp [foVars, hj])
      show (∃ p < (f w).length, Sat (f w) (Function.update fo i p) so φ) ↔
        (∃ p < w.length, Sat w (Function.update fo i p) so (substRel χ φ))
      rw [hlen w]
      constructor
      · rintro ⟨p, hp, hsat⟩
        refine ⟨p, hp, (ih hfo hfresh' w _ so ?_).mp hsat⟩
        intro j hj
        by_cases hji : j = i
        · rw [hji, Function.update_self]; exact hp
        · rw [Function.update_of_ne hji]; exact hpos j ⟨hj, hji⟩
      · rintro ⟨p, hp, hsat⟩
        refine ⟨p, hp, (ih hfo hfresh' w _ so ?_).mpr hsat⟩
        intro j hj
        by_cases hji : j = i
        · rw [hji, Function.update_self]; exact hp
        · rw [Function.update_of_ne hji]; exact hpos j ⟨hj, hji⟩
  | exSO i φ _ => intro h; exact h.elim

end MSO
end Lax314295Proofs.Transducers
