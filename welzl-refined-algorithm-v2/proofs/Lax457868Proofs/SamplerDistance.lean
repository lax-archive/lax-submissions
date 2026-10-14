import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Finite-set distance lemmas used by the refined sampler.  The distance is
the size of the symmetric difference, matching the disagreement quantity in
the public sample contract.
-/

namespace Lax457868Proofs.SamplerDistance

/-- The number of elements on which two finite sets disagree. -/
def disagreement {α : Type*} [DecidableEq α] (X Y : Finset α) : ℕ :=
  ((X \ Y) ∪ (Y \ X)).card

/-- Disagreement is symmetric. -/
lemma disagreement_symm {α : Type*} [DecidableEq α] (X Y : Finset α) :
    disagreement X Y = disagreement Y X := by
  unfold disagreement
  rw [Finset.union_comm]

/-- A finite set has zero disagreement with itself. -/
lemma disagreement_self {α : Type*} [DecidableEq α] (X : Finset α) :
    disagreement X X = 0 := by
  simp [disagreement]

/-- Symmetric-difference cardinality satisfies the triangle inequality. -/
lemma disagreement_triangle {α : Type*} [DecidableEq α]
    (X Y Z : Finset α) : disagreement X Z ≤ disagreement X Y + disagreement Y Z := by
  unfold disagreement
  have hsub : (X \ Z) ∪ (Z \ X) ⊆
      ((X \ Y) ∪ (Y \ X)) ∪ ((Y \ Z) ∪ (Z \ Y)) := by
    intro a ha
    simp only [Finset.mem_union, Finset.mem_sdiff] at ha ⊢
    rcases ha with ⟨hxa, hza⟩ | ⟨hza, hxa⟩
    · by_cases hya : a ∈ Y
      · exact Or.inr (Or.inl ⟨hya, hza⟩)
      · exact Or.inl (Or.inl ⟨hxa, hya⟩)
    · by_cases hya : a ∈ Y
      · exact Or.inl (Or.inr ⟨hya, hxa⟩)
      · exact Or.inr (Or.inr ⟨hza, hya⟩)
  calc
    ((X \ Z) ∪ (Z \ X)).card ≤
        (((X \ Y) ∪ (Y \ X)) ∪ ((Y \ Z) ∪ (Z \ Y))).card :=
      Finset.card_le_card hsub
    _ ≤ ((X \ Y) ∪ (Y \ X)).card + ((Y \ Z) ∪ (Z \ Y)).card :=
      Finset.card_union_le _ _

/-- Two nonexceptional sets disagree on at most `k` elements when each is
within one third of `k` from the reference set. -/
lemma disagreement_le_of_third_bounds {α : Type*} [DecidableEq α]
    (X Y R : Finset α) (k : ℕ)
    (hX : 3 * disagreement X R ≤ k)
    (hY : 3 * disagreement Y R ≤ k) :
    disagreement X Y ≤ k := by
  have htri := disagreement_triangle X R Y
  rw [disagreement_symm R Y] at htri
  omega

/-- A mild exceptional set and a nonexceptional set disagree on at most `k`
elements under the corresponding two-thirds and one-third bounds. -/
lemma disagreement_le_of_mild_exception_bounds {α : Type*} [DecidableEq α]
    (X Y R : Finset α) (k : ℕ)
    (hX : 3 * disagreement X R ≤ 2 * k)
    (hY : 3 * disagreement Y R ≤ k) :
    disagreement X Y ≤ k := by
  have htri := disagreement_triangle X R Y
  rw [disagreement_symm R Y] at htri
  omega

/-- If `B` is far from a representative and `V` is close to that
representative, more than half the disagreements between `B` and the
representative are also disagreements between `B` and `V`. -/
lemma disagreement_inter_majority {α : Type*} [DecidableEq α]
    (B R V : Finset α) (k : ℕ)
    (hfar : 2 * k < 3 * disagreement B R)
    (hnear : 3 * disagreement V R ≤ k) :
    2 * (((B \ R) ∪ (R \ B)) ∩ ((B \ V) ∪ (V \ B))).card >
      ((B \ R) ∪ (R \ B)).card := by
  let X := (B \ R) ∪ (R \ B)
  let D := (B \ V) ∪ (V \ B)
  have hmiss : X \ D ⊆ (V \ R) ∪ (R \ V) := by
    intro a ha
    simp only [X, D, Finset.mem_sdiff, Finset.mem_union] at ha ⊢
    rcases ha.1 with ⟨hB, hR⟩ | ⟨hR, hB⟩
    · exact Or.inl ⟨by
        by_contra hnotV
        exact ha.2 (Or.inl ⟨hB, hnotV⟩), hR⟩
    · exact Or.inr ⟨hR, by
        intro hV
        exact ha.2 (Or.inr ⟨hV, hB⟩)⟩
  have hsplit : X = (X ∩ D) ∪ (X \ D) := by
    ext a
    by_cases hX : a ∈ X <;> by_cases hD : a ∈ D <;> simp [hX, hD]
  have hcard : X.card ≤ (X ∩ D).card + disagreement V R := by
    calc
      X.card = ((X ∩ D) ∪ (X \ D)).card := congrArg Finset.card hsplit
      _ ≤ (X ∩ D).card + (X \ D).card := Finset.card_union_le _ _
      _ ≤ (X ∩ D).card + disagreement V R := by
        exact Nat.add_le_add_left (Finset.card_le_card hmiss) _
  change 2 * k < 3 * X.card at hfar
  change 3 * disagreement V R ≤ k at hnear
  have htwo : 2 * disagreement V R < X.card := by omega
  have hmajority : X.card < 2 * (X ∩ D).card := by omega
  simpa [X, D] using hmajority

end Lax457868Proofs.SamplerDistance
