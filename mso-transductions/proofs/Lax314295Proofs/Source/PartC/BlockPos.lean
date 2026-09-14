/-
Positions of a string over the alphabet `A + 1`, and their blocks.

The prime functions `mapReverse` and `mapDuplicate` act separately on each
maximal block of the input that avoids the separator `#` (modelled by `none`).
The first-order transductions that compute them describe the blocks by the
first-order formula "there is no separator between `x` and `y`", and this file
develops the corresponding combinatorics:

* `Transducers.SepAt w p`: the position `p` of `w` carries the separator;
* `Transducers.SameBlk w p q`: `p` and `q` are positions of `w` and no position
  between them (inclusive) carries the separator -- that is, `p` and `q` lie in
  the same block and neither is a separator;

together with the basic properties of `SameBlk` (it is symmetric, transitive,
convex) and its computation on a string of the shape
`u.map some ++ none :: w'`, which is the shape of a string presented by its
blocks (`Transducers.blockStr`).
-/
import Lax916827Proofs.Source.PartC.RegPair
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

open RegPair

variable {A : Type}

/-- The position `p` of `w` carries the separator. -/
def SepAt (w : List (Option A)) (p : ℕ) : Prop := w[p]? = some none

/-- `p` and `q` are positions of `w` with no separator anywhere between them
(endpoints included).  Equivalently: neither is a separator and they lie in the
same maximal separator-free block. -/
def SameBlk (w : List (Option A)) (p q : ℕ) : Prop :=
  p < w.length ∧ q < w.length ∧ ∀ r, min p q ≤ r → r ≤ max p q → ¬ SepAt w r

/-! ## Basic properties -/

lemma sameBlk_symm {w : List (Option A)} {p q : ℕ} (h : SameBlk w p q) : SameBlk w q p := by
  obtain ⟨hp, hq, hr⟩ := h
  refine ⟨hq, hp, fun r h₁ h₂ => hr r ?_ ?_⟩
  · rwa [min_comm]
  · rwa [max_comm]

lemma sameBlk_comm {w : List (Option A)} {p q : ℕ} : SameBlk w p q ↔ SameBlk w q p :=
  ⟨sameBlk_symm, sameBlk_symm⟩

lemma not_sepAt_of_sameBlk_left {w : List (Option A)} {p q : ℕ} (h : SameBlk w p q) :
    ¬ SepAt w p :=
  h.2.2 p (min_le_left _ _) (le_max_left _ _)

lemma not_sepAt_of_sameBlk_right {w : List (Option A)} {p q : ℕ} (h : SameBlk w p q) :
    ¬ SepAt w q :=
  not_sepAt_of_sameBlk_left (sameBlk_symm h)

lemma sameBlk_self_iff {w : List (Option A)} {p : ℕ} :
    SameBlk w p p ↔ p < w.length ∧ ¬ SepAt w p := by
  constructor
  · intro h; exact ⟨h.1, not_sepAt_of_sameBlk_left h⟩
  · rintro ⟨hp, hs⟩
    refine ⟨hp, hp, fun r h₁ h₂ => ?_⟩
    simp only [min_self] at h₁
    simp only [max_self] at h₂
    have : r = p := le_antisymm h₂ h₁
    rw [this]; exact hs

/-- `SameBlk` is convex: any position between two positions of a block is in the
same block. -/
lemma sameBlk_of_between {w : List (Option A)} {p q r : ℕ} (h : SameBlk w p q)
    (h₁ : min p q ≤ r) (h₂ : r ≤ max p q) : SameBlk w p r := by
  obtain ⟨hp, hq, hs⟩ := h
  have hrlen : r < w.length := by omega
  exact ⟨hp, hrlen, fun s hs₁ hs₂ => hs s (by omega) (by omega)⟩

lemma sameBlk_trans {w : List (Option A)} {p q r : ℕ} (h₁ : SameBlk w p q)
    (h₂ : SameBlk w q r) : SameBlk w p r := by
  refine ⟨h₁.1, h₂.2.1, fun s hs₁ hs₂ => ?_⟩
  by_cases hc : min p q ≤ s ∧ s ≤ max p q
  · exact h₁.2.2 s hc.1 hc.2
  · exact h₂.2.2 s (by omega) (by omega)

lemma not_sameBlk_trans {w : List (Option A)} {p q r : ℕ} (h₁ : SameBlk w p q)
    (h₂ : ¬ SameBlk w q r) : ¬ SameBlk w p r :=
  fun h => h₂ (sameBlk_trans (sameBlk_symm h₁) h)

/-- If `x` and `y` are in the same block, `z` is not in the block of `y` and
`y ≤ z`, then `x ≤ z`: the whole block of `y` is at or before `z`. -/
lemma le_of_sameBlk_of_not_sameBlk {w : List (Option A)} {x y z : ℕ} (hxy : SameBlk w x y)
    (hyz : ¬ SameBlk w y z) (h : y ≤ z) : x ≤ z := by
  by_contra hlt
  push_neg at hlt
  exact hyz (sameBlk_of_between (sameBlk_symm hxy) (by omega) (by omega))

/-- The mirror image of `le_of_sameBlk_of_not_sameBlk`: if `y` and `z` are in
the same block, `x` is not in the block of `y` and `x ≤ y`, then `x ≤ z`. -/
lemma le_of_not_sameBlk_of_sameBlk {w : List (Option A)} {x y z : ℕ} (hxy : ¬ SameBlk w x y)
    (hyz : SameBlk w y z) (h : x ≤ y) : x ≤ z := by
  by_contra hlt
  push_neg at hlt
  exact hxy (sameBlk_symm (sameBlk_of_between hyz (by omega) (by omega)))

/-! ## Positions of a string with a distinguished first block -/

section Decomp

variable (u : List A) (w' : List (Option A))

/-- The length of `u # w'`. -/
lemma length_block_decomp :
    (u.map some ++ none :: w').length = u.length + 1 + w'.length := by
  simp [Nat.add_comm, Nat.add_left_comm]

lemma getElem?_block_left {p : ℕ} (hp : p < u.length) :
    (u.map some ++ none :: w')[p]? = some (some u[p]) := by
  rw [List.getElem?_append_left (by simpa using hp)]
  simp [List.getElem?_eq_getElem (show p < (u.map some).length by simpa using hp)]

lemma getElem?_block_mid : (u.map some ++ none :: w')[u.length]? = some (none : Option A) := by
  rw [List.getElem?_append_right (by simp)]
  simp

lemma getElem?_block_right (k : ℕ) :
    (u.map some ++ none :: w')[u.length + 1 + k]? = w'[k]? := by
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map]
  have : u.length + 1 + k - u.length = k + 1 := by omega
  rw [this]
  simp

lemma not_sepAt_block_left {p : ℕ} (hp : p < u.length) :
    ¬ SepAt (u.map some ++ none :: w') p := by
  rw [SepAt, getElem?_block_left u w' hp]
  simp

lemma sepAt_block_mid : SepAt (u.map some ++ none :: w') u.length := by
  rw [SepAt, getElem?_block_mid]

lemma sepAt_block_right (k : ℕ) :
    SepAt (u.map some ++ none :: w') (u.length + 1 + k) ↔ SepAt w' k := by
  rw [SepAt, SepAt, getElem?_block_right]

/-- Two positions of the first block are in the same block. -/
lemma sameBlk_block_left {p q : ℕ} (hp : p < u.length) (hq : q < u.length) :
    SameBlk (u.map some ++ none :: w') p q := by
  refine ⟨by rw [length_block_decomp]; omega, by rw [length_block_decomp]; omega,
    fun r _ h₂ => ?_⟩
  have : r < u.length := lt_of_le_of_lt h₂ (max_lt hp hq)
  exact not_sepAt_block_left u w' this

/-- A position of the first block and a position at or after the separator are
in different blocks. -/
lemma not_sameBlk_block_cross {p q : ℕ} (hp : p < u.length) (hq : u.length ≤ q) :
    ¬ SameBlk (u.map some ++ none :: w') p q := by
  intro h
  refine h.2.2 u.length ?_ ?_ (sepAt_block_mid u w')
  · exact le_trans (min_le_left _ _) hp.le
  · exact le_trans hq (le_max_right _ _)

/-- Positions after the separator: the blocks are those of the remaining
string. -/
lemma sameBlk_block_right (i j : ℕ) :
    SameBlk (u.map some ++ none :: w') (u.length + 1 + i) (u.length + 1 + j) ↔
      SameBlk w' i j := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    rw [length_block_decomp] at h₁ h₂
    refine ⟨by omega, by omega, fun r hr₁ hr₂ hsep => ?_⟩
    refine h₃ (u.length + 1 + r) ?_ ?_ ?_
    · rcases le_total i j with h | h
      · simp only [min_eq_left h] at hr₁ ⊢
        omega
      · simp only [min_eq_right h] at hr₁ ⊢
        omega
    · rcases le_total i j with h | h
      · simp only [max_eq_right h] at hr₂ ⊢
        omega
      · simp only [max_eq_left h] at hr₂ ⊢
        omega
    · rwa [sepAt_block_right]
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨by rw [length_block_decomp]; omega, by rw [length_block_decomp]; omega,
      fun r hr₁ hr₂ hsep => ?_⟩
    have hmin : min (u.length + 1 + i) (u.length + 1 + j) = u.length + 1 + min i j := by
      rcases le_total i j with h | h
      · simp [min_eq_left h, min_eq_left (show u.length + 1 + i ≤ u.length + 1 + j by omega)]
      · simp [min_eq_right h, min_eq_right (show u.length + 1 + j ≤ u.length + 1 + i by omega)]
    have hmax : max (u.length + 1 + i) (u.length + 1 + j) = u.length + 1 + max i j := by
      rcases le_total i j with h | h
      · simp [max_eq_right h, max_eq_right (show u.length + 1 + i ≤ u.length + 1 + j by omega)]
      · simp [max_eq_left h, max_eq_left (show u.length + 1 + j ≤ u.length + 1 + i by omega)]
    rw [hmin] at hr₁
    rw [hmax] at hr₂
    have hr : r = u.length + 1 + (r - (u.length + 1)) := by omega
    rw [hr, sepAt_block_right] at hsep
    exact h₃ _ (by omega) (by omega) hsep

end Decomp

/-! ## Strings with no separator -/

lemma not_sepAt_map_some (u : List A) (p : ℕ) : ¬ SepAt (u.map some) p := by
  rw [SepAt]
  rcases lt_or_ge p u.length with h | h
  · rw [List.getElem?_eq_getElem (show p < (u.map some).length by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    simp

lemma sameBlk_map_some_iff (u : List A) (p q : ℕ) :
    SameBlk (u.map some) p q ↔ p < u.length ∧ q < u.length := by
  constructor
  · rintro ⟨h₁, h₂, -⟩
    simp only [List.length_map] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by simpa using h₁, by simpa using h₂, fun r _ _ => not_sepAt_map_some u r⟩

/-! ## Every string is presented by its blocks -/

lemma blockStr_splitSep (w : List (Option A)) : blockStr (splitSep w) = w := by
  have h := mapLift_eq_blockStr (id : List A → List A) w
  rw [mapLift_id] at h
  simpa using h.symm

end Lax314295Proofs.Transducers
