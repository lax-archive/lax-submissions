import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
Finite counting facts for the collision-free random keys used by the program.
-/

namespace Lax235315Proofs.Construction.FiniteRandomKeys

open Finset

/-- All independent assignments of an `M`-valued key to a finite type. -/
def allAssignments (α : Type*) [Fintype α] [DecidableEq α] (M : ℕ) :
    Finset (α → Fin M) := Finset.univ

/-- Assignments on which the two designated coordinates collide. -/
def pairCollisions (α : Type*) [Fintype α] [DecidableEq α]
    (M : ℕ) (x y : α) : Finset (α → Fin M) :=
  (allAssignments α M).filter fun f => f x = f y

/-- Assignments having at least one collision on distinct coordinates. -/
def collisions (α : Type*) [Fintype α] [DecidableEq α] (M : ℕ) :
    Finset (α → Fin M) :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : α × α => p.1 ≠ p.2).biUnion
    fun p => pairCollisions α M p.1 p.2

theorem card_allAssignments (α : Type*) [Fintype α] [DecidableEq α]
    (M : ℕ) :
    (allAssignments α M).card = M ^ Fintype.card α := by
  simp [allAssignments]

/-- Fixing equality of two distinct coordinates removes one independent key
choice. -/
theorem card_pairCollisions_le (α : Type*) [Fintype α] [DecidableEq α]
    (M : ℕ) {x y : α} (hxy : x ≠ y) :
    (pairCollisions α M x y).card ≤ M ^ (Fintype.card α - 1) := by
  classical
  let rest := {z : α // z ≠ y}
  let restrict : {f // f ∈ pairCollisions α M x y} → (rest → Fin M) :=
    fun f z => f.1 z.1
  have hinj : Function.Injective restrict := by
    intro f g heq
    apply Subtype.ext
    funext z
    by_cases hzy : z = y
    · subst z
      have hfxy : f.1 x = f.1 y := by
        exact (Finset.mem_filter.mp f.2).2
      have hgxy : g.1 x = g.1 y := by
        exact (Finset.mem_filter.mp g.2).2
      rw [← hfxy, ← hgxy]
      exact congrFun heq ⟨x, hxy⟩
    · exact congrFun heq ⟨z, hzy⟩
  calc
    (pairCollisions α M x y).card =
        Fintype.card {f // f ∈ pairCollisions α M x y} := by simp
    _ ≤ Fintype.card (rest → Fin M) :=
      Fintype.card_le_of_injective restrict hinj
    _ = M ^ (Fintype.card α - 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]
      congr 1
      simp [rest, Fintype.card_subtype_compl (fun z : α => z = y)]

/-- Union bound for key collisions. -/
theorem card_collisions_le (α : Type*) [Fintype α] [DecidableEq α]
    (M : ℕ) :
    (collisions α M).card ≤
      Fintype.card α ^ 2 *
        M ^ (Fintype.card α - 1) := by
  classical
  let P := (Finset.univ ×ˢ Finset.univ).filter fun p : α × α => p.1 ≠ p.2
  calc
    (collisions α M).card ≤
        ∑ p ∈ P, (pairCollisions α M p.1 p.2).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, M ^ (Fintype.card α - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact card_pairCollisions_le α M (Finset.mem_filter.mp hp).2
    _ = P.card * M ^ (Fintype.card α - 1) := by
      simp
    _ ≤ Fintype.card α ^ 2 * M ^ (Fintype.card α - 1) := by
      apply Nat.mul_le_mul_right
      calc
        P.card ≤ (Finset.univ ×ˢ (Finset.univ : Finset α)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = Fintype.card α ^ 2 := by simp [pow_two]

/-- In probability form, the collision fraction is at most `a²/M`. -/
theorem collision_fraction_le (α : Type*) [Fintype α] [DecidableEq α]
    {M : ℕ} (hM : 0 < M) :
    ((collisions α M).card : ℝ) / (allAssignments α M).card ≤
      (Fintype.card α : ℝ) ^ 2 / M := by
  let a := Fintype.card α
  have hcard := card_collisions_le α M
  rw [card_allAssignments]
  by_cases ha : a = 0
  · have hc0 : (collisions α M).card = 0 := by
      exact Nat.le_zero.mp (by simpa [a, ha] using hcard)
    rw [hc0]
    simp [a, ha]
  · have ha' : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hpow : M ^ a = M ^ (a - 1) * M := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      simp [pow_succ]
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have hpowreal : (0 : ℝ) < M ^ (a - 1) := by positivity
    have hcardR : ((collisions α M).card : ℝ) ≤
        (a : ℝ) ^ 2 * (M : ℝ) ^ (a - 1) := by
      exact_mod_cast (show (collisions α M).card ≤
        a ^ 2 * M ^ (a - 1) from hcard)
    calc
      ((collisions α M).card : ℝ) / (M ^ a : ℕ) ≤
          ((a : ℝ) ^ 2 * (M : ℝ) ^ (a - 1)) / (M ^ a : ℕ) :=
        div_le_div_of_nonneg_right hcardR (by positivity)
      _ = (a : ℝ) ^ 2 / M := by
        rw [hpow]
        push_cast
        field_simp

end Lax235315Proofs.Construction.FiniteRandomKeys
