import Lax235315Proofs.Construction.NearAccumulateSource
import Mathlib.Tactic

/-! Finite-prefix semantics of the batched degree/intersection sweep. -/

namespace Lax235315Proofs.Construction.NearSweepMath

open Lax235315Proofs.Construction.NeighborScan
open Lax235315Proofs.Construction.NearAccumulateSource

/-- The distinct active `B` targets in vertex `a`'s CSR block. -/
def neighborBlock (target off activeB : ℕ → ℕ) (a : ℕ) : Finset ℕ :=
  activeTargets target activeB (off a) (off (a + 1))

/-- Number of processed active `A` vertices adjacent to `b`. -/
def degreePrefix (target off activeA activeB : ℕ → ℕ)
    (a b : ℕ) : ℕ :=
  ((Finset.range a).filter fun u =>
    activeA u = 1 ∧ b ∈ neighborBlock target off activeB u).card

/-- Number of processed active `A` vertices adjacent to both `b` and its
chosen representative. -/
def commonPrefix (target off activeA activeB rep : ℕ → ℕ)
    (a b : ℕ) : ℕ :=
  ((Finset.range a).filter fun u =>
    activeA u = 1 ∧ b ∈ neighborBlock target off activeB u ∧
      rep b ∈ neighborBlock target off activeB u).card

@[simp] theorem degreePrefix_zero
    (target off activeA activeB : ℕ → ℕ) (b : ℕ) :
    degreePrefix target off activeA activeB 0 b = 0 := by
  simp [degreePrefix]

@[simp] theorem commonPrefix_zero
    (target off activeA activeB rep : ℕ → ℕ) (b : ℕ) :
    commonPrefix target off activeA activeB rep 0 b = 0 := by
  simp [commonPrefix]

theorem degreePrefix_succ_of_active
    {target off activeA activeB : ℕ → ℕ} {a : ℕ}
    (ha : activeA a = 1) :
    degreePrefix target off activeA activeB (a + 1) =
      addOn (neighborBlock target off activeB a)
        (degreePrefix target off activeA activeB a) := by
  funext b
  rw [degreePrefix, Finset.range_add_one,
    Finset.filter_insert]
  by_cases hb : b ∈ neighborBlock target off activeB a
  · simp [degreePrefix, addOn, ha, hb, Finset.card_insert_of_notMem]
  · simp [degreePrefix, addOn, ha, hb]

theorem commonPrefix_succ_of_active
    {target off activeA activeB rep : ℕ → ℕ} {a : ℕ}
    (ha : activeA a = 1) :
    commonPrefix target off activeA activeB rep (a + 1) =
      addCommon (neighborBlock target off activeB a)
        (neighborBlock target off activeB a) rep
        (commonPrefix target off activeA activeB rep a) := by
  funext b
  rw [commonPrefix, Finset.range_add_one,
    Finset.filter_insert]
  by_cases hb : b ∈ neighborBlock target off activeB a ∧
      rep b ∈ neighborBlock target off activeB a
  · simp [commonPrefix, addCommon, ha, hb, Finset.card_insert_of_notMem]
  · simp [commonPrefix, addCommon, ha, hb]

theorem degreePrefix_succ_of_inactive
    {target off activeA activeB : ℕ → ℕ} {a : ℕ}
    (ha : activeA a ≠ 1) :
    degreePrefix target off activeA activeB (a + 1) =
      degreePrefix target off activeA activeB a := by
  funext b
  rw [degreePrefix, Finset.range_add_one,
    Finset.filter_insert]
  simp [degreePrefix, ha]

theorem commonPrefix_succ_of_inactive
    {target off activeA activeB rep : ℕ → ℕ} {a : ℕ}
    (ha : activeA a ≠ 1) :
    commonPrefix target off activeA activeB rep (a + 1) =
      commonPrefix target off activeA activeB rep a := by
  funext b
  rw [commonPrefix, Finset.range_add_one,
    Finset.filter_insert]
  simp [commonPrefix, ha]

theorem degreePrefix_le (target off activeA activeB : ℕ → ℕ)
    (a b : ℕ) : degreePrefix target off activeA activeB a b ≤ a := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range a)

theorem commonPrefix_le (target off activeA activeB rep : ℕ → ℕ)
    (a b : ℕ) : commonPrefix target off activeA activeB rep a b ≤ a := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range a)

end Lax235315Proofs.Construction.NearSweepMath
