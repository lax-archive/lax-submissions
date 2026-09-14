/-
**The blocks of a chain of pieces.**

A chain of pieces (`Transducers.TwoWay.Chk.ChainData`) cuts the input into
`N + 2` blocks, the `m`-th one being the factor between the positions `Y m` and
`Y (m+1)`.  The `0`-th block is always empty and the last one may be; all the
others are nonempty.  This file provides the inverse of the cutting map: the
index `Transducers.TwoWay.Chk.ChainData.blkOf` of the block containing a
position, and the two facts that the annotation built in
`RequestProject/PartC/SnakeChkBuild.lean` needs -- that it takes its values in
`{1, …, N+1}`, and that it either stays the same or increases by one when the
position advances by one.
-/
import Lax916827Proofs.Source.PartC.SnakeChkData
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q : Type}

namespace ChainData

variable {M : TwoWay A B Q} {K : ℕ} {w : List A} (d : ChainData M K w)

/-- The index of the block of the chain containing the position `j`. -/
def blkOf (j : ℕ) : ℕ := Nat.findGreatest (fun m => d.Y m ≤ j) (d.N + 1)

lemma blkOf_def (j : ℕ) : d.blkOf j = Nat.findGreatest (fun m => d.Y m ≤ j) (d.N + 1) := rfl

lemma blkOf_le (j : ℕ) : d.blkOf j ≤ d.N + 1 := Nat.findGreatest_le _

lemma one_le_blkOf (j : ℕ) : 1 ≤ d.blkOf j :=
  Nat.le_findGreatest (P := fun m => d.Y m ≤ j) (n := d.N + 1) (m := 1) (by omega)
    (by show d.Y 1 ≤ j; rw [d.Y_one]; exact Nat.zero_le _)

lemma Y_blkOf_le (j : ℕ) : d.Y (d.blkOf j) ≤ j :=
  Nat.findGreatest_spec (P := fun m => d.Y m ≤ j) (n := d.N + 1) (m := 1) (by omega)
    (by show d.Y 1 ≤ j; rw [d.Y_one]; exact Nat.zero_le _)

lemma lt_Y_blkOf_succ {j : ℕ} (hj : j < w.length) : j < d.Y (d.blkOf j + 1) := by
  rcases Nat.lt_or_ge (d.blkOf j) (d.N + 1) with hlt | hge
  · have hkey : ¬ (d.Y (d.blkOf j + 1) ≤ j) := by
      refine Nat.findGreatest_is_greatest (P := fun m => d.Y m ≤ j) (n := d.N + 1) ?_ (by omega)
      rw [← blkOf_def]
      omega
    omega
  · have hb : d.blkOf j = d.N + 1 := le_antisymm (d.blkOf_le j) hge
    have hlast : d.Y (d.N + 2) = w.length := d.Y_last
    rw [hb]
    have h2 : d.Y (d.N + 1 + 1) = d.Y (d.N + 2) := rfl
    omega

lemma blkOf_eq {j m : ℕ} (hm : m ≤ d.N + 1) (h1 : d.Y m ≤ j) (h2 : j < d.Y (m + 1)) :
    d.blkOf j = m := by
  have hge : m ≤ d.blkOf j :=
    Nat.le_findGreatest (P := fun m => d.Y m ≤ j) (n := d.N + 1) hm h1
  have hle : d.blkOf j ≤ m := by
    by_contra hcon
    push_neg at hcon
    have hy : d.Y (m + 1) ≤ d.Y (d.blkOf j) := d.Y_le (by omega)
    have := d.Y_blkOf_le j
    omega
  omega

lemma blkOf_zero : d.blkOf 0 = 1 := by
  have h1 : d.Y 0 < d.Y 2 := d.Y_lt 0 (Nat.zero_le _)
  have h2 : d.Y 0 = 0 := d.Y_zero
  refine d.blkOf_eq (by omega) (le_of_eq d.Y_one) ?_
  show 0 < d.Y 2
  omega

/-- **A position either lies in the same block as its predecessor, or starts the
next block.** -/
lemma blkOf_succ {j : ℕ} (hj : j + 1 < w.length) :
    d.blkOf (j + 1) = d.blkOf j ∨
      (d.blkOf (j + 1) = d.blkOf j + 1 ∧ d.Y (d.blkOf j + 1) = j + 1) := by
  have hjl : j < w.length := by omega
  have hm : d.Y (d.blkOf j) ≤ j := d.Y_blkOf_le j
  have hm2 : j < d.Y (d.blkOf j + 1) := d.lt_Y_blkOf_succ hjl
  have hge : d.blkOf j ≤ d.blkOf (j + 1) :=
    Nat.le_findGreatest (P := fun m => d.Y m ≤ j + 1) (n := d.N + 1) (d.blkOf_le j) (by omega)
  have hle : d.blkOf (j + 1) ≤ d.blkOf j + 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : d.Y (d.blkOf j + 2) ≤ d.Y (d.blkOf (j + 1)) := d.Y_le (by omega)
    have h2 : d.Y (d.blkOf (j + 1)) ≤ j + 1 := d.Y_blkOf_le (j + 1)
    have h4 : d.blkOf (j + 1) ≤ d.N + 1 := d.blkOf_le (j + 1)
    have hnb : d.blkOf j + 1 ≤ d.N := by omega
    have h5 : d.Y (d.blkOf j + 1) < d.Y (d.blkOf j + 1 + 1) :=
      d.Y_blk (d.blkOf j + 1) (by omega) hnb
    have h6 : d.Y (d.blkOf j + 1 + 1) = d.Y (d.blkOf j + 2) := rfl
    omega
  rcases Nat.eq_or_lt_of_le hge with h | h
  · exact Or.inl h.symm
  · have heq : d.blkOf (j + 1) = d.blkOf j + 1 := by omega
    have h2 : d.Y (d.blkOf (j + 1)) ≤ j + 1 := d.Y_blkOf_le (j + 1)
    rw [heq] at h2
    exact Or.inr ⟨heq, by omega⟩

end ChainData

end Chk

end TwoWay

end Lax916827Proofs.Transducers
