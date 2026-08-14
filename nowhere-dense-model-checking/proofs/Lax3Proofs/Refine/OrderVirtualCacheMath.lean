import Lax3Proofs.Refine.OrderVirtualOrient

/-!
# Linear heavy-row cache for virtual incoming two-walks

Regenerating an incoming row once for every outgoing occurrence of its root
is not globally controlled by an in-degree bound.  This file records the
heavy/light split needed by the executable repair.  Rows whose roots have
out-degree greater than `d²` are cached.  Their bounded incoming rows occupy
at most `n` slots in total; every uncached root is requested at most `d²`
times.

These are the two resource facts that a recursive virtual augmentation must
use.  Merely summing the unmodified nested-provider charge is insufficient.
-/

namespace Lax3Proofs.Refine.OrderVirtualCacheMath

open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamAugment
open Lax3Proofs.Refine.OrderVirtualOrient

variable {n : ℕ}

/-- Roots whose incoming row is worth retaining because the nested incoming
two-walk generator would otherwise request it more than `d²` times. -/
noncomputable def heavyRoots (D : Orientation n) (d : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => d * d < (outSet D v).card

@[simp] theorem mem_heavyRoots {D : Orientation n} {d : ℕ} {v : Fin n} :
    v ∈ heavyRoots D d ↔ d * d < (outSet D v).card := by
  simp [heavyRoots]

theorem out_card_le_sq_of_not_heavy {D : Orientation n} {d : ℕ} {v : Fin n}
    (hv : v ∉ heavyRoots D d) :
    (outSet D v).card ≤ d * d := by
  simpa [heavyRoots, Nat.not_lt] using hv

/-- Number of incoming-row entries retained by the heavy cache. -/
noncomputable def heavyInSlots (D : Orientation n) (d : ℕ) : ℕ :=
  ∑ v ∈ heavyRoots D d, (D.inN v).card

/-- Every heavy root contributes more than `d²` outgoing arcs. -/
theorem heavy_count_mul_sq_le_arcs {D : Orientation n} {d : ℕ} :
    (heavyRoots D d).card * (d * d) ≤
      ∑ v : Fin n, (outSet D v).card := by
  classical
  calc
    (heavyRoots D d).card * (d * d)
        = ∑ _v ∈ heavyRoots D d, d * d := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ heavyRoots D d, (outSet D v).card := by
          apply Finset.sum_le_sum
          intro v hv
          exact Nat.le_of_lt (mem_heavyRoots.1 hv)
    _ ≤ ∑ v : Fin n, (outSet D v).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- With in-degree at most `d`, all cached incoming rows together fit in one
carrier-sized arena. -/
theorem heavyInSlots_le {D : Orientation n} {d : ℕ}
    (hd : D.InDegLE d) : heavyInSlots D d ≤ n := by
  classical
  by_cases hd0 : d = 0
  · subst d
    have harcs : (∑ v : Fin n, (outSet D v).card) = 0 := by
      rw [sum_card_outSet]
      exact Finset.sum_eq_zero fun v _ => Nat.eq_zero_of_le_zero (hd v)
    have hempty : heavyRoots D 0 = ∅ := by
      ext v
      constructor
      · intro hv
        have hpos := mem_heavyRoots.1 hv
        have hle : (outSet D v).card ≤
            ∑ z : Fin n, (outSet D z).card :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ v) (f := fun z : Fin n => (outSet D z).card)
        rw [harcs] at hle
        omega
      · simp
    simp [heavyInSlots, hempty]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hslots :
        heavyInSlots D d ≤ (heavyRoots D d).card * d := by
      calc
        heavyInSlots D d
            ≤ ∑ _v ∈ heavyRoots D d, d := by
              apply Finset.sum_le_sum
              intro v _
              exact hd v
        _ = (heavyRoots D d).card * d := by
          rw [Finset.sum_const, smul_eq_mul]
    have harcs : (∑ v : Fin n, (outSet D v).card) ≤ n * d :=
      Lax3Proofs.Refine.OrderVirtualOrient.sum_orientSet_card_le .outgoing hd
    have hheavy := heavy_count_mul_sq_le_arcs (D := D) (d := d)
    have hmul : ((heavyRoots D d).card * d) * d ≤ n * d := by
      calc
        ((heavyRoots D d).card * d) * d =
            (heavyRoots D d).card * (d * d) := by ring
        _ ≤ ∑ v : Fin n, (outSet D v).card := hheavy
        _ ≤ n * d := harcs
    have hcount : (heavyRoots D d).card * d ≤ n :=
      le_of_mul_le_mul_right hmul hdpos
    exact hslots.trans hcount

/-- Exchange the two finite sums in an incoming-row walk.  The multiplicity
of a source root is exactly its out-degree. -/
theorem sum_inN_weight (D : Orientation n) (f : Fin n → ℕ) :
    (∑ v : Fin n, ∑ z ∈ D.inN v, f z) =
      ∑ z : Fin n, (outSet D z).card * f z := by
  classical
  calc
    (∑ v : Fin n, ∑ z ∈ D.inN v, f z) =
        ∑ v : Fin n, ∑ z : Fin n,
          if z ∈ D.inN v then f z else 0 := by
            apply Finset.sum_congr rfl
            intro v _
            simp
    _ = ∑ z : Fin n, ∑ v : Fin n,
          if z ∈ D.inN v then f z else 0 := Finset.sum_comm
    _ = ∑ z : Fin n, (outSet D z).card * f z := by
          apply Finset.sum_congr rfl
          intro z _
          simp only [outSet, Finset.card_filter]
          rw [← Finset.sum_filter]
          simp [Finset.sum_const, smul_eq_mul]

/-- Provider charge paid only on uncached roots during all incoming
two-walk rows. -/
noncomputable def lightIncomingCharge (D : Orientation n) (d : ℕ)
    (kappa : Fin n → ℕ) : ℕ :=
  ∑ v : Fin n, ∑ z ∈ D.inN v,
    if z ∈ heavyRoots D d then 0 else kappa z

/-- Every uncached provider is reinvoked at most `d²` times.  This is the
time half of the heavy/light repair. -/
theorem lightIncomingCharge_le (D : Orientation n) (d : ℕ)
    (kappa : Fin n → ℕ) :
    lightIncomingCharge D d kappa ≤
      d * d * (∑ z : Fin n, kappa z) := by
  classical
  rw [lightIncomingCharge, sum_inN_weight]
  calc
    (∑ z : Fin n,
        (outSet D z).card *
          (if z ∈ heavyRoots D d then 0 else kappa z))
        ≤ ∑ z : Fin n, (d * d) * kappa z := by
          apply Finset.sum_le_sum
          intro z _
          by_cases hz : z ∈ heavyRoots D d
          · simp [hz]
          · simp only [hz, if_false]
            exact Nat.mul_le_mul_right _ (out_card_le_sq_of_not_heavy hz)
    _ = d * d * (∑ z : Fin n, kappa z) := by
      rw [Finset.mul_sum]

/-! ## Axiom audit -/

#print axioms heavyInSlots_le
#print axioms sum_inN_weight
#print axioms lightIncomingCharge_le

end Lax3Proofs.Refine.OrderVirtualCacheMath
