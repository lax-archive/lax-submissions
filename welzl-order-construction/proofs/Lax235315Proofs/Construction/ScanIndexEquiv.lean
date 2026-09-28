import Lax235315Proofs.Construction.PartitionSource
import Mathlib.Tactic

/-! The source scan order is an explicit enumeration of the active vertices. -/

namespace Lax235315Proofs.Construction.ScanIndexEquiv

open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PartitionSource

/-- Vertices whose active-array cell is one. -/
abbrev ActiveVertex (n : ℕ) (active : ℕ → ℕ) :=
  {v : Fin n // active v.val = 1}

/-- The active vertex at one position in the actual increasing source scan. -/
def scanIndexFun (active : ℕ → ℕ) (n : ℕ) :
    Fin (activeVertices n active).card → ActiveVertex n active := by
  intro i
  let xs := scanList active 0 n
  have hlen : xs.length = (activeVertices n active).card := by
    exact scanList_length_eq_activeVertices_card active n
  have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
  let x := xs.get ⟨i.val, hi⟩
  have hxmem : x ∈ xs := List.get_mem xs ⟨i.val, hi⟩
  have hx := mem_scanList.mp (by simpa [xs] using hxmem)
  exact ⟨⟨x, by omega⟩, hx.2.2⟩

/-- At every valid scan index, the active vertex value is the `getD` value of
that position in the source's scan list. -/
lemma scanIndexFun_val (active : ℕ → ℕ) (n : ℕ)
    (i : Fin (activeVertices n active).card) :
    (scanIndexFun active n i).val.val = (scanList active 0 n).getD i.val 0 := by
  let xs := scanList active 0 n
  have hlen : xs.length = (activeVertices n active).card :=
    scanList_length_eq_activeVertices_card active n
  have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
  change xs.get ⟨i.val, hi⟩ = xs.getD i.val 0
  rw [List.getD_eq_getElem _ _ hi, List.get_eq_getElem]

/-- Every scan position names exactly one active vertex, so the scan order is
a finite equivalence with the active-vertex subtype. -/
noncomputable def scanIndexEquiv (active : ℕ → ℕ) (n : ℕ) :
    Fin (activeVertices n active).card ≃ ActiveVertex n active :=
  Equiv.ofBijective (scanIndexFun active n) (by
    have hnodup : (scanList active 0 n).Nodup := scanList_nodup active 0 n
    have hlen : (scanList active 0 n).length = (activeVertices n active).card :=
      scanList_length_eq_activeVertices_card active n
    constructor
    · intro i j hij
      apply Fin.ext
      have hvalues : (scanList active 0 n).get
          ⟨i.val, by rw [hlen]; exact i.isLt⟩ =
          (scanList active 0 n).get
          ⟨j.val, by rw [hlen]; exact j.isLt⟩ := by
        have := congrArg (fun v : ActiveVertex n active => v.val.val) hij
        simpa [scanIndexFun] using this
      have hindices := (hnodup.get_inj_iff).mp hvalues
      have hval : i.val = j.val := by
        simpa [hlen] using
          congrArg (fun k : Fin (scanList active 0 n).length => k.val) hindices
      exact hval
    · intro v
      have hvScan : v.val.val ∈ scanList active 0 n := by
        rw [mem_scanList]
        exact ⟨Nat.zero_le _, by omega, v.property⟩
      obtain ⟨i, hi, hvalue⟩ := List.mem_iff_getElem.mp hvScan
      let j : Fin (activeVertices n active).card := ⟨i, by rw [← hlen]; exact hi⟩
      refine ⟨j, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      have hscan : (scanIndexFun active n j).val.val =
          (scanList active 0 n).getD j.val 0 := scanIndexFun_val active n j
      rw [hscan, List.getD_eq_getElem _ _ hi]
      exact hvalue)

/-- The equivalence's forward map retains the source scan's exact order. -/
lemma scanIndexEquiv_val (active : ℕ → ℕ) (n : ℕ)
    (i : Fin (activeVertices n active).card) :
    (scanIndexEquiv active n i).val.val = (scanList active 0 n).getD i.val 0 := by
  change (scanIndexFun active n i).val.val = _
  exact scanIndexFun_val active n i

end Lax235315Proofs.Construction.ScanIndexEquiv
