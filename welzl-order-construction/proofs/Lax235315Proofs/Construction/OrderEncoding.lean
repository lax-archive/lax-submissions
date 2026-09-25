import Lax195003.WelzlOrdersInGraphs
import Lax235315Proofs.Construction.ListCrossing

/-!
Bridge between the list produced by the RAM and the permutation used by the
submitted definition of a graph Welzl order.
-/

namespace Lax235315Proofs.Construction.OrderEncoding

open Lax195003.WelzlOrders

noncomputable section

/-- The entry of `l` at a position in `Fin n`, using the asserted length. -/
def vertexAt {n : ℕ} (l : List (Fin n)) (hlen : l.length = n)
    (i : Fin n) : Fin n :=
  l.get ⟨i.val, by omega⟩

theorem vertexAt_bijective {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) :
    Function.Bijective (vertexAt l hlen) := by
  constructor
  · intro i j hij
    apply Fin.ext
    have hget : (⟨i.val, by omega⟩ : Fin l.length) = ⟨j.val, by omega⟩ :=
      hl.get_inj_iff.mp hij
    exact congrArg (fun z : Fin l.length => z.val) hget
  · intro v
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hall v)
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    exact hi

/-- The permutation whose inverse enumerates `l` from left to right. -/
def permutationOfList {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) :
    Equiv.Perm (Fin n) :=
  (Equiv.ofBijective (vertexAt l hlen)
    (vertexAt_bijective l hl hall hlen)).symm

/-- Reading the inverse permutation in position order returns the original
enumeration. -/
theorem ofFn_permutationOfList_symm {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) :
    List.ofFn (permutationOfList l hl hall hlen).symm = l := by
  apply List.ext_get
  · simpa using hlen.symm
  · intro i hi h'i
    simp only [List.get_ofFn]
    rfl

/-- The natural-number word obtained from a complete duplicate-free vertex
list has exactly the encoding shape used in the theorem statement. -/
theorem map_val_eq_ofFn {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) :
    l.map Fin.val = List.ofFn
      (fun i : Fin n => ((permutationOfList l hl hall hlen).symm i).val) := by
  calc
    l.map Fin.val =
        (List.ofFn (permutationOfList l hl hall hlen).symm).map Fin.val := by
          rw [ofFn_permutationOfList_symm l hl hall hlen]
    _ = List.ofFn
        (fun i : Fin n => ((permutationOfList l hl hall hlen).symm i).val) := by
          rw [List.map_ofFn]
          rfl

/-- The position assigned by `permutationOfList` is the list index. -/
theorem permutationOfList_val_eq_idxOf {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n)
    (v : Fin n) :
    ((permutationOfList l hl hall hlen) v).val = l.idxOf v := by
  let π := permutationOfList l hl hall hlen
  have hget : vertexAt l hlen (π v) = v := by
    exact Equiv.apply_symm_apply
      (Equiv.ofBijective (vertexAt l hlen)
        (vertexAt_bijective l hl hall hlen)) v
  have hidx := List.get_idxOf hl
    (⟨(π v).val, by have := (π v).isLt; omega⟩ : Fin l.length)
  change l.idxOf (vertexAt l hlen (π v)) = (π v).val at hidx
  rw [hget] at hidx
  exact hidx.symm

/-- The submitted permutation crossing count agrees exactly with the
consecutive-pair count of the list from which the permutation was built. -/
theorem crossingCount_permutationOfList {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n)
    (X : Set (Fin n)) :
    Lax195003.WelzlOrders.crossingCount
        (permutationOfList l hl hall hlen) X =
      Lax235315Proofs.Construction.ListCrossing.crossingCount X l := by
  rw [← Lax235315Proofs.Construction.ListCrossing.ncard_crossingEndpoints X hl]
  unfold Lax195003.WelzlOrders.crossingCount
  congr 1
  ext u
  rw [Set.mem_setOf_eq,
    Lax235315Proofs.Construction.ListCrossing.mem_crossingEndpoints_iff]
  constructor
  · rintro ⟨v, hpos, hcross⟩
    refine ⟨v, ?_, hcross⟩
    rw [Lax235315Proofs.Construction.ListCrossing.mem_zip_tail_iff_idxOf_succ hl]
    refine ⟨hall u, hall v, ?_⟩
    simpa only [← permutationOfList_val_eq_idxOf l hl hall hlen] using hpos
  · rintro ⟨v, huv, hcross⟩
    refine ⟨v, ?_, hcross⟩
    rw [Lax235315Proofs.Construction.ListCrossing.mem_zip_tail_iff_idxOf_succ hl] at huv
    simpa only [← permutationOfList_val_eq_idxOf l hl hall hlen] using huv.2.2

end

end Lax235315Proofs.Construction.OrderEncoding
