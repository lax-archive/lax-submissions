import Lax214022.CographWelzlUpperBound
import Lax214022Proofs.TreeOrder

/-!
The submitted upper bound, proved from the width-zero cotree extracted in
`Cotree` and the heavy-path order analyzed in `TreeOrder`.
-/

namespace Lax214022Proofs.CographWelzlUpperBound

open Lax214022.Cographs
open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax214022Proofs.Cotree
open Lax214022Proofs.ListCrossings
open Lax214022Proofs.TreeOrder

noncomputable section

theorem radius_one_mem_iff_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (v u : Fin n) :
    (u ≠ v ∧ ∃ w : G.Walk v u, w.length ≤ 1) ↔ G.Adj v u := by
  constructor
  · rintro ⟨huv, w, hw⟩
    have hlen : w.length = 1 := by
      have hpos : 0 < w.length := by
        by_contra hz
        have hz' : w.length = 0 := Nat.eq_zero_of_not_pos hz
        exact huv (w.eq_of_length_eq_zero hz').symm
      omega
    exact w.adj_of_length_eq_one hlen
  · intro huv
    exact ⟨huv.ne.symm, huv.toWalk, by simp⟩

theorem radius_one_set_eq_neighborSet {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) :
    {u : Fin n | u ≠ v ∧ ∃ w : G.Walk v u, w.length ≤ 1} =
      G.neighborSet v := by
  ext u
  exact radius_one_mem_iff_adj G v u

/-- A duplicate-free complete list determines the permutation whose inverse
enumerates that list. -/
theorem exists_perm_of_nodup_complete {n : ℕ} (L : List (Fin n))
    (hL : L.Nodup) (hall : ∀ v : Fin n, v ∈ L) (hlen : L.length = n) :
    ∃ π : Equiv.Perm (Fin n),
      List.ofFn (fun i : Fin n => π.symm i) = L := by
  let e : Fin L.length ≃ Fin n :=
    List.Nodup.getEquivOfForallMemList L hL hall
  let castToLength : Fin n ≃ Fin L.length :=
    Equiv.cast (congrArg Fin hlen.symm)
  let enum : Equiv.Perm (Fin n) := castToLength.trans e
  refine ⟨enum.symm, ?_⟩
  apply List.ext_get
  · simp [hlen]
  · intro i hi hLi
    simp [enum, castToLength, e]
    congr 1
    have hin : i < n := by omega
    let j : Fin n := ⟨i, hin⟩
    have hij : (⟨i, by omega⟩ : Fin n) = j := Fin.ext rfl
    calc
      ↑(cast (congrArg Fin hlen.symm) ⟨i, by omega⟩) =
          ↑(cast (congrArg Fin hlen.symm) j) := by rw [hij]
      _ = ↑(Fin.cast hlen.symm j) := by
        exact congrArg Fin.val (congrFun (Fin.cast_eq_cast hlen.symm) j).symm
      _ = i := Fin.val_cast hlen.symm j

theorem crossingNumber_le_of_rows {n K : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n))
    (hπ : ∀ v : Fin n, crossingCount π (G.neighborSet v) ≤ K) :
    crossingNumber (neighborhoodSetSystem G 1) π ≤ K := by
  classical
  unfold crossingNumber
  let S : Set ℕ :=
    {q | ∃ X ∈ neighborhoodSetSystem G 1, q = crossingCount π X}
  have hbound : ∀ q ∈ S, q ≤ K := by
    intro q hq
    rcases hq with ⟨X, hX, rfl⟩
    rcases hX with ⟨v, rfl⟩
    rw [radius_one_set_eq_neighborSet]
    exact hπ v
  have hbdd : ∃ m, ∀ q ∈ S, q ≤ m := ⟨K, hbound⟩
  change sSup S ≤ K
  rw [Nat.sSup_def hbdd]
  exact Nat.find_min' hbdd hbound

/--
---
conclusion: Lax214022.CographWelzlUpperBound.exists_welzlOrder_crossingNumber_le_four_clog_add_one
---
Every cograph has a Welzl order with at most
`4 * (ceil(log₂ n) + 1)` crossings per open-neighborhood row.

# Proof strategy

Extract a binary cotree from the width-zero contraction sequence and order
its leaves along recursively chosen heavy paths.  A light subtree attached
at a join node contributes a constant `true` row, while one attached at a
union node contributes a constant `false` row.  Their placement makes these
constant rows coalesce with canonical boundary values.  Thus unequal-rank
nodes are free, equal-rank nodes cost at most four changes, and the number
of costly levels is the Strahler rank, at most `ceil(log₂ n)`.

# Attribution

The cotree ordering follows the logarithmic cograph-contiguity construction
of Crespelle and Gambette; the framed-row invariant and its Lean proof are
given here directly for Welzl crossing number.
-/
theorem exists_welzlOrder_crossingNumber_le_four_clog_add_one
    (n : ℕ) (G : SimpleGraph (Fin n)) (hG : IsCograph G) :
    ∃ π : Equiv.Perm (Fin n),
      IsWelzlOrder (neighborhoodSetSystem G 1) π
        (4 * (Nat.clog 2 n + 1)) := by
  classical
  rcases n with _ | n
  · refine ⟨Equiv.refl _, ?_⟩
    simp [IsWelzlOrder, crossingNumber, neighborhoodSetSystem]
  · letI : Nonempty (Fin (n + 1)) := ⟨0⟩
    obtain ⟨t, htuniv, ht⟩ :=
      exists_represents_of_hasTwinWidthAtMost_zero hG
    let L : List (Fin (n + 1)) := treeOrder t
    have hnodup : L.Nodup := nodup_treeOrder ht
    have hall : ∀ v : Fin (n + 1), v ∈ L := by
      intro v
      rw [mem_treeOrder_iff, htuniv]
      simp
    have hlen : L.length = n + 1 := by
      calc
        L.length = t.leafCount := length_treeOrder t
        _ = t.leafSet.card := Tree.leafCount_eq_card_leafSet ht
        _ = n + 1 := by simp [htuniv]
    obtain ⟨π, hπlist⟩ := exists_perm_of_nodup_complete L hnodup hall hlen
    refine ⟨π, ?_⟩
    unfold IsWelzlOrder
    apply crossingNumber_le_of_rows G π
    intro v
    rw [crossingCount_eq_crossingCountInList, hπlist]
    have hcc : crossingCountInList (fun u => u ∈ G.neighborSet v) L =
        crossingCountInList (G.Adj v) L := by
      simp [crossingCountInList]
    rw [hcc]
    have hv : v ∈ t.leafSet := by simp [htuniv]
    have hrow := changes_framed_row_le G ht hv false false
    have hraw : crossingCountInList (G.Adj v) L ≤ 4 * t.rank + 2 := by
      simpa [L, frame, row, crossingCountInList] using hrow
    have htcount : t.leafCount = n + 1 :=
      (length_treeOrder t).symm.trans hlen
    have hrank : t.rank ≤ Nat.clog 2 (n + 1) :=
      (Tree.rank_le_clog_leafCount t).trans_eq
        (congrArg (Nat.clog 2) htcount)
    omega

end

end Lax214022Proofs.CographWelzlUpperBound
