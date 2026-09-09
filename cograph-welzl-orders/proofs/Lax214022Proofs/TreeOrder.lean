import Lax214022Proofs.Cotree
import Lax214022Proofs.ListCrossings

/-!
# A logarithmic order extracted from a cotree

The unique maximum-rank child is kept on a heavy root path.  Subtrees hung
from join nodes are placed before that path and subtrees hung from union nodes
after it.  Consequently they merge into the `true` left boundary or the
`false` right boundary of every row belonging to the heavy child.  A rank is
spent only when both children have the same rank.
-/

namespace Lax214022Proofs.TreeOrder

open Lax214022Proofs.Cotree
open Lax214022Proofs.ListCrossings
open Lax48Proofs.Main

noncomputable section

variable {V : Type}

/-- The heavy-path order.  At a join node the light child goes to the left;
at a union node it goes to the right. -/
def treeOrder : Tree V → List V
  | .leaf v => [v]
  | .node joined l r =>
      if l.rank = r.rank then
        treeOrder l ++ treeOrder r
      else if r.rank < l.rank then
        if joined then treeOrder r ++ treeOrder l else treeOrder l ++ treeOrder r
      else
        if joined then treeOrder l ++ treeOrder r else treeOrder r ++ treeOrder l

@[simp] theorem treeOrder_leaf (v : V) : treeOrder (Tree.leaf v) = [v] := rfl

theorem treeOrder_node (joined : Bool) (l r : Tree V) :
    treeOrder (Tree.node joined l r) =
      if l.rank = r.rank then
        treeOrder l ++ treeOrder r
      else if r.rank < l.rank then
        if joined then treeOrder r ++ treeOrder l else treeOrder l ++ treeOrder r
      else
        if joined then treeOrder l ++ treeOrder r else treeOrder r ++ treeOrder l := rfl

@[simp] theorem length_treeOrder (t : Tree V) : (treeOrder t).length = t.leafCount := by
  induction t with
  | leaf => simp
  | node joined l r ihl ihr =>
      by_cases heq : l.rank = r.rank
      · simp [treeOrder, heq, ihl, ihr, Tree.leafCount]
      · by_cases hlt : r.rank < l.rank <;> cases joined <;>
          simp [treeOrder, heq, hlt, ihl, ihr, Tree.leafCount, Nat.add_comm]

theorem leafCount_pos (t : Tree V) : 0 < t.leafCount := by
  induction t <;> simp_all [Tree.leafCount]

theorem treeOrder_nonempty (t : Tree V) : treeOrder t ≠ [] := by
  exact List.ne_nil_of_length_pos (by simpa using leafCount_pos t)

@[simp] theorem toFinset_treeOrder [DecidableEq V] (t : Tree V) :
    (treeOrder t).toFinset = t.leafSet := by
  induction t with
  | leaf v => simp [treeOrder, Tree.leafSet]
  | node joined l r ihl ihr =>
      by_cases heq : l.rank = r.rank
      · simp [treeOrder, heq, ihl, ihr, Tree.leafSet]
      · by_cases hlt : r.rank < l.rank <;> cases joined <;>
          simp [treeOrder, heq, hlt, ihl, ihr, Tree.leafSet,
            Finset.union_comm]

theorem mem_treeOrder_iff [DecidableEq V] {t : Tree V} {v : V} :
    v ∈ treeOrder t ↔ v ∈ t.leafSet := by
  constructor
  · intro h
    have hv : v ∈ (treeOrder t).toFinset := List.mem_toFinset.mpr h
    rwa [toFinset_treeOrder] at hv
  · intro h
    apply List.mem_toFinset.mp
    rwa [toFinset_treeOrder]

theorem nodup_treeOrder [DecidableEq V] {G : SimpleGraph V} {t : Tree V}
    (ht : t.Represents G) : (treeOrder t).Nodup := by
  induction t with
  | leaf v => simp
  | node joined l r ihl ihr =>
      simp only [Tree.Represents] at ht
      have hd : (treeOrder l).Disjoint (treeOrder r) := by
        rw [List.disjoint_left]
        intro x hxl hxr
        exact (Finset.disjoint_left.mp ht.2.2.1)
          (mem_treeOrder_iff.mp hxl) (mem_treeOrder_iff.mp hxr)
      by_cases heq : l.rank = r.rank
      · rw [treeOrder_node, if_pos heq]
        exact List.Nodup.append (ihl ht.1) (ihr ht.2.1) hd
      · rw [treeOrder_node, if_neg heq]
        by_cases hlt : r.rank < l.rank
        · rw [if_pos hlt]
          cases joined
          · exact List.Nodup.append (ihl ht.1) (ihr ht.2.1) hd
          · exact List.Nodup.append (ihr ht.2.1) (ihl ht.1) hd.symm
        · rw [if_neg hlt]
          cases joined
          · exact List.Nodup.append (ihr ht.2.1) (ihl ht.1) hd.symm
          · exact List.Nodup.append (ihl ht.1) (ihr ht.2.1) hd

variable {V : Type} [DecidableEq V]

/-- Boolean adjacency row of `u` on a vertex list. -/
def row (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (xs : List V) :
    List Bool :=
  xs.map fun v => decide (G.Adj u v)

omit [DecidableEq V] in
@[simp] theorem row_append (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (xs ys : List V) :
    row G u (xs ++ ys) = row G u xs ++ row G u ys := by
  simp [row]

/-- Optional canonical endpoint values: join pieces coalesce with `true` on
the left and union pieces coalesce with `false` on the right. -/
def frame (left right : Bool) (xs : List Bool) : List Bool :=
  (if left then [true] else []) ++ xs ++ (if right then [false] else [])

theorem changes_four_le (a b c d : List Bool) :
    changes (a ++ b ++ c ++ d) ≤
      changes a + changes b + changes c + changes d + 3 := by
  have hab := changes_append_le a b
  have habc := changes_append_le (a ++ b) c
  have habcd := changes_append_le (a ++ b ++ c) d
  omega

theorem changes_frame_append_le (left right : Bool) (xs ys : List Bool) :
    changes (frame left right (xs ++ ys)) ≤
      changes xs + changes ys + 3 := by
  cases left <;> cases right
  · simpa [frame, List.append_assoc] using changes_four_le [] xs ys []
  · simpa [frame, List.append_assoc] using changes_four_le [] xs ys [false]
  · simpa [frame, List.append_assoc] using changes_four_le [true] xs ys []
  · simpa [frame, List.append_assoc] using changes_four_le [true] xs ys [false]

@[simp] theorem changes_cons_replicate (b : Bool) (m : ℕ)
    (xs : List Bool) :
    changes (b :: (List.replicate m b ++ xs)) = changes (b :: xs) := by
  simpa [List.replicate_succ] using
    changes_replicate_succ_append m b xs

@[simp] theorem changes_append_cons_replicate (xs : List Bool)
    (b : Bool) (m : ℕ) :
    changes (xs ++ b :: List.replicate m b) = changes (xs ++ [b]) := by
  simpa [List.replicate_succ, List.append_assoc] using
    changes_append_replicate_succ xs m b

theorem changes_frame_replicate_true_left (left right : Bool)
    {m : ℕ} (hm : 0 < m) (xs : List Bool) :
    changes (frame left right (List.replicate m true ++ xs)) =
      changes (frame true right xs) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  cases left <;> cases right <;>
    simp [frame, List.replicate_succ, List.append_assoc]

theorem changes_frame_replicate_false_right (left right : Bool)
    {m : ℕ} (hm : 0 < m) (xs : List Bool) :
    changes (frame left right (xs ++ List.replicate m false)) =
      changes (frame left true xs) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hrep : List.replicate (m + 1) false ++ [false] =
      List.replicate (m + 2) false := by
    rw [show [false] = List.replicate 1 false by rfl, ← List.replicate_add]
  cases left <;> cases right
  · simp [frame, List.replicate_succ]
  · simp only [frame]
    simp
    rw [hrep]
    exact changes_append_replicate_succ xs (m + 1) false
  · simpa [frame, List.replicate_succ, List.append_assoc] using
      changes_append_replicate_succ (true :: xs) m false
  · simp only [frame]
    simp
    change changes ((true :: xs) ++
        (List.replicate (m + 1) false ++ [false])) =
      changes ((true :: xs) ++ [false])
    rw [hrep]
    exact changes_append_replicate_succ (true :: xs) (m + 1) false

omit [DecidableEq V] in
theorem row_eq_replicate_true (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (xs : List V) (h : ∀ v ∈ xs, G.Adj u v) :
    row G u xs = List.replicate xs.length true := by
  induction xs with
  | nil => simp [row]
  | cons v xs ih =>
      simp only [row, List.map_cons, List.length_cons, List.replicate_succ]
      rw [show decide (G.Adj u v) = true by simp [h v (by simp)]]
      congr 1
      change row G u xs = List.replicate xs.length true
      exact ih (fun w hw => h w (by simp [hw]))

omit [DecidableEq V] in
theorem row_eq_replicate_false (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (xs : List V) (h : ∀ v ∈ xs, ¬ G.Adj u v) :
    row G u xs = List.replicate xs.length false := by
  induction xs with
  | nil => simp [row]
  | cons v xs ih =>
      simp only [row, List.map_cons, List.length_cons, List.replicate_succ]
      rw [show decide (G.Adj u v) = false by simp [h v (by simp)]]
      congr 1
      change row G u xs = List.replicate xs.length false
      exact ih (fun w hw => h w (by simp [hw]))

theorem row_right_eq_replicate (G : SimpleGraph V) [DecidableRel G.Adj]
    (joined : Bool) (l r : Tree V)
    (ht : (Tree.node joined l r).Represents G) {u : V}
    (hu : u ∈ l.leafSet) :
    row G u (treeOrder r) = List.replicate (treeOrder r).length joined := by
  simp only [Tree.Represents] at ht
  cases joined
  · apply row_eq_replicate_false
    intro v hv
    exact ht.2.2.2 u hu v (mem_treeOrder_iff.mp hv)
  · apply row_eq_replicate_true
    intro v hv
    exact ht.2.2.2 u hu v (mem_treeOrder_iff.mp hv)

theorem row_left_eq_replicate (G : SimpleGraph V) [DecidableRel G.Adj]
    (joined : Bool) (l r : Tree V)
    (ht : (Tree.node joined l r).Represents G) {u : V}
    (hu : u ∈ r.leafSet) :
    row G u (treeOrder l) = List.replicate (treeOrder l).length joined := by
  simp only [Tree.Represents] at ht
  cases joined
  · apply row_eq_replicate_false
    intro v hv hadj
    exact ht.2.2.2 v (mem_treeOrder_iff.mp hv) u hu hadj.symm
  · apply row_eq_replicate_true
    intro v hv
    exact (ht.2.2.2 v (mem_treeOrder_iff.mp hv) u hu).symm

/-- Every row, even with the two canonical boundary values attached, has
at most `4 rank + 2` changes.  Unequal-rank nodes are free: their light
subtree is absorbed by the matching boundary. -/
theorem changes_framed_row_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : Tree V} (ht : t.Represents G) {u : V} (hu : u ∈ t.leafSet)
    (left right : Bool) :
    changes (frame left right (row G u (treeOrder t))) ≤ 4 * t.rank + 2 := by
  induction t generalizing u left right with
  | leaf v =>
      have huv : u = v := by simpa [Tree.leafSet] using hu
      subst u
      cases left <;> cases right <;>
        simp [frame, row]
  | node joined l r ihl ihr =>
      simp only [Tree.Represents] at ht
      have hu' : u ∈ l.leafSet ∪ r.leafSet := by
        simpa [Tree.leafSet] using hu
      rcases Finset.mem_union.mp hu' with hul | hur
      · have hrow := row_right_eq_replicate G joined l r
          (by simpa [Tree.Represents] using ht) hul
        have ih := ihl ht.1 hul false false
        have ih0 : changes (row G u (treeOrder l)) ≤ 4 * l.rank + 2 := by
          simpa [frame] using ih
        by_cases heq : l.rank = r.rank
        · have hcat := changes_frame_append_le left right
              (row G u (treeOrder l)) (row G u (treeOrder r))
          rw [hrow, changes_replicate] at hcat
          simp only [length_treeOrder] at hcat
          simp [treeOrder, heq, hrow]
          simp [Tree.rank, heq]
          omega
        · by_cases hlt : r.rank < l.rank
          · cases joined
            · simp [treeOrder, heq, hlt, hrow]
              rw [changes_frame_replicate_false_right left right
                (by simpa using leafCount_pos r) (row G u (treeOrder l))]
              have hheavy := ihl ht.1 hul left true
              simpa [Tree.rank, heq, max_eq_left hlt.le] using hheavy
            · simp [treeOrder, heq, hlt, hrow]
              rw [changes_frame_replicate_true_left left right
                (by simpa using leafCount_pos r) (row G u (treeOrder l))]
              have hheavy := ihl ht.1 hul true right
              simpa [Tree.rank, heq, max_eq_left hlt.le] using hheavy
          · have hrl : l.rank < r.rank := lt_of_le_of_ne (Nat.le_of_not_gt hlt) heq
            cases joined
            · simp [treeOrder, heq, hlt, hrow]
              have hcat := changes_frame_append_le left right
                (row G u (treeOrder r)) (row G u (treeOrder l))
              rw [hrow, changes_replicate] at hcat
              simp only [length_treeOrder] at hcat
              simp only [Tree.rank, if_neg heq, max_eq_right hrl.le]
              omega
            · simp [treeOrder, heq, hlt, hrow]
              have hcat := changes_frame_append_le left right
                (row G u (treeOrder l)) (row G u (treeOrder r))
              rw [hrow, changes_replicate] at hcat
              simp only [length_treeOrder] at hcat
              simp only [Tree.rank, if_neg heq, max_eq_right hrl.le]
              omega
      · have hrow := row_left_eq_replicate G joined l r
          (by simpa [Tree.Represents] using ht) hur
        have ih := ihr ht.2.1 hur false false
        have ih0 : changes (row G u (treeOrder r)) ≤ 4 * r.rank + 2 := by
          simpa [frame] using ih
        by_cases heq : l.rank = r.rank
        · have hcat := changes_frame_append_le left right
              (row G u (treeOrder l)) (row G u (treeOrder r))
          rw [hrow, changes_replicate] at hcat
          simp only [length_treeOrder] at hcat
          simp [treeOrder, heq, hrow]
          simp [Tree.rank, heq]
          omega
        · by_cases hlt : r.rank < l.rank
          · cases joined
            · simp [treeOrder, heq, hlt, hrow]
              have hcat := changes_frame_append_le left right
                (row G u (treeOrder l)) (row G u (treeOrder r))
              rw [hrow, changes_replicate] at hcat
              simp only [length_treeOrder] at hcat
              simp only [Tree.rank, if_neg heq, max_eq_left hlt.le]
              omega
            · simp [treeOrder, heq, hlt, hrow]
              have hcat := changes_frame_append_le left right
                (row G u (treeOrder r)) (row G u (treeOrder l))
              rw [hrow, changes_replicate] at hcat
              simp only [length_treeOrder] at hcat
              simp only [Tree.rank, if_neg heq, max_eq_left hlt.le]
              omega
          · have hrl : l.rank < r.rank := lt_of_le_of_ne (Nat.le_of_not_gt hlt) heq
            cases joined
            · simp [treeOrder, heq, hlt, hrow]
              rw [changes_frame_replicate_false_right left right
                (by simpa using leafCount_pos l) (row G u (treeOrder r))]
              have hheavy := ihr ht.2.1 hur left true
              simpa [Tree.rank, heq, max_eq_right hrl.le] using hheavy
            · simp [treeOrder, heq, hlt, hrow]
              rw [changes_frame_replicate_true_left left right
                (by simpa using leafCount_pos l) (row G u (treeOrder r))]
              have hheavy := ihr ht.2.1 hur true right
              simpa [Tree.rank, heq, max_eq_right hrl.le] using hheavy

end

end Lax214022Proofs.TreeOrder
