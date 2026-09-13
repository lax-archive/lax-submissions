import Lax17Proofs.Source.ChekuriChuzhoyRootedTreePruning

namespace Lax17Proofs

universe u v w

/-!
# Distance along rooted-tree parent chains

The parent map of `ChekuriChuzhoyRootedTreePruning` moves each nonroot vertex
one step toward the root. Consequently, its iterates reach the root for the
first time after exactly the root distance of the starting vertex.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyRootedTreePruning


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H : _root_.SimpleGraph V}

/-- A nonroot vertex is exactly one edge farther from the root than its parent. -/
theorem dist_parent_add_one (hH : H.IsTree) (root : V) {x : V}
    (hx : x ≠ root) :
    H.dist root (parent hH root x) + 1 = H.dist root x := by
  rw [parent_eq_penultimate hH root hx]
  let p := rootPath hH root x
  have hp : p.length = H.dist root x := rootPath_length hH root x
  have hdrop : p.dropLast.length = H.dist root p.penultimate :=
    _root_.SimpleGraph.length_eq_dist_of_subwalk hp
      (_root_.SimpleGraph.Walk.isSubwalk_take p (p.length - 1))
  calc
    H.dist root p.penultimate + 1 = p.dropLast.length + 1 := by rw [hdrop]
    _ = p.length :=
      p.length_dropLast_add_one
        (_root_.SimpleGraph.Walk.not_nil_of_ne hx.symm)
    _ = H.dist root x := hp

/-- Applying the parent map truncates the root distance by one. This also
holds at the root, where both sides are zero. -/
theorem dist_parent (hH : H.IsTree) (root x : V) :
    H.dist root (parent hH root x) = H.dist root x - 1 := by
  by_cases hx : x = root
  · subst x
    simp
  · have := dist_parent_add_one hH root hx
    omega

/-- The parent of every nonroot vertex is strictly closer to the root. -/
theorem dist_parent_lt (hH : H.IsTree) (root : V) {x : V}
    (hx : x ≠ root) :
    H.dist root (parent hH root x) < H.dist root x := by
  have := dist_parent_add_one hH root hx
  omega

/-- After `n` parent steps, the root distance is the original distance minus
`n`. -/
theorem dist_iterate_parent (hH : H.IsTree) (root x : V) (n : ℕ) :
    H.dist root ((parent hH root)^[n] x) = H.dist root x - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', dist_parent, ih, Nat.sub_sub]

/-- A parent iterate is the root exactly when the number of steps is at least
the starting root distance. -/
theorem iterate_parent_eq_root_iff (hH : H.IsTree) (root x : V) (n : ℕ) :
    (parent hH root)^[n] x = root ↔ H.dist root x ≤ n := by
  constructor
  · intro hit
    have hz : H.dist root ((parent hH root)^[n] x) = 0 := by simp [hit]
    rw [dist_iterate_parent hH root x n] at hz
    exact Nat.sub_eq_zero_iff_le.mp hz
  · intro hn
    have hz : H.dist root ((parent hH root)^[n] x) = 0 := by
      rw [dist_iterate_parent hH root x n, Nat.sub_eq_zero_of_le hn]
    exact (hH.connected.dist_eq_zero_iff.mp hz).symm

/-- Before the starting root distance has elapsed, the parent chain has not
yet reached the root. -/
theorem iterate_parent_ne_root_iff (hH : H.IsTree) (root x : V) (n : ℕ) :
    (parent hH root)^[n] x ≠ root ↔ n < H.dist root x := by
  rw [ne_eq, iterate_parent_eq_root_iff hH root x n, not_le]

/-- The parent chain reaches the root after exactly the starting root
distance. -/
theorem iterate_parent_eq_root (hH : H.IsTree) (root x : V) :
    (parent hH root)^[H.dist root x] x = root :=
  (iterate_parent_eq_root_iff hH root x _).2 le_rfl

/-- The root distance is the first index at which the parent chain reaches
the root. -/
theorem iterate_parent_first_reaches_root (hH : H.IsTree) (root x : V) :
    (parent hH root)^[H.dist root x] x = root ∧
      ∀ n < H.dist root x, (parent hH root)^[n] x ≠ root := by
  refine ⟨iterate_parent_eq_root hH root x, ?_⟩
  intro n hn
  exact (iterate_parent_ne_root_iff hH root x n).2 hn

/-- Every nonroot vertex reaches the root after a positive number of parent
steps. -/
theorem exists_pos_iterate_parent_eq_root (hH : H.IsTree) (root : V) {x : V}
    (hx : x ≠ root) :
    ∃ n, 0 < n ∧ (parent hH root)^[n] x = root := by
  exact ⟨H.dist root x, hH.connected.pos_dist_of_ne hx.symm,
    iterate_parent_eq_root hH root x⟩

/-- Root distance in a finite tree is strictly smaller than the number of
vertices. -/
theorem dist_lt_card (hH : H.IsTree) (root x : V) :
    H.dist root x < Fintype.card V := by
  rw [← rootPath_length hH root x]
  exact (rootPath_isPath hH root x).length_lt

/-- Every vertex belongs to the descendant set of the root. -/
theorem mem_descendants_root (hH : H.IsTree) (root x : V) :
    x ∈ descendants hH root root := by
  rw [mem_descendants]
  exact ⟨H.dist root x, (dist_lt_card hH root x).le,
    iterate_parent_eq_root hH root x⟩

end ChekuriChuzhoyRootedTreePruning
end SimpleGraph

end Lax17Proofs
