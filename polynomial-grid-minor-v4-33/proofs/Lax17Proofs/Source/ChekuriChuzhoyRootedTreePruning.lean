import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Rooted finite-tree pruning infrastructure

This module supplies the parent map missing from mathlib's undirected tree
API.  It is intentionally limited to the rooted unique paths used by
Chekuri--Chuzhoy Observation 2.12.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyRootedTreePruning


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H : _root_.SimpleGraph V}

/-- The unique shortest root-to-vertex path in a tree. -/
noncomputable def rootPath (hH : H.IsTree) (root x : V) : H.Walk root x :=
  Classical.choose (hH.connected.exists_path_of_dist root x)

theorem rootPath_isPath (hH : H.IsTree) (root x : V) :
    (rootPath hH root x).IsPath :=
  (Classical.choose_spec (hH.connected.exists_path_of_dist root x)).1

theorem rootPath_length (hH : H.IsTree) (root x : V) :
    (rootPath hH root x).length = H.dist root x :=
  (Classical.choose_spec (hH.connected.exists_path_of_dist root x)).2

/-- The parent is the penultimate point of the unique root path; the root is
its own parent. -/
noncomputable def parent (hH : H.IsTree) (root x : V) : V :=
  if x = root then root else (rootPath hH root x).penultimate

@[simp] theorem parent_root (hH : H.IsTree) (root : V) :
    parent hH root root = root := by
  simp [parent]

theorem parent_eq_penultimate (hH : H.IsTree) (root : V) {x : V}
    (hx : x ≠ root) :
    parent hH root x = (rootPath hH root x).penultimate := by
  simp [parent, hx]

theorem parent_adj (hH : H.IsTree) (root : V) {x : V}
    (hx : x ≠ root) : H.Adj (parent hH root x) x := by
  rw [parent_eq_penultimate hH root hx]
  exact (rootPath hH root x).adj_penultimate
    (by
      intro hnil
      exact hx hnil.eq.symm)

theorem parent_ne (hH : H.IsTree) (root : V) {x : V}
    (hx : x ≠ root) : parent hH root x ≠ x :=
  (parent_adj hH root hx).ne

/-- Vertices whose parent chain passes through `v`. -/
noncomputable def descendants (hH : H.IsTree) (root v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ n ≤ Fintype.card V, (parent hH root)^[n] x = v

@[simp] theorem mem_descendants (hH : H.IsTree) (root v x : V) :
    x ∈ descendants hH root v ↔
      ∃ n ≤ Fintype.card V, (parent hH root)^[n] x = v := by
  classical
  simp [descendants]

theorem self_mem_descendants (hH : H.IsTree) (root v : V) :
    v ∈ descendants hH root v := by
  rw [mem_descendants]
  exact ⟨0, Nat.zero_le _, rfl⟩

end ChekuriChuzhoyRootedTreePruning
end SimpleGraph

end Lax17Proofs
