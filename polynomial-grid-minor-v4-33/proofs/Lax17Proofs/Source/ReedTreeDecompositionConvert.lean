import Lax17Proofs.Source.ReedTreeDecomposition

namespace Lax17Proofs

universe u v w

/-!
# Converting region decompositions to tree decompositions

A region decomposition of the full vertex set already has the coverage fields
of a tree decomposition.  Its walk-based running-intersection invariant lifts
the witnessing walks to the induced graph on the bag indices containing a
fixed vertex.
-/

namespace SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]

namespace ReedTreeDecomposition
namespace RegionDecomposition

variable {G : _root_.SimpleGraph V}

/-- Regard a region decomposition of the full vertex set as an ordinary tree
decomposition. -/
noncomputable def toTreeDecomposition
    (D : RegionDecomposition G (Finset.univ : Finset V)) :
    TreeDecomposition G where
  Node := D.Node
  nodeFintype := D.nodeFintype
  nodeDecidableEq := D.nodeDecidableEq
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  vertex_mem_bag := by
    intro v
    exact D.vertex_mem_bag (Finset.mem_univ v)
  edge_mem_bag := by
    intro u v huv
    exact D.edge_mem_bag huv (Finset.mem_univ u) (Finset.mem_univ v)
  bag_indices_connected := by
    intro v
    have hv : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
    obtain ⟨root, hroot⟩ := D.vertex_mem_bag hv
    letI : Nonempty {i : D.Node | v ∈ D.bag i} := ⟨⟨root, hroot⟩⟩
    refine ⟨fun i j => ?_⟩
    obtain ⟨p, hp⟩ := D.bag_walk hv i.property j.property
    exact ⟨p.induce {n : D.Node | v ∈ D.bag n} hp⟩

/-- A uniform upper bound on region bag cardinalities bounds the width of the
converted tree decomposition by one less. -/
theorem toTreeDecomposition_width_le
    (D : RegionDecomposition G (Finset.univ : Finset V)) (k : ℕ)
    (hbag : ∀ i : D.Node, (D.bag i).card ≤ k) :
    D.toTreeDecomposition.width ≤ k - 1 := by
  classical
  letI : Fintype D.Node := D.nodeFintype
  have hsup :
      (Finset.univ.sup fun i : D.Node => (D.bag i).card) ≤ k := by
    exact Finset.sup_le fun i _ => hbag i
  change (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1 ≤ k - 1
  exact Nat.sub_le_sub_right hsup 1

end RegionDecomposition
end ReedTreeDecomposition
end SimpleGraph

end Lax17Proofs
