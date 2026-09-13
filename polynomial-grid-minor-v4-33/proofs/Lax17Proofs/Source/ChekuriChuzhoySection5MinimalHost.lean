import Mathlib.Tactic
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Edge-minimal host for Chekuri--Chuzhoy Section 5

The nonconstructive argument at the start of Chekuri--Chuzhoy Section 5
assumes that the host graph is inclusion-minimal subject to the terminals
being node-well-linked.  This module supplies that finite choice for the
repository's same-vertex simple-graph model.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5MinimalHost


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A same-vertex host subgraph that preserves the Section 5 terminal
node-well-linkedness assumption and is minimal under deletion of one edge. -/
structure EdgeMinimalNodeWellLinkedHost
    (G : _root_.SimpleGraph V) (terminals : Finset V) where
  H : _root_.SimpleGraph V
  le_original : H ≤ G
  nodeWellLinked : NodeWellLinkedIn H Finset.univ terminals
  deleteEdge_not_nodeWellLinked :
    ∀ ⦃a b : V⦄, H.Adj a b →
      ¬ NodeWellLinkedIn
        (H.deleteEdges ({s(a, b)} : Set (Sym2 V))) Finset.univ terminals

omit [DecidableEq V] in
private theorem edgeSet_deleteEdges_singleton_ncard_lt
    (H : _root_.SimpleGraph V) {a b : V} (hab : H.Adj a b) :
    ((H.deleteEdges ({s(a, b)} : Set (Sym2 V))).edgeSet).ncard <
      H.edgeSet.ncard := by
  classical
  let e : Sym2 V := s(a, b)
  have heH : e ∈ H.edgeSet := by
    simpa [_root_.SimpleGraph.mem_edgeSet, e] using hab
  rw [_root_.SimpleGraph.edgeSet_deleteEdges]
  have hcard :
      (H.edgeSet \ ({e} : Set (Sym2 V))).ncard + 1 = H.edgeSet.ncard :=
    Set.ncard_diff_singleton_add_one heH (Set.toFinite H.edgeSet)
  exact (Nat.lt_succ_self _).trans_eq hcard

/-- Finite edge-minimal host selection used by the nonconstructive router
argument in Chekuri--Chuzhoy Section 5. -/
theorem exists_edgeMinimalNodeWellLinkedHost
    {terminals : Finset V}
    (hwell : NodeWellLinkedIn G Finset.univ terminals) :
    Nonempty (EdgeMinimalNodeWellLinkedHost G terminals) := by
  classical
  let Candidate :=
    {H : _root_.SimpleGraph V //
      H ≤ G ∧ NodeWellLinkedIn H Finset.univ terminals}
  let HasEdgeCount : ℕ → Prop := fun n =>
    ∃ H : Candidate, H.1.edgeSet.ncard = n
  have hExists : ∃ n : ℕ, HasEdgeCount n := by
    refine ⟨G.edgeSet.ncard, ⟨G, le_rfl, hwell⟩, rfl⟩
  let edgeMin := Nat.find hExists
  rcases Nat.find_spec hExists with ⟨Hmin, hHminCard⟩
  refine ⟨{
    H := Hmin.1
    le_original := Hmin.2.1
    nodeWellLinked := Hmin.2.2
    deleteEdge_not_nodeWellLinked := ?_ }⟩
  intro a b hab hdelete
  let Hdel : Candidate :=
    ⟨Hmin.1.deleteEdges ({s(a, b)} : Set (Sym2 V)),
      (_root_.SimpleGraph.deleteEdges_le
        ({s(a, b)} : Set (Sym2 V))).trans Hmin.2.1,
      hdelete⟩
  have hDelCandidate : HasEdgeCount Hdel.1.edgeSet.ncard :=
    ⟨Hdel, rfl⟩
  have hMinLe : edgeMin ≤ Hdel.1.edgeSet.ncard :=
    Nat.find_min' (H := hExists) hDelCandidate
  have hDelLt : Hdel.1.edgeSet.ncard < Hmin.1.edgeSet.ncard := by
    simpa [Hdel] using edgeSet_deleteEdges_singleton_ncard_lt Hmin.1 hab
  omega

/-- Restoring the ambient edges preserves node-well-linkedness of a selected
minimal host. -/
theorem EdgeMinimalNodeWellLinkedHost.nodeWellLinked_original
    {terminals : Finset V}
    (M : EdgeMinimalNodeWellLinkedHost G terminals) :
    NodeWellLinkedIn G Finset.univ terminals :=
  NodeWellLinkedIn.mono_graph M.nodeWellLinked M.le_original

end ChekuriChuzhoySection5MinimalHost
end SimpleGraph

end Lax17Proofs
