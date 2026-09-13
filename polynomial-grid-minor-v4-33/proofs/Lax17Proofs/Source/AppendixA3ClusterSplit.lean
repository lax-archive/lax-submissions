import Mathlib.Tactic
import Lax17Proofs.Source.FlowDegree
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Section 7: preliminary cluster-splitting lemmas

This file formalizes source lemmas from Section 7 of Chuzhoy's improved-grid
paper.  Chuzhoy--Tan use that theorem as their Appendix A.3 input.
-/

namespace SimpleGraph
namespace AppendixA3ClusterSplit


open Finset

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-! ## Boundary vertices -/

/-- Chuzhoy's `Gamma_G(S)`: vertices of `S` incident with an edge leaving
`S`. -/
noncomputable def boundaryVertices [Fintype V]
    (G : _root_.SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact S.filter fun v => ∃ w : V, w ∉ S ∧ G.Adj v w

@[simp] theorem mem_boundaryVertices [Fintype V]
    {S : Finset V} {v : V} :
    v ∈ boundaryVertices G S ↔
      v ∈ S ∧ ∃ w : V, w ∉ S ∧ G.Adj v w := by
  classical
  simp [boundaryVertices]

/-- Every edge leaving `S` is incident with a boundary vertex on its `S`
side. -/
theorem clusterBoundary_subset_boundaryVertices_biUnion_incidence [Fintype V]
    (S : Finset V) :
    Section44.clusterBoundary G S ⊆
      (boundaryVertices G S).biUnion fun v => incidentEdgeFinset G v := by
  classical
  intro e he
  rcases
      ((Section44.mem_edgeBoundary (G := G) S
        ((Finset.univ : Finset V) \ S) e).1 he) with
    ⟨heG, x, hx, y, hy, rfl⟩
  have hyNot : y ∉ S := (Finset.mem_sdiff.mp hy).2
  have hxy : G.Adj x y := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using heG
  have hxBoundary : x ∈ boundaryVertices G S :=
    mem_boundaryVertices.mpr ⟨hx, y, hyNot, hxy⟩
  refine Finset.mem_biUnion.mpr ⟨x, hxBoundary, ?_⟩
  exact (mem_incidentEdgeFinset G x s(x, y)).2 ⟨heG, by simp⟩

/-- In a graph of maximum degree `Delta`, the number of edges leaving a set is
at most `Delta` times the number of its boundary vertices. -/
theorem clusterBoundary_card_le_maxDegree_mul_boundaryVertices_card
    [Fintype V] {S : Finset V} {Delta : ℕ}
    (hdegree : MaxDegreeAtMost G Delta) :
    (Section44.clusterBoundary G S).card ≤
      Delta * (boundaryVertices G S).card := by
  classical
  let U := (boundaryVertices G S).biUnion fun v => incidentEdgeFinset G v
  have hsubset : Section44.clusterBoundary G S ⊆ U :=
    clusterBoundary_subset_boundaryVertices_biUnion_incidence S
  calc
    (Section44.clusterBoundary G S).card ≤ U.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ v ∈ boundaryVertices G S, (incidentEdgeFinset G v).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ boundaryVertices G S, Delta := by
      exact Finset.sum_le_sum fun v _hv => by
        exact incidentEdgeFinset_card_le_maxDegree (G := G) hdegree v
    _ = Delta * (boundaryVertices G S).card := by
      simp [Nat.mul_comm]

/-- The augmented boundary `Gamma'(S) = Gamma(S) union (T intersect S)` used
throughout Chuzhoy Section 7. -/
noncomputable def augmentedBoundaryVertices [Fintype V]
    (G : _root_.SimpleGraph V) (S T : Finset V) : Finset V :=
  boundaryVertices G S ∪ (T ∩ S)

namespace PathPacking

/-- A vertex-disjoint path packing is, in particular, an edge-disjoint path
packing with the same paths and index type. -/
def toEdgePathPacking {S T : Finset V} (P : PathPacking G S T) :
    EdgePathPacking G S T where
  Index := P.Index
  path := P.path
  connects := P.connects
  edge_disjoint := fun _i _j hij =>
    GraphPath.edgeDisjoint_of_nodeDisjoint (P.node_disjoint hij)

@[simp] theorem toEdgePathPacking_card {S T : Finset V}
    (P : PathPacking G S T) :
    (toEdgePathPacking P).card = P.card := rfl

theorem card_le_edgeBoundary_of_staysIn_partition [Fintype V]
    {C S T X Y : Finset V} (P : PathPacking G S T)
    (hS : S ⊆ X) (hT : T ⊆ Y) (hstay : P.StaysIn C)
    (hcover : X ∪ Y = C) (hdisj : Disjoint X Y) :
    P.card ≤ (Section44.edgeBoundary G X Y).card := by
  let Q : EdgePathPacking G (X ∩ (S ∪ T)) (Y ∩ (S ∪ T)) := {
    Index := P.Index
    path := P.path
    connects := by
      intro i
      rcases P.connects i with hconn | hconn
      · exact Or.inl
          ⟨mem_inter.mpr ⟨hS hconn.1, mem_union_left T hconn.1⟩,
            mem_inter.mpr ⟨hT hconn.2, mem_union_right S hconn.2⟩⟩
      · exact Or.inr
          ⟨mem_inter.mpr ⟨hT hconn.1, mem_union_right S hconn.1⟩,
            mem_inter.mpr ⟨hS hconn.2, mem_union_left T hconn.2⟩⟩
    edge_disjoint := fun _i _j hij =>
      GraphPath.edgeDisjoint_of_nodeDisjoint (P.node_disjoint hij)
  }
  have hQstay : Q.StaysIn C := by
    intro i
    exact hstay i
  have hQle :=
    Section46.EdgePathPacking.card_le_edgeBoundary_of_staysIn_partition
      (G := G) (C := C) (T := S ∪ T) (X := X) (Y := Y)
      Q hQstay hcover hdisj
  simpa [Q, EdgePathPacking.card, PathPacking.card] using hQle

end PathPacking

/-- Scaled cut well-linkedness is preserved when edges are added to the graph. -/
theorem scaledEdgeWellLinkedIn_mono_graph [Fintype V]
    {H : _root_.SimpleGraph V} {C T : Finset V}
    {alphaNum alphaDen : ℕ}
    (h : Section46.ScaledEdgeWellLinkedIn H C T alphaNum alphaDen)
    (hHG : H ≤ G) :
    Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen := by
  classical
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro X Y hXC hYC hcover hdisj
  have hsub :
      Section44.edgeBoundary H X Y ⊆ Section44.edgeBoundary G X Y := by
    intro e he
    rcases ((Section44.mem_edgeBoundary (G := H) X Y e).1 he) with
      ⟨heH, x, hx, y, hy, hexy⟩
    exact (Section44.mem_edgeBoundary (G := G) X Y e).2
      ⟨_root_.SimpleGraph.edgeSet_mono hHG heH, x, hx, y, hy, hexy⟩
  exact (h.2.2.2 X Y hXC hYC hcover hdisj).trans
    (Nat.mul_le_mul_left alphaDen (Finset.card_le_card hsub))

/-- Chuzhoy, Section 7, Observation 7.1.

If two disjoint terminal sets are each node-well-linked in a cluster and are
node-linked to one another there, then their union is `1/3`-well-linked in the
paper's cut sense.  The local hypotheses actually imply the stronger `1/2`
counting inequality; this statement retains the source constant. -/
theorem observation_7_1_union_scaledEdgeWellLinkedIn [Fintype V]
    {C A B : Finset V}
    (hA : NodeWellLinkedIn G C A)
    (hB : NodeWellLinkedIn G C B)
    (hAB : NodeLinkedIn G C A B) :
    Section46.ScaledEdgeWellLinkedIn G C (A ∪ B) 1 3 := by
  classical
  refine ⟨by norm_num, by norm_num, union_subset hA.1 hB.1, ?_⟩
  intro X Y hXC hYC hcover hdisj
  have hXY (S T : Finset V) (P : PathPacking G S T)
      (hS : S ⊆ X) (hT : T ⊆ Y) (hstay : P.StaysIn C) :
      P.card ≤ (Section44.edgeBoundary G X Y).card :=
    PathPacking.card_le_edgeBoundary_of_staysIn_partition
      P hS hT hstay hcover hdisj

  have hAXAY :
      min (X ∩ A).card (Y ∩ A).card ≤
        (Section44.edgeBoundary G X Y).card := by
    rcases hA.2 inter_subset_right inter_subset_right
        (hdisj.mono inter_subset_left inter_subset_left) with
      ⟨P, hcard, hstay⟩
    simpa [hcard] using
      hXY (X ∩ A) (Y ∩ A) P inter_subset_left inter_subset_left hstay
  have hBXBY :
      min (X ∩ B).card (Y ∩ B).card ≤
        (Section44.edgeBoundary G X Y).card := by
    rcases hB.2 inter_subset_right inter_subset_right
        (hdisj.mono inter_subset_left inter_subset_left) with
      ⟨P, hcard, hstay⟩
    simpa [hcard] using
      hXY (X ∩ B) (Y ∩ B) P inter_subset_left inter_subset_left hstay
  have hAXBY :
      min (X ∩ A).card (Y ∩ B).card ≤
        (Section44.edgeBoundary G X Y).card := by
    rcases hAB.2.2.2 inter_subset_right inter_subset_right with
      ⟨P, hcard, hstay⟩
    simpa [hcard] using
      hXY (X ∩ A) (Y ∩ B) P inter_subset_left inter_subset_left hstay
  have hAYBX :
      min (Y ∩ A).card (X ∩ B).card ≤
        (Section44.edgeBoundary G X Y).card := by
    rcases hAB.2.2.2 inter_subset_right inter_subset_right with
      ⟨P, hcard, hstay⟩
    have hcoverYX : Y ∪ X = C := by
      simpa [union_comm] using hcover
    have hYX :
        P.card ≤ (Section44.edgeBoundary G Y X).card :=
      PathPacking.card_le_edgeBoundary_of_staysIn_partition
        P inter_subset_left inter_subset_left hstay hcoverYX hdisj.symm
    simpa [hcard, Section44.edgeBoundary_comm (G := G) Y X] using hYX

  have hXsplit : X ∩ (A ∪ B) = (X ∩ A) ∪ (X ∩ B) := by
    ext v
    simp only [mem_inter, mem_union]
    tauto
  have hYsplit : Y ∩ (A ∪ B) = (Y ∩ A) ∪ (Y ∩ B) := by
    ext v
    simp only [mem_inter, mem_union]
    tauto
  have hXdisj : Disjoint (X ∩ A) (X ∩ B) :=
    hAB.2.2.1.mono inter_subset_right inter_subset_right
  have hYdisj : Disjoint (Y ∩ A) (Y ∩ B) :=
    hAB.2.2.1.mono inter_subset_right inter_subset_right
  have hXcard :
      (X ∩ (A ∪ B)).card = (X ∩ A).card + (X ∩ B).card := by
    rw [hXsplit, Finset.card_union_of_disjoint hXdisj]
  have hYcard :
      (Y ∩ (A ∪ B)).card = (Y ∩ A).card + (Y ∩ B).card := by
    rw [hYsplit, Finset.card_union_of_disjoint hYdisj]

  rw [hXcard, hYcard]
  omega

/-! ## Edge-minimal well-linked subgraph -/

/-- A same-vertex subgraph that preserves a scaled well-linked terminal set
and is minimal under deletion of any one of its edges. -/
structure EdgeMinimalScaledWellLinkedSubgraph [Fintype V]
    (G : _root_.SimpleGraph V) (C T : Finset V)
    (alphaNum alphaDen : ℕ) where
  H : _root_.SimpleGraph V
  le_original : H ≤ G
  wellLinked : Section46.ScaledEdgeWellLinkedIn H C T alphaNum alphaDen
  deleteEdge_not_wellLinked :
    ∀ ⦃a b : V⦄, H.Adj a b →
      ¬ Section46.ScaledEdgeWellLinkedIn
        (H.deleteEdges ({s(a, b)} : Set (Sym2 V)))
        C T alphaNum alphaDen

omit [DecidableEq V] in
private theorem edgeSet_deleteEdges_singleton_ncard_lt [Fintype V]
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

/-- The edge-minimal graph chosen immediately before Chuzhoy Section 7,
Lemma 7.2, exists because the ambient graph has finitely many edges. -/
theorem exists_edgeMinimalScaledWellLinkedSubgraph [Fintype V]
    {C T : Finset V} {alphaNum alphaDen : ℕ}
    (hwell :
      Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen) :
    Nonempty
      (EdgeMinimalScaledWellLinkedSubgraph G C T alphaNum alphaDen) := by
  classical
  let Candidate :=
    {H : _root_.SimpleGraph V //
      H ≤ G ∧
        Section46.ScaledEdgeWellLinkedIn H C T alphaNum alphaDen}
  let HasEdgeCount : ℕ → Prop := fun n =>
    ∃ H : Candidate, H.1.edgeSet.ncard = n
  have hExists : ∃ n : ℕ, HasEdgeCount n := by
    refine ⟨G.edgeSet.ncard, ⟨G, le_rfl, hwell⟩, rfl⟩
  let edgeMin := Nat.find hExists
  rcases Nat.find_spec hExists with ⟨Hmin, hHminCard⟩
  refine ⟨{
    H := Hmin.1
    le_original := Hmin.2.1
    wellLinked := Hmin.2.2
    deleteEdge_not_wellLinked := ?_ }⟩
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

/-- Restoring the deleted ambient edges preserves the terminal
well-linkedness certified by an edge-minimal package. -/
theorem EdgeMinimalScaledWellLinkedSubgraph.wellLinked_original [Fintype V]
    {C T : Finset V} {alphaNum alphaDen : ℕ}
    (M : EdgeMinimalScaledWellLinkedSubgraph G C T alphaNum alphaDen) :
    Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen :=
  scaledEdgeWellLinkedIn_mono_graph M.wellLinked M.le_original

/-- Chuzhoy, Section 7, Observation 7.12.

Three pairwise node-linked terminal sets that are individually
node-well-linked have a `1/5`-well-linked union.  No equal-cardinality
assumption is needed for the cut formulation. -/
theorem observation_7_12_triple_union_scaledEdgeWellLinkedIn [Fintype V]
    {C A B D : Finset V}
    (hA : NodeWellLinkedIn G C A)
    (hB : NodeWellLinkedIn G C B)
    (hD : NodeWellLinkedIn G C D)
    (hAB : NodeLinkedIn G C A B)
    (hAD : NodeLinkedIn G C A D)
    (hBD : NodeLinkedIn G C B D) :
    Section46.ScaledEdgeWellLinkedIn G C (A ∪ B ∪ D) 1 5 := by
  classical
  refine ⟨by norm_num, by norm_num,
    union_subset (union_subset hA.1 hB.1) hD.1, ?_⟩
  intro X Y hXC hYC hcover hdisj
  have hcoverYX : Y ∪ X = C := by
    simpa [union_comm] using hcover

  have hsame (T : Finset V) (hT : NodeWellLinkedIn G C T) :
      min (X ∩ T).card (Y ∩ T).card ≤
        (Section44.edgeBoundary G X Y).card := by
    rcases hT.2 inter_subset_right inter_subset_right
        (hdisj.mono inter_subset_left inter_subset_left) with
      ⟨P, hcard, hstay⟩
    have hP := PathPacking.card_le_edgeBoundary_of_staysIn_partition
      P inter_subset_left inter_subset_left hstay hcover hdisj
    simpa [hcard] using hP
  have hforward (S T : Finset V) (hST : NodeLinkedIn G C S T) :
      min (X ∩ S).card (Y ∩ T).card ≤
        (Section44.edgeBoundary G X Y).card := by
    rcases hST.2.2.2 inter_subset_right inter_subset_right with
      ⟨P, hcard, hstay⟩
    have hP := PathPacking.card_le_edgeBoundary_of_staysIn_partition
      P inter_subset_left inter_subset_left hstay hcover hdisj
    simpa [hcard] using hP
  have hbackward (S T : Finset V) (hST : NodeLinkedIn G C S T) :
      min (Y ∩ S).card (X ∩ T).card ≤
        (Section44.edgeBoundary G X Y).card := by
    rcases hST.2.2.2 inter_subset_right inter_subset_right with
      ⟨P, hcard, hstay⟩
    have hP := PathPacking.card_le_edgeBoundary_of_staysIn_partition
      P inter_subset_left inter_subset_left hstay hcoverYX hdisj.symm
    simpa [hcard, Section44.edgeBoundary_comm (G := G) Y X] using hP

  have hAXAY := hsame A hA
  have hBXBY := hsame B hB
  have hDXDY := hsame D hD
  have hAXBY := hforward A B hAB
  have hAYBX := hbackward A B hAB
  have hAXDY := hforward A D hAD
  have hAYDX := hbackward A D hAD
  have hBXDY := hforward B D hBD
  have hBYDX := hbackward B D hBD

  have hXAB : Disjoint (X ∩ A) (X ∩ B) :=
    hAB.2.2.1.mono inter_subset_right inter_subset_right
  have hYAB : Disjoint (Y ∩ A) (Y ∩ B) :=
    hAB.2.2.1.mono inter_subset_right inter_subset_right
  have hXAB_D : Disjoint ((X ∩ A) ∪ (X ∩ B)) (X ∩ D) := by
    rw [Finset.disjoint_left]
    intro v hvAB hvD
    rcases mem_union.mp hvAB with hvA | hvB
    · exact Finset.disjoint_left.mp hAD.2.2.1
        (mem_inter.mp hvA).2 (mem_inter.mp hvD).2
    · exact Finset.disjoint_left.mp hBD.2.2.1
        (mem_inter.mp hvB).2 (mem_inter.mp hvD).2
  have hYAB_D : Disjoint ((Y ∩ A) ∪ (Y ∩ B)) (Y ∩ D) := by
    rw [Finset.disjoint_left]
    intro v hvAB hvD
    rcases mem_union.mp hvAB with hvA | hvB
    · exact Finset.disjoint_left.mp hAD.2.2.1
        (mem_inter.mp hvA).2 (mem_inter.mp hvD).2
    · exact Finset.disjoint_left.mp hBD.2.2.1
        (mem_inter.mp hvB).2 (mem_inter.mp hvD).2
  have hXsplit :
      X ∩ (A ∪ B ∪ D) = ((X ∩ A) ∪ (X ∩ B)) ∪ (X ∩ D) := by
    ext v
    simp only [mem_inter, mem_union]
    tauto
  have hYsplit :
      Y ∩ (A ∪ B ∪ D) = ((Y ∩ A) ∪ (Y ∩ B)) ∪ (Y ∩ D) := by
    ext v
    simp only [mem_inter, mem_union]
    tauto
  have hXcard :
      (X ∩ (A ∪ B ∪ D)).card =
        (X ∩ A).card + (X ∩ B).card + (X ∩ D).card := by
    rw [hXsplit, Finset.card_union_of_disjoint hXAB_D,
      Finset.card_union_of_disjoint hXAB]
  have hYcard :
      (Y ∩ (A ∪ B ∪ D)).card =
        (Y ∩ A).card + (Y ∩ B).card + (Y ∩ D).card := by
    rw [hYsplit, Finset.card_union_of_disjoint hYAB_D,
      Finset.card_union_of_disjoint hYAB]

  rw [hXcard, hYcard]
  omega

end AppendixA3ClusterSplit
end SimpleGraph

end Lax17Proofs
