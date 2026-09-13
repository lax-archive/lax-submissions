import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Leaves
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Bundle
import Lax17Proofs.Source.Degree

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5.4.1: restoring the Claim 5.15 paths

This module implements the step immediately after preprint Claim 5.15
(journal Claim 5.17).  A full-source packing in the replicated, router-pruned
network is projected back to the host.  Its first artificial edge is replaced
by the corresponding original boundary edge.

The outside suffixes are globally node-disjoint.  Router-side boundary
vertices can still repeat: at most `Delta` restored incidences use one such
vertex in a graph of maximum degree `Delta`.  Starting Claim 5.15 with
`Delta * q` replicas and retaining one copy for each of `q` distinct boundary
vertices therefore gives exactly `q` globally node-disjoint host paths per
selected router.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase1Restoration


open Finset

open ChekuriChuzhoySection5Phase1Leaves

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {m r q Delta : Nat}
variable {cluster : Fin m -> Finset V} {root : Finset V}

/-- The exact replicated-network packing produced by Claim 5.15. -/
abbrev NetworkPacking
    (G : _root_.SimpleGraph V) (cluster : Fin m -> Finset V)
    (root : Finset V) (r : Nat) :=
  PathPacking
    (Vertex.graph (q := r) G cluster)
    (Vertex.sources (V := V) (m := m) (q := r))
    (Vertex.oldImage (m := m) (q := r) root)

section CanonicalRestoration

variable
  (P : NetworkPacking G cluster root r)
  (hsourceSet :
    P.sourceSet = Vertex.sources (V := V) (m := m) (q := r))

/-- The unique packed path that starts at the replica `(i,a)`. -/
noncomputable def networkIndex (i : Fin m) (a : Fin r) : P.Index :=
  Classical.choose
    (P.exists_orient_source_eq_of_mem_sourceSet (by
      rw [hsourceSet]
      exact Vertex.mem_sources_source (V := V) i a))

@[simp] theorem networkIndex_source (i : Fin m) (a : Fin r) :
    (P.orient.path (networkIndex P hsourceSet i a)).source =
      Vertex.source (V := V) i a :=
  Classical.choose_spec
    (P.exists_orient_source_eq_of_mem_sourceSet (by
      rw [hsourceSet]
      exact Vertex.mem_sources_source (V := V) i a))

theorem networkIndex_injective :
    Function.Injective
      (fun z : Fin m × Fin r =>
        networkIndex P hsourceSet z.1 z.2) := by
  intro z w hzw
  have hs :=
    (networkIndex_source P hsourceSet z.1 z.2).symm.trans
      ((congrArg (fun k => (P.orient.path k).source) hzw).trans
        (networkIndex_source P hsourceSet w.1 w.2))
  injection hs with hi ha
  exact Prod.ext hi ha

/-- The oriented replicated-network path belonging to `(i,a)`. -/
noncomputable def networkPath (i : Fin m) (a : Fin r) :
    Lax17Proofs.SimpleGraph.GraphPath (Vertex.graph (q := r) G cluster) :=
  P.orient.path (networkIndex P hsourceSet i a)

@[simp] theorem networkPath_source (i : Fin m) (a : Fin r) :
    (networkPath P hsourceSet i a).source =
      Vertex.source (V := V) i a :=
  networkIndex_source P hsourceSet i a

theorem networkPath_target_mem_oldImage (i : Fin m) (a : Fin r) :
    (networkPath P hsourceSet i a).target ∈
      Vertex.oldImage (m := m) (q := r) root :=
  Lax17Proofs.SimpleGraph.GraphPath.orient_target_mem
    (P.path (networkIndex P hsourceSet i a))
    (P.connects (networkIndex P hsourceSet i a))

theorem networkPath_source_ne_target (i : Fin m) (a : Fin r) :
    (networkPath P hsourceSet i a).source ≠
      (networkPath P hsourceSet i a).target := by
  intro h
  have hs :
      (networkPath P hsourceSet i a).source ∈
        Vertex.sources (V := V) (m := m) (q := r) := by
    rw [networkPath_source]
    exact Vertex.mem_sources_source (V := V) i a
  exact Finset.disjoint_left.mp (Vertex.sources_disjoint_oldImage root)
    hs (by
      have ht := networkPath_target_mem_oldImage P hsourceSet i a
      rw [← h] at ht
      exact ht)

/-- The old-only suffix obtained by deleting the artificial source edge. -/
noncomputable def droppedNetworkPath (i : Fin m) (a : Fin r) :
    Lax17Proofs.SimpleGraph.GraphPath (Vertex.graph (q := r) G cluster) :=
  Vertex.GraphPath.dropFirst (networkPath P hsourceSet i a)

theorem droppedNetworkPath_subset_oldRegion (i : Fin m) (a : Fin r) :
    (droppedNetworkPath P hsourceSet i a).vertexSet ⊆
      Vertex.oldRegion (V := V) (m := m) (q := r) :=
  Vertex.packing_dropFirst_subset_oldRegion P hsourceSet
    (networkIndex P hsourceSet i a)

theorem droppedNetworkPath_vertexSet_subset_networkPath
    (i : Fin m) (a : Fin r) :
    (droppedNetworkPath P hsourceSet i a).vertexSet ⊆
      (networkPath P hsourceSet i a).vertexSet :=
  Vertex.GraphPath.dropFirst_vertexSet_subset _

/-- The first old vertex of the packed path, outside every selected router. -/
noncomputable def outsideVertex (i : Fin m) (a : Fin r) : V :=
  Vertex.oldRegionValue
    ⟨(droppedNetworkPath P hsourceSet i a).source,
      droppedNetworkPath_subset_oldRegion P hsourceSet i a
        (droppedNetworkPath P hsourceSet i a).source_mem_vertexSet⟩

theorem old_outsideVertex (i : Fin m) (a : Fin r) :
    Vertex.old (m := m) (q := r) (outsideVertex P hsourceSet i a) =
      (droppedNetworkPath P hsourceSet i a).source :=
  Vertex.old_oldRegionValue _

theorem network_source_adj_old_outside (i : Fin m) (a : Fin r) :
    (Vertex.graph (q := r) G cluster).Adj
      (Vertex.source (V := V) i a)
      (Vertex.old (m := m) (q := r)
        (outsideVertex P hsourceSet i a)) := by
  simpa only [networkPath_source, old_outsideVertex] using
    Vertex.GraphPath.source_adj_dropFirst_source
      (networkPath P hsourceSet i a)
      (networkPath_source_ne_target P hsourceSet i a)

theorem outsideVertex_not_mem_selectedUnion (i : Fin m) (a : Fin r) :
    outsideVertex P hsourceSet i a ∉ selectedUnion cluster := by
  have h :=
    (Vertex.adj_source_old_iff (G := G) (cluster := cluster) i a).mp
      (network_source_adj_old_outside P hsourceSet i a)
  exact (Finset.mem_sdiff.mp h.1).2

/-- A canonical router-side endpoint restoring the artificial first edge. -/
noncomputable def boundaryVertex (i : Fin m) (a : Fin r) : V :=
  Classical.choose
    ((Vertex.adj_source_old_iff (G := G) (cluster := cluster) i a).mp
      (network_source_adj_old_outside P hsourceSet i a)).2

theorem boundaryVertex_mem_cluster (i : Fin m) (a : Fin r) :
    boundaryVertex P hsourceSet i a ∈ cluster i :=
  (Classical.choose_spec
    ((Vertex.adj_source_old_iff (G := G) (cluster := cluster) i a).mp
      (network_source_adj_old_outside P hsourceSet i a)).2).1

theorem boundaryVertex_adj_outside (i : Fin m) (a : Fin r) :
    G.Adj (boundaryVertex P hsourceSet i a)
      (outsideVertex P hsourceSet i a) :=
  (Classical.choose_spec
    ((Vertex.adj_source_old_iff (G := G) (cluster := cluster) i a).mp
      (network_source_adj_old_outside P hsourceSet i a)).2).2

/-- The old suffix projected to the pruned host. -/
noncomputable def prunedSuffix (i : Fin m) (a : Fin r) :
    Lax17Proofs.SimpleGraph.GraphPath (prunedHost G cluster) :=
  Vertex.GraphPath.projectOld
    (droppedNetworkPath P hsourceSet i a)
    (droppedNetworkPath_subset_oldRegion P hsourceSet i a)

@[simp] theorem prunedSuffix_source (i : Fin m) (a : Fin r) :
    (prunedSuffix P hsourceSet i a).source =
      outsideVertex P hsourceSet i a :=
  rfl

theorem old_prunedSuffix_target (i : Fin m) (a : Fin r) :
    Vertex.old (m := m) (q := r)
        (prunedSuffix P hsourceSet i a).target =
      (networkPath P hsourceSet i a).target := by
  calc
    Vertex.old (m := m) (q := r)
        (prunedSuffix P hsourceSet i a).target =
        (droppedNetworkPath P hsourceSet i a).target :=
      Vertex.old_oldRegionValue _
    _ = (networkPath P hsourceSet i a).target := by
      simp [droppedNetworkPath]

theorem prunedSuffix_target_mem_root (i : Fin m) (a : Fin r) :
    (prunedSuffix P hsourceSet i a).target ∈ root := by
  have ht := networkPath_target_mem_oldImage P hsourceSet i a
  rw [← old_prunedSuffix_target P hsourceSet i a] at ht
  exact Vertex.mem_oldImage.mp ht

theorem mem_prunedSuffix_vertexSet_iff
    (i : Fin m) (a : Fin r) (x : V) :
    x ∈ (prunedSuffix P hsourceSet i a).vertexSet ↔
      Vertex.old (m := m) (q := r) x ∈
        (droppedNetworkPath P hsourceSet i a).vertexSet := by
  classical
  rw [prunedSuffix, Vertex.GraphPath.projectOld,
    ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective_vertexSet]
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, hzx⟩
    have hzP :
        z.1 ∈ (droppedNetworkPath P hsourceSet i a).vertexSet :=
      (Lax17Proofs.SimpleGraph.GraphPath.mem_induce_vertexSet
        (droppedNetworkPath P hsourceSet i a) _
        (droppedNetworkPath_subset_oldRegion P hsourceSet i a) z).mp hz
    have hval : Vertex.old (m := m) (q := r) x = z.1 := by
      rw [← Vertex.old_oldRegionValue z]
      exact congrArg (Vertex.old (m := m) (q := r)) hzx.symm
    simpa [hval] using hzP
  · intro hx
    let z :
        {z : Vertex V m r //
          z ∈ Vertex.oldRegion (V := V) (m := m) (q := r)} :=
      ⟨Vertex.old (m := m) (q := r) x,
        Vertex.mem_oldRegion_old x⟩
    exact Finset.mem_image.mpr
      ⟨z,
        (Lax17Proofs.SimpleGraph.GraphPath.mem_induce_vertexSet
          (droppedNetworkPath P hsourceSet i a) _
          (droppedNetworkPath_subset_oldRegion P hsourceSet i a) z).mpr hx,
        by
          change Vertex.oldRegionValue z = x
          apply Vertex.old_injective (m := m) (q := r)
          rw [Vertex.old_oldRegionValue]⟩

private theorem inducedWalk_support_subset
    {C : Finset V} {x y : V}
    (W : (inducedOnFinset G C).Walk x y) (hx : x ∈ C) :
    ∀ z : V, z ∈ W.support -> z ∈ C := by
  induction W with
  | nil =>
      intro z hz
      simp at hz
      subst z
      exact hx
  | cons hxy W ih =>
      intro z hz
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hxy.2.1
      · exact ih hxy.2.2 z hz

theorem prunedSuffix_vertexSet_subset_compl_selectedUnion
    (i : Fin m) (a : Fin r) :
    (prunedSuffix P hsourceSet i a).vertexSet ⊆
      Finset.univ \ selectedUnion cluster := by
  intro z hz
  let C := Finset.univ \ selectedUnion cluster
  have hs : (prunedSuffix P hsourceSet i a).source ∈ C := by
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, outsideVertex_not_mem_selectedUnion
        P hsourceSet i a⟩
  have hzSupport :
      z ∈ (prunedSuffix P hsourceSet i a).walk.support := by
    simpa [Lax17Proofs.SimpleGraph.GraphPath.vertexSet] using hz
  exact inducedWalk_support_subset
    (G := G) (C := C) (prunedSuffix P hsourceSet i a).walk hs z hzSupport

/-- Restore the original router boundary edge and view the suffix in `G`. -/
noncomputable def restoredPath (i : Fin m) (a : Fin r) :
    Lax17Proofs.SimpleGraph.GraphPath G := by
  let L :=
    ChekuriChuzhoyPendantVertex.GraphPath.ofAdj
      (boundaryVertex_adj_outside P hsourceSet i a)
  let Q :=
    (prunedSuffix P hsourceSet i a).mapLe
      (prunedHost_le (G := G) (cluster := cluster))
  have hLQ : L.target = Q.source := by
    change outsideVertex P hsourceSet i a =
      (prunedSuffix P hsourceSet i a).source
    exact (prunedSuffix_source P hsourceSet i a).symm
  exact L.appendWithEqToPath Q hLQ

@[simp] theorem restoredPath_source (i : Fin m) (a : Fin r) :
    (restoredPath P hsourceSet i a).source =
      boundaryVertex P hsourceSet i a := by
  simp [restoredPath]

@[simp] theorem restoredPath_target (i : Fin m) (a : Fin r) :
    (restoredPath P hsourceSet i a).target =
      (prunedSuffix P hsourceSet i a).target :=
  rfl

theorem restoredPath_target_mem_root (i : Fin m) (a : Fin r) :
    (restoredPath P hsourceSet i a).target ∈ root := by
  rw [restoredPath_target]
  exact prunedSuffix_target_mem_root P hsourceSet i a

theorem restoredPath_vertexSet_subset
    (i : Fin m) (a : Fin r) :
    (restoredPath P hsourceSet i a).vertexSet ⊆
      {boundaryVertex P hsourceSet i a} ∪
        (prunedSuffix P hsourceSet i a).vertexSet := by
  classical
  let L :=
    ChekuriChuzhoyPendantVertex.GraphPath.ofAdj
      (boundaryVertex_adj_outside P hsourceSet i a)
  let Q :=
    (prunedSuffix P hsourceSet i a).mapLe
      (prunedHost_le (G := G) (cluster := cluster))
  have hglue : L.target = Q.source := by
    change outsideVertex P hsourceSet i a =
      (prunedSuffix P hsourceSet i a).source
    exact (prunedSuffix_source P hsourceSet i a).symm
  intro z hz
  have hzPieces : z ∈ L.vertexSet ∪ Q.vertexSet := by
    exact L.appendWithEqToPath_vertexSet_subset Q hglue (by
      simpa [restoredPath, L, Q] using hz)
  rcases Finset.mem_union.mp hzPieces with hzL | hzQ
  · have hzPair :=
      ChekuriChuzhoyPendantVertex.GraphPath.ofAdj_vertexSet_subset_pair
        (boundaryVertex_adj_outside P hsourceSet i a) hzL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
    rcases hzPair with rfl | rfl
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_right _
        (by
          rw [← prunedSuffix_source P hsourceSet i a]
          exact Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet _)
  · exact Finset.mem_union_right _ (by
      simpa [Q] using hzQ)

theorem restoredPath_internallyDisjointFrom_selectedUnion
    (i : Fin m) (a : Fin r) :
    (restoredPath P hsourceSet i a).InternallyDisjointFromSet
      (selectedUnion cluster) := by
  intro z hzPath hzSelected
  rcases Finset.mem_union.mp
      (restoredPath_vertexSet_subset P hsourceSet i a hzPath) with
    hzBoundary | hzSuffix
  · have hz : z = boundaryVertex P hsourceSet i a := by
      simpa using hzBoundary
    exact Or.inl (by simpa [hz] using restoredPath_source P hsourceSet i a)
  · exact False.elim
      ((Finset.mem_sdiff.mp
        (prunedSuffix_vertexSet_subset_compl_selectedUnion
          P hsourceSet i a hzSuffix)).2 hzSelected)

theorem prunedSuffix_nodeDisjoint_of_index_ne
    {i j : Fin m} {a b : Fin r}
    (hne :
      networkIndex P hsourceSet i a ≠
        networkIndex P hsourceSet j b) :
    Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint
      (prunedSuffix P hsourceSet i a)
      (prunedSuffix P hsourceSet j b) := by
  classical
  rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro z hzi hzj
  have hziOld :=
    (mem_prunedSuffix_vertexSet_iff P hsourceSet i a z).mp hzi
  have hzjOld :=
    (mem_prunedSuffix_vertexSet_iff P hsourceSet j b z).mp hzj
  exact Finset.disjoint_left.mp (P.orient.node_disjoint hne)
    (droppedNetworkPath_vertexSet_subset_networkPath P hsourceSet i a hziOld)
    (droppedNetworkPath_vertexSet_subset_networkPath P hsourceSet j b hzjOld)

theorem restoredPath_nodeDisjoint_of_boundary_ne
    {i j : Fin m} {a b : Fin r}
    (hboundary :
      boundaryVertex P hsourceSet i a ≠
        boundaryVertex P hsourceSet j b) :
    Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint
      (restoredPath P hsourceSet i a)
      (restoredPath P hsourceSet j b) := by
  classical
  have hindex :
      networkIndex P hsourceSet i a ≠
        networkIndex P hsourceSet j b := by
    intro h
    have hz :
        (i, a) = (j, b) :=
      networkIndex_injective P hsourceSet h
    cases hz
    exact hboundary rfl
  have hsuffix :=
    prunedSuffix_nodeDisjoint_of_index_ne P hsourceSet hindex
  rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro z hzi hzj
  rcases Finset.mem_union.mp
      (restoredPath_vertexSet_subset P hsourceSet i a hzi) with
    hziBoundary | hziSuffix
  · have hziEq : z = boundaryVertex P hsourceSet i a := by
      simpa using hziBoundary
    rcases Finset.mem_union.mp
        (restoredPath_vertexSet_subset P hsourceSet j b hzj) with
      hzjBoundary | hzjSuffix
    · have hzjEq : z = boundaryVertex P hsourceSet j b := by
        simpa using hzjBoundary
      exact hboundary (hziEq.symm.trans hzjEq)
    · have hiSelected :
          boundaryVertex P hsourceSet i a ∈
            selectedUnion cluster :=
        mem_selectedUnion.mpr
          ⟨i, boundaryVertex_mem_cluster P hsourceSet i a⟩
      exact (Finset.mem_sdiff.mp
        (prunedSuffix_vertexSet_subset_compl_selectedUnion
          P hsourceSet j b hzjSuffix)).2 (hziEq ▸ hiSelected)
  · rcases Finset.mem_union.mp
        (restoredPath_vertexSet_subset P hsourceSet j b hzj) with
      hzjBoundary | hzjSuffix
    · have hzjEq : z = boundaryVertex P hsourceSet j b := by
        simpa using hzjBoundary
      have hjSelected :
          boundaryVertex P hsourceSet j b ∈
            selectedUnion cluster :=
        mem_selectedUnion.mpr
          ⟨j, boundaryVertex_mem_cluster P hsourceSet j b⟩
      exact (Finset.mem_sdiff.mp
        (prunedSuffix_vertexSet_subset_compl_selectedUnion
          P hsourceSet i a hziSuffix)).2 (hzjEq ▸ hjSelected)
    · exact Finset.disjoint_left.mp hsuffix hziSuffix hzjSuffix

theorem outsideVertex_injective :
    Function.Injective
      (fun z : Fin m × Fin r =>
        outsideVertex P hsourceSet z.1 z.2) := by
  intro z w houtside
  change outsideVertex P hsourceSet z.1 z.2 =
    outsideVertex P hsourceSet w.1 w.2 at houtside
  apply networkIndex_injective P hsourceSet
  by_contra hne
  have hdisj := P.orient.node_disjoint hne
  have hz :
      Vertex.old (m := m) (q := r)
          (outsideVertex P hsourceSet z.1 z.2) ∈
        (networkPath P hsourceSet z.1 z.2).vertexSet :=
    droppedNetworkPath_vertexSet_subset_networkPath
      P hsourceSet z.1 z.2 (by
        rw [old_outsideVertex P hsourceSet z.1 z.2]
        exact (droppedNetworkPath P hsourceSet z.1 z.2).source_mem_vertexSet)
  have hw :
      Vertex.old (m := m) (q := r)
          (outsideVertex P hsourceSet z.1 z.2) ∈
        (networkPath P hsourceSet w.1 w.2).vertexSet := by
    rw [houtside]
    exact droppedNetworkPath_vertexSet_subset_networkPath
      P hsourceSet w.1 w.2 (by
        rw [old_outsideVertex P hsourceSet w.1 w.2]
        exact (droppedNetworkPath P hsourceSet w.1 w.2).source_mem_vertexSet)
  exact Finset.disjoint_left.mp hdisj hz hw

theorem boundaryVertex_fiber_card_le
    (hdegree : MaxDegreeAtMost G Delta)
    (i : Fin m) (x : V) :
    ((Finset.univ : Finset (Fin r)).filter
      fun a => boundaryVertex P hsourceSet i a = x).card ≤ Delta := by
  classical
  let fiber :=
    (Finset.univ : Finset (Fin r)).filter
      fun a => boundaryVertex P hsourceSet i a = x
  have houtsideInj :
      Set.InjOn (fun a : Fin r => outsideVertex P hsourceSet i a) fiber := by
    intro a _ha b _hb hab
    have hz :
        (i, a) = (i, b) :=
      outsideVertex_injective P hsourceSet hab
    exact congrArg Prod.snd hz
  have himage :
      fiber.image (fun a => outsideVertex P hsourceSet i a) ⊆
        MaxDegreeAtMost.neighborFinset hdegree x := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
    have hax :
        boundaryVertex P hsourceSet i a = x :=
      (Finset.mem_filter.mp ha).2
    exact (MaxDegreeAtMost.mem_neighborFinset hdegree x _).2
      (hax ▸ boundaryVertex_adj_outside P hsourceSet i a)
  calc
    fiber.card =
        (fiber.image fun a => outsideVertex P hsourceSet i a).card := by
      symm
      exact Finset.card_image_of_injOn houtsideInj
    _ ≤ (MaxDegreeAtMost.neighborFinset hdegree x).card :=
      Finset.card_le_card himage
    _ ≤ Delta :=
      MaxDegreeAtMost.card_neighborFinset_le hdegree x

/-- All distinct router-side boundary vertices available for router `i`. -/
noncomputable def availableBoundary (i : Fin m) : Finset V :=
  (Finset.univ : Finset (Fin r)).image
    fun a => boundaryVertex P hsourceSet i a

theorem replicaCount_le_degree_mul_availableBoundary_card
    (hdegree : MaxDegreeAtMost G Delta) (i : Fin m) :
    r ≤ Delta * (availableBoundary P hsourceSet i).card := by
  simpa [availableBoundary] using
    Finset.card_le_mul_card_image
      (Finset.univ : Finset (Fin r)) Delta
      (fun x _ =>
        boundaryVertex_fiber_card_le P hsourceSet hdegree i x)

end CanonicalRestoration

/-- An exact choice of `q` distinct restored boundary vertices in every
selected router. -/
structure BoundarySelection
    (P : NetworkPacking G cluster root r)
    (hsourceSet :
      P.sourceSet = Vertex.sources (V := V) (m := m) (q := r))
    (q : Nat) where
  sourceSet : Fin m -> Finset V
  sourceSet_subset_available :
    ∀ i, sourceSet i ⊆ availableBoundary P hsourceSet i
  sourceSet_card : ∀ i, (sourceSet i).card = q

theorem exists_boundarySelection
    (P : NetworkPacking G cluster root r)
    (hsourceSet :
      P.sourceSet = Vertex.sources (V := V) (m := m) (q := r))
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (hreplicas : Delta * q ≤ r) :
    Nonempty (BoundarySelection P hsourceSet q) := by
  classical
  have hlarge :
      ∀ i : Fin m, q ≤ (availableBoundary P hsourceSet i).card := by
    intro i
    have hmul :
        Delta * q ≤
          Delta * (availableBoundary P hsourceSet i).card :=
      hreplicas.trans
        (replicaCount_le_degree_mul_availableBoundary_card
          P hsourceSet hdegree i)
    exact Nat.le_of_mul_le_mul_left hmul hDelta
  let A : Fin m -> Finset V := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hlarge i))
  have hA : ∀ i : Fin m,
      A i ⊆ availableBoundary P hsourceSet i ∧ (A i).card = q := by
    intro i
    exact Classical.choose_spec
      (Finset.exists_subset_card_eq (hlarge i))
  exact ⟨{
    sourceSet := A
    sourceSet_subset_available := fun i => (hA i).1
    sourceSet_card := fun i => (hA i).2
  }⟩

section SelectedRestoration

variable
  (P : NetworkPacking G cluster root r)
  (hsourceSet :
    P.sourceSet = Vertex.sources (V := V) (m := m) (q := r))
  (B : BoundarySelection P hsourceSet q)

theorem BoundarySelection.sourceSet_subset_cluster (i : Fin m) :
    B.sourceSet i ⊆ cluster i := by
  intro x hx
  have hxAvailable := B.sourceSet_subset_available i hx
  rcases Finset.mem_image.mp hxAvailable with ⟨a, _ha, hax⟩
  rw [← hax]
  exact boundaryVertex_mem_cluster P hsourceSet i a

theorem BoundarySelection.sourceSet_subset_interface (i : Fin m) :
    B.sourceSet i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) := by
  intro x hx
  have hxAvailable := B.sourceSet_subset_available i hx
  rcases Finset.mem_image.mp hxAvailable with ⟨a, _ha, hax⟩
  rw [← hax]
  apply ChekuriChuzhoySection5Clustering.mem_interfaceVertices.mpr
  refine ⟨boundaryVertex_mem_cluster P hsourceSet i a,
    outsideVertex P hsourceSet i a, ?_,
    boundaryVertex_adj_outside P hsourceSet i a⟩
  intro houtside
  exact outsideVertex_not_mem_selectedUnion P hsourceSet i a
    (mem_selectedUnion.mpr ⟨i, houtside⟩)

/-- A source replica whose restored boundary vertex is the selected vertex
`x`. -/
noncomputable def copyOfBoundary (i : Fin m)
    (x : {x : V // x ∈ B.sourceSet i}) : Fin r :=
  Classical.choose
    (Finset.mem_image.mp
      (B.sourceSet_subset_available i x.2))

@[simp] theorem boundaryVertex_copyOfBoundary (i : Fin m)
    (x : {x : V // x ∈ B.sourceSet i}) :
    boundaryVertex P hsourceSet i (copyOfBoundary P hsourceSet B i x) =
      x.1 :=
  (Classical.choose_spec
    (Finset.mem_image.mp
      (B.sourceSet_subset_available i x.2))).2

theorem copyOfBoundary_injective (i : Fin m) :
    Function.Injective (copyOfBoundary P hsourceSet B i) := by
  intro x y hxy
  apply Subtype.ext
  rw [← boundaryVertex_copyOfBoundary P hsourceSet B i x,
    ← boundaryVertex_copyOfBoundary P hsourceSet B i y, hxy]

/-- The restored host path indexed by a selected boundary vertex. -/
noncomputable def selectedPath (i : Fin m)
    (x : {x : V // x ∈ B.sourceSet i}) :
    Lax17Proofs.SimpleGraph.GraphPath G :=
  restoredPath P hsourceSet i (copyOfBoundary P hsourceSet B i x)

@[simp] theorem selectedPath_source (i : Fin m)
    (x : {x : V // x ∈ B.sourceSet i}) :
    (selectedPath P hsourceSet B i x).source = x.1 := by
  rw [selectedPath, restoredPath_source,
    boundaryVertex_copyOfBoundary]

theorem selectedPath_target_mem_root (i : Fin m)
    (x : {x : V // x ∈ B.sourceSet i}) :
    (selectedPath P hsourceSet B i x).target ∈ root :=
  restoredPath_target_mem_root P hsourceSet i
    (copyOfBoundary P hsourceSet B i x)

theorem selectedPath_internallyDisjointFrom_selectedUnion
    (i : Fin m) (x : {x : V // x ∈ B.sourceSet i}) :
    (selectedPath P hsourceSet B i x).InternallyDisjointFromSet
      (selectedUnion cluster) :=
  restoredPath_internallyDisjointFrom_selectedUnion P hsourceSet i
    (copyOfBoundary P hsourceSet B i x)

theorem selectedPath_nodeDisjoint_of_val_ne
    {i j : Fin m}
    {x : {x : V // x ∈ B.sourceSet i}}
    {y : {y : V // y ∈ B.sourceSet j}}
    (hxy : x.1 ≠ y.1) :
    Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint
      (selectedPath P hsourceSet B i x)
      (selectedPath P hsourceSet B j y) := by
  apply restoredPath_nodeDisjoint_of_boundary_ne P hsourceSet
  simpa only [boundaryVertex_copyOfBoundary] using hxy

/-- The exact set of root endpoints used by router `i`. -/
noncomputable def selectedTargetSet (i : Fin m) : Finset V :=
  (Finset.univ : Finset {x : V // x ∈ B.sourceSet i}).image
    fun x => (selectedPath P hsourceSet B i x).target

theorem selectedPath_target_injective (i : Fin m) :
    Function.Injective
      (fun x : {x : V // x ∈ B.sourceSet i} =>
        (selectedPath P hsourceSet B i x).target) := by
  intro x y htarget
  by_contra hxy
  have hval : x.1 ≠ y.1 := fun h =>
    hxy (Subtype.ext h)
  have hdisj :=
    selectedPath_nodeDisjoint_of_val_ne P hsourceSet B hval
  exact Finset.disjoint_left.mp hdisj
    (selectedPath P hsourceSet B i x).target_mem_vertexSet
    (by
      change
        (selectedPath P hsourceSet B i x).target =
          (selectedPath P hsourceSet B i y).target at htarget
      have hy := (selectedPath P hsourceSet B i y).target_mem_vertexSet
      rw [← htarget] at hy
      exact hy)

@[simp] theorem selectedTargetSet_card (i : Fin m) :
    (selectedTargetSet P hsourceSet B i).card = q := by
  rw [selectedTargetSet,
    Finset.card_image_of_injective
      (Finset.univ : Finset {x : V // x ∈ B.sourceSet i})
      (selectedPath_target_injective P hsourceSet B i)]
  simpa using B.sourceSet_card i

theorem selectedTargetSet_subset_root (i : Fin m) :
    selectedTargetSet P hsourceSet B i ⊆ root := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
  exact selectedPath_target_mem_root P hsourceSet B i x

/-- Enumerate the selected boundary set by a small (`Type 0`) index type,
as required by `PathPacking.Index`. -/
noncomputable def selectedBoundaryAt (i : Fin m)
    (a : Fin (B.sourceSet i).card) :
    {x : V // x ∈ B.sourceSet i} :=
  (B.sourceSet i).equivFin.symm a

/-- The exact `q` restored host paths belonging to router `i`. -/
noncomputable def selectedPacking (i : Fin m) :
    PathPacking G (B.sourceSet i)
      (selectedTargetSet P hsourceSet B i) where
  Index := Fin (B.sourceSet i).card
  path := fun a =>
    selectedPath P hsourceSet B i
      (selectedBoundaryAt P hsourceSet B i a)
  connects := by
    intro a
    let x := selectedBoundaryAt P hsourceSet B i a
    exact Or.inl
      ⟨by
        rw [selectedPath_source]
        exact x.2,
       Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  node_disjoint := by
    intro a b hab
    exact selectedPath_nodeDisjoint_of_val_ne P hsourceSet B
      (fun h => hab
        ((B.sourceSet i).equivFin.symm.injective (Subtype.ext h)))

@[simp] theorem selectedPacking_card (i : Fin m) :
    (selectedPacking P hsourceSet B i).card = q := by
  simp [selectedPacking, PathPacking.card, B.sourceSet_card]

theorem selectedPacking_sourceSet (i : Fin m) :
    (selectedPacking P hsourceSet B i).sourceSet = B.sourceSet i := by
  apply (selectedPacking P hsourceSet B i).sourceSet_eq_left_of_card_eq
  rw [selectedPacking_card, B.sourceSet_card]

theorem selectedPacking_targetSet (i : Fin m) :
    (selectedPacking P hsourceSet B i).targetSet =
      selectedTargetSet P hsourceSet B i := by
  apply (selectedPacking P hsourceSet B i).targetSet_eq_right_of_card_eq
  rw [selectedPacking_card, selectedTargetSet_card]

theorem selectedPacking_internallyDisjointFrom_selectedUnion (i : Fin m) :
    (selectedPacking P hsourceSet B i).InternallyDisjointFromSet
      (selectedUnion cluster) := by
  intro a
  change
    (selectedPath P hsourceSet B i
      (selectedBoundaryAt P hsourceSet B i a)).InternallyDisjointFromSet
        (selectedUnion cluster)
  exact selectedPath_internallyDisjointFrom_selectedUnion
    P hsourceSet B i (selectedBoundaryAt P hsourceSet B i a)

theorem selectedPacking_mutuallyNodeDisjoint
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j -> Disjoint (cluster i) (cluster j))
    {i j : Fin m} (hij : i ≠ j) :
    (selectedPacking P hsourceSet B i).MutuallyNodeDisjoint
      (selectedPacking P hsourceSet B j) := by
  intro a b
  change
    Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint
      (selectedPath P hsourceSet B i (selectedBoundaryAt P hsourceSet B i a))
      (selectedPath P hsourceSet B j (selectedBoundaryAt P hsourceSet B j b))
  apply selectedPath_nodeDisjoint_of_val_ne P hsourceSet B
  intro hxy
  exact Finset.disjoint_left.mp (hclusterDisjoint hij)
    (BoundarySelection.sourceSet_subset_cluster P hsourceSet B i
      (selectedBoundaryAt P hsourceSet B i a).2)
    (by
      rw [hxy]
      exact BoundarySelection.sourceSet_subset_cluster P hsourceSet B j
        (selectedBoundaryAt P hsourceSet B j b).2)

end SelectedRestoration

/-- The concrete post-Claim-5.15 output.  Every selected router has exactly
`q` paths with exact, distinct endpoint sets; all paths avoid the selected
routers internally, and different router packings are mutually node-disjoint.
-/
structure RestoredLeafPackingFamily
    (G : _root_.SimpleGraph V) (cluster : Fin m -> Finset V)
    (root : Finset V) (q : Nat) where
  sourceSet : Fin m -> Finset V
  targetSet : Fin m -> Finset V
  packing : ∀ i, PathPacking G (sourceSet i) (targetSet i)
  sourceSet_subset_cluster : ∀ i, sourceSet i ⊆ cluster i
  sourceSet_subset_interface : ∀ i,
    sourceSet i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i)
  targetSet_subset_root : ∀ i, targetSet i ⊆ root
  sourceSet_card : ∀ i, (sourceSet i).card = q
  targetSet_card : ∀ i, (targetSet i).card = q
  path_count : ∀ i, (packing i).card = q
  exact_sourceSet : ∀ i, (packing i).sourceSet = sourceSet i
  exact_targetSet : ∀ i, (packing i).targetSet = targetSet i
  internallyDisjoint :
    ∀ i, (packing i).InternallyDisjointFromSet (selectedUnion cluster)
  mutuallyNodeDisjoint :
    ∀ ⦃i j : Fin m⦄, i ≠ j ->
      (packing i).MutuallyNodeDisjoint (packing j)

/-- Restore and thin a full-source Claim 5.15 packing.  The factor `Delta`
is exactly the possible multiplicity of a router-side restored endpoint. -/
theorem exists_restoredLeafPackingFamily_of_fullSourcePacking
    (P : NetworkPacking G cluster root r)
    (hsourceSet :
      P.sourceSet = Vertex.sources (V := V) (m := m) (q := r))
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (hreplicas : Delta * q ≤ r)
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j -> Disjoint (cluster i) (cluster j)) :
    Nonempty (RestoredLeafPackingFamily G cluster root q) := by
  classical
  let B :=
    Classical.choice
      (exists_boundarySelection P hsourceSet hdegree hDelta hreplicas)
  exact ⟨{
    sourceSet := B.sourceSet
    targetSet := selectedTargetSet P hsourceSet B
    packing := selectedPacking P hsourceSet B
    sourceSet_subset_cluster := B.sourceSet_subset_cluster
    sourceSet_subset_interface := B.sourceSet_subset_interface
    targetSet_subset_root :=
      selectedTargetSet_subset_root P hsourceSet B
    sourceSet_card := B.sourceSet_card
    targetSet_card := selectedTargetSet_card P hsourceSet B
    path_count := selectedPacking_card P hsourceSet B
    exact_sourceSet := selectedPacking_sourceSet P hsourceSet B
    exact_targetSet := selectedPacking_targetSet P hsourceSet B
    internallyDisjoint :=
      selectedPacking_internallyDisjointFrom_selectedUnion P hsourceSet B
    mutuallyNodeDisjoint := by
      intro i j hij
      exact selectedPacking_mutuallyNodeDisjoint
        P hsourceSet B hclusterDisjoint hij
  }⟩

/-! ## Support-tree Claim 5.14/5.15 composition -/

open ChekuriChuzhoySection5Phase1Bundle
open ChekuriChuzhoySection5RouterSkeleton

/-- The complete support-tree flow, integral extraction, restoration, and
endpoint-thinning package for Claims 5.14 and 5.15. -/
theorem exists_restoredLeafPackingFamily_of_supportTree_leafFamily
    {n : Nat} {router : Fin n → Finset V}
    (S : RouterPathSkeleton G router)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {width cap routerDen eta replicas : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (hleafInjective : Function.Injective leafRouter)
    (hleaf : ∀ i, DegreeEquals T (leafRouter i) 1)
    (rootRouter : Fin n)
    (hrootLeaf : ∀ i, rootRouter ≠ leafRouter i)
    (hrouterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (router i) (router j))
    (hband :
      ∀ i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (router i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      ∀ i,
        1 + (T.dist rootRouter (leafRouter i) - 1) *
            (routerDen + 1) ≤ eta)
    {c : Rat} (hc : 0 ≤ c)
    (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1)
    (hthin : Delta * q ≤ replicas) :
    Nonempty
      (RestoredLeafPackingFamily G
        (fun i => router (leafRouter i)) (router rootRouter) q) := by
  rcases
      claim514_claim515_of_supportTree_leafFamily
        S T hT hload hdegree hDelta B leafRouter hleaf rootRouter
        hrootLeaf hrouterDisjoint hband hcap heta hc hreplicasPos
        hreplicaValue hcapacity with
    ⟨P, _hPcard, hsourceSet, _holdRegion⟩
  have hselectedDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j →
        Disjoint (router (leafRouter i)) (router (leafRouter j)) := by
    intro i j hij
    exact hrouterDisjoint (fun h => hij (hleafInjective h))
  exact
    exists_restoredLeafPackingFamily_of_fullSourcePacking
      P hsourceSet hdegree hDelta hthin hselectedDisjoint

/-- The complete support-tree restoration package with root endpoints recorded
in the interface of the root router.  This is the source-faithful form needed
for the root-router Corollary 2.12 extraction. -/
theorem exists_restoredLeafPackingFamily_of_supportTree_leafFamily_interfaceRoot
    {n : Nat} {router : Fin n → Finset V}
    (S : RouterPathSkeleton G router)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {width cap routerDen eta replicas : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (hleafInjective : Function.Injective leafRouter)
    (hleaf : ∀ i, DegreeEquals T (leafRouter i) 1)
    (rootRouter : Fin n)
    (hrootLeaf : ∀ i, rootRouter ≠ leafRouter i)
    (hrouterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (router i) (router j))
    (hband :
      ∀ i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (router i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      ∀ i,
        1 + (T.dist rootRouter (leafRouter i) - 1) *
            (routerDen + 1) ≤ eta)
    {c : Rat} (hc : 0 ≤ c)
    (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1)
    (hthin : Delta * q ≤ replicas) :
    Nonempty
      (RestoredLeafPackingFamily G
        (fun i => router (leafRouter i))
        (ChekuriChuzhoySection5Clustering.interfaceVertices
          G (router rootRouter))
        q) := by
  rcases
      claim514_claim515_of_supportTree_leafFamily_interfaceRoot
        S T hT hload hdegree hDelta B leafRouter hleaf rootRouter
        hrootLeaf hrouterDisjoint hband hcap heta hc hreplicasPos
        hreplicaValue hcapacity with
    ⟨P, _hPcard, hsourceSet, _holdRegion⟩
  have hselectedDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j →
        Disjoint (router (leafRouter i)) (router (leafRouter j)) := by
    intro i j hij
    exact hrouterDisjoint (fun h => hij (hleafInjective h))
  exact
    exists_restoredLeafPackingFamily_of_fullSourcePacking
      P hsourceSet hdegree hDelta hthin hselectedDisjoint

end ChekuriChuzhoySection5Phase1Restoration
end SimpleGraph

end Lax17Proofs
