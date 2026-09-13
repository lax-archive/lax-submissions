import Lax17Proofs.Source.ChekuriChuzhoyPendantTerminals
import Lax17Proofs.Source.Flow
import Lax17Proofs.Source.FlowIntegrality
import Lax17Proofs.Source.LocalSubgraph

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5.4.1: the leaf-flow extraction

This module formalizes the semantic integrality step in preprint Claim 5.15
(journal Claim 5.17).  Algorithmic running time and the preceding randomized
construction of the fractional flows are not part of the statement.

The paper uses a directed auxiliary network to prevent a path from re-entering
one of the selected leaf routers.  Here the same condition is encoded by
deleting every selected-router vertex from the old part of the network.
Replicated source vertices attach directly across original boundary edges.
After integral extraction, each source incidence is restored.  At most
`Delta` restored incidences can use one router vertex, so a final finite
transversal loses one factor `Delta` and makes the boundary endpoints
distinct.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase1Leaves


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {m q Delta : Nat}
variable {cluster : Fin m -> Finset V} {root : Finset V}

/-- The union of the routers selected as leaves in Phase 1. -/
noncomputable def selectedUnion (cluster : Fin m -> Finset V) : Finset V :=
  Finset.univ.biUnion cluster

@[simp] theorem mem_selectedUnion {v : V} :
    v ∈ selectedUnion cluster ↔ ∃ i : Fin m, v ∈ cluster i := by
  classical
  simp [selectedUnion]

/-- The old part of the Claim 5.15 network.  All selected leaf routers are
isolated; paths in this graph therefore avoid them completely. -/
noncomputable def prunedHost
    (G : _root_.SimpleGraph V) (cluster : Fin m -> Finset V) :
    _root_.SimpleGraph V :=
  inducedOnFinset G (Finset.univ \ selectedUnion cluster)

theorem prunedHost_le :
    prunedHost G cluster ≤ G :=
  inducedOnFinset_le

/-- Vertices in the finite undirected encoding of the Claim 5.15 network.
There are `q` source copies for every selected router. -/
inductive Vertex (V : Type u) (m q : Nat) where
  | old : V -> Vertex V m q
  | source : Fin m -> Fin q -> Vertex V m q
deriving DecidableEq

namespace Vertex

instance : Fintype (Vertex V m q) where
  elems :=
    (Finset.univ.image old) ∪
      ((Finset.univ : Finset (Fin m × Fin q)).image
        fun z => source z.1 z.2)
  complete := by
    intro z
    cases z with
    | old v => simp
    | source i a => simp

/-- Directed presentation used by `SimpleGraph.fromRel`. -/
def rel
    (G : _root_.SimpleGraph V) (cluster : Fin m -> Finset V) :
    Vertex V m q -> Vertex V m q -> Prop
  | old x, old y => (prunedHost G cluster).Adj x y
  | source i _, old y =>
      y ∈ Finset.univ \ selectedUnion cluster ∧
        ∃ x ∈ cluster i, G.Adj x y
  | _, _ => False

/-- The finite source-replicated, router-pruned network for Claim 5.15. -/
def graph
    (G : _root_.SimpleGraph V) (cluster : Fin m -> Finset V) :
    _root_.SimpleGraph (Vertex V m q) :=
  _root_.SimpleGraph.fromRel (rel G cluster)

@[simp] theorem graph_adj {a b : Vertex V m q} :
    (graph G cluster).Adj a b ↔
      a ≠ b ∧ (rel G cluster a b ∨ rel G cluster b a) :=
  Iff.rfl

@[simp] theorem adj_old_old_iff {x y : V} :
    (graph (q := q) G cluster).Adj
      (old (q := q) x) (old (q := q) y) ↔
      (prunedHost G cluster).Adj x y := by
  rw [graph_adj]
  constructor
  · rintro ⟨_hne, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨by
      intro hxy
      cases hxy
      exact h.ne rfl, Or.inl h⟩

@[simp] theorem adj_source_old_iff (i : Fin m) (a : Fin q) {y : V} :
    (graph (q := q) G cluster).Adj (source i a) (old (q := q) y) ↔
      y ∈ Finset.univ \ selectedUnion cluster ∧
        ∃ x ∈ cluster i, G.Adj x y := by
  rw [graph_adj]
  constructor
  · rintro ⟨_hne, h | h⟩
    · exact h
    · exact False.elim h
  · intro h
    exact ⟨by simp, Or.inl h⟩

@[simp] theorem adj_old_source_iff (i : Fin m) (a : Fin q) {y : V} :
    (graph (q := q) G cluster).Adj (old (q := q) y) (source i a) ↔
      y ∈ Finset.univ \ selectedUnion cluster ∧
        ∃ x ∈ cluster i, G.Adj x y := by
  rw [(graph (q := q) G cluster).adj_comm, adj_source_old_iff]

@[simp] theorem not_adj_source_source
    (i j : Fin m) (a b : Fin q) :
    ¬(graph (q := q) G cluster).Adj (source i a) (source j b) := by
  simp [graph_adj, rel]

/-- The old-copy inclusion of the pruned host. -/
def oldHom :
    prunedHost G cluster →g graph (q := q) G cluster where
  toFun := old (q := q)
  map_rel' := by
    intro x y hxy
    exact adj_old_old_iff.mpr hxy

theorem old_injective :
    Function.Injective (old : V -> Vertex V m q) := by
  intro x y h
  injection h

/-- All replicated source vertices. -/
noncomputable def sources : Finset (Vertex V m q) :=
  (Finset.univ : Finset (Fin m × Fin q)).image
    fun z => source z.1 z.2

@[simp] theorem mem_sources_source (i : Fin m) (a : Fin q) :
    source (V := V) i a ∈ sources (V := V) (m := m) (q := q) := by
  classical
  exact Finset.mem_image.mpr ⟨(i, a), by simp, rfl⟩

@[simp] theorem not_mem_sources_old (x : V) :
    old (m := m) (q := q) x ∉ sources (V := V) (m := m) (q := q) := by
  classical
  simp [sources]

@[simp] theorem sources_card :
    (sources (V := V) (m := m) (q := q)).card = m * q := by
  classical
  rw [sources, Finset.card_image_of_injective]
  · simp
  · intro a b h
    injection h with hi ha
    exact Prod.ext hi ha

/-- Old-copy image of a finite host set. -/
noncomputable def oldImage (A : Finset V) : Finset (Vertex V m q) :=
  A.image old

@[simp] theorem mem_oldImage {A : Finset V} {x : V} :
    old (m := m) (q := q) x ∈ oldImage (m := m) (q := q) A ↔ x ∈ A := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, h⟩
    exact old_injective h ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem sources_disjoint_oldImage (A : Finset V) :
    Disjoint (sources (V := V) (m := m) (q := q))
      (oldImage (m := m) (q := q) A) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzSource hzOld
  rcases Finset.mem_image.mp hzSource with ⟨⟨i, a⟩, _h, rfl⟩
  rcases Finset.mem_image.mp hzOld with ⟨x, _hx, h⟩
  cases h

/-- The old-copy region of the replicated network. -/
noncomputable def oldRegion : Finset (Vertex V m q) :=
  Finset.univ.image (old (m := m) (q := q))

@[simp] theorem mem_oldRegion_old (x : V) :
    old (m := m) (q := q) x ∈ oldRegion (V := V) (m := m) (q := q) := by
  classical
  exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

@[simp] theorem not_mem_oldRegion_source (i : Fin m) (a : Fin q) :
    source (V := V) i a ∉ oldRegion (V := V) (m := m) (q := q) := by
  classical
  simp [oldRegion]

/-- Forget the `old` constructor on a vertex certified to be in the old
region. -/
noncomputable def oldRegionValue
    (z : {z : Vertex V m q //
      z ∈ oldRegion (V := V) (m := m) (q := q)}) : V :=
  Classical.choose (Finset.mem_image.mp z.2)

theorem old_oldRegionValue
    (z : {z : Vertex V m q //
      z ∈ oldRegion (V := V) (m := m) (q := q)}) :
    old (m := m) (q := q) (oldRegionValue z) = z.1 :=
  (Classical.choose_spec (Finset.mem_image.mp z.2)).2

@[simp] theorem oldRegionValue_old (x : V) :
    oldRegionValue
      ⟨old (m := m) (q := q) x, mem_oldRegion_old x⟩ = x := by
  apply old_injective (m := m) (q := q)
  exact old_oldRegionValue
    ⟨old (m := m) (q := q) x, mem_oldRegion_old x⟩

/-- The old-copy region projects homomorphically to the pruned host. -/
noncomputable def oldRegionProjectionHom :
    (graph (q := q) G cluster).induce
      {z : Vertex V m q |
        z ∈ oldRegion (V := V) (m := m) (q := q)} →g
      prunedHost G cluster where
  toFun := oldRegionValue
  map_rel' := by
    intro a b hab
    have hab' : (graph (q := q) G cluster).Adj a.1 b.1 := by
      simpa using hab
    rw [← old_oldRegionValue a, ← old_oldRegionValue b] at hab'
    exact adj_old_old_iff.mp hab'

theorem oldRegionProjectionHom_injective :
    Function.Injective
      (oldRegionProjectionHom (G := G) (cluster := cluster)
        (m := m) (q := q)) := by
  intro a b hab
  apply Subtype.ext
  rw [← old_oldRegionValue a, ← old_oldRegionValue b]
  exact congrArg (old (m := m) (q := q)) hab

namespace GraphPath

variable {i : Fin m}

/-- Map a pruned-host path into the old part of the replicated network. -/
noncomputable def mapOld
    (P : Lax17Proofs.SimpleGraph.GraphPath (prunedHost G cluster)) :
    Lax17Proofs.SimpleGraph.GraphPath (graph (q := q) G cluster) :=
  ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective
    P (oldHom (q := q)) old_injective

@[simp] theorem mapOld_source
    (P : Lax17Proofs.SimpleGraph.GraphPath (prunedHost G cluster)) :
    (mapOld (q := q) P).source = old (q := q) P.source :=
  rfl

@[simp] theorem mapOld_target
    (P : Lax17Proofs.SimpleGraph.GraphPath (prunedHost G cluster)) :
    (mapOld (q := q) P).target = old (q := q) P.target :=
  rfl

@[simp] theorem mapOld_vertexSet
    (P : Lax17Proofs.SimpleGraph.GraphPath (prunedHost G cluster)) :
    (mapOld (q := q) P).vertexSet =
      P.vertexSet.image (old (q := q)) := by
  exact
    ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective_vertexSet
      P (oldHom (q := q)) old_injective

/-- Project an augmented path known to stay in the old-copy region back to
the pruned host. -/
noncomputable def projectOld
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (q := q) G cluster))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (m := m) (q := q)) :
    Lax17Proofs.SimpleGraph.GraphPath (prunedHost G cluster) :=
  ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective
    (P.induce (oldRegion (V := V) (m := m) (q := q)) hP)
    oldRegionProjectionHom oldRegionProjectionHom_injective

@[simp] theorem projectOld_source
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (q := q) G cluster))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (m := m) (q := q)) :
    (projectOld P hP).source =
      oldRegionValue ⟨P.source, hP P.source_mem_vertexSet⟩ :=
  rfl

@[simp] theorem projectOld_target
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (q := q) G cluster))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (m := m) (q := q)) :
    (projectOld P hP).target =
      oldRegionValue ⟨P.target, hP P.target_mem_vertexSet⟩ :=
  rfl

/-- Remove the first edge of an oriented host path. -/
def dropFirst (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    Lax17Proofs.SimpleGraph.GraphPath G :=
  P.reverse.dropLast.reverse

@[simp] theorem dropFirst_source (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (dropFirst P).source = P.reverse.penultimate :=
  rfl

@[simp] theorem dropFirst_target (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (dropFirst P).target = P.target :=
  rfl

theorem dropFirst_vertexSet_subset (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (dropFirst P).vertexSet ⊆ P.vertexSet := by
  intro x hx
  have hx' : x ∈ P.reverse.dropLast.vertexSet := by
    simpa [dropFirst] using hx
  have hxrev := P.reverse.dropLast_vertexSet_subset hx'
  simpa using hxrev

theorem source_not_mem_dropFirst
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (hne : P.source ≠ P.target) :
    P.source ∉ (dropFirst P).vertexSet := by
  have hrev : P.reverse.source ≠ P.reverse.target := by
    simpa using hne.symm
  have hnot := P.reverse.target_not_mem_dropLast_vertexSet hrev
  simpa [dropFirst] using hnot

theorem source_adj_dropFirst_source
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (hne : P.source ≠ P.target) :
    G.Adj P.source (dropFirst P).source := by
  have hrev : P.reverse.source ≠ P.reverse.target := by
    simpa using hne.symm
  have h := P.reverse.penultimate_adj_target hrev
  simpa [dropFirst] using h.symm

/-- Directness makes the suffix after the first edge avoid every selected
router vertex. -/
theorem dropFirst_subset_compl_selectedUnion
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (hroot : Disjoint root (selectedUnion cluster))
    (hsource : P.source ∈ cluster i) (htarget : P.target ∈ root)
    (hdirect : P.InternallyDisjointFromSet (selectedUnion cluster)) :
    (dropFirst P).vertexSet ⊆
      Finset.univ \ selectedUnion cluster := by
  classical
  have hsourceU : P.source ∈ selectedUnion cluster :=
    mem_selectedUnion.mpr ⟨i, hsource⟩
  have htargetNotU : P.target ∉ selectedUnion cluster := by
    intro htargetU
    exact Finset.disjoint_left.mp hroot htarget htargetU
  have hne : P.source ≠ P.target := by
    intro h
    exact htargetNotU (h ▸ hsourceU)
  intro x hx
  rw [Finset.mem_sdiff]
  refine ⟨by simp, ?_⟩
  intro hxU
  have hxP : x ∈ P.vertexSet := dropFirst_vertexSet_subset P hx
  rcases hdirect hxP hxU with hxSource | hxTarget
  · exact source_not_mem_dropFirst P hne (by simpa [hxSource] using hx)
  · exact htargetNotU (hxTarget ▸ hxU)

/-- Add one replicated source incidence to a direct host-flow path. -/
noncomputable def addSource
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (hroot : Disjoint root (selectedUnion cluster))
    (hsource : P.source ∈ cluster i) (htarget : P.target ∈ root)
    (hdirect : P.InternallyDisjointFromSet (selectedUnion cluster))
    (a : Fin q) :
    Lax17Proofs.SimpleGraph.GraphPath (graph (q := q) G cluster) := by
  have houtside :=
    dropFirst_subset_compl_selectedUnion P hroot hsource htarget hdirect
  let Q := (dropFirst P).inInducedOnFinset houtside
  have hne : P.source ≠ P.target := by
    intro h
    have hsourceU : P.source ∈ selectedUnion cluster :=
      mem_selectedUnion.mpr ⟨i, hsource⟩
    exact Finset.disjoint_left.mp hroot htarget (h ▸ hsourceU)
  let L :=
    ChekuriChuzhoyPendantVertex.GraphPath.ofAdj
      ((adj_source_old_iff (G := G) (cluster := cluster) i a).2
        ⟨houtside (by
            simpa [Q] using
              Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet Q),
          P.source, hsource, by
            simpa [Q] using source_adj_dropFirst_source P hne⟩)
  let R := mapOld (q := q) Q
  have hLR : L.target = R.source := by
    rfl
  exact L.appendWithEqToPath R hLR

@[simp] theorem addSource_source
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (hroot : Disjoint root (selectedUnion cluster))
    (hsource : P.source ∈ cluster i) (htarget : P.target ∈ root)
    (hdirect : P.InternallyDisjointFromSet (selectedUnion cluster))
    (a : Fin q) :
    (addSource P hroot hsource htarget hdirect a).source = source i a := by
  simp [addSource]

@[simp] theorem addSource_target
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (hroot : Disjoint root (selectedUnion cluster))
    (hsource : P.source ∈ cluster i) (htarget : P.target ∈ root)
    (hdirect : P.InternallyDisjointFromSet (selectedUnion cluster))
    (a : Fin q) :
    (addSource P hroot hsource htarget hdirect a).target = old P.target := by
  simp [addSource, Lax17Proofs.SimpleGraph.GraphPath.inInducedOnFinset]

/-- Every old vertex retained by `addSource` came from the original flow
path. -/
theorem old_mem_original_of_mem_addSource
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (hroot : Disjoint root (selectedUnion cluster))
    (hsource : P.source ∈ cluster i) (htarget : P.target ∈ root)
    (hdirect : P.InternallyDisjointFromSet (selectedUnion cluster))
    (a : Fin q) {x : V}
    (hx : old (m := m) (q := q) x ∈
      (addSource P hroot hsource htarget hdirect a).vertexSet) :
    x ∈ P.vertexSet := by
  classical
  let houtside :=
    dropFirst_subset_compl_selectedUnion P hroot hsource htarget hdirect
  let Q := (dropFirst P).inInducedOnFinset houtside
  have hne : P.source ≠ P.target := by
    intro h
    exact Finset.disjoint_left.mp hroot htarget
      (h ▸ mem_selectedUnion.mpr ⟨i, hsource⟩)
  let hAdj :=
    (adj_source_old_iff (G := G) (cluster := cluster) i a).2
      ⟨houtside (by
          simpa [Q] using
            Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet Q),
        P.source, hsource, by
          simpa [Q] using source_adj_dropFirst_source P hne⟩
  let L := ChekuriChuzhoyPendantVertex.GraphPath.ofAdj hAdj
  let R := mapOld (q := q) Q
  have hLR : L.target = R.source := by
    rfl
  have hxUnion : old (m := m) (q := q) x ∈ L.vertexSet ∪ R.vertexSet := by
    exact L.appendWithEqToPath_vertexSet_subset R
      hLR (by
        simpa [addSource, houtside, Q, hne, hAdj, L, R] using hx)
  rcases Finset.mem_union.mp hxUnion with hxL | hxR
  · have hxPair :=
      ChekuriChuzhoyPendantVertex.GraphPath.ofAdj_vertexSet_subset_pair
        hAdj hxL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
    rcases hxPair with hfalse | hxSource
    · cases hfalse
    · have hxEq : x = Q.source := old_injective hxSource
      exact dropFirst_vertexSet_subset P (by
        simpa [Q, hxEq] using
          Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet Q)
  · rw [mapOld_vertexSet (q := q)] at hxR
    rcases Finset.mem_image.mp hxR with ⟨y, hy, hyx⟩
    have hxy : y = x := old_injective hyx
    have hy' : y ∈ (dropFirst P).vertexSet := by
      change
        y ∈ ((dropFirst P).inInducedOnFinset houtside).vertexSet at hy
      simpa only [
        Lax17Proofs.SimpleGraph.GraphPath.inInducedOnFinset_vertexSet] using hy
    exact dropFirst_vertexSet_subset P (by simpa [hxy] using hy')

/-- The artificial source is the only source-copy vertex on an augmented
path. -/
theorem source_mem_addSource_iff
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (hroot : Disjoint root (selectedUnion cluster))
    (hsource : P.source ∈ cluster i) (htarget : P.target ∈ root)
    (hdirect : P.InternallyDisjointFromSet (selectedUnion cluster))
    (a : Fin q) (j : Fin m) (b : Fin q) :
    source (V := V) j b ∈
        (addSource P hroot hsource htarget hdirect a).vertexSet ↔
      j = i ∧ b = a := by
  classical
  constructor
  · intro hx
    let houtside :=
      dropFirst_subset_compl_selectedUnion P hroot hsource htarget hdirect
    let Q := (dropFirst P).inInducedOnFinset houtside
    have hne : P.source ≠ P.target := by
      intro h
      exact Finset.disjoint_left.mp hroot htarget
        (h ▸ mem_selectedUnion.mpr ⟨i, hsource⟩)
    let hAdj :=
      (adj_source_old_iff (G := G) (cluster := cluster) i a).2
        ⟨houtside (by
            simpa [Q] using
              Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet Q),
          P.source, hsource, by
            simpa [Q] using source_adj_dropFirst_source P hne⟩
    let L := ChekuriChuzhoyPendantVertex.GraphPath.ofAdj hAdj
    let R := mapOld (q := q) Q
    have hLR : L.target = R.source := by
      rfl
    have hxUnion : source (V := V) j b ∈ L.vertexSet ∪ R.vertexSet := by
      exact L.appendWithEqToPath_vertexSet_subset R
        hLR (by
          simpa [addSource, houtside, Q, hne, hAdj, L, R] using hx)
    rcases Finset.mem_union.mp hxUnion with hxL | hxR
    · have hxPair :=
        ChekuriChuzhoyPendantVertex.GraphPath.ofAdj_vertexSet_subset_pair
          hAdj hxL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with hEq | hfalse
      · injection hEq with hji hba
        exact ⟨hji, hba⟩
      · cases hfalse
    · rw [mapOld_vertexSet (q := q)] at hxR
      rcases Finset.mem_image.mp hxR with ⟨x, _hx, hfalse⟩
      cases hfalse
  · rintro ⟨rfl, rfl⟩
    exact Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet _

end GraphPath

/-! ## Replicating the fractional leaf flows -/

variable
  (F : ∀ i : Fin m, OrientedPathFlow G (cluster i) root)

/-- The source-faithful directness condition on the scaled flows preceding
Claim 5.15. -/
def FlowsDirect : Prop :=
  ∀ (i : Fin m) (a : (F i).Index),
    ((F i).path a).InternallyDisjointFromSet (selectedUnion cluster)

/-- The aggregate unit vertex-capacity condition used by Claim 5.15. -/
def AggregateVertexCongestionAtMostOne : Prop :=
  ∀ v : V, ∑ i : Fin m, (F i).vertexLoad v ≤ 1

/-- Every normalized router flow has positive value when it carries at least
the positive natural quota `q`. -/
theorem flow_value_pos
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value)
    (i : Fin m) :
    0 < (F i).value := by
  have hqRat : (0 : Rat) < q := by exact_mod_cast hq
  exact hqRat.trans_le (hvalue i)

/-- Copy the normalized flow of router `i` once for each of its `q` source
tokens.  Its old path is first pruned to the suffix outside every selected
router. -/
noncomputable def replicatedFlow
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value) :
    OrientedPathFlow
      (graph (q := q) G cluster)
      (sources (V := V) (m := m) (q := q))
      (oldImage (m := m) (q := q) root) where
  Index := Σ i : Fin m, Fin q × (F i).Index
  path := fun z =>
    GraphPath.addSource ((F z.1).path z.2.2)
      hroot ((F z.1).source_mem z.2.2) ((F z.1).target_mem z.2.2)
      (hdirect z.1 z.2.2) z.2.1
  source_mem := by
    intro z
    simpa using mem_sources_source (V := V) z.1 z.2.1
  target_mem := by
    intro z
    rw [GraphPath.addSource_target]
    exact mem_oldImage.mpr ((F z.1).target_mem z.2.2)
  weight := fun z => (F z.1).weight z.2.2 / (F z.1).value
  weight_nonneg := by
    intro z
    exact div_nonneg ((F z.1).weight_nonneg z.2.2)
      (le_of_lt (flow_value_pos F hq hvalue z.1))

theorem replicatedFlow_sourceLoad_source
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value)
    (i : Fin m) (a : Fin q) :
    (replicatedFlow F hroot hdirect hq hvalue).sourceLoad
      (source (V := V) i a) = 1 := by
  classical
  unfold OrientedPathFlow.sourceLoad
  simp only [replicatedFlow, GraphPath.addSource_source]
  change
    (∑ x : Σ j : Fin m, Fin q × (F j).Index,
      if source (V := V) x.1 x.2.1 = source i a then
        (F x.1).weight x.2.2 / (F x.1).value
      else 0) = 1
  rw [Fintype.sum_sigma
    (fun x : Σ j : Fin m, Fin q × (F j).Index =>
      if source (V := V) x.1 x.2.1 = source i a then
        (F x.1).weight x.2.2 / (F x.1).value
      else 0)]
  rw [Finset.sum_eq_single i]
  · rw [Fintype.sum_prod_type
      (fun z : Fin q × (F i).Index =>
        if source (V := V) i z.1 = source i a then
          (F i).weight z.2 / (F i).value
        else 0)]
    rw [Finset.sum_eq_single a]
    · simp only [ite_true]
      rw [← Finset.sum_div]
      change (F i).value / (F i).value = 1
      exact div_self (ne_of_gt (flow_value_pos F hq hvalue i))
    · intro b _hb hbi
      simp [hbi]
    · simp
  · intro j _hj hji
    simp [hji]
  · simp

theorem replicatedFlow_sourceLoadExactlyOne
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value) :
    (replicatedFlow F hroot hdirect hq hvalue).SourceLoadExactlyOne := by
  intro z hz
  classical
  rcases Finset.mem_image.mp hz with ⟨⟨i, a⟩, _ha, rfl⟩
  exact replicatedFlow_sourceLoad_source F hroot hdirect hq hvalue i a

@[simp] theorem replicatedFlow_vertexLoad_source
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value)
    (i : Fin m) (a : Fin q) :
    (replicatedFlow F hroot hdirect hq hvalue).vertexLoad
      (source (V := V) i a) = 1 := by
  classical
  rw [OrientedPathFlow.vertexLoad]
  change
    (∑ x : Σ j : Fin m, Fin q × (F j).Index,
      if source (V := V) i a ∈
          (GraphPath.addSource ((F x.1).path x.2.2)
            hroot ((F x.1).source_mem x.2.2) ((F x.1).target_mem x.2.2)
            (hdirect x.1 x.2.2) x.2.1).vertexSet
      then (F x.1).weight x.2.2 / (F x.1).value
      else 0) = 1
  have hterms :
      (∑ x : Σ j : Fin m, Fin q × (F j).Index,
        if source (V := V) i a ∈
            (GraphPath.addSource ((F x.1).path x.2.2)
              hroot ((F x.1).source_mem x.2.2) ((F x.1).target_mem x.2.2)
              (hdirect x.1 x.2.2) x.2.1).vertexSet
        then (F x.1).weight x.2.2 / (F x.1).value
        else 0) =
        (replicatedFlow F hroot hdirect hq hvalue).sourceLoad
          (source (V := V) i a) := by
    rw [OrientedPathFlow.sourceLoad]
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [replicatedFlow, GraphPath.source_mem_addSource_iff,
      GraphPath.addSource_source]
    by_cases h : i = x.1 ∧ a = x.2.1
    · have h' : x.1 = i ∧ x.2.1 = a := ⟨h.1.symm, h.2.symm⟩
      have hs :
          source (V := V) x.1 x.2.1 = source i a := by
        have hp : (x.1, x.2.1) = (i, a) :=
          Prod.ext h'.1 h'.2
        exact congrArg
          (fun z : Fin m × Fin q => source (V := V) z.1 z.2)
          hp
      rw [if_pos h, if_pos hs]
    · have h' : ¬(x.1 = i ∧ x.2.1 = a) := by
        rintro ⟨hi, ha⟩
        exact h ⟨hi.symm, ha.symm⟩
      have hs :
          source (V := V) x.1 x.2.1 ≠ source i a := by
        intro heq
        injection heq with hi ha
        exact h' ⟨hi, ha⟩
      rw [if_neg h, if_neg hs]
  rw [hterms]
  exact replicatedFlow_sourceLoad_source F hroot hdirect hq hvalue i a

theorem flow_vertexLoad_nonneg (i : Fin m) (v : V) :
    0 ≤ (F i).vertexLoad v := by
  classical
  unfold OrientedPathFlow.vertexLoad
  exact Finset.sum_nonneg fun k _hk => by
    by_cases hv : v ∈ ((F i).path k).vertexSet
    · simpa [hv] using (F i).weight_nonneg k
    · simp [hv]

set_option maxHeartbeats 1000000 in
theorem replicatedFlow_vertexLoad_old_le
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value)
    (v : V) :
    (replicatedFlow F hroot hdirect hq hvalue).vertexLoad
        (old (m := m) (q := q) v) ≤
      ∑ i : Fin m, (F i).vertexLoad v := by
  classical
  unfold OrientedPathFlow.vertexLoad
  change
    (∑ x : Σ i : Fin m, Fin q × (F i).Index,
      if old (m := m) (q := q) v ∈
          (GraphPath.addSource ((F x.1).path x.2.2)
            hroot ((F x.1).source_mem x.2.2) ((F x.1).target_mem x.2.2)
            (hdirect x.1 x.2.2) x.2.1).vertexSet
      then (F x.1).weight x.2.2 / (F x.1).value
      else 0) ≤ ∑ i : Fin m, (F i).vertexLoad v
  rw [Fintype.sum_sigma
    (fun x : Σ i : Fin m, Fin q × (F i).Index =>
      if old (m := m) (q := q) v ∈
          (GraphPath.addSource ((F x.1).path x.2.2)
            hroot ((F x.1).source_mem x.2.2) ((F x.1).target_mem x.2.2)
            (hdirect x.1 x.2.2) x.2.1).vertexSet
      then (F x.1).weight x.2.2 / (F x.1).value
      else 0)]
  calc
    (∑ i : Fin m, ∑ z : Fin q × (F i).Index,
        if old (m := m) (q := q) v ∈
            (GraphPath.addSource ((F i).path z.2)
              hroot ((F i).source_mem z.2) ((F i).target_mem z.2)
              (hdirect i z.2) z.1).vertexSet
        then (F i).weight z.2 / (F i).value
        else 0)
        ≤ ∑ i : Fin m, ∑ z : Fin q × (F i).Index,
            if v ∈ ((F i).path z.2).vertexSet
            then (F i).weight z.2 / (F i).value
            else 0 := by
          refine Finset.sum_le_sum fun i _hi => ?_
          refine Finset.sum_le_sum fun z _hz => ?_
          by_cases haug :
              old (m := m) (q := q) v ∈
                (GraphPath.addSource ((F i).path z.2)
                  hroot ((F i).source_mem z.2) ((F i).target_mem z.2)
                  (hdirect i z.2) z.1).vertexSet
          · rw [if_pos haug, if_pos
              (GraphPath.old_mem_original_of_mem_addSource
                ((F i).path z.2) hroot ((F i).source_mem z.2)
                ((F i).target_mem z.2) (hdirect i z.2) z.1 haug)]
          · rw [if_neg haug]
            by_cases hv : v ∈ ((F i).path z.2).vertexSet
            · rw [if_pos hv]
              exact div_nonneg ((F i).weight_nonneg z.2)
                (le_of_lt (flow_value_pos F hq hvalue i))
            · simp [hv]
    _ = ∑ i : Fin m,
          (q : Rat) * ((F i).vertexLoad v / (F i).value) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Fintype.sum_prod_type
            (fun z : Fin q × (F i).Index =>
              if v ∈ ((F i).path z.2).vertexSet
              then (F i).weight z.2 / (F i).value
              else 0)]
          have hinner :
              (∑ k : (F i).Index,
                if v ∈ ((F i).path k).vertexSet
                then (F i).weight k / (F i).value
                else 0) =
                (F i).vertexLoad v / (F i).value := by
            rw [OrientedPathFlow.vertexLoad, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro k _hk
            by_cases hv : v ∈ ((F i).path k).vertexSet <;> simp [hv]
          simp_rw [hinner]
          simp
    _ ≤ ∑ i : Fin m, (F i).vertexLoad v := by
          refine Finset.sum_le_sum fun i _hi => ?_
          have hden : 0 < (F i).value :=
            flow_value_pos F hq hvalue i
          have hratio : (q : Rat) / (F i).value ≤ 1 :=
            (div_le_one hden).2 (hvalue i)
          calc
            (q : Rat) * ((F i).vertexLoad v / (F i).value) =
                ((q : Rat) / (F i).value) * (F i).vertexLoad v := by
                  field_simp
            _ ≤ 1 * (F i).vertexLoad v :=
              mul_le_mul_of_nonneg_right hratio (flow_vertexLoad_nonneg F i v)
            _ = (F i).vertexLoad v := one_mul _

theorem replicatedFlow_vertexCongestionAtMostOne
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value)
    (hcapacity : AggregateVertexCongestionAtMostOne F) :
    (replicatedFlow F hroot hdirect hq hvalue).VertexCongestionAtMost 1 := by
  intro z
  cases z with
  | old v =>
      exact (replicatedFlow_vertexLoad_old_le F hroot hdirect hq hvalue v).trans
        (hcapacity v)
  | source i a =>
      exact le_of_eq
        (replicatedFlow_vertexLoad_source F hroot hdirect hq hvalue i a)

@[simp] theorem replicatedFlow_value
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value) :
    (replicatedFlow F hroot hdirect hq hvalue).value = m * q := by
  rw [(replicatedFlow F hroot hdirect hq hvalue).value_eq_card_source_of_sourceLoadExactlyOne
    (replicatedFlow_sourceLoadExactlyOne F hroot hdirect hq hvalue)]
  simp

/-- If a packing uses every replicated source, deleting the first edge of
each oriented path leaves only old-copy vertices. -/
theorem packing_dropFirst_subset_oldRegion
    (P : PathPacking
      (graph (q := q) G cluster)
      (sources (V := V) (m := m) (q := q))
      (oldImage (m := m) (q := q) root))
    (hsourceSet :
      P.sourceSet = sources (V := V) (m := m) (q := q))
    (k : P.Index) :
    (GraphPath.dropFirst (P.orient.path k)).vertexSet ⊆
      oldRegion (V := V) (m := m) (q := q) := by
  classical
  intro z hz
  cases z with
  | old v => exact mem_oldRegion_old v
  | source i a =>
      have hzPath :
          source (V := V) i a ∈ (P.orient.path k).vertexSet :=
        GraphPath.dropFirst_vertexSet_subset (P.orient.path k) hz
      have hzUsed : source (V := V) i a ∈ P.sourceSet := by
        rw [hsourceSet]
        exact mem_sources_source (V := V) i a
      rcases P.exists_orient_source_eq_of_mem_sourceSet hzUsed with
        ⟨l, hl⟩
      by_cases hlk : l = k
      · subst l
        have hne :
            (P.orient.path k).source ≠ (P.orient.path k).target := by
          intro heq
          have hs :
              (P.orient.path k).source ∈
                sources (V := V) (m := m) (q := q) :=
            Lax17Proofs.SimpleGraph.GraphPath.orient_source_mem
              (P.path k) (P.connects k)
          have ht :
              (P.orient.path k).target ∈
                oldImage (m := m) (q := q) root :=
            Lax17Proofs.SimpleGraph.GraphPath.orient_target_mem
              (P.path k) (P.connects k)
          exact Finset.disjoint_left.mp (sources_disjoint_oldImage root)
            hs (by simpa [← heq] using ht)
        exact False.elim
          (GraphPath.source_not_mem_dropFirst (P.orient.path k) hne
            (by simpa [hl] using hz))
      · have hdisj := P.orient.node_disjoint hlk
        have hzl :
            source (V := V) i a ∈ (P.orient.path l).vertexSet := by
          simpa [hl] using
            Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet
              (P.orient.path l)
        exact False.elim
          (Finset.disjoint_left.mp hdisj hzl hzPath)

/-- Every path in a full-source packing has a checked realization consisting
of one original boundary incidence followed by a path in the pruned host.
Mapping `Q` along `prunedHost_le` gives the corresponding suffix in `G`. -/
theorem packing_path_has_pruned_realization
    (P : PathPacking
      (graph (q := q) G cluster)
      (sources (V := V) (m := m) (q := q))
      (oldImage (m := m) (q := q) root))
    (hsourceSet :
      P.sourceSet = sources (V := V) (m := m) (q := q))
    (k : P.Index) :
    ∃ (i : Fin m) (a : Fin q) (x y : V)
        (Q : Lax17Proofs.SimpleGraph.GraphPath (prunedHost G cluster)),
      (P.orient.path k).source = source (V := V) i a ∧
      x ∈ cluster i ∧
      y ∈ Finset.univ \ selectedUnion cluster ∧
      G.Adj x y ∧
      Q.source = y ∧
      Q.target ∈ root := by
  classical
  let R := P.orient.path k
  have hs :
      R.source ∈ sources (V := V) (m := m) (q := q) :=
    Lax17Proofs.SimpleGraph.GraphPath.orient_source_mem
      (P.path k) (P.connects k)
  have ht :
      R.target ∈ oldImage (m := m) (q := q) root :=
    Lax17Proofs.SimpleGraph.GraphPath.orient_target_mem
      (P.path k) (P.connects k)
  rcases Finset.mem_image.mp hs with ⟨⟨i, a⟩, _hia, hsource⟩
  rcases Finset.mem_image.mp ht with ⟨t, htRoot, htarget⟩
  have hne : R.source ≠ R.target := by
    intro heq
    exact Finset.disjoint_left.mp (sources_disjoint_oldImage root)
      hs (by simpa [← heq] using ht)
  let D := GraphPath.dropFirst R
  have hOld :
      D.vertexSet ⊆ oldRegion (V := V) (m := m) (q := q) :=
    packing_dropFirst_subset_oldRegion P hsourceSet k
  let z :
      {z : Vertex V m q //
        z ∈ oldRegion (V := V) (m := m) (q := q)} :=
    ⟨D.source, hOld D.source_mem_vertexSet⟩
  let y := oldRegionValue z
  have hy : old (m := m) (q := q) y = D.source :=
    old_oldRegionValue z
  have hsourceAdj : (graph (q := q) G cluster).Adj R.source D.source :=
    GraphPath.source_adj_dropFirst_source R hne
  have hsourceAdj' :
      (graph (q := q) G cluster).Adj
        (source (V := V) i a) (old (m := m) (q := q) y) := by
    rw [hsource, hy]
    exact hsourceAdj
  rcases (adj_source_old_iff (G := G) (cluster := cluster) i a).mp
      hsourceAdj' with ⟨hyOutside, x, hxCluster, hxy⟩
  let Q := GraphPath.projectOld D hOld
  have hQsource : Q.source = y := by
    change oldRegionValue
      ⟨D.source, hOld D.source_mem_vertexSet⟩ = y
    apply old_injective (m := m) (q := q)
    exact (old_oldRegionValue
      ⟨D.source, hOld D.source_mem_vertexSet⟩).trans hy.symm
  have hQtarget : Q.target = t := by
    change oldRegionValue
      ⟨D.target, hOld D.target_mem_vertexSet⟩ = t
    apply old_injective (m := m) (q := q)
    calc
      old (m := m) (q := q)
          (oldRegionValue
            ⟨D.target, hOld D.target_mem_vertexSet⟩) =
          D.target :=
        old_oldRegionValue
          ⟨D.target, hOld D.target_mem_vertexSet⟩
      _ = R.target := GraphPath.dropFirst_target R
      _ = old (m := m) (q := q) t := htarget.symm
  exact ⟨i, a, x, y, Q, hsource.symm, hxCluster, hyOutside, hxy,
    hQsource, hQtarget ▸ htRoot⟩

/-- Semantic content of Chekuri--Chuzhoy preprint Claim 5.15 (journal
Claim 5.17), through its integral leaf-path extraction.

The conclusion is an exact global packing in the source-replicated,
router-pruned network.  Each of the `q` copies of every one of the `m`
selected leaf routers is used.  Old-old edges of this network lie in
`prunedHost G cluster`, and each source-old edge records an original boundary
edge of the corresponding router, by `adj_old_old_iff` and
`adj_source_old_iff`. -/
theorem claim515_exists_integral_leaf_paths_in_prunedNetwork
    (hroot : Disjoint root (selectedUnion cluster))
    (hdirect : FlowsDirect F)
    (hq : 0 < q)
    (hvalue : ∀ i : Fin m, (q : Rat) ≤ (F i).value)
    (hcapacity : AggregateVertexCongestionAtMostOne F) :
    ∃ P : PathPacking
        (graph (q := q) G cluster)
        (sources (V := V) (m := m) (q := q))
        (oldImage (m := m) (q := q) root),
      P.card = m * q ∧
      P.sourceSet = sources (V := V) (m := m) (q := q) ∧
      ∀ k : P.Index,
        (GraphPath.dropFirst (P.orient.path k)).vertexSet ⊆
          oldRegion (V := V) (m := m) (q := q) := by
  let R := replicatedFlow F hroot hdirect hq hvalue
  have hunit :
      OrientedPathFlow.HasUnitVertexCapacityValueAtLeast
        (graph (q := q) G cluster)
        (sources (V := V) (m := m) (q := q))
        (oldImage (m := m) (q := q) root)
        (m * q) := by
    refine ⟨R, ?_, ?_⟩
    · change ((m * q : Nat) : Rat) ≤ R.value
      rw [show R.value = m * q by
        exact replicatedFlow_value F hroot hdirect hq hvalue]
      norm_num
    · exact replicatedFlow_vertexCongestionAtMostOne
        F hroot hdirect hq hvalue hcapacity
  have hpaths :
      HasDisjointSTPaths
        (graph (q := q) G cluster)
        (sources (V := V) (m := m) (q := q))
        (oldImage (m := m) (q := q) root)
        (m * q) :=
    FlowIntegrality.unitVertexCapacityFlow_hasDisjointSTPaths hunit
  rcases HasAtLeastDisjointPaths.exists_exact hpaths with ⟨P, hPcard⟩
  have hsourceSet :
      P.sourceSet = sources (V := V) (m := m) (q := q) := by
    apply P.sourceSet_eq_left_of_card_eq
    rw [hPcard, sources_card]
  exact ⟨P, hPcard, hsourceSet,
    packing_dropFirst_subset_oldRegion P hsourceSet⟩

/-! ## Flows whose terminals are contained in the selected routers

In Claim 5.15 the sets supporting the fractional flows need not contain every
vertex of the selected leaf routers.  The pruning operation, however, must
still delete the whole router family.  The declarations below separate these
two roles. -/

variable {terminal router : Fin m -> Finset V}

/-- Directness of a family of terminal-to-root flows with respect to the
possibly larger family of selected routers that will be pruned from the host.
-/
def FlowsDirectToRouters
    (router : Fin m -> Finset V)
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root) : Prop :=
  forall (i : Fin m) (a : (F i).Index),
    ((F i).path a).InternallyDisjointFromSet (selectedUnion router)

/-- Re-declare a path flow on a larger source set.  No path, weight, or load is
changed; only the source-membership certificate is widened. -/
def widenFlowSources
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i) :
    forall i : Fin m, OrientedPathFlow G (router i) root :=
  fun i => {
    Index := (F i).Index
    path := (F i).path
    source_mem := fun a => hterminal i ((F i).source_mem a)
    target_mem := (F i).target_mem
    weight := (F i).weight
    weight_nonneg := (F i).weight_nonneg
  }

@[simp] theorem widenFlowSources_path
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (i : Fin m) (a : (F i).Index) :
    ((widenFlowSources F hterminal i).path a) = (F i).path a :=
  rfl

@[simp] theorem widenFlowSources_weight
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (i : Fin m) (a : (F i).Index) :
    (widenFlowSources F hterminal i).weight a = (F i).weight a :=
  rfl

@[simp] theorem widenFlowSources_value
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (i : Fin m) :
    (widenFlowSources F hterminal i).value = (F i).value :=
  rfl

@[simp] theorem widenFlowSources_vertexLoad
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (i : Fin m) (v : V) :
    (widenFlowSources F hterminal i).vertexLoad v =
      (F i).vertexLoad v :=
  rfl

theorem flowsDirect_widenFlowSources_iff
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i) :
    FlowsDirect (widenFlowSources F hterminal) ↔
      FlowsDirectToRouters router F :=
  Iff.rfl

theorem aggregateVertexCongestionAtMostOne_widenFlowSources_iff
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i) :
    AggregateVertexCongestionAtMostOne (widenFlowSources F hterminal) ↔
      AggregateVertexCongestionAtMostOne F := by
  simp only [AggregateVertexCongestionAtMostOne,
    widenFlowSources_vertexLoad]

/-- The replicated Claim 5.15 flow when the fractional flow terminals are
subsets of the selected routers.  The auxiliary graph is built from `router`,
not from `terminal`. -/
noncomputable def replicatedFlowOfTerminalSubsets
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (hroot : Disjoint root (selectedUnion router))
    (hdirect : FlowsDirectToRouters router F)
    (hq : 0 < q)
    (hvalue : forall i : Fin m, (q : Rat) ≤ (F i).value) :
    OrientedPathFlow
      (graph (q := q) G router)
      (sources (V := V) (m := m) (q := q))
      (oldImage (m := m) (q := q) root) :=
  replicatedFlow (widenFlowSources F hterminal) hroot
    ((flowsDirect_widenFlowSources_iff F hterminal).2 hdirect) hq
    (fun i => by simpa using hvalue i)

theorem replicatedFlowOfTerminalSubsets_sourceLoadExactlyOne
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (hroot : Disjoint root (selectedUnion router))
    (hdirect : FlowsDirectToRouters router F)
    (hq : 0 < q)
    (hvalue : forall i : Fin m, (q : Rat) ≤ (F i).value) :
    (replicatedFlowOfTerminalSubsets F hterminal hroot hdirect hq hvalue
      ).SourceLoadExactlyOne :=
  replicatedFlow_sourceLoadExactlyOne
    (widenFlowSources F hterminal) hroot
    ((flowsDirect_widenFlowSources_iff F hterminal).2 hdirect) hq
    (fun i => by simpa using hvalue i)

theorem replicatedFlowOfTerminalSubsets_vertexCongestionAtMostOne
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (hroot : Disjoint root (selectedUnion router))
    (hdirect : FlowsDirectToRouters router F)
    (hq : 0 < q)
    (hvalue : forall i : Fin m, (q : Rat) ≤ (F i).value)
    (hcapacity : AggregateVertexCongestionAtMostOne F) :
    (replicatedFlowOfTerminalSubsets F hterminal hroot hdirect hq hvalue
      ).VertexCongestionAtMost 1 :=
  replicatedFlow_vertexCongestionAtMostOne
    (widenFlowSources F hterminal) hroot
    ((flowsDirect_widenFlowSources_iff F hterminal).2 hdirect) hq
    (fun i => by simpa using hvalue i)
    ((aggregateVertexCongestionAtMostOne_widenFlowSources_iff
      F hterminal).2 hcapacity)

@[simp] theorem replicatedFlowOfTerminalSubsets_value
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (hroot : Disjoint root (selectedUnion router))
    (hdirect : FlowsDirectToRouters router F)
    (hq : 0 < q)
    (hvalue : forall i : Fin m, (q : Rat) ≤ (F i).value) :
    (replicatedFlowOfTerminalSubsets F hterminal hroot hdirect hq hvalue
      ).value = m * q :=
  replicatedFlow_value
    (widenFlowSources F hterminal) hroot
    ((flowsDirect_widenFlowSources_iff F hterminal).2 hdirect) hq
    (fun i => by simpa using hvalue i)

/-- Chekuri--Chuzhoy preprint Claim 5.15 (journal Claim 5.17) with the
fractional-flow terminal sets separated from the selected routers.  Every
`terminal i` is contained in `router i`; the integral packing lives in the
network obtained by pruning the full union of the routers. -/
theorem claim515_exists_integral_leaf_paths_in_prunedNetwork_of_terminal_subsets
    (F : forall i : Fin m, OrientedPathFlow G (terminal i) root)
    (hterminal : forall i : Fin m, terminal i ⊆ router i)
    (hroot : Disjoint root (selectedUnion router))
    (hdirect : FlowsDirectToRouters router F)
    (hq : 0 < q)
    (hvalue : forall i : Fin m, (q : Rat) ≤ (F i).value)
    (hcapacity : AggregateVertexCongestionAtMostOne F) :
    ∃ P : PathPacking
        (graph (q := q) G router)
        (sources (V := V) (m := m) (q := q))
        (oldImage (m := m) (q := q) root),
      P.card = m * q ∧
      P.sourceSet = sources (V := V) (m := m) (q := q) ∧
      ∀ k : P.Index,
        (GraphPath.dropFirst (P.orient.path k)).vertexSet ⊆
          oldRegion (V := V) (m := m) (q := q) :=
  claim515_exists_integral_leaf_paths_in_prunedNetwork
    (F := widenFlowSources F hterminal) hroot
    ((flowsDirect_widenFlowSources_iff F hterminal).2 hdirect) hq
    (fun i => by simpa using hvalue i)
    ((aggregateVertexCongestionAtMostOne_widenFlowSources_iff
      F hterminal).2 hcapacity)

end Vertex

end ChekuriChuzhoySection5Phase1Leaves
end SimpleGraph

end Lax17Proofs
