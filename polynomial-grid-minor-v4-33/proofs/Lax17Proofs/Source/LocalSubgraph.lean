import Mathlib.Combinatorics.SimpleGraph.Basic
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Local spanning subgraphs on fixed vertex types

The polynomial grid-minor proof repeatedly considers local graphs such as a
cluster together with a family of connector paths.  Mathlib's `SimpleGraph.induce`
changes the vertex type to a subtype; this file provides same-vertex-type
spanning subgraphs with all vertices outside the local region isolated.
-/

namespace SimpleGraph

/-- The spanning subgraph of `G` whose edges are exactly the `G`-edges with both
endpoints in `C`.  Vertices outside `C` are present but isolated. -/
def inducedOnFinset {V : Type*} (G : _root_.SimpleGraph V) (C : Finset V) :
    _root_.SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ C ∧ v ∈ C
  symm := by
    intro u v huv
    exact ⟨G.symm huv.1, huv.2.2, huv.2.1⟩
  loopless := ⟨by
    intro v hv
    exact G.loopless.irrefl v hv.1⟩

/-- The local induced-on-finset graph is a subgraph of the ambient graph. -/
theorem inducedOnFinset_le {V : Type*} {G : _root_.SimpleGraph V}
    {C : Finset V} :
    inducedOnFinset G C ≤ G := by
  intro u v huv
  exact huv.1

@[simp] theorem inducedOnFinset_adj {V : Type*}
    (G : _root_.SimpleGraph V) (C : Finset V) (u v : V) :
    (inducedOnFinset G C).Adj u v ↔ G.Adj u v ∧ u ∈ C ∧ v ∈ C :=
  Iff.rfl

namespace Walk

/-- A walk whose vertices all lie in `C` can be regarded as a walk in the
same-vertex induced-on-finset graph. -/
def toInducedOnFinset {V : Type*} {G : _root_.SimpleGraph V} {C : Finset V}
    {u v : V} :
    (p : G.Walk u v) → (∀ x : V, x ∈ p.support → x ∈ C) →
      (inducedOnFinset G C).Walk u v
  | .nil, _ => .nil
  | .cons (v := u') huv p, hp =>
      .cons ⟨huv, hp _ (by simp), hp _ (by simp)⟩
        (toInducedOnFinset p (by
          intro x hx
          exact hp x (by simp [hx])))

@[simp] theorem support_toInducedOnFinset {V : Type*}
    {G : _root_.SimpleGraph V} {C : Finset V} {u v : V} :
    ∀ (p : G.Walk u v) hp,
      (toInducedOnFinset (G := G) (C := C) p hp).support = p.support
  | .nil, _ => rfl
  | .cons _ p, hp => by
      simp [toInducedOnFinset, support_toInducedOnFinset]

@[simp] theorem edges_toInducedOnFinset {V : Type*}
    {G : _root_.SimpleGraph V} {C : Finset V} {u v : V} :
    ∀ (p : G.Walk u v) hp,
      (toInducedOnFinset (G := G) (C := C) p hp).edges = p.edges
  | .nil, _ => rfl
  | .cons _ p, hp => by
      simp [toInducedOnFinset, edges_toInducedOnFinset]

end Walk

namespace GraphPath

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- Restrict a graph path to the same-vertex induced-on-finset graph, provided
all vertices of the path lie in the finite set. -/
def inInducedOnFinset (P : GraphPath G) {C : Finset V}
    (hPC : P.vertexSet ⊆ C) :
    GraphPath (inducedOnFinset G C) where
  source := P.source
  target := P.target
  walk := Walk.toInducedOnFinset P.walk (by
    intro x hx
    exact hPC (by simpa [vertexSet] using hx))
  isPath := by
    rw [_root_.SimpleGraph.Walk.isPath_def]
    simpa using P.isPath.support_nodup

@[simp] theorem inInducedOnFinset_vertexSet (P : GraphPath G)
    {C : Finset V} (hPC : P.vertexSet ⊆ C) :
    (P.inInducedOnFinset hPC).vertexSet = P.vertexSet := by
  classical
  simp [inInducedOnFinset, vertexSet]

@[simp] theorem inInducedOnFinset_edgeSet (P : GraphPath G)
    {C : Finset V} (hPC : P.vertexSet ⊆ C) :
    (P.inInducedOnFinset hPC).edgeSet = P.edgeSet := by
  classical
  simp [inInducedOnFinset, edgeSet]

end GraphPath

namespace PathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- Restrict a path packing to the same-vertex induced-on-finset graph when
every path in the packing stays inside the finite set. -/
def inInducedOnFinset (P : PathPacking G S T) {C : Finset V}
    (hP : P.StaysIn C) :
    PathPacking (inducedOnFinset G C) S T where
  Index := P.Index
  path := fun i => (P.path i).inInducedOnFinset (hP i)
  connects := by
    intro i
    simpa [GraphPath.inInducedOnFinset, GraphPath.Connects] using P.connects i
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

@[simp] theorem inInducedOnFinset_card (P : PathPacking G S T)
    {C : Finset V} (hP : P.StaysIn C) :
    (P.inInducedOnFinset hP).card = P.card := rfl

@[simp] theorem inInducedOnFinset_path_vertexSet (P : PathPacking G S T)
    {C : Finset V} (hP : P.StaysIn C) (i : P.Index) :
    ((P.inInducedOnFinset hP).path i).vertexSet = (P.path i).vertexSet := by
  simp [inInducedOnFinset]

/-- Restricting a packing to an induced-on-finset graph preserves the fact that
its paths stay in that finite set. -/
theorem inInducedOnFinset_staysIn (P : PathPacking G S T)
    {C : Finset V} (hP : P.StaysIn C) :
    (P.inInducedOnFinset hP).StaysIn C := by
  intro i
  simpa [inInducedOnFinset_path_vertexSet] using hP i

end PathPacking

namespace PerfectPathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- Restrict a perfect path packing to the same-vertex induced-on-finset graph
when every path in the packing stays inside the finite set. -/
def inInducedOnFinset (P : PerfectPathPacking G S T) {C : Finset V}
    (hP : P.toPathPacking.StaysIn C) :
    PerfectPathPacking (inducedOnFinset G C) S T where
  toPathPacking := P.toPathPacking.inInducedOnFinset hP
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_bijective := by
    simpa [PathPacking.inInducedOnFinset, GraphPath.inInducedOnFinset]
      using P.source_bijective
  target_bijective := by
    simpa [PathPacking.inInducedOnFinset, GraphPath.inInducedOnFinset]
      using P.target_bijective

@[simp] theorem inInducedOnFinset_card (P : PerfectPathPacking G S T)
    {C : Finset V} (hP : P.toPathPacking.StaysIn C) :
    (P.inInducedOnFinset hP).card = P.card := rfl

@[simp] theorem inInducedOnFinset_path_vertexSet (P : PerfectPathPacking G S T)
    {C : Finset V} (hP : P.toPathPacking.StaysIn C) (i : P.Index) :
    ((P.inInducedOnFinset hP).path i).vertexSet = (P.path i).vertexSet := by
  simp [inInducedOnFinset, PathPacking.inInducedOnFinset]

/-- Restricting a perfect packing to an induced-on-finset graph preserves the
fact that its paths stay in that finite set. -/
theorem inInducedOnFinset_staysIn (P : PerfectPathPacking G S T)
    {C : Finset V} (hP : P.toPathPacking.StaysIn C) :
    (P.inInducedOnFinset hP).toPathPacking.StaysIn C := by
  intro i
  simpa [inInducedOnFinset_path_vertexSet] using hP i

end PerfectPathPacking

/-- The local graph consisting of a cluster plus one path packing. -/
noncomputable def clusterWithPackingGraph {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C S T : Finset V)
    (P : PathPacking G S T) : _root_.SimpleGraph V :=
  inducedOnFinset G C ⊔ P.spanningGraph

/-- The vertices that can be incident to an edge of `clusterWithPackingGraph`:
the cluster vertices together with the vertices used by the distinguished
packing. -/
noncomputable def clusterWithPackingVertexSet {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} (C : Finset V) {S T : Finset V}
    (P : PathPacking G S T) : Finset V :=
  C ∪ P.vertexSet

/-- The induced cluster graph is contained in the cluster-plus-packing graph. -/
theorem inducedOnFinset_le_clusterWithPackingGraph {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) :
    inducedOnFinset G C ≤ clusterWithPackingGraph G C S T P := by
  intro u v huv
  exact Or.inl huv

/-- The spanning graph of the distinguished packing is contained in the
cluster-plus-packing graph. -/
theorem spanningGraph_le_clusterWithPackingGraph {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) :
    P.spanningGraph ≤ clusterWithPackingGraph G C S T P := by
  intro u v huv
  exact Or.inr huv

/-- A cluster-plus-packing graph is a subgraph of the ambient graph. -/
theorem clusterWithPackingGraph_le {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) :
    clusterWithPackingGraph G C S T P ≤ G := by
  intro u v huv
  rcases huv with huv | huv
  · exact inducedOnFinset_le huv
  · exact P.spanningGraph_le huv

/-- If one distinguished packing spans a subgraph of another, then the
corresponding cluster-plus-packing local graph is a subgraph as well.  The
terminal sets may differ; only the common cluster and spanned edges matter. -/
theorem clusterWithPackingGraph_le_of_spanningGraph_le
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (hQP : Q.spanningGraph ≤ P.spanningGraph) :
    clusterWithPackingGraph G C S' T' Q ≤ clusterWithPackingGraph G C S T P := by
  intro u v huv
  rcases huv with huv | huv
  · exact Or.inl huv
  · exact Or.inr (hQP huv)

/-- If the left endpoint of a queried edge is outside the cluster, adjacency in
the cluster-plus-packing graph can only come from the distinguished packing. -/
theorem clusterWithPackingGraph_adj_iff_spanningGraph_adj_of_left_not_mem
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) {u v : V} (hu : u ∉ C) :
    (clusterWithPackingGraph G C S T P).Adj u v ↔ P.spanningGraph.Adj u v := by
  constructor
  · intro huv
    rcases huv with huv | huv
    · exact False.elim (hu huv.2.1)
    · exact huv
  · intro huv
    exact Or.inr huv

/-- If the right endpoint of a queried edge is outside the cluster, adjacency in
the cluster-plus-packing graph can only come from the distinguished packing. -/
theorem clusterWithPackingGraph_adj_iff_spanningGraph_adj_of_right_not_mem
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) {u v : V} (hv : v ∉ C) :
    (clusterWithPackingGraph G C S T P).Adj u v ↔ P.spanningGraph.Adj u v := by
  rw [_root_.SimpleGraph.adj_comm, P.spanningGraph.adj_comm]
  exact clusterWithPackingGraph_adj_iff_spanningGraph_adj_of_left_not_mem P hv

/-- The left endpoint of every local edge lies in the cluster-plus-packing
vertex set. -/
theorem clusterWithPackingGraph_adj_left_mem_vertexSet
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) {u v : V}
    (huv : (clusterWithPackingGraph G C S T P).Adj u v) :
    u ∈ clusterWithPackingVertexSet C P := by
  classical
  rcases huv with huv | huv
  · exact Finset.mem_union_left _ huv.2.1
  · rcases (P.spanningGraph_adj_iff_exists_path_edge).mp huv with
      ⟨⟨i, hedge⟩, _hne⟩
    have hu :
        u ∈ (P.path i).vertexSet := by
      have huSupport :
          u ∈ (P.path i).walk.support :=
        (P.path i).walk.fst_mem_support_of_mem_edges
          (by simpa [GraphPath.edgeSet] using hedge)
      simpa [GraphPath.vertexSet] using huSupport
    exact Finset.mem_union_right C ((P.mem_vertexSet).2 ⟨i, hu⟩)

/-- The right endpoint of every local edge lies in the cluster-plus-packing
vertex set. -/
theorem clusterWithPackingGraph_adj_right_mem_vertexSet
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) {u v : V}
    (huv : (clusterWithPackingGraph G C S T P).Adj u v) :
    v ∈ clusterWithPackingVertexSet C P := by
  classical
  exact clusterWithPackingGraph_adj_left_mem_vertexSet P
    ((clusterWithPackingGraph G C S T P).symm huv)

namespace Walk

/-- A walk in a cluster-plus-packing graph whose source lies in the local
vertex footprint never leaves that footprint. -/
theorem support_subset_clusterWithPackingVertexSet
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T) {u v : V}
    (p : (clusterWithPackingGraph G C S T P).Walk u v)
    (hu : u ∈ clusterWithPackingVertexSet C P) :
    ∀ x : V, x ∈ p.support → x ∈ clusterWithPackingVertexSet C P := by
  induction p with
  | nil =>
      intro x hx
      simp at hx
      subst x
      exact hu
  | cons huv p ih =>
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih (clusterWithPackingGraph_adj_right_mem_vertexSet P huv) x hx

end Walk

namespace GraphPath

/-- A graph path in a cluster-plus-packing graph whose source lies in the local
vertex footprint stays inside that footprint. -/
theorem vertexSet_subset_clusterWithPackingVertexSet
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {C S T : Finset V}
    (P : PathPacking G S T)
    (Q : GraphPath (clusterWithPackingGraph G C S T P))
    (hsource : Q.source ∈ clusterWithPackingVertexSet C P) :
    Q.vertexSet ⊆ clusterWithPackingVertexSet C P := by
  intro v hv
  exact Walk.support_subset_clusterWithPackingVertexSet P Q.walk hsource v
    (by simpa [GraphPath.vertexSet] using hv)

end GraphPath

namespace PathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B C S T : Finset V}

/-- A packing that stays in the cluster can also be viewed inside any local
cluster-plus-packing graph built on that cluster. -/
noncomputable def inClusterWithPackingGraph (Q : PathPacking G A B) (hQ : Q.StaysIn C)
    (P : PathPacking G S T) :
    PathPacking (clusterWithPackingGraph G C S T P) A B :=
  PathPacking.mapLe (Q.inInducedOnFinset hQ)
    (inducedOnFinset_le_clusterWithPackingGraph P)

@[simp] theorem inClusterWithPackingGraph_card (Q : PathPacking G A B)
    (hQ : Q.StaysIn C) (P : PathPacking G S T) :
    (Q.inClusterWithPackingGraph hQ P).card = Q.card := by
  simp [inClusterWithPackingGraph]

@[simp] theorem inClusterWithPackingGraph_path_vertexSet
    (Q : PathPacking G A B) (hQ : Q.StaysIn C)
    (P : PathPacking G S T) (i : Q.Index) :
    ((Q.inClusterWithPackingGraph hQ P).path i).vertexSet =
      (Q.path i).vertexSet := by
  change (((Q.inInducedOnFinset hQ).mapLe
    (inducedOnFinset_le_clusterWithPackingGraph P)).path i).vertexSet =
      (Q.path i).vertexSet
  simp [PathPacking.mapLe]

/-- Viewing a cluster-contained packing inside a cluster-plus-packing graph
preserves the cluster containment of each path. -/
theorem inClusterWithPackingGraph_staysIn
    (Q : PathPacking G A B) (hQ : Q.StaysIn C)
    (P : PathPacking G S T) :
    (Q.inClusterWithPackingGraph hQ P).StaysIn C := by
  intro i
  simpa [inClusterWithPackingGraph_path_vertexSet] using hQ i

/-- The distinguished packing used to build a local cluster-plus-packing graph
is itself available inside that local graph. -/
noncomputable def inOwnClusterWithPackingGraph (P : PathPacking G S T)
    (C : Finset V) :
    PathPacking (clusterWithPackingGraph G C S T P) S T :=
  P.inSpanningGraph.mapLe (spanningGraph_le_clusterWithPackingGraph (C := C) P)

@[simp] theorem inOwnClusterWithPackingGraph_card (P : PathPacking G S T)
    (C : Finset V) :
    (P.inOwnClusterWithPackingGraph C).card = P.card := by
  simp [inOwnClusterWithPackingGraph]

@[simp] theorem inOwnClusterWithPackingGraph_path_vertexSet
    (P : PathPacking G S T) (C : Finset V) (i : P.Index) :
    ((P.inOwnClusterWithPackingGraph C).path i).vertexSet =
      (P.path i).vertexSet := by
  simp [inOwnClusterWithPackingGraph, PathPacking.mapLe]

end PathPacking

namespace PerfectPathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B C S T : Finset V}

/-- A perfect packing that stays in the cluster can be viewed inside any local
cluster-plus-packing graph built on that cluster. -/
noncomputable def inClusterWithPackingGraph (Q : PerfectPathPacking G A B)
    (hQ : Q.toPathPacking.StaysIn C) (P : PathPacking G S T) :
    PerfectPathPacking (clusterWithPackingGraph G C S T P) A B :=
  PerfectPathPacking.mapLe (Q.inInducedOnFinset hQ)
    (inducedOnFinset_le_clusterWithPackingGraph P)

@[simp] theorem inClusterWithPackingGraph_card (Q : PerfectPathPacking G A B)
    (hQ : Q.toPathPacking.StaysIn C) (P : PathPacking G S T) :
    (Q.inClusterWithPackingGraph hQ P).card = Q.card := by
  simp [inClusterWithPackingGraph]

@[simp] theorem inClusterWithPackingGraph_path_vertexSet
    (Q : PerfectPathPacking G A B) (hQ : Q.toPathPacking.StaysIn C)
    (P : PathPacking G S T) (i : Q.Index) :
    ((Q.inClusterWithPackingGraph hQ P).path i).vertexSet =
      (Q.path i).vertexSet := by
  change (((Q.inInducedOnFinset hQ).mapLe
    (inducedOnFinset_le_clusterWithPackingGraph P)).path i).vertexSet =
      (Q.path i).vertexSet
  simp [PerfectPathPacking.mapLe, PathPacking.mapLe]

/-- Viewing a cluster-contained perfect packing inside a cluster-plus-packing
graph preserves the cluster containment of each path. -/
theorem inClusterWithPackingGraph_staysIn
    (Q : PerfectPathPacking G A B) (hQ : Q.toPathPacking.StaysIn C)
    (P : PathPacking G S T) :
    (Q.inClusterWithPackingGraph hQ P).toPathPacking.StaysIn C := by
  intro i
  simpa [inClusterWithPackingGraph_path_vertexSet] using hQ i

/-- The distinguished perfect packing used to build a local
cluster-plus-packing graph is itself available inside that local graph. -/
noncomputable def inOwnClusterWithPackingGraph (P : PerfectPathPacking G S T)
    (C : Finset V) :
    PerfectPathPacking (clusterWithPackingGraph G C S T P.toPathPacking) S T :=
  P.inSpanningGraph.mapLe
    (spanningGraph_le_clusterWithPackingGraph (C := C) P.toPathPacking)

@[simp] theorem inOwnClusterWithPackingGraph_card (P : PerfectPathPacking G S T)
    (C : Finset V) :
    (P.inOwnClusterWithPackingGraph C).card = P.card := by
  simp [inOwnClusterWithPackingGraph]

@[simp] theorem inOwnClusterWithPackingGraph_path_vertexSet
    (P : PerfectPathPacking G S T) (C : Finset V) (i : P.Index) :
    ((P.inOwnClusterWithPackingGraph C).path i).vertexSet =
      (P.path i).vertexSet := by
  simp [inOwnClusterWithPackingGraph, PerfectPathPacking.mapLe,
    PathPacking.mapLe]

end PerfectPathPacking

end SimpleGraph

end Lax17Proofs
