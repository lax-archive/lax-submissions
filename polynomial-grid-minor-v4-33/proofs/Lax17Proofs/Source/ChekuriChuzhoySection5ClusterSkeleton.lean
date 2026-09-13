import Lax17Proofs.Source.ChekuriChuzhoySection5Theorem510
import Lax17Proofs.Source.ChekuriChuzhoySection5Clustering

namespace Lax17Proofs

universe u v w

/-!
# Cluster-valued terminal skeletons

Phase 2 of Chekuri--Chuzhoy Section 5 applies Theorem 5.10 after replacing
each router by a temporary terminal.  Stripping those temporary terminal
edges produces the object below: a parallel-edge-preserving graph on router
indices together with direct host paths between the corresponding clusters.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5ClusterSkeleton


open Finset
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {m : Nat}

/-- The cluster-level form of the terminal skeleton used in the final
tree-of-sets assembly.  The stored host paths are fully node-disjoint after
one representative is chosen from every group; this is the strengthened
conclusion obtained after stripping the temporary degree-one terminal
incidences in Phase 2. -/
structure ClusterPathSkeleton
    (G : _root_.SimpleGraph V) (cluster : Fin m → Finset V) where
  graph : FiniteEdgeIndexedGraph (Fin m)
  hostPath : graph.Edge → GraphPath G
  host_source_mem :
    ∀ e, (hostPath e).source ∈ cluster (graph.left e)
  host_target_mem :
    ∀ e, (hostPath e).target ∈ cluster (graph.right e)
  host_source_interface :
    ∀ e, (hostPath e).source ∈
      ChekuriChuzhoySection5Clustering.interfaceVertices G
        (cluster (graph.left e))
  host_target_interface :
    ∀ e, (hostPath e).target ∈
      ChekuriChuzhoySection5Clustering.interfaceVertices G
        (cluster (graph.right e))
  groups : Finpartition (Finset.univ : Finset graph.Edge)
  internally_disjoint_clusters :
    ∀ e r, (hostPath e).InternallyDisjointFromSet (cluster r)
  one_per_group_node_disjoint :
    ∀ selected : Finset graph.Edge,
      (∀ U ∈ groups.parts, (selected ∩ U).card = 1) →
        ∀ ⦃e⦄, e ∈ selected → ∀ ⦃f⦄, f ∈ selected → e ≠ f →
          (hostPath e).NodeDisjoint (hostPath f)

namespace ClusterPathSkeleton

variable {cluster : Fin m → Finset V}

instance (S : ClusterPathSkeleton G cluster) : Fintype S.graph.Edge :=
  S.graph.edgeFintype

instance (S : ClusterPathSkeleton G cluster) : DecidableEq S.graph.Edge :=
  S.graph.edgeDecidableEq

/-- Every skeleton group has at most `k` edge copies. -/
def GroupSizeAtMost (S : ClusterPathSkeleton G cluster) (k : Nat) : Prop :=
  ∀ U ∈ S.groups.parts, U.card ≤ k

/-- A global one-per-group choice. -/
def IsGroupTransversal
    (S : ClusterPathSkeleton G cluster)
    (selected : Finset S.graph.Edge) : Prop :=
  ∀ U ∈ S.groups.parts, (selected ∩ U).card = 1

/-- The unoriented pair of cluster indices joined by a named edge copy. -/
def edgeKey
    (S : ClusterPathSkeleton G cluster) (e : S.graph.Edge) : Sym2 (Fin m) :=
  s(S.graph.left e, S.graph.right e)

/-- The named copies with a prescribed unoriented cluster pair. -/
noncomputable def edgeBundleKey
    (S : ClusterPathSkeleton G cluster) (p : Sym2 (Fin m)) :
    Finset S.graph.Edge := by
  classical
  exact Finset.univ.filter fun e => S.edgeKey e = p

@[simp] theorem mem_edgeBundleKey
    (S : ClusterPathSkeleton G cluster)
    {p : Sym2 (Fin m)} {e : S.graph.Edge} :
    e ∈ S.edgeBundleKey p ↔ S.edgeKey e = p := by
  simp [edgeBundleKey]

/-- The named edge copies joining two cluster indices, independent of the
stored endpoint orientation. -/
noncomputable def edgeBundle
    (S : ClusterPathSkeleton G cluster) (i j : Fin m) :
    Finset S.graph.Edge := by
  classical
  exact Finset.univ.filter fun e => S.graph.Joins e i j

@[simp] theorem mem_edgeBundle
    (S : ClusterPathSkeleton G cluster) {i j : Fin m} {e : S.graph.Edge} :
    e ∈ S.edgeBundle i j ↔ S.graph.Joins e i j := by
  simp [edgeBundle]

private theorem sym2_eq_of_joins
    (S : ClusterPathSkeleton G cluster) {e : S.graph.Edge} {i j : Fin m}
    (h : S.graph.Joins e i j) :
    s(S.graph.left e, S.graph.right e) = s(i, j) := by
  rcases h with h | h
  · simp [h.1, h.2]
  · simpa [h.1, h.2, Sym2.eq_swap]

theorem edgeBundle_eq_edgeBundleKey
    (S : ClusterPathSkeleton G cluster) (i j : Fin m) :
    S.edgeBundle i j = S.edgeBundleKey s(i, j) := by
  ext e
  simp only [mem_edgeBundle, mem_edgeBundleKey, edgeKey]
  constructor
  · exact sym2_eq_of_joins S
  · intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩

theorem edgeBundle_comm
    (S : ClusterPathSkeleton G cluster) (i j : Fin m) :
    S.edgeBundle i j = S.edgeBundle j i := by
  ext e
  simp only [mem_edgeBundle]
  exact S.graph.joins_comm e i j

theorem edgeBundle_subset_univ
    (S : ClusterPathSkeleton G cluster) (i j : Fin m) :
    S.edgeBundle i j ⊆ Finset.univ :=
  Finset.subset_univ _

/-- Bundles belonging to distinct unoriented cluster pairs are disjoint. -/
theorem edgeBundle_disjoint_of_pair_ne
    (S : ClusterPathSkeleton G cluster)
    {i j p q : Fin m} (hne : s(i, j) ≠ s(p, q)) :
    Disjoint (S.edgeBundle i j) (S.edgeBundle p q) := by
  rw [Finset.disjoint_left]
  intro e heij hepq
  exact hne ((sym2_eq_of_joins S (S.mem_edgeBundle.mp heij)).symm.trans
    (sym2_eq_of_joins S (S.mem_edgeBundle.mp hepq)))

theorem edgeBundleKey_disjoint_of_ne
    (S : ClusterPathSkeleton G cluster)
    {p q : Sym2 (Fin m)} (hne : p ≠ q) :
    Disjoint (S.edgeBundleKey p) (S.edgeBundleKey q) := by
  rw [Finset.disjoint_left]
  intro e hep heq
  exact hne ((S.mem_edgeBundleKey.mp hep).symm.trans
    (S.mem_edgeBundleKey.mp heq))

/-- The stored path for an edge in a bundle connects the corresponding
clusters. -/
theorem hostPath_connects_of_mem_edgeBundle
    (S : ClusterPathSkeleton G cluster)
    {i j : Fin m} {e : S.graph.Edge} (he : e ∈ S.edgeBundle i j) :
    (S.hostPath e).Connects (cluster i) (cluster j) := by
  rcases S.mem_edgeBundle.mp he with h | h
  · exact Or.inl
      ⟨h.1 ▸ S.host_source_mem e, h.2 ▸ S.host_target_mem e⟩
  · exact Or.inr
      ⟨h.2 ▸ S.host_source_mem e, h.1 ▸ S.host_target_mem e⟩

/-- Both endpoints of a bundled host path belong to the corresponding router
interfaces, independent of orientation. -/
theorem hostPath_endpoints_interface_of_mem_edgeBundle
    (S : ClusterPathSkeleton G cluster)
    {i j : Fin m} {e : S.graph.Edge} (he : e ∈ S.edgeBundle i j) :
    ((S.hostPath e).source ∈
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) ∧
      (S.hostPath e).target ∈
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster j)) ∨
    ((S.hostPath e).source ∈
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster j) ∧
      (S.hostPath e).target ∈
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i)) := by
  rcases S.mem_edgeBundle.mp he with h | h
  · exact Or.inl
      ⟨h.1 ▸ S.host_source_interface e, h.2 ▸ S.host_target_interface e⟩
  · exact Or.inr
      ⟨h.2 ▸ S.host_source_interface e, h.1 ▸ S.host_target_interface e⟩

end ClusterPathSkeleton
end ChekuriChuzhoySection5ClusterSkeleton
end SimpleGraph

end Lax17Proofs
