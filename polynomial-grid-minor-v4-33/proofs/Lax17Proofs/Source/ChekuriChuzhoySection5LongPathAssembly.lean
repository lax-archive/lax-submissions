import Mathlib.Combinatorics.SimpleGraph.Hasse
import Lax17Proofs.Source.ChekuriChuzhoySection5EndpointThinning
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Bundle
import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthBridge
import Lax17Proofs.Source.TreeOfSetsBandwidth

namespace Lax17Proofs

universe u v w

/-!
# Long-support-path tree-of-sets assembly

This module closes the structural Case 1 gap in Chekuri--Chuzhoy Section
5.4.1.  Exact endpoint-thinned bundles on a simple support-tree path are
assembled into the ordinary bandwidth tree-of-sets system consumed by the
source-sharp strongification theorem.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5LongPathAssembly


open ChekuriChuzhoySection5EndpointThinning
open ChekuriChuzhoySection5RouterSkeleton

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A path graph is a tree whenever it embeds into a tree.  Connectedness is
intrinsic to the path graph; injectivity transfers acyclicity from the host
tree. -/
theorem pathGraph_isTree_of_injective_hom
    {m : Nat} (hm : 0 < m) {W : Type*}
    {T : _root_.SimpleGraph W}
    (hT : T.IsTree) (f : _root_.SimpleGraph.pathGraph m →g T)
    (hf : Function.Injective f) :
    (_root_.SimpleGraph.pathGraph m).IsTree := by
  refine ⟨?_, hT.isAcyclic.comap f hf⟩
  have hconnected := _root_.SimpleGraph.pathGraph_connected (m - 1)
  have hmEq : m - 1 + 1 = m := by omega
  rw [hmEq] at hconnected
  exact hconnected

/-- The canonical path graph has maximum degree at most three.  The loose
bound `3` matches the tree-of-sets API and avoids endpoint case splits. -/
theorem pathGraph_maxDegreeAtMost_three (m : Nat) :
    MaxDegreeAtMost (_root_.SimpleGraph.pathGraph m) 3 := by
  classical
  intro v
  let pred : Fin m := ⟨v.1 - 1, by omega⟩
  let succ : Fin m :=
    if h : v.1 + 1 < m then ⟨v.1 + 1, h⟩ else v
  let N : Finset (Fin m) :=
    ({pred, succ, v} : Finset (Fin m)).filter fun u =>
      (_root_.SimpleGraph.pathGraph m).Adj v u
  refine ⟨N, ?_, ?_⟩
  · intro u
    constructor
    · exact fun hu => (Finset.mem_filter.mp hu).2
    · intro huv
      apply Finset.mem_filter.mpr
      refine ⟨?_, huv⟩
      rw [_root_.SimpleGraph.pathGraph_adj] at huv
      rcases huv with huv | huv
      · have hsucc : v.1 + 1 < m := by omega
        have hu : u = succ := by
          apply Fin.ext
          simp [succ, hsucc, huv]
        simp [hu]
      · have hu : u = pred := by
          apply Fin.ext
          simp [pred]
          omega
        simp [hu]
  · exact (Finset.card_filter_le _ _).trans Finset.card_le_three

variable {G : _root_.SimpleGraph V} {n Delta : Nat}
variable {cluster : Fin n → Finset V}

/-- The middle `m` routers of a buffered support-tree path. -/
def bufferedRouter {m : Nat} (order : Fin (m + 2) → Fin n)
    (i : Fin m) : Fin n :=
  order ⟨i.1 + 1, by omega⟩

/-- Left endpoint router of the `r`-th edge between middle routers. -/
def bufferedEdgeLeft {m : Nat} (order : Fin (m + 2) → Fin n)
    (r : Fin (m - 1)) : Fin n :=
  order ⟨r.1 + 1, by omega⟩

/-- Right endpoint router of the `r`-th edge between middle routers. -/
def bufferedEdgeRight {m : Nat} (order : Fin (m + 2) → Fin n)
    (r : Fin (m - 1)) : Fin n :=
  order ⟨r.1 + 2, by omega⟩

theorem bufferedEdgeLeft_ne_right
    {m : Nat} (order : Fin (m + 2) → Fin n)
    (horder : Function.Injective order) (r : Fin (m - 1)) :
    bufferedEdgeLeft order r ≠ bufferedEdgeRight order r := by
  intro h
  have hidx := horder h
  have := congrArg Fin.val hidx
  simp [bufferedEdgeLeft, bufferedEdgeRight] at this

/-- A selected exact bundle, interpreted as a node-disjoint path packing
between its two router endpoint sets. -/
noncomputable def exactBundlePathPacking
    {R : Type*} [Fintype R] [DecidableEq R]
    (S : RouterPathSkeleton G cluster)
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (request : Finset R) (left right : R → Fin n)
    (candidate : R → Finset S.graph.Edge) {width : Nat}
    (A : RouterExactBundleFamily S request left right candidate width)
    (hcandidateGlobal : ∀ r ∈ request, candidate r ⊆ global)
    (hcandidateJoins : ∀ r ∈ request, ∀ e ∈ candidate r,
      S.graph.Joins e (left r) (right r))
    (hleftRight : ∀ r ∈ request, left r ≠ right r)
    (hclusterDisjoint : ∀ r ∈ request,
      Disjoint (cluster (left r)) (cluster (right r)))
    (r : R) (hr : r ∈ request) :
    PathPacking G
      (routerBundleEndpointSet S (left r) (A.exact r))
      (routerBundleEndpointSet S (right r) (A.exact r)) where
  Index := {e : S.graph.Edge // e ∈ A.exact r}
  path := fun e => S.hostPath e.1
  connects := by
    intro e
    have heCandidate := A.exact_subset r hr e.2
    rcases routerEndpointAt_pair_of_joins S (hleftRight r hr) e.1
        (hcandidateJoins r hr e.1 heCandidate) with h | h
    · exact Or.inl ⟨
        (mem_routerBundleEndpointSet S (left r) (A.exact r) _).mpr
          ⟨e.1, e.2, h.1⟩,
        (mem_routerBundleEndpointSet S (right r) (A.exact r) _).mpr
          ⟨e.1, e.2, h.2⟩⟩
    · exact Or.inr ⟨
        (mem_routerBundleEndpointSet S (right r) (A.exact r) _).mpr
          ⟨e.1, e.2, h.2⟩,
        (mem_routerBundleEndpointSet S (left r) (A.exact r) _).mpr
          ⟨e.1, e.2, h.1⟩⟩
  node_disjoint := by
    intro e f hef
    exact routerHostPath_nodeDisjoint_of_endpoint_injective
      S (hleftRight r hr) (hclusterDisjoint r hr)
      global (A.exact r) htransversal
      ((A.exact_subset r hr).trans (hcandidateGlobal r hr))
      (fun e he => hcandidateJoins r hr e (A.exact_subset r hr he))
      (A.left_injective r hr) (A.right_injective r hr)
      e.2 f.2 (fun h => hef (Subtype.ext h))

@[simp] theorem exactBundlePathPacking_card
    {R : Type*} [Fintype R] [DecidableEq R]
    (S : RouterPathSkeleton G cluster)
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (request : Finset R) (left right : R → Fin n)
    (candidate : R → Finset S.graph.Edge) {width : Nat}
    (A : RouterExactBundleFamily S request left right candidate width)
    (hcandidateGlobal : ∀ r ∈ request, candidate r ⊆ global)
    (hcandidateJoins : ∀ r ∈ request, ∀ e ∈ candidate r,
      S.graph.Joins e (left r) (right r))
    (hleftRight : ∀ r ∈ request, left r ≠ right r)
    (hclusterDisjoint : ∀ r ∈ request,
      Disjoint (cluster (left r)) (cluster (right r)))
    (r : R) (hr : r ∈ request) :
    (exactBundlePathPacking S global htransversal request left right candidate
      A hcandidateGlobal hcandidateJoins hleftRight hclusterDisjoint r hr).card =
      width := by
  classical
  simpa [exactBundlePathPacking, PathPacking.card] using A.exact_card r hr

/-- Perfect form of `exactBundlePathPacking`; endpoint injectivity and exact
cardinality ensure that every selected endpoint is used once. -/
noncomputable def exactBundlePerfectPacking
    {R : Type*} [Fintype R] [DecidableEq R]
    (S : RouterPathSkeleton G cluster)
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (request : Finset R) (left right : R → Fin n)
    (candidate : R → Finset S.graph.Edge) {width : Nat}
    (A : RouterExactBundleFamily S request left right candidate width)
    (hcandidateGlobal : ∀ r ∈ request, candidate r ⊆ global)
    (hcandidateJoins : ∀ r ∈ request, ∀ e ∈ candidate r,
      S.graph.Joins e (left r) (right r))
    (hleftRight : ∀ r ∈ request, left r ≠ right r)
    (hclusterDisjoint : ∀ r ∈ request,
      Disjoint (cluster (left r)) (cluster (right r)))
    (r : R) (hr : r ∈ request) :
    PerfectPathPacking G
      (routerBundleEndpointSet S (left r) (A.exact r))
      (routerBundleEndpointSet S (right r) (A.exact r)) := by
  let P := exactBundlePathPacking S global htransversal request left right
    candidate A hcandidateGlobal hcandidateJoins hleftRight hclusterDisjoint r hr
  exact P.toPerfectOfCardEq
    ((exactBundlePathPacking_card S global htransversal request left right
      candidate A hcandidateGlobal hcandidateJoins hleftRight
      hclusterDisjoint r hr).trans
      ((routerBundleEndpointSet_card S (left r) (A.exact r)
        (A.left_injective r hr)).trans (A.exact_card r hr)).symm)
    ((exactBundlePathPacking_card S global htransversal request left right
      candidate A hcandidateGlobal hcandidateJoins hleftRight
      hclusterDisjoint r hr).trans
      ((routerBundleEndpointSet_card S (right r) (A.exact r)
        (A.right_injective r hr)).trans (A.exact_card r hr)).symm)

/-- Index of the unoriented edge represented by an adjacency of `pathGraph`.
The value is the lower endpoint. -/
def pathEdgeIndex {m : Nat} {i j : Fin m}
    (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) : Fin (m - 1) :=
  if h : i.1 + 1 = j.1 then
    ⟨i.1, by rw [_root_.SimpleGraph.pathGraph_adj] at hij; omega⟩
  else
    ⟨j.1, by rw [_root_.SimpleGraph.pathGraph_adj] at hij; omega⟩

theorem pathEdgeIndex_orientation
    {m : Nat} (order : Fin (m + 2) → Fin n) {i j : Fin m}
    (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    (bufferedEdgeLeft order (pathEdgeIndex hij) = bufferedRouter order i ∧
        bufferedEdgeRight order (pathEdgeIndex hij) = bufferedRouter order j) ∨
      (bufferedEdgeLeft order (pathEdgeIndex hij) = bufferedRouter order j ∧
        bufferedEdgeRight order (pathEdgeIndex hij) = bufferedRouter order i) := by
  rw [_root_.SimpleGraph.pathGraph_adj] at hij
  rcases hij with hij | hij
  · left
    constructor <;> apply congrArg order <;> apply Fin.ext <;>
      simp [pathEdgeIndex, bufferedEdgeLeft, bufferedEdgeRight,
        bufferedRouter, hij]
  · right
    have hnot : ¬ i.1 + 1 = j.1 := by omega
    constructor <;> apply congrArg order <;> apply Fin.ext <;>
      simp [pathEdgeIndex, bufferedEdgeLeft, bufferedEdgeRight,
        bufferedRouter, hij, hnot]

theorem sym2_eq_of_pathEdgeIndex_eq
    {m : Nat} {i j p q : Fin m}
    (hij : (_root_.SimpleGraph.pathGraph m).Adj i j)
    (hpq : (_root_.SimpleGraph.pathGraph m).Adj p q)
    (hindex : pathEdgeIndex hij = pathEdgeIndex hpq) :
    s(i, j) = s(p, q) := by
  have hij' := hij
  have hpq' := hpq
  rw [_root_.SimpleGraph.pathGraph_adj] at hij' hpq'
  rcases hij' with hij' | hij' <;> rcases hpq' with hpq' | hpq'
  · have hv := congrArg Fin.val hindex
    simp [pathEdgeIndex, hij', hpq'] at hv
    apply Sym2.eq_iff.mpr
    exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · have hnot : ¬ p.1 + 1 = q.1 := by omega
    have hv := congrArg Fin.val hindex
    simp [pathEdgeIndex, hij', hpq', hnot] at hv
    apply Sym2.eq_iff.mpr
    exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · have hnot : ¬ i.1 + 1 = j.1 := by omega
    have hv := congrArg Fin.val hindex
    simp [pathEdgeIndex, hij', hpq', hnot] at hv
    apply Sym2.eq_iff.mpr
    exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · have hnotI : ¬ i.1 + 1 = j.1 := by omega
    have hnotP : ¬ p.1 + 1 = q.1 := by omega
    have hv := congrArg Fin.val hindex
    simp [pathEdgeIndex, hij', hpq', hnotI, hnotP] at hv
    apply Sym2.eq_iff.mpr
    exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem pathEdgeIndex_symm
    {m : Nat} {i j : Fin m}
    (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    pathEdgeIndex ((_root_.SimpleGraph.pathGraph m).symm hij) =
      pathEdgeIndex hij := by
  have hij' := hij
  rw [_root_.SimpleGraph.pathGraph_adj] at hij'
  rcases hij' with hij' | hij'
  · have hnot : ¬ j.1 + 1 = i.1 := by omega
    apply Fin.ext
    simp [pathEdgeIndex, hij', hnot]
  · have hnot : ¬ i.1 + 1 = j.1 := by omega
    apply Fin.ext
    simp [pathEdgeIndex, hij', hnot]

private theorem copyTerminals_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ S₁' T₁' S₂' T₂' : Finset V}
    (P : PerfectPathPacking G S₁ T₁) (Q : PerfectPathPacking G S₂ T₂)
    (hS₁ : S₁ = S₁') (hT₁ : T₁ = T₁')
    (hS₂ : S₂ = S₂') (hT₂ : T₂ = T₂')
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    (P.copyTerminals hS₁ hT₁).toPathPacking.MutuallyNodeDisjoint
      (Q.copyTerminals hS₂ hT₂).toPathPacking := by
  exact h

private theorem reverse_left_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁) (Q : PerfectPathPacking G S₂ T₂)
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    P.reverse.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking := by
  intro a b
  simpa [GraphPath.NodeDisjoint] using h a b

private theorem reverse_right_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁) (Q : PerfectPathPacking G S₂ T₂)
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    P.toPathPacking.MutuallyNodeDisjoint Q.reverse.toPathPacking := by
  intro a b
  simpa [GraphPath.NodeDisjoint] using h a b

private theorem reverse_both_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁) (Q : PerfectPathPacking G S₂ T₂)
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    P.reverse.toPathPacking.MutuallyNodeDisjoint Q.reverse.toPathPacking :=
  reverse_left_mutuallyNodeDisjoint P Q.reverse
    (reverse_right_mutuallyNodeDisjoint P Q h)

/-- Complete exact-bundle data for the buffered long-path branch. -/
structure BufferedPathAssemblyData
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    (width cap alphaNum alphaDen : Nat) {m : Nat}
    (order : Fin (m + 2) → Fin n) where
  m_two : 2 ≤ m
  width_pos : 0 < width
  supportTree : T.IsTree
  order_injective : Function.Injective order
  order_adj : ∀ r : Fin (m + 1),
    T.Adj (order ⟨r.1, by omega⟩) (order ⟨r.1 + 1, by omega⟩)
  global : Finset S.graph.Edge
  global_transversal : S.IsGroupTransversal global
  candidate : Fin (m - 1) → Finset S.graph.Edge
  candidate_global : ∀ r, candidate r ⊆ global
  candidate_joins : ∀ r, ∀ e ∈ candidate r,
    S.graph.Joins e (bufferedEdgeLeft order r) (bufferedEdgeRight order r)
  exactFamily : RouterExactBundleFamily S Finset.univ
    (bufferedEdgeLeft order) (bufferedEdgeRight order) candidate width
  cluster_connected : ∀ i, IsCluster G (cluster i)
  cluster_disjoint : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j)
  cluster_bandwidth : ∀ i,
    ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
      G (cluster i) cap alphaNum alphaDen
  cap_width : 3 * width ≤ cap

namespace BufferedPathAssemblyData

variable {T : _root_.SimpleGraph (Fin n)}
variable {m width cap alphaNum alphaDen : Nat}
variable {order : Fin (m + 2) → Fin n}
variable {S : RouterPathSkeleton G cluster}

theorem edge_left_ne_right
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (r : Fin (m - 1)) :
    bufferedEdgeLeft order r ≠ bufferedEdgeRight order r :=
  bufferedEdgeLeft_ne_right order D.order_injective r

theorem edge_cluster_disjoint
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (r : Fin (m - 1)) :
    Disjoint (cluster (bufferedEdgeLeft order r))
      (cluster (bufferedEdgeRight order r)) :=
  D.cluster_disjoint _ _ (D.edge_left_ne_right r)

noncomputable def edgePacking
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (r : Fin (m - 1)) :
    PerfectPathPacking G
      (routerBundleEndpointSet S (bufferedEdgeLeft order r)
        (D.exactFamily.exact r))
      (routerBundleEndpointSet S (bufferedEdgeRight order r)
        (D.exactFamily.exact r)) :=
  exactBundlePerfectPacking S D.global D.global_transversal Finset.univ
    (bufferedEdgeLeft order) (bufferedEdgeRight order) D.candidate
    D.exactFamily (fun r _ => D.candidate_global r)
    (fun r _ e he => D.candidate_joins r e he)
    (fun r _ => D.edge_left_ne_right r)
    (fun r _ => D.edge_cluster_disjoint r) r (Finset.mem_univ r)

@[simp] theorem edgePacking_card
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (r : Fin (m - 1)) :
    (D.edgePacking r).card = width := by
  classical
  change Fintype.card {e : S.graph.Edge // e ∈ D.exactFamily.exact r} = width
  simpa using D.exactFamily.exact_card r (Finset.mem_univ r)

/-- Interface at `i` on the oriented path-graph edge `i--j`. -/
noncomputable def interface
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    Finset V := by
  let r := pathEdgeIndex hij
  if h : i.1 + 1 = j.1 then
    exact routerBundleEndpointSet S (bufferedEdgeLeft order r)
      (D.exactFamily.exact r)
  else
    exact routerBundleEndpointSet S (bufferedEdgeRight order r)
      (D.exactFamily.exact r)

theorem interface_subset_cluster
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    D.interface i j hij ⊆ cluster (bufferedRouter order i) := by
  classical
  by_cases h : i.1 + 1 = j.1
  · have hleft : bufferedEdgeLeft order (pathEdgeIndex hij) =
        bufferedRouter order i := by
      apply congrArg order
      apply Fin.ext
      simp [bufferedEdgeLeft, bufferedRouter, pathEdgeIndex, h]
    simp only [interface, dif_pos h]
    rw [← hleft]
    exact routerBundleEndpointSet_subset_cluster S _ _
      (D.exactFamily.left_mem _ (Finset.mem_univ _) )
  · have hrev : j.1 + 1 = i.1 := by
      rw [_root_.SimpleGraph.pathGraph_adj] at hij
      omega
    have hright : bufferedEdgeRight order (pathEdgeIndex hij) =
        bufferedRouter order i := by
      apply congrArg order
      apply Fin.ext
      simp [bufferedEdgeRight, bufferedRouter, pathEdgeIndex, h, hrev]
    simp only [interface, dif_neg h]
    rw [← hright]
    exact routerBundleEndpointSet_subset_cluster S _ _
      (D.exactFamily.right_mem _ (Finset.mem_univ _))

theorem interface_subset_interfaceVertices
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    D.interface i j hij ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G
        (cluster (bufferedRouter order i)) := by
  classical
  let r := pathEdgeIndex hij
  by_cases h : i.1 + 1 = j.1
  · have hleft : bufferedEdgeLeft order r = bufferedRouter order i := by
      apply congrArg order
      apply Fin.ext
      simp [r, bufferedEdgeLeft, bufferedRouter, pathEdgeIndex, h]
    simp only [interface, dif_pos h]
    rw [← hleft]
    simpa [routerBundleEndpointSet,
      ChekuriChuzhoySection5Phase1Bundle.endpointSetAt] using
      ChekuriChuzhoySection5Phase1Bundle.endpointSetAt_subset_interfaceVertices
        S (D.edge_left_ne_right r) (D.edge_cluster_disjoint r)
        (D.exactFamily.exact r)
        (fun e he => D.candidate_joins r e
          (D.exactFamily.exact_subset r (Finset.mem_univ r) he))
  · have hrev : j.1 + 1 = i.1 := by
      rw [_root_.SimpleGraph.pathGraph_adj] at hij
      omega
    have hright : bufferedEdgeRight order r = bufferedRouter order i := by
      apply congrArg order
      apply Fin.ext
      simp [r, bufferedEdgeRight, bufferedRouter, pathEdgeIndex, h, hrev]
    simp only [interface, dif_neg h]
    rw [← hright]
    simpa [routerBundleEndpointSet,
      ChekuriChuzhoySection5Phase1Bundle.endpointSetAt] using
      ChekuriChuzhoySection5Phase1Bundle.endpointSetAt_subset_interfaceVertices
        S (D.edge_left_ne_right r).symm (D.edge_cluster_disjoint r).symm
        (D.exactFamily.exact r)
        (fun e he => (S.graph.joins_comm e
          (bufferedEdgeRight order r) (bufferedEdgeLeft order r)).mpr
            (D.candidate_joins r e
              (D.exactFamily.exact_subset r (Finset.mem_univ r) he)))

@[simp] theorem interface_card
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    (D.interface i j hij).card = width := by
  classical
  by_cases h : i.1 + 1 = j.1
  · simp only [interface, dif_pos h]
    rw [
      routerBundleEndpointSet_card S _ _
        (D.exactFamily.left_injective _ (Finset.mem_univ _)),
      D.exactFamily.exact_card _ (Finset.mem_univ _)]
  · simp only [interface, dif_neg h]
    rw [
      routerBundleEndpointSet_card S _ _
        (D.exactFamily.right_injective _ (Finset.mem_univ _)),
      D.exactFamily.exact_card _ (Finset.mem_univ _)]

theorem interface_subset_endpointUnion
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    D.interface i j hij ⊆
      routerBundleEndpointUnion S
        (bufferedEdgeLeft order (pathEdgeIndex hij))
        (bufferedEdgeRight order (pathEdgeIndex hij))
        (D.exactFamily.exact (pathEdgeIndex hij)) := by
  classical
  by_cases h : i.1 + 1 = j.1
  · simp [interface, h, routerBundleEndpointUnion]
  · simp [interface, h, routerBundleEndpointUnion]

theorem interface_disjoint
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    {i j k : Fin m}
    (hij : (_root_.SimpleGraph.pathGraph m).Adj i j)
    (hik : (_root_.SimpleGraph.pathGraph m).Adj i k) (hjk : j ≠ k) :
    Disjoint (D.interface i j hij) (D.interface i k hik) := by
  classical
  have hindex : pathEdgeIndex hij ≠ pathEdgeIndex hik := by
    intro h
    have hedge := sym2_eq_of_pathEdgeIndex_eq hij hik h
    have := Sym2.congr_right.mp hedge
    exact hjk this
  exact Finset.disjoint_of_subset_left (D.interface_subset_endpointUnion i j hij)
    (Finset.disjoint_of_subset_right (D.interface_subset_endpointUnion i k hik)
      (D.exactFamily.endpoint_disjoint _ (Finset.mem_univ _) _
        (Finset.mem_univ _) hindex))

/-- The exact bundle on an unoriented support edge, oriented from `i` to `j`
and definitionally retargeted to the interfaces stored by the tree-of-sets
record. -/
noncomputable def connector
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    PerfectPathPacking G (D.interface i j hij)
      (D.interface j i ((_root_.SimpleGraph.pathGraph m).symm hij)) := by
  classical
  by_cases h : i.1 + 1 = j.1
  · let P := D.edgePacking (pathEdgeIndex hij)
    exact P.copyTerminals
      (by simp [P, interface, h])
      (by
        have hrev : ¬ j.1 + 1 = i.1 := by omega
        simp [P, interface, hrev, pathEdgeIndex_symm hij])
  · let P := (D.edgePacking (pathEdgeIndex hij)).reverse
    exact P.copyTerminals
      (by simp [P, interface, h])
      (by
        have hrev : j.1 + 1 = i.1 := by
          rw [_root_.SimpleGraph.pathGraph_adj] at hij
          omega
        simp [P, interface, hrev, pathEdgeIndex_symm hij])

@[simp] theorem connector_card
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    (D.connector i j hij).card = width := by
  classical
  by_cases h : i.1 + 1 = j.1
  · simpa [connector, h] using D.edgePacking_card (pathEdgeIndex hij)
  · simpa [connector, h] using D.edgePacking_card (pathEdgeIndex hij)

theorem edgePacking_internallyDisjointFromSet
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (r : Fin (m - 1)) (a : (D.edgePacking r).Index) (t : Fin n) :
    ((D.edgePacking r).path a).InternallyDisjointFromSet (cluster t) := by
  let P := exactBundlePathPacking S D.global D.global_transversal Finset.univ
    (bufferedEdgeLeft order) (bufferedEdgeRight order) D.candidate
    D.exactFamily (fun r _ => D.candidate_global r)
    (fun r _ e he => D.candidate_joins r e he)
    (fun r _ => D.edge_left_ne_right r)
    (fun r _ => D.edge_cluster_disjoint r) r (Finset.mem_univ r)
  have hP : P.InternallyDisjointFromSet (cluster t) := by
    intro b
    exact S.internally_disjoint_clusters b.1 t
  have horient := PathPacking.orient_internallyDisjointFromSet hP a
  simpa [edgePacking, exactBundlePerfectPacking, P] using horient

theorem edgePacking_internallyDisjointFromSet_all
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (r : Fin (m - 1)) (t : Fin n) :
    (D.edgePacking r).toPathPacking.InternallyDisjointFromSet (cluster t) :=
  fun a => D.edgePacking_internallyDisjointFromSet r a t

theorem edgePacking_mutuallyNodeDisjoint
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    {r t : Fin (m - 1)} (hrt : r ≠ t) :
    (D.edgePacking r).toPathPacking.MutuallyNodeDisjoint
    (D.edgePacking t).toPathPacking := by
  intro a b
  simpa [edgePacking, exactBundlePerfectPacking, exactBundlePathPacking,
    PathPacking.toPerfectOfCardEq, GraphPath.NodeDisjoint] using
    D.exactFamily.hostPath_nodeDisjoint_of_ne S D.global
    D.global_transversal Finset.univ (bufferedEdgeLeft order)
    (bufferedEdgeRight order) D.candidate
    (fun r _ => D.candidate_global r)
    (fun r _ e he => D.candidate_joins r e he)
    (Finset.mem_univ _) (Finset.mem_univ _) hrt a.2 b.2

theorem connector_internallyDisjointFromSet
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j)
    (t : Fin n) (a : (D.connector i j hij).Index) :
    ((D.connector i j hij).path a).InternallyDisjointFromSet (cluster t) := by
  classical
  have hconnector :
      (D.connector i j hij).toPathPacking.InternallyDisjointFromSet
        (cluster t) := by
    by_cases h : i.1 + 1 = j.1
    · simpa [connector, h] using
        D.edgePacking_internallyDisjointFromSet_all (pathEdgeIndex hij) t
    · have hreverse := PerfectPathPacking.reverse_internallyDisjointFromSet
        (D.edgePacking (pathEdgeIndex hij))
        (D.edgePacking_internallyDisjointFromSet_all (pathEdgeIndex hij) t)
      simpa [connector, h] using hreverse
  exact hconnector a

theorem connector_mutuallyNodeDisjoint
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j)
    (p q : Fin m) (hpq : (_root_.SimpleGraph.pathGraph m).Adj p q)
    (hedge : s(i, j) ≠ s(p, q)) :
    (D.connector i j hij).toPathPacking.MutuallyNodeDisjoint
      (D.connector p q hpq).toPathPacking := by
  classical
  have hindex : pathEdgeIndex hij ≠ pathEdgeIndex hpq := by
    intro h
    exact hedge (sym2_eq_of_pathEdgeIndex_eq hij hpq h)
  have hbase := D.edgePacking_mutuallyNodeDisjoint hindex
  simp only [connector]
  split <;> split
  · apply copyTerminals_mutuallyNodeDisjoint
    exact hbase
  · apply copyTerminals_mutuallyNodeDisjoint
    exact reverse_right_mutuallyNodeDisjoint _ _ hbase
  · apply copyTerminals_mutuallyNodeDisjoint
    exact reverse_left_mutuallyNodeDisjoint _ _ hbase
  · apply copyTerminals_mutuallyNodeDisjoint
    exact reverse_both_mutuallyNodeDisjoint _ _ hbase

noncomputable def boundaryReserve
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i : Fin m) : Finset V :=
  let hdegree := pathGraph_maxDegreeAtMost_three m
  (MaxDegreeAtMost.neighborFinset hdegree i).attach.biUnion fun j =>
    D.interface i j.1
      ((MaxDegreeAtMost.mem_neighborFinset hdegree i j.1).1 j.2)

theorem interface_subset_boundaryReserve
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i j : Fin m) (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    D.interface i j hij ⊆ D.boundaryReserve i := by
  classical
  intro v hv
  let hdegree := pathGraph_maxDegreeAtMost_three m
  have hjmem : j ∈ MaxDegreeAtMost.neighborFinset hdegree i :=
    (MaxDegreeAtMost.mem_neighborFinset hdegree i j).2 hij
  let j' : {x : Fin m // x ∈ MaxDegreeAtMost.neighborFinset hdegree i} :=
    ⟨j, hjmem⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨j', by simp [j'], ?_⟩
  simpa [boundaryReserve, hdegree, j'] using hv

theorem boundaryReserve_subset_interfaceVertices
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i : Fin m) :
    D.boundaryReserve i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G
        (cluster (bufferedRouter order i)) := by
  classical
  intro v hv
  let hdegree := pathGraph_maxDegreeAtMost_three m
  rcases Finset.mem_biUnion.mp hv with ⟨j, _hj, hvj⟩
  exact D.interface_subset_interfaceVertices i j.1
    ((MaxDegreeAtMost.mem_neighborFinset hdegree i j.1).1 j.2) hvj

theorem boundaryReserve_subset_cluster
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i : Fin m) :
    D.boundaryReserve i ⊆ cluster (bufferedRouter order i) :=
  (D.boundaryReserve_subset_interfaceVertices i).trans
    (ChekuriChuzhoySection5Clustering.interfaceVertices_subset G _)

theorem boundaryReserve_card_le
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    (i : Fin m) : (D.boundaryReserve i).card ≤ 3 * width := by
  classical
  let hdegree := pathGraph_maxDegreeAtMost_three m
  calc
    (D.boundaryReserve i).card ≤
        (MaxDegreeAtMost.neighborFinset hdegree i).attach.card * width := by
      apply Finset.card_biUnion_le_card_mul
      intro j _hj
      exact (D.interface_card i j.1
        ((MaxDegreeAtMost.mem_neighborFinset hdegree i j.1).1 j.2)).le
    _ = (MaxDegreeAtMost.neighborFinset hdegree i).card * width := by simp
    _ ≤ 3 * width := Nat.mul_le_mul_right width
      (MaxDegreeAtMost.card_neighborFinset_le hdegree i)

theorem bufferedRouter_injective
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order) :
    Function.Injective (bufferedRouter order : Fin m → Fin n) := by
  intro i j hij
  have horder := D.order_injective hij
  apply Fin.ext
  have hval := congrArg Fin.val horder
  simp [bufferedRouter] at hval
  omega

theorem bufferedRouter_adj
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order)
    {i j : Fin m} (hij : (_root_.SimpleGraph.pathGraph m).Adj i j) :
    T.Adj (bufferedRouter order i) (bufferedRouter order j) := by
  rw [_root_.SimpleGraph.pathGraph_adj] at hij
  rcases hij with hij | hij
  · let r : Fin (m + 1) := ⟨i.1 + 1, by omega⟩
    simpa [r, bufferedRouter, hij] using D.order_adj r
  · let r : Fin (m + 1) := ⟨j.1 + 1, by omega⟩
    simpa [r, bufferedRouter, hij] using (D.order_adj r).symm

/-- The buffered path branch produces the ordinary bandwidth tree-of-sets
system required by source-sharp strongification. -/
noncomputable def toBandwidthTreeOfSetsSystem
    (D : BufferedPathAssemblyData S T width cap alphaNum alphaDen order) :
    BandwidthTreeOfSetsSystem G m width alphaNum alphaDen := by
  let metaHom : (_root_.SimpleGraph.pathGraph m) →g T := {
    toFun := bufferedRouter order
    map_rel' := fun {_ _} hij => D.bufferedRouter_adj hij }
  exact {
    toTreeOfSetsSystem := {
      clusterCount_pos := lt_of_lt_of_le (by omega) D.m_two
      width_pos := D.width_pos
      metaTree := _root_.SimpleGraph.pathGraph m
      meta_isTree := pathGraph_isTree_of_injective_hom
        (lt_of_lt_of_le (by omega) D.m_two) D.supportTree metaHom
        (by
          intro i j hij
          exact D.bufferedRouter_injective hij)
      meta_maxDegree_three := pathGraph_maxDegreeAtMost_three m
      cluster := fun i => cluster (bufferedRouter order i)
      cluster_connected := fun i => D.cluster_connected _
      cluster_disjoint := by
        intro i j hij
        exact D.cluster_disjoint _ _ (fun h => hij (D.bufferedRouter_injective h))
      interface := D.interface
      interface_subset_cluster := D.interface_subset_cluster
      interface_card := D.interface_card
      interface_disjoint := D.interface_disjoint
      connector := D.connector
      connector_card := D.connector_card
      connector_internally_disjoint_clusters := by
        intro i j hij r a
        exact D.connector_internallyDisjointFromSet i j hij
          (bufferedRouter order r) a
      connector_mutually_nodeDisjoint := D.connector_mutuallyNodeDisjoint }
    boundaryReserve := D.boundaryReserve
    boundaryReserve_subset_cluster := D.boundaryReserve_subset_cluster
    interface_subset_boundaryReserve := D.interface_subset_boundaryReserve
    boundaryReserve_scaledEdgeWellLinked := by
      intro i
      exact
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth.scaledEdgeWellLinkedIn_of_subset_interface
          (D.cluster_bandwidth (bufferedRouter order i))
          (D.boundaryReserve_subset_interfaceVertices i)
          ((D.boundaryReserve_card_le i).trans D.cap_width) }

end BufferedPathAssemblyData

/-- Simultaneous endpoint thinning along every middle edge of a buffered
support-tree path.  The first summand in `hretain` pays for globally distinct
interfaces and the second is the bounded-degree matching loss. -/
theorem exists_bufferedPathAssemblyData
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {m width cap alphaNum alphaDen q : Nat}
    (order : Fin (m + 2) → Fin n)
    (hm : 2 ≤ m) (hwidth : 0 < width)
    (hTree : T.IsTree)
    (horderInjective : Function.Injective order)
    (horderAdj : ∀ r : Fin (m + 1),
      T.Adj (order ⟨r.1, by omega⟩) (order ⟨r.1 + 1, by omega⟩))
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T q)
    (hretain :
      16 * Delta * (m - 1) * width + 8 * Delta ^ 2 * width ≤ q)
    (hclusterConnected : ∀ i, IsCluster G (cluster i))
    (hclusterDisjoint : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband : ∀ i,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * width ≤ cap) :
    Nonempty
      (BufferedPathAssemblyData S T width cap alphaNum alphaDen order) := by
  classical
  let candidate : Fin (m - 1) → Finset S.graph.Edge := fun r =>
    B.selected ∩ S.edgeBundle
      (bufferedEdgeLeft order r) (bufferedEdgeRight order r)
  have hleftRight : ∀ r : Fin (m - 1),
      bufferedEdgeLeft order r ≠ bufferedEdgeRight order r :=
    fun r => bufferedEdgeLeft_ne_right order horderInjective r
  have hcandidateGlobal : ∀ r : Fin (m - 1), candidate r ⊆ B.selected :=
    fun _ => Finset.inter_subset_left
  have hcandidateJoins : ∀ r : Fin (m - 1), ∀ e ∈ candidate r,
      S.graph.Joins e (bufferedEdgeLeft order r)
        (bufferedEdgeRight order r) := by
    intro r e he
    exact S.mem_edgeBundle.mp (Finset.mem_inter.mp he).2
  have hmiddleAdj : ∀ r : Fin (m - 1),
      T.Adj (bufferedEdgeLeft order r) (bufferedEdgeRight order r) := by
    intro r
    let s : Fin (m + 1) := ⟨r.1 + 1, by omega⟩
    simpa [s, bufferedEdgeLeft, bufferedEdgeRight] using horderAdj s
  have hcandidateLarge : ∀ r ∈ (Finset.univ : Finset (Fin (m - 1))),
      16 * Delta * (Finset.univ : Finset (Fin (m - 1))).card * width +
          8 * Delta ^ 2 * width ≤ (candidate r).card := by
    intro r _hr
    calc
      16 * Delta * (Finset.univ : Finset (Fin (m - 1))).card * width +
          8 * Delta ^ 2 * width =
          16 * Delta * (m - 1) * width + 8 * Delta ^ 2 * width := by simp
      _ ≤ q := hretain
      _ ≤ (candidate r).card := by
        simpa [candidate] using B.retained
          (bufferedEdgeLeft order r) (bufferedEdgeRight order r)
          (hmiddleAdj r)
  rcases exists_routerExactBundleFamily S hload hdegree hDelta B.selected
      B.groupTransversal Finset.univ (bufferedEdgeLeft order)
      (bufferedEdgeRight order) (fun r _ => hleftRight r)
      (fun r _ => hclusterDisjoint _ _ (hleftRight r)) candidate
      (fun r _ => hcandidateGlobal r)
      (fun r _ e he => hcandidateJoins r e he) hcandidateLarge with
    ⟨A⟩
  exact ⟨{
    m_two := hm
    width_pos := hwidth
    supportTree := hTree
    order_injective := horderInjective
    order_adj := horderAdj
    global := B.selected
    global_transversal := B.groupTransversal
    candidate := candidate
    candidate_global := hcandidateGlobal
    candidate_joins := hcandidateJoins
    exactFamily := A
    cluster_connected := hclusterConnected
    cluster_disjoint := hclusterDisjoint
    cluster_bandwidth := hband
    cap_width := hcap }⟩

theorem exists_bandwidthTreeOfSetsSystem_of_bufferedSupportPath
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {m width cap alphaNum alphaDen q : Nat}
    (order : Fin (m + 2) → Fin n)
    (hm : 2 ≤ m) (hwidth : 0 < width)
    (hTree : T.IsTree)
    (horderInjective : Function.Injective order)
    (horderAdj : ∀ r : Fin (m + 1),
      T.Adj (order ⟨r.1, by omega⟩) (order ⟨r.1 + 1, by omega⟩))
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T q)
    (hretain :
      16 * Delta * (m - 1) * width + 8 * Delta ^ 2 * width ≤ q)
    (hclusterConnected : ∀ i, IsCluster G (cluster i))
    (hclusterDisjoint : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband : ∀ i,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * width ≤ cap) :
    Nonempty (BandwidthTreeOfSetsSystem G m width alphaNum alphaDen) := by
  rcases exists_bufferedPathAssemblyData S T order hm hwidth hTree
      horderInjective horderAdj hload hdegree hDelta B hretain
      hclusterConnected hclusterDisjoint hband hcap with ⟨D⟩
  exact ⟨D.toBandwidthTreeOfSetsSystem⟩

end ChekuriChuzhoySection5LongPathAssembly
end SimpleGraph

end Lax17Proofs
