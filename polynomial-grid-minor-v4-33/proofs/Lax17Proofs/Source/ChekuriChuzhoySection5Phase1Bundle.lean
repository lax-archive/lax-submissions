import Lax17Proofs.Source.ChekuriChuzhoySection5EndpointThinning
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Flow
import Lax17Proofs.Source.ChekuriChuzhoySection5RouterSelection
import Lax17Proofs.Source.ChekuriChuzhoyRootedTreePruning

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Phase 1 selected support bundles

This module turns the endpoint matching selected on one Phase 1 support-tree
edge into the synchronized integral routing consumed by Claim 5.14.

Source: Chekuri--Chuzhoy, preprint Section 5.4.1, proof of Claim 5.14
(journal Claim 5.16).
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase1Bundle


open Finset
open ChekuriChuzhoySection5EndpointThinning
open ChekuriChuzhoySection5Phase1Flow
open ChekuriChuzhoySection5RouterSkeleton
open ChekuriChuzhoySection5TerminalSkeleton

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {n : Nat} {cluster : Fin n → Finset V}

/-- The global support-tree transversal, with the paper's endpoint-thinning
reserve built into its retained multiplicity, supplies an exact-width matching
on every requested support edge. -/
theorem exists_exactRouterBundle_of_supportBundleTransversal
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta width : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (hTij : T.Adj i j) :
    ∃ exact : Finset S.graph.Edge,
      exact ⊆ B.selected ∧
        exact.card = width ∧
        Set.InjOn (routerEndpointAt S i) exact ∧
        Set.InjOn (routerEndpointAt S j) exact ∧
        (∀ e ∈ exact, S.graph.Joins e i j) := by
  classical
  let selected := B.selected ∩ S.edgeBundle i j
  have hselectedGlobal : selected ⊆ B.selected :=
    Finset.inter_subset_left
  have hjoins :
      ∀ e ∈ selected, S.graph.Joins e i j := by
    intro e he
    exact S.mem_edgeBundle.mp (Finset.mem_inter.mp he).2
  have hretained :
      8 * Delta ^ 2 * width ≤ selected.card := by
    simpa [selected] using B.retained i j hTij
  have hwidth :
      width ≤ selected.card / (8 * Delta ^ 2) := by
    apply (Nat.le_div_iff_mul_le
      (by positivity : 0 < 8 * Delta ^ 2)).2
    calc
      width * (8 * Delta ^ 2) = 8 * Delta ^ 2 * width := by ring
      _ ≤ selected.card := hretained
  rcases exists_routerBundle_exact_endpoint_thinning
      S hload hdegree hDelta hij hclusterDisjoint
      B.selected B.groupTransversal selected hselectedGlobal
      hjoins hwidth with
    ⟨exact, hexactSelected, hexactCard, hinjI, hinjJ, _hmemI, _hmemJ⟩
  exact
    ⟨exact, hexactSelected.trans hselectedGlobal, hexactCard,
      hinjI, hinjJ, fun e he => hjoins e (hexactSelected he)⟩

/-- Orient a decoded skeleton path away from router `i`. -/
noncomputable def orientedHostPathAt
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (e : S.graph.Edge) : GraphPath G :=
  if S.graph.left e = i then S.hostPath e else (S.hostPath e).reverse

@[simp] theorem orientedHostPathAt_source
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (e : S.graph.Edge) :
    (orientedHostPathAt S i e).source = routerEndpointAt S i e := by
  by_cases h : S.graph.left e = i <;>
    simp [orientedHostPathAt, routerEndpointAt, h]

@[simp] theorem orientedHostPathAt_target
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j) (e : S.graph.Edge)
    (he : S.graph.Joins e i j) :
    (orientedHostPathAt S i e).target = routerEndpointAt S j e := by
  rcases he with he | he
  · simp [orientedHostPathAt, routerEndpointAt, he.1, hij]
  · have hji : j ≠ i := hij.symm
    simp [orientedHostPathAt, routerEndpointAt, he.2, hji]

@[simp] theorem orientedHostPathAt_vertexSet
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (e : S.graph.Edge) :
    (orientedHostPathAt S i e).vertexSet = (S.hostPath e).vertexSet := by
  by_cases h : S.graph.left e = i <;> simp [orientedHostPathAt, h]

theorem orientedHostPathAt_isEndpoint_iff_hostPath
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (e : S.graph.Edge) (v : V) :
    (orientedHostPathAt S i e).IsEndpoint v ↔
      (S.hostPath e).IsEndpoint v := by
  by_cases h : S.graph.left e = i <;>
    simp [orientedHostPathAt, GraphPath.IsEndpoint, h, or_comm]

theorem orientedHostPathAt_isEndpoint_iff
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j) (e : S.graph.Edge)
    (he : S.graph.Joins e i j) (v : V) :
    (orientedHostPathAt S i e).IsEndpoint v ↔
      v = routerEndpointAt S i e ∨ v = routerEndpointAt S j e := by
  simp only [GraphPath.IsEndpoint, orientedHostPathAt_source,
    orientedHostPathAt_target S hij e he]

/-- Endpoints at router `i` of a selected named support bundle. -/
noncomputable def endpointSetAt
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (selected : Finset S.graph.Edge) : Finset V :=
  selected.image (routerEndpointAt S i)

@[simp] theorem mem_endpointSetAt
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (selected : Finset S.graph.Edge) (v : V) :
    v ∈ endpointSetAt S i selected ↔
      ∃ e ∈ selected, routerEndpointAt S i e = v := by
  simp [endpointSetAt]

theorem endpointSetAt_card
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (selected : Finset S.graph.Edge)
    (hinj : Set.InjOn (routerEndpointAt S i) selected) :
    (endpointSetAt S i selected).card = selected.card := by
  exact Finset.card_image_of_injOn hinj

/-- An endpoint of a support path joining two disjoint router clusters is an
interface vertex of its incident router.  The first edge of the support path
leaves the router: otherwise its second vertex would be a non-endpoint vertex
of the path inside that router, contradicting the skeleton's directness
condition. -/
theorem routerEndpointAt_mem_interfaceVertices_of_joins
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (e : S.graph.Edge) (he : S.graph.Joins e i j) :
    routerEndpointAt S i e ∈
      ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) := by
  let P := orientedHostPathAt S i e
  have hendpoint :=
    routerEndpointAt_mem_cluster_of_joins S hij e he
  have hsource : P.source ∈ cluster i := by
    change (orientedHostPathAt S i e).source ∈ cluster i
    simpa using hendpoint.1
  have htarget : P.target ∈ cluster j := by
    change (orientedHostPathAt S i e).target ∈ cluster j
    rw [orientedHostPathAt_target S hij e he]
    exact hendpoint.2
  have hne : P.source ≠ P.target := by
    intro h
    exact Finset.disjoint_left.mp hclusterDisjoint
      hsource (by simpa [h] using htarget)
  have hsndMem : P.walk.snd ∈ P.vertexSet :=
    Section44.GraphPath.snd_mem_vertexSet P hne
  have hadj : G.Adj P.source P.walk.snd :=
    P.walk.adj_snd (P.walk_not_nil_of_source_ne_target hne)
  have hsndNot : P.walk.snd ∉ cluster i := by
    intro hsnd
    have hhostSnd :
        P.walk.snd ∈ (S.hostPath e).vertexSet := by
      simpa [P] using hsndMem
    have hhostEndpoint :
        (S.hostPath e).IsEndpoint P.walk.snd :=
      S.internally_disjoint_clusters e i hhostSnd hsnd
    have hendpointP : P.IsEndpoint P.walk.snd :=
      (orientedHostPathAt_isEndpoint_iff_hostPath S i e P.walk.snd).2
        hhostEndpoint
    rcases hendpointP with hsndSource | hsndTarget
    · exact hadj.ne hsndSource.symm
    · exact Finset.disjoint_left.mp hclusterDisjoint
        hsnd (by simpa [hsndTarget] using htarget)
  exact
    ChekuriChuzhoySection5Clustering.mem_interfaceVertices.mpr
      ⟨hendpoint.1, P.walk.snd, hsndNot, by
        change G.Adj P.source P.walk.snd at hadj
        simpa [P] using hadj⟩

/-- Every endpoint in a selected support bundle lies in the corresponding
router interface. -/
theorem endpointSetAt_subset_interfaceVertices
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (selected : Finset S.graph.Edge)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j) :
    endpointSetAt S i selected ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) := by
  intro v hv
  rcases (mem_endpointSetAt S i selected v).1 hv with ⟨e, he, rfl⟩
  exact routerEndpointAt_mem_interfaceVertices_of_joins
    S hij hclusterDisjoint e (hjoins e he)

/-- A selected support bundle whose endpoints are injective on both routers
is a node-disjoint path packing after orienting all paths from `i` to `j`.
The global group transversal supplies internal disjointness; directness through
all router clusters excludes an endpoint of one path from the interior of
another. -/
noncomputable def selectedPathPacking
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected) :
    PathPacking G (endpointSetAt S i selected)
      (endpointSetAt S j selected) where
  Index := selected
  path := fun e => orientedHostPathAt S i e.1
  connects := by
    intro e
    exact Or.inl ⟨by
      exact mem_endpointSetAt S i selected _ |>.2
        ⟨e.1, e.2, (orientedHostPathAt_source S i e.1).symm⟩,
      by
        exact mem_endpointSetAt S j selected _ |>.2
          ⟨e.1, e.2, (orientedHostPathAt_target S hij e.1
            (hjoins e.1 e.2)).symm⟩⟩
  node_disjoint := by
    intro a b hab
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hva hvb
    have habVal : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    have hva' : v ∈ (S.hostPath a.1).vertexSet := by
      simpa using hva
    have hvb' : v ∈ (S.hostPath b.1).vertexSet := by
      simpa using hvb
    have hcommon :=
      S.one_per_group_internally_node_disjoint
        global htransversal
          (hselectedGlobal a.2) (hselectedGlobal b.2) habVal hva' hvb'
    have haEnd :
        v = routerEndpointAt S i a.1 ∨
          v = routerEndpointAt S j a.1 := by
      apply (orientedHostPathAt_isEndpoint_iff
        S hij a.1 (hjoins a.1 a.2) v).1
      exact
        (orientedHostPathAt_isEndpoint_iff_hostPath S i a.1 v).2 hcommon.1
    have hbEnd :
        v = routerEndpointAt S i b.1 ∨
          v = routerEndpointAt S j b.1 := by
      apply (orientedHostPathAt_isEndpoint_iff
        S hij b.1 (hjoins b.1 b.2) v).1
      exact
        (orientedHostPathAt_isEndpoint_iff_hostPath S i b.1 v).2 hcommon.2
    have haMem :=
      routerEndpointAt_mem_cluster_of_joins
        S hij a.1 (hjoins a.1 a.2)
    have hbMem :=
      routerEndpointAt_mem_cluster_of_joins
        S hij b.1 (hjoins b.1 b.2)
    rcases haEnd with haI | haJ <;> rcases hbEnd with hbI | hbJ
    · exact habVal (hinjI a.2 b.2 (haI.symm.trans hbI))
    · exact Finset.disjoint_left.mp hclusterDisjoint
        (haI ▸ haMem.1) (hbJ ▸ hbMem.2)
    · exact Finset.disjoint_left.mp hclusterDisjoint
        (hbI ▸ hbMem.1) (haJ ▸ haMem.2)
    · exact habVal (hinjJ a.2 b.2 (haJ.symm.trans hbJ))

@[simp] theorem selectedPathPacking_card
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected) :
    (selectedPathPacking S hij hclusterDisjoint global htransversal
      selected hselectedGlobal hjoins hinjI hinjJ).card = selected.card := by
  simp [selectedPathPacking, PathPacking.card]

/-- Every selected support path is direct with respect to the union of any
specified family of router clusters.  This is the directness condition used
when the specified routers are the selected leaves in Claim 5.14. -/
theorem selectedPathPacking_internallyDisjointFrom_selectedUnion
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected)
    {m : Nat} (leafRouter : Fin m → Fin n) :
    PathPacking.InternallyDisjointFromSet
      (selectedPathPacking S hij hclusterDisjoint global htransversal
        selected hselectedGlobal hjoins hinjI hinjJ)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r))) := by
  intro e v hvPath hvSelected
  rcases
      (ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion).1
        hvSelected with
    ⟨r, hvr⟩
  have hvHost :
      v ∈ (S.hostPath e.1).vertexSet := by
    simpa [selectedPathPacking] using hvPath
  have hvEndpoint :
      (S.hostPath e.1).IsEndpoint v :=
    S.internally_disjoint_clusters e.1 (leafRouter r) hvHost hvr
  exact
    (orientedHostPathAt_isEndpoint_iff_hostPath S i e.1 v).2 hvEndpoint

namespace SynchronizedRouting

private theorem edgeDisjoint_of_nodeDisjoint
    {P Q : GraphPath G} (h : P.NodeDisjoint Q) :
    P.EdgeDisjoint Q := by
  classical
  rw [GraphPath.EdgeDisjoint, Finset.disjoint_left]
  intro edge heP heQ
  induction edge using Sym2.ind with
  | h x y =>
      have hePWalk : s(x, y) ∈ P.walk.edges := by
        simpa [GraphPath.edgeSet] using heP
      have heQWalk : s(x, y) ∈ Q.walk.edges := by
        simpa [GraphPath.edgeSet] using heQ
      have hxP : x ∈ P.vertexSet := by
        have := P.walk.fst_mem_support_of_mem_edges hePWalk
        simpa [GraphPath.vertexSet] using this
      have hxQ : x ∈ Q.vertexSet := by
        have := Q.walk.fst_mem_support_of_mem_edges heQWalk
        simpa [GraphPath.vertexSet] using this
      exact Finset.disjoint_left.mp h hxP hxQ

/-- A node-disjoint path packing, oriented from its left terminal set to its
right terminal set, is a synchronized routing. -/
noncomputable def ofPathPacking
    {S T : Finset V} (P : PathPacking G S T) :
    SynchronizedRouting G S T P.Index where
  path := fun i => P.orient.path i
  source_mem := fun i => GraphPath.orient_source_mem (P.path i) (P.connects i)
  target_mem := fun i => GraphPath.orient_target_mem (P.path i) (P.connects i)
  source_injective := by
    intro i j hij
    by_contra hne
    have hdisj := P.orient.node_disjoint hne
    exact Finset.disjoint_left.mp hdisj
      (GraphPath.source_mem_vertexSet (P.orient.path i))
      (by simpa [hij] using
        GraphPath.source_mem_vertexSet (P.orient.path j))
  target_injective := P.orient_target_injective

/-- Node-disjoint support paths have integral edge congestion one. -/
theorem ofPathPacking_edgeCongestionAtMost_one
    {S T : Finset V} (P : PathPacking G S T) :
    (ofPathPacking P).EdgeCongestionAtMost 1 := by
  classical
  intro edge _hedge
  rw [ChekuriChuzhoySection5Phase1Flow.SynchronizedRouting.edgeLoadNat,
    Finset.card_le_one]
  intro i hi j hj
  have hiEdge : edge ∈ (P.orient.path i).edgeSet :=
    (Finset.mem_filter.mp hi).2
  have hjEdge : edge ∈ (P.orient.path j).edgeSet :=
    (Finset.mem_filter.mp hj).2
  by_contra hij
  exact Finset.disjoint_left.mp
    (edgeDisjoint_of_nodeDisjoint (P.orient.node_disjoint hij))
      hiEdge hjEdge

end SynchronizedRouting

/-- Exact endpoint-thinned support paths give a `Fin width` synchronized
routing of congestion one between their endpoint sets. -/
theorem exists_synchronizedRouting_of_selectedRouterBundle
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected)
    {width : Nat} (hcard : selected.card = width) :
    ∃ R : SynchronizedRouting G
        (endpointSetAt S i selected) (endpointSetAt S j selected) (Fin width),
      R.EdgeCongestionAtMost 1 := by
  classical
  let P :=
    selectedPathPacking S hij hclusterDisjoint global htransversal
      selected hselectedGlobal hjoins hinjI hinjJ
  let R₀ : SynchronizedRouting G
      (endpointSetAt S i selected) (endpointSetAt S j selected) P.Index :=
    SynchronizedRouting.ofPathPacking P
  have hIndexCard : Fintype.card P.Index = width := by
    simpa [P, selectedPathPacking, PathPacking.card] using hcard
  let e : Fin width ≃ P.Index :=
    (Fintype.equivFinOfCardEq hIndexCard).symm
  refine ⟨R₀.reindex e, ?_⟩
  exact SynchronizedRouting.reindex_edgeCongestionAtMost R₀ e
    (SynchronizedRouting.ofPathPacking_edgeCongestionAtMost_one P)

/-- The selected support-bundle routing also remains direct with respect to
any specified union of router clusters. -/
theorem
    exists_synchronizedRouting_of_selectedRouterBundle_internallyDisjoint
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected)
    {width : Nat} (hcard : selected.card = width)
    {m : Nat} (leafRouter : Fin m → Fin n) :
    ∃ R : SynchronizedRouting G
        (endpointSetAt S i selected) (endpointSetAt S j selected) (Fin width),
      R.EdgeCongestionAtMost 1 ∧
        R.InternallyDisjointFromSet
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun r => cluster (leafRouter r))) := by
  classical
  let P :=
    selectedPathPacking S hij hclusterDisjoint global htransversal
      selected hselectedGlobal hjoins hinjI hinjJ
  let R₀ : SynchronizedRouting G
      (endpointSetAt S i selected) (endpointSetAt S j selected) P.Index :=
    SynchronizedRouting.ofPathPacking P
  have hIndexCard : Fintype.card P.Index = width := by
    simpa [P, selectedPathPacking, PathPacking.card] using hcard
  let e : Fin width ≃ P.Index :=
    (Fintype.equivFinOfCardEq hIndexCard).symm
  let R := R₀.reindex e
  refine ⟨R, ?_, ?_⟩
  · exact SynchronizedRouting.reindex_edgeCongestionAtMost R₀ e
      (SynchronizedRouting.ofPathPacking_edgeCongestionAtMost_one P)
  · have hP :
        P.InternallyDisjointFromSet
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun r => cluster (leafRouter r))) := by
      exact selectedPathPacking_internallyDisjointFrom_selectedUnion
        S hij hclusterDisjoint global htransversal selected
        hselectedGlobal hjoins hinjI hinjJ leafRouter
    have hPorient :
        P.orient.InternallyDisjointFromSet
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun r => cluster (leafRouter r))) :=
      PathPacking.orient_internallyDisjointFromSet hP
    intro x
    exact hPorient (e x)

/-! ## Endpoint synchronization -/

/-- The source endpoint map of a full synchronized routing, viewed in the
source-set subtype. -/
def sourceEndpointMap
    {A B : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G A B ι) : ι → A :=
  fun i => ⟨(R.path i).source, R.source_mem i⟩

/-- The target endpoint map of a full synchronized routing, viewed in the
target-set subtype. -/
def targetEndpointMap
    {A B : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G A B ι) : ι → B :=
  fun i => ⟨(R.path i).target, R.target_mem i⟩

/-- If the number of routed tokens equals the source-set cardinality, the
source endpoint map is an equivalence. -/
noncomputable def sourceEndpointEquiv
    {A B : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G A B ι)
    (hcard : Fintype.card ι = A.card) : ι ≃ A := by
  apply Equiv.ofBijective (sourceEndpointMap R)
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    exact R.source_injective (congrArg Subtype.val hij)
  · simpa using hcard

/-- If the number of routed tokens equals the target-set cardinality, the
target endpoint map is an equivalence. -/
noncomputable def targetEndpointEquiv
    {A B : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G A B ι)
    (hcard : Fintype.card ι = B.card) : ι ≃ B := by
  apply Equiv.ofBijective (targetEndpointMap R)
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    exact R.target_injective (congrArg Subtype.val hij)
  · simpa using hcard

@[simp] theorem sourceEndpointEquiv_val
    {A B : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G A B ι)
    (hcard : Fintype.card ι = A.card) (i : ι) :
    (sourceEndpointEquiv R hcard i).1 = (R.path i).source :=
  rfl

@[simp] theorem targetEndpointEquiv_val
    {A B : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G A B ι)
    (hcard : Fintype.card ι = B.card) (i : ι) :
    (targetEndpointEquiv R hcard i).1 = (R.path i).target :=
  rfl

/-- Reindex a following synchronized routing so that each of its source
endpoints is the preceding routing's target endpoint. -/
noncomputable def alignAfter
    {A B C : Finset V}
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G A B ι)
    (Q : SynchronizedRouting G B C κ)
    (hRCard : Fintype.card ι = B.card)
    (hQCard : Fintype.card κ = B.card) :
    SynchronizedRouting G B C ι :=
  Q.reindex
    ((targetEndpointEquiv R hRCard).trans
      (sourceEndpointEquiv Q hQCard).symm)

@[simp] theorem alignAfter_source
    {A B C : Finset V}
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G A B ι)
    (Q : SynchronizedRouting G B C κ)
    (hRCard : Fintype.card ι = B.card)
    (hQCard : Fintype.card κ = B.card) (i : ι) :
    ((alignAfter R Q hRCard hQCard).path i).source =
      (R.path i).target := by
  change
    (sourceEndpointEquiv Q hQCard
      ((sourceEndpointEquiv Q hQCard).symm
        (targetEndpointEquiv R hRCard i))).1 =
      (targetEndpointEquiv R hRCard i).1
  rw [Equiv.apply_symm_apply]

theorem alignAfter_edgeCongestionAtMost
    {A B C : Finset V}
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G A B ι)
    (Q : SynchronizedRouting G B C κ)
    (hRCard : Fintype.card ι = B.card)
    (hQCard : Fintype.card κ = B.card)
    {eta : Nat} (hQ : Q.EdgeCongestionAtMost eta) :
    (alignAfter R Q hRCard hQCard).EdgeCongestionAtMost eta := by
  exact
    ChekuriChuzhoySection5Phase1Flow.SynchronizedRouting.reindex_edgeCongestionAtMost
      Q
      ((targetEndpointEquiv R hRCard).trans
        (sourceEndpointEquiv Q hQCard).symm)
      hQ

theorem alignAfter_internallyDisjointFromSet
    {A B C forbidden : Finset V}
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G A B ι)
    (Q : SynchronizedRouting G B C κ)
    (hRCard : Fintype.card ι = B.card)
    (hQCard : Fintype.card κ = B.card)
    (hQ :
      Q.InternallyDisjointFromSet forbidden) :
    (alignAfter R Q hRCard hQCard).InternallyDisjointFromSet forbidden := by
  intro i
  exact hQ _

/-- Concatenate two full synchronized routings after matching their shared
boundary endpoints by reindexing. -/
noncomputable def concatAligned
    {A B C : Finset V}
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G A B ι)
    (Q : SynchronizedRouting G B C κ)
    (hRCard : Fintype.card ι = B.card)
    (hQCard : Fintype.card κ = B.card) :
    SynchronizedRouting G A C ι :=
  R.concat (alignAfter R Q hRCard hQCard)
    (fun i => (alignAfter_source R Q hRCard hQCard i).symm)

theorem concatAligned_edgeCongestionAtMost
    {A B C : Finset V}
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G A B ι)
    (Q : SynchronizedRouting G B C κ)
    (hRCard : Fintype.card ι = B.card)
    (hQCard : Fintype.card κ = B.card)
    {etaR etaQ : Nat}
    (hR : R.EdgeCongestionAtMost etaR)
    (hQ : Q.EdgeCongestionAtMost etaQ) :
    (concatAligned R Q hRCard hQCard).EdgeCongestionAtMost
      (etaR + etaQ) := by
  exact
    ChekuriChuzhoySection5Phase1Flow.SynchronizedRouting.concat_edgeCongestionAtMost
      R (alignAfter R Q hRCard hQCard)
      (fun i => (alignAfter_source R Q hRCard hQCard i).symm)
      hR (alignAfter_edgeCongestionAtMost R Q hRCard hQCard hQ)

theorem concatAligned_internallyDisjointFromSet
    {A B C forbidden : Finset V}
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G A B ι)
    (Q : SynchronizedRouting G B C κ)
    (hRCard : Fintype.card ι = B.card)
    (hQCard : Fintype.card κ = B.card)
    (hR : R.InternallyDisjointFromSet forbidden)
    (hQ : Q.InternallyDisjointFromSet forbidden)
    (hB : Disjoint B forbidden) :
    (concatAligned R Q hRCard hQCard).InternallyDisjointFromSet
      forbidden := by
  exact
    ChekuriChuzhoySection5Phase1Flow.SynchronizedRouting.concat_internallyDisjointFromSet
      R (alignAfter R Q hRCard hQCard)
      (fun i => (alignAfter_source R Q hRCard hQCard i).symm)
      hR (alignAfter_internallyDisjointFromSet
        R Q hRCard hQCard hQ)
      hB

/-! ## One internal-router turn -/

/-- Route one thinned support bundle into a router, cross that router using
its truncated bandwidth, and leave on the next thinned support bundle.

This is the local construction repeated in the proof of Chekuri--Chuzhoy
Claim 5.14.  The endpoint equivalences reindex the three routings so that
their paths concatenate, while congestion adds as
`etaIn + routerDen + etaOut`. -/
theorem exists_supportRouterSupportRouting_of_truncatedScaledBandwidth
    {A B C E router : Finset V}
    {width cap routerDen etaIn etaOut : Nat}
    (incoming : SynchronizedRouting G A B (Fin width))
    (outgoing : SynchronizedRouting G C E (Fin width))
    (hincoming : incoming.EdgeCongestionAtMost etaIn)
    (houtgoing : outgoing.EdgeCongestionAtMost etaOut)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G router cap 1 routerDen)
    (hBinterface :
      B ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G router)
    (hCinterface :
      C ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G router)
    (hcap : (B ∪ C).card ≤ cap)
    (hBcard : B.card = width) (hCcard : C.card = width) :
    ∃ routing : SynchronizedRouting G A E (Fin width),
      routing.EdgeCongestionAtMost (etaIn + routerDen + etaOut) := by
  rcases
      exists_synchronizedRouting_of_truncatedScaledBandwidth_one
        hband hBinterface hCinterface hcap hBcard hCcard with
    ⟨inside, hinside, _hinsideStay⟩
  have hBindex : Fintype.card (Fin width) = B.card := by
    simpa using hBcard.symm
  have hCindex : Fintype.card (Fin width) = C.card := by
    simpa using hCcard.symm
  let first :
      SynchronizedRouting G A C (Fin width) :=
    concatAligned incoming inside hBindex hBindex
  let routing :
      SynchronizedRouting G A E (Fin width) :=
    concatAligned first outgoing hCindex hCindex
  refine ⟨routing, ?_⟩
  exact
    concatAligned_edgeCongestionAtMost first outgoing hCindex hCindex
      (concatAligned_edgeCongestionAtMost
        incoming inside hBindex hBindex hincoming hinside)
      houtgoing

/-- Directness-preserving form of the preceding router-turn construction.
When the intermediate router is disjoint from the selected leaf-router union,
the internally produced paths avoid that union entirely. -/
theorem
    exists_supportRouterSupportRouting_of_truncatedScaledBandwidth_direct
    {A B C E router forbidden : Finset V}
    {width cap routerDen etaIn etaOut : Nat}
    (incoming : SynchronizedRouting G A B (Fin width))
    (outgoing : SynchronizedRouting G C E (Fin width))
    (hincoming : incoming.EdgeCongestionAtMost etaIn)
    (houtgoing : outgoing.EdgeCongestionAtMost etaOut)
    (hincomingDirect :
      incoming.InternallyDisjointFromSet forbidden)
    (houtgoingDirect :
      outgoing.InternallyDisjointFromSet forbidden)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G router cap 1 routerDen)
    (hBinterface :
      B ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G router)
    (hCinterface :
      C ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G router)
    (hcap : (B ∪ C).card ≤ cap)
    (hBcard : B.card = width) (hCcard : C.card = width)
    (hrouterForbidden : Disjoint router forbidden) :
    ∃ routing : SynchronizedRouting G A E (Fin width),
      routing.EdgeCongestionAtMost (etaIn + routerDen + etaOut) ∧
        routing.InternallyDisjointFromSet forbidden := by
  rcases exists_synchronizedRouting_of_truncatedScaledBandwidth_one
      hband hBinterface hCinterface hcap hBcard hCcard with
    ⟨inside, hinside, hinsideStay⟩
  have hinsideDirect :
      inside.InternallyDisjointFromSet forbidden := by
    intro k v hvPath hvForbidden
    exact False.elim
      (Finset.disjoint_left.mp hrouterForbidden
        (hinsideStay k hvPath) hvForbidden)
  have hBdisjoint : Disjoint B forbidden := by
    rw [Finset.disjoint_left]
    intro v hvB hvForbidden
    exact Finset.disjoint_left.mp hrouterForbidden
      (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
        G router (hBinterface hvB))
      hvForbidden
  have hCdisjoint : Disjoint C forbidden := by
    rw [Finset.disjoint_left]
    intro v hvC hvForbidden
    exact Finset.disjoint_left.mp hrouterForbidden
      (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
        G router (hCinterface hvC))
      hvForbidden
  have hBindex : Fintype.card (Fin width) = B.card := by
    simpa using hBcard.symm
  have hCindex : Fintype.card (Fin width) = C.card := by
    simpa using hCcard.symm
  let first :
      SynchronizedRouting G A C (Fin width) :=
    concatAligned incoming inside hBindex hBindex
  let routing :
      SynchronizedRouting G A E (Fin width) :=
    concatAligned first outgoing hCindex hCindex
  refine ⟨routing, ?_, ?_⟩
  · exact
      concatAligned_edgeCongestionAtMost first outgoing hCindex hCindex
        (concatAligned_edgeCongestionAtMost
          incoming inside hBindex hBindex hincoming hinside)
        houtgoing
  · exact
      concatAligned_internallyDisjointFromSet
        first outgoing hCindex hCindex
        (concatAligned_internallyDisjointFromSet
          incoming inside hBindex hBindex
          hincomingDirect hinsideDirect hBdisjoint)
        houtgoingDirect hCdisjoint

/-- A bounded support-path chain carrying the directness invariant needed by
the selected-leaf pruning step. -/
structure DirectBoundedRoutingChain
    (G : _root_.SimpleGraph V) (ι : Type)
    [Fintype ι] [DecidableEq ι]
    (S T forbidden : Finset V) (eta : Nat) where
  chain : BoundedRoutingChain G ι S T eta
  direct : chain.toRouting.InternallyDisjointFromSet forbidden

/-- Start a direct bounded chain from one synchronized support routing. -/
def DirectBoundedRoutingChain.single
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B forbidden : Finset V} {eta : Nat}
    (R : SynchronizedRouting G A B ι)
    (hR : R.EdgeCongestionAtMost eta)
    (hDirect : R.InternallyDisjointFromSet forbidden) :
    DirectBoundedRoutingChain G ι A B forbidden eta where
  chain := BoundedRoutingChain.single R hR
  direct := hDirect

/-- Enlarge the recorded congestion budget of a direct chain. -/
def DirectBoundedRoutingChain.weaken
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B forbidden : Finset V} {eta eta' : Nat}
    (chain : DirectBoundedRoutingChain G ι A B forbidden eta)
    (heta : eta ≤ eta') :
    DirectBoundedRoutingChain G ι A B forbidden eta' where
  chain := chain.chain.weaken heta
  direct := chain.direct

/-- Advance a direct bounded chain across one intermediate router and one
following support segment.  Iterating this declaration realizes every
nonempty root-to-leaf support path. -/
theorem exists_directBoundedRoutingChain_snoc_router
    {A B C E router forbidden : Finset V}
    {width cap routerDen eta etaOut : Nat}
    (prior :
      DirectBoundedRoutingChain G (Fin width) A B forbidden eta)
    (outgoing : SynchronizedRouting G C E (Fin width))
    (houtgoing : outgoing.EdgeCongestionAtMost etaOut)
    (houtgoingDirect :
      outgoing.InternallyDisjointFromSet forbidden)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G router cap 1 routerDen)
    (hBinterface :
      B ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G router)
    (hCinterface :
      C ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G router)
    (hcap : (B ∪ C).card ≤ cap)
    (hBcard : B.card = width) (hCcard : C.card = width)
    (hrouterForbidden : Disjoint router forbidden) :
    Nonempty (DirectBoundedRoutingChain G (Fin width)
      A E forbidden (eta + routerDen + etaOut)) := by
  rcases
      exists_supportRouterSupportRouting_of_truncatedScaledBandwidth_direct
        prior.chain.toRouting outgoing prior.chain.bounded houtgoing
        prior.direct houtgoingDirect hband hBinterface hCinterface hcap
        hBcard hCcard hrouterForbidden with
    ⟨routing, hrouting, hdirect⟩
  exact ⟨⟨⟨routing, hrouting⟩, hdirect⟩⟩

/-- Start a bounded root-to-leaf chain from the first endpoint-thinned support
bundle. -/
theorem exists_boundedRoutingChain_of_selectedRouterBundle
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected)
    {width : Nat} (hcard : selected.card = width) :
    Nonempty (BoundedRoutingChain G (Fin width)
      (endpointSetAt S i selected) (endpointSetAt S j selected) 1) := by
  rcases exists_synchronizedRouting_of_selectedRouterBundle
      S hij hclusterDisjoint global htransversal selected
      hselectedGlobal hjoins hinjI hinjJ hcard with
    ⟨routing, hrouting⟩
  exact ⟨BoundedRoutingChain.single routing hrouting⟩

/-- Directness-carrying start of the selected-bundle chain induction. -/
theorem exists_directBoundedRoutingChain_of_selectedRouterBundle
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected)
    {width : Nat} (hcard : selected.card = width)
    {m : Nat} (leafRouter : Fin m → Fin n) :
    Nonempty (DirectBoundedRoutingChain G (Fin width)
      (endpointSetAt S i selected) (endpointSetAt S j selected)
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
        (fun r => cluster (leafRouter r)))
      1) := by
  rcases
      exists_synchronizedRouting_of_selectedRouterBundle_internallyDisjoint
        S hij hclusterDisjoint global htransversal selected
        hselectedGlobal hjoins hinjI hinjJ hcard leafRouter with
    ⟨routing, hrouting, hdirect⟩
  exact ⟨DirectBoundedRoutingChain.single routing hrouting hdirect⟩

/-- Advance a bounded chain through one intermediate router and over the next
endpoint-thinned support bundle.

This is the induction step for the root-to-leaf construction in Claim 5.14.
Both boundary-interface hypotheses are derived from the skeleton paths; the
only numerical side condition left to the caller is that their union fits
under the router's truncation cap. -/
theorem exists_boundedRoutingChain_snoc_selectedRouterBundle
    (S : RouterPathSkeleton G cluster)
    {A : Finset V}
    {p i j : Fin n} (hpi : p ≠ i) (hij : i ≠ j)
    (hclusterPI : Disjoint (cluster p) (cluster i))
    (hclusterIJ : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (incomingSelected outgoingSelected : Finset S.graph.Edge)
    (hincomingJoins :
      ∀ e ∈ incomingSelected, S.graph.Joins e p i)
    (hincomingInjI :
      Set.InjOn (routerEndpointAt S i) incomingSelected)
    (houtgoingGlobal : outgoingSelected ⊆ global)
    (houtgoingJoins :
      ∀ e ∈ outgoingSelected, S.graph.Joins e i j)
    (houtgoingInjI :
      Set.InjOn (routerEndpointAt S i) outgoingSelected)
    (houtgoingInjJ :
      Set.InjOn (routerEndpointAt S j) outgoingSelected)
    {width cap routerDen eta : Nat}
    (hincomingCard : incomingSelected.card = width)
    (houtgoingCard : outgoingSelected.card = width)
    (chain : BoundedRoutingChain G (Fin width)
      A
      (endpointSetAt S i incomingSelected) eta)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap 1 routerDen)
    (hcap :
      (endpointSetAt S i incomingSelected ∪
        endpointSetAt S i outgoingSelected).card ≤ cap) :
    Nonempty (BoundedRoutingChain G (Fin width)
      A
      (endpointSetAt S j outgoingSelected)
      (eta + routerDen + 1)) := by
  have hincomingAtI :
      ∀ e ∈ incomingSelected, S.graph.Joins e i p := by
    intro e he
    exact (S.graph.joins_comm e p i).mp (hincomingJoins e he)
  have hincomingInterface :
      endpointSetAt S i incomingSelected ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hpi.symm hclusterPI.symm incomingSelected hincomingAtI
  have houtgoingInterface :
      endpointSetAt S i outgoingSelected ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hij hclusterIJ outgoingSelected houtgoingJoins
  have hincomingEndpointCard :
      (endpointSetAt S i incomingSelected).card = width := by
    exact (endpointSetAt_card S i incomingSelected hincomingInjI).trans
      hincomingCard
  have houtgoingEndpointCard :
      (endpointSetAt S i outgoingSelected).card = width :=
    (endpointSetAt_card S i outgoingSelected houtgoingInjI).trans
      houtgoingCard
  rcases exists_synchronizedRouting_of_selectedRouterBundle
      S hij hclusterIJ global htransversal outgoingSelected
      houtgoingGlobal houtgoingJoins houtgoingInjI houtgoingInjJ
      houtgoingCard with
    ⟨outgoing, houtgoing⟩
  rcases exists_supportRouterSupportRouting_of_truncatedScaledBandwidth
      chain.toRouting outgoing chain.bounded houtgoing hband
      hincomingInterface houtgoingInterface hcap
      hincomingEndpointCard houtgoingEndpointCard with
    ⟨routing, hrouting⟩
  exact ⟨⟨routing, hrouting⟩⟩

/-- Directness-carrying selected-bundle induction step for Claim 5.14. -/
theorem exists_directBoundedRoutingChain_snoc_selectedRouterBundle
    (S : RouterPathSkeleton G cluster)
    {A : Finset V}
    {p i j : Fin n} (hpi : p ≠ i) (hij : i ≠ j)
    (hclusterPI : Disjoint (cluster p) (cluster i))
    (hclusterIJ : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (incomingSelected outgoingSelected : Finset S.graph.Edge)
    (hincomingJoins :
      ∀ e ∈ incomingSelected, S.graph.Joins e p i)
    (hincomingInjI :
      Set.InjOn (routerEndpointAt S i) incomingSelected)
    (houtgoingGlobal : outgoingSelected ⊆ global)
    (houtgoingJoins :
      ∀ e ∈ outgoingSelected, S.graph.Joins e i j)
    (houtgoingInjI :
      Set.InjOn (routerEndpointAt S i) outgoingSelected)
    (houtgoingInjJ :
      Set.InjOn (routerEndpointAt S j) outgoingSelected)
    {width cap routerDen eta m : Nat}
    (hincomingCard : incomingSelected.card = width)
    (houtgoingCard : outgoingSelected.card = width)
    (leafRouter : Fin m → Fin n)
    (prior : DirectBoundedRoutingChain G (Fin width)
      A (endpointSetAt S i incomingSelected)
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
        (fun r => cluster (leafRouter r)))
      eta)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap 1 routerDen)
    (hcap :
      (endpointSetAt S i incomingSelected ∪
        endpointSetAt S i outgoingSelected).card ≤ cap)
    (hintermediate :
      Disjoint (cluster i)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))) :
    Nonempty (DirectBoundedRoutingChain G (Fin width)
      A (endpointSetAt S j outgoingSelected)
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
        (fun r => cluster (leafRouter r)))
      (eta + routerDen + 1)) := by
  have hincomingAtI :
      ∀ e ∈ incomingSelected, S.graph.Joins e i p := by
    intro e he
    exact (S.graph.joins_comm e p i).mp (hincomingJoins e he)
  have hincomingInterface :
      endpointSetAt S i incomingSelected ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hpi.symm hclusterPI.symm incomingSelected hincomingAtI
  have houtgoingInterface :
      endpointSetAt S i outgoingSelected ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hij hclusterIJ outgoingSelected houtgoingJoins
  have hincomingEndpointCard :
      (endpointSetAt S i incomingSelected).card = width :=
    (endpointSetAt_card S i incomingSelected hincomingInjI).trans
      hincomingCard
  have houtgoingEndpointCard :
      (endpointSetAt S i outgoingSelected).card = width :=
    (endpointSetAt_card S i outgoingSelected houtgoingInjI).trans
      houtgoingCard
  rcases
      exists_synchronizedRouting_of_selectedRouterBundle_internallyDisjoint
        S hij hclusterIJ global htransversal outgoingSelected
        houtgoingGlobal houtgoingJoins houtgoingInjI houtgoingInjJ
        houtgoingCard leafRouter with
    ⟨outgoing, houtgoing, houtgoingDirect⟩
  exact exists_directBoundedRoutingChain_snoc_router
    prior outgoing houtgoing houtgoingDirect hband
    hincomingInterface houtgoingInterface hcap
    hincomingEndpointCard houtgoingEndpointCard hintermediate

/-! ## Transversal-produced support-path prefixes -/

/-- A realized nonempty prefix of a root-to-leaf support-tree path.  The
incoming selected bundle is retained because it supplies the boundary set
used by the next internal-router turn. -/
structure DirectSelectedSupportPrefix
    (S : RouterPathSkeleton G cluster)
    (rootRouter forbidden : Finset V)
    (previous current : Fin n) (width eta : Nat) where
  sourceBoundary : Finset V
  sourceBoundary_subset_root : sourceBoundary ⊆ rootRouter
  sourceBoundary_subset_interfaceRoot :
    sourceBoundary ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G rootRouter
  sourceBoundary_card : sourceBoundary.card = width
  previous_ne_current : previous ≠ current
  incomingSelected : Finset S.graph.Edge
  incomingJoins :
    ∀ e ∈ incomingSelected, S.graph.Joins e previous current
  incomingInjCurrent :
    Set.InjOn (routerEndpointAt S current) incomingSelected
  incomingCard : incomingSelected.card = width
  routing :
    DirectBoundedRoutingChain G (Fin width)
      sourceBoundary (endpointSetAt S current incomingSelected)
      forbidden eta

/-- Enlarge the common congestion budget recorded by a realized prefix. -/
noncomputable def DirectSelectedSupportPrefix.weaken
    {S : RouterPathSkeleton G cluster}
    {rootRouter forbidden : Finset V}
    {previous current : Fin n} {width eta eta' : Nat}
    (P : DirectSelectedSupportPrefix S rootRouter forbidden
      previous current width eta)
    (heta : eta ≤ eta') :
    DirectSelectedSupportPrefix S rootRouter forbidden
      previous current width eta' where
  sourceBoundary := P.sourceBoundary
  sourceBoundary_subset_root := P.sourceBoundary_subset_root
  sourceBoundary_subset_interfaceRoot :=
    P.sourceBoundary_subset_interfaceRoot
  sourceBoundary_card := P.sourceBoundary_card
  previous_ne_current := P.previous_ne_current
  incomingSelected := P.incomingSelected
  incomingJoins := P.incomingJoins
  incomingInjCurrent := P.incomingInjCurrent
  incomingCard := P.incomingCard
  routing := P.routing.weaken heta

/-- Realize the first support-tree edge of a path directly from the global
bundle transversal. -/
theorem exists_directSelectedSupportPrefix_of_transversal
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta width m : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (hTij : T.Adj i j)
    (leafRouter : Fin m → Fin n) :
    Nonempty
      (DirectSelectedSupportPrefix S (cluster i)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))
        i j width 1) := by
  classical
  rcases exists_exactRouterBundle_of_supportBundleTransversal
      S T hload hdegree hDelta B hij hclusterDisjoint hTij with
    ⟨exact, hexactGlobal, hexactCard, hinjI, hinjJ, hjoins⟩
  rcases exists_directBoundedRoutingChain_of_selectedRouterBundle
      S hij hclusterDisjoint B.selected B.groupTransversal exact
      hexactGlobal hjoins hinjI hinjJ hexactCard leafRouter with
    ⟨routing⟩
  have hsourceSubset :
      endpointSetAt S i exact ⊆ cluster i := by
    intro v hv
    rcases (mem_endpointSetAt S i exact v).mp hv with ⟨e, he, rfl⟩
    exact (routerEndpointAt_mem_cluster_of_joins S hij e (hjoins e he)).1
  have hsourceInterface :
      endpointSetAt S i exact ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hij hclusterDisjoint exact hjoins
  exact ⟨{
    sourceBoundary := endpointSetAt S i exact
    sourceBoundary_subset_root := hsourceSubset
    sourceBoundary_subset_interfaceRoot := hsourceInterface
    sourceBoundary_card := (endpointSetAt_card S i exact hinjI).trans
      hexactCard
    previous_ne_current := hij
    incomingSelected := exact
    incomingJoins := hjoins
    incomingInjCurrent := hinjJ
    incomingCard := hexactCard
    routing := routing
  }⟩

/-- Extend a realized support-path prefix by one tree edge.  Exact endpoint
thinning on the new edge is produced internally from the same global
transversal. -/
theorem exists_directSelectedSupportPrefix_snoc_of_transversal
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta width cap routerDen eta m : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    {rootRouter : Finset V}
    {p i j : Fin n} (hpi : p ≠ i) (hij : i ≠ j)
    (hclusterPI : Disjoint (cluster p) (cluster i))
    (hclusterIJ : Disjoint (cluster i) (cluster j))
    (hTij : T.Adj i j)
    (leafRouter : Fin m → Fin n)
    (prior :
      DirectSelectedSupportPrefix S rootRouter
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))
        p i width eta)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate :
      Disjoint (cluster i)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))) :
    Nonempty
      (DirectSelectedSupportPrefix S rootRouter
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))
        i j width (eta + routerDen + 1)) := by
  classical
  rcases exists_exactRouterBundle_of_supportBundleTransversal
      S T hload hdegree hDelta B hij hclusterIJ hTij with
    ⟨exact, hexactGlobal, hexactCard, hinjI, hinjJ, hjoins⟩
  have hendpointCap :
      (endpointSetAt S i prior.incomingSelected ∪
        endpointSetAt S i exact).card ≤ cap := by
    calc
      (endpointSetAt S i prior.incomingSelected ∪
          endpointSetAt S i exact).card ≤
          (endpointSetAt S i prior.incomingSelected).card +
            (endpointSetAt S i exact).card :=
        Finset.card_union_le _ _
      _ = width + width := by
        rw [endpointSetAt_card S i prior.incomingSelected
          prior.incomingInjCurrent,
          endpointSetAt_card S i exact hinjI,
          prior.incomingCard, hexactCard]
      _ = 2 * width := by omega
      _ ≤ cap := hcap
  rcases exists_directBoundedRoutingChain_snoc_selectedRouterBundle
      S hpi hij hclusterPI hclusterIJ B.selected B.groupTransversal
      prior.incomingSelected exact prior.incomingJoins
      prior.incomingInjCurrent hexactGlobal hjoins hinjI hinjJ
      prior.incomingCard hexactCard leafRouter prior.routing
      hband hendpointCap hintermediate with
    ⟨routing⟩
  exact ⟨{
    sourceBoundary := prior.sourceBoundary
    sourceBoundary_subset_root := prior.sourceBoundary_subset_root
    sourceBoundary_subset_interfaceRoot :=
      prior.sourceBoundary_subset_interfaceRoot
    sourceBoundary_card := prior.sourceBoundary_card
    previous_ne_current := hij
    incomingSelected := exact
    incomingJoins := hjoins
    incomingInjCurrent := hinjJ
    incomingCard := hexactCard
    routing := routing
  }⟩

/-! ## Finite support-path realization -/

/-- Realize every edge of an injective support-tree vertex sequence.

The sequence has `steps + 2` vertices, so `steps = 0` is the one-edge base
case.  Each of the `steps` internal routers contributes `routerDen`, and each
selected support bundle contributes one unit of edge congestion. -/
theorem exists_directSelectedSupportPrefix_of_injective_order
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta width cap routerDen m steps : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (order : Fin (steps + 2) → Fin n)
    (hinjective : Function.Injective order)
    (hadj :
      ∀ r : Fin (steps + 1),
        T.Adj (order ⟨r.1, by omega⟩)
          (order ⟨r.1 + 1, by omega⟩))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ r : Fin steps,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster (order ⟨r.1 + 1, by omega⟩))
          cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate :
      ∀ r : Fin steps,
        Disjoint (cluster (order ⟨r.1 + 1, by omega⟩))
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))) :
    Nonempty
      (DirectSelectedSupportPrefix S
        (cluster (order ⟨0, by omega⟩))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s)))
        (order ⟨steps, by omega⟩)
        (order ⟨steps + 1, by omega⟩)
        width (1 + steps * (routerDen + 1))) := by
  induction steps with
  | zero =>
      have hne :
          order ⟨0, by omega⟩ ≠ order ⟨1, by omega⟩ := by
        exact hinjective.ne (by simp)
      simpa using
        exists_directSelectedSupportPrefix_of_transversal
          S T hload hdegree hDelta B hne
          (hclusterDisjoint hne) (hadj ⟨0, by omega⟩) leafRouter
  | succ steps ih =>
      let shorter : Fin (steps + 2) → Fin n :=
        fun r => order ⟨r.1, by omega⟩
      have hshorterInjective : Function.Injective shorter := by
        intro a b hab
        apply Fin.ext
        have hcast :=
          congrArg Fin.val
            (hinjective hab :
            (⟨a.1, by omega⟩ : Fin (steps + 3)) =
              ⟨b.1, by omega⟩)
        simpa using hcast
      have hshorterAdj :
          ∀ r : Fin (steps + 1),
            T.Adj (shorter ⟨r.1, by omega⟩)
              (shorter ⟨r.1 + 1, by omega⟩) := by
        intro r
        exact hadj ⟨r.1, by omega⟩
      have hshorterBand :
          ∀ r : Fin steps,
            ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
              G (cluster (shorter ⟨r.1 + 1, by omega⟩))
              cap 1 routerDen := by
        intro r
        exact hband ⟨r.1, by omega⟩
      have hshorterIntermediate :
          ∀ r : Fin steps,
            Disjoint (cluster (shorter ⟨r.1 + 1, by omega⟩))
              (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
                (fun s => cluster (leafRouter s))) := by
        intro r
        exact hintermediate ⟨r.1, by omega⟩
      rcases ih shorter hshorterInjective hshorterAdj
          hshorterBand hshorterIntermediate with
        ⟨prior⟩
      have hpi :
          shorter ⟨steps, by omega⟩ ≠
            shorter ⟨steps + 1, by omega⟩ := by
        exact hshorterInjective.ne (by simp)
      have hij :
          order ⟨steps + 1, by omega⟩ ≠
            order ⟨steps + 2, by omega⟩ := by
        exact hinjective.ne (by simp)
      rcases
          exists_directSelectedSupportPrefix_snoc_of_transversal
            S T hload hdegree hDelta B hpi hij
            (hclusterDisjoint hpi)
            (hclusterDisjoint hij)
            (hadj ⟨steps + 1, by omega⟩)
            leafRouter prior
            (hband ⟨steps, by omega⟩)
            hcap
            (hintermediate ⟨steps, by omega⟩) with
        ⟨result⟩
      have hresult : Nonempty
          (DirectSelectedSupportPrefix S
            (cluster (shorter ⟨0, by omega⟩))
            (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
              (fun s => cluster (leafRouter s)))
            (shorter ⟨steps + 1, by omega⟩)
            (order ⟨steps + 2, by omega⟩)
            width ((1 + steps * (routerDen + 1)) + routerDen + 1)) :=
        ⟨result⟩
      have heta :
          (1 + steps * (routerDen + 1)) + routerDen + 1 =
            1 + (steps + 1) * (routerDen + 1) := by
        simp only [Nat.add_mul, one_mul]
        omega
      rw [heta] at hresult
      simpa [shorter] using hresult

/-- Uniform-budget form of finite support-path realization.  It allows paths
of different lengths to inhabit one family indexed by the common budget
consumed by Claim 5.14. -/
theorem exists_directSelectedSupportPrefix_of_injective_order_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta width cap routerDen m steps eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (order : Fin (steps + 2) → Fin n)
    (hinjective : Function.Injective order)
    (hadj :
      ∀ r : Fin (steps + 1),
        T.Adj (order ⟨r.1, by omega⟩)
          (order ⟨r.1 + 1, by omega⟩))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ r : Fin steps,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster (order ⟨r.1 + 1, by omega⟩))
          cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate :
      ∀ r : Fin steps,
        Disjoint (cluster (order ⟨r.1 + 1, by omega⟩))
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s))))
    (heta : 1 + steps * (routerDen + 1) ≤ eta) :
    Nonempty
      (DirectSelectedSupportPrefix S
        (cluster (order ⟨0, by omega⟩))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s)))
        (order ⟨steps, by omega⟩)
        (order ⟨steps + 1, by omega⟩)
        width eta) := by
  rcases exists_directSelectedSupportPrefix_of_injective_order
      S T hload hdegree hDelta B leafRouter order hinjective hadj
      hclusterDisjoint hband hcap hintermediate with
    ⟨P⟩
  exact ⟨P.weaken heta⟩

/-- Convert an actual simple path in the support graph into the finite
injective order consumed by the routing-chain recursion. -/
theorem exists_directSelectedSupportPrefix_of_graphPath_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta width cap routerDen m steps eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (P : GraphPath T)
    (hlength : P.walk.length = steps + 1)
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ r : Fin steps,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster (P.walk.getVert (r.1 + 1)))
          cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate :
      ∀ r : Fin steps,
        Disjoint (cluster (P.walk.getVert (r.1 + 1)))
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s))))
    (heta : 1 + steps * (routerDen + 1) ≤ eta) :
    ∃ previous : Fin n,
      Nonempty
        (DirectSelectedSupportPrefix S (cluster P.source)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          previous P.target width eta) := by
  let order : Fin (steps + 2) → Fin n :=
    fun r => P.walk.getVert r.1
  have hinjective : Function.Injective order := by
    intro a b hab
    apply Fin.ext
    exact P.isPath.getVert_injOn
      (by simp; omega)
      (by simp; omega)
      hab
  have hadj :
      ∀ r : Fin (steps + 1),
        T.Adj (order ⟨r.1, by omega⟩)
          (order ⟨r.1 + 1, by omega⟩) := by
    intro r
    apply P.walk.adj_getVert_succ
    rw [hlength]
    exact r.isLt
  have hbandOrder :
      ∀ r : Fin steps,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster (order ⟨r.1 + 1, by omega⟩))
          cap 1 routerDen := by
    intro r
    exact hband r
  have hintermediateOrder :
      ∀ r : Fin steps,
        Disjoint (cluster (order ⟨r.1 + 1, by omega⟩))
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s))) := by
    intro r
    exact hintermediate r
  rcases exists_directSelectedSupportPrefix_of_injective_order_bounded
      S T hload hdegree hDelta B leafRouter order hinjective hadj
      hclusterDisjoint hbandOrder hcap hintermediateOrder heta with
    ⟨routePrefix⟩
  refine ⟨order ⟨steps, by omega⟩, ?_⟩
  have hsource : order ⟨0, by omega⟩ = P.source := by
    simp [order]
  have htarget : order ⟨steps + 1, by omega⟩ = P.target := by
    change P.walk.getVert (steps + 1) = P.target
    rw [← hlength]
    exact P.walk.getVert_length
  rw [hsource, htarget] at routePrefix
  exact ⟨routePrefix⟩

/-- The canonical simple graph path obtained from the unique shortest walk in
a finite tree. -/
noncomputable def supportTreePath
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    (root leaf : Fin n) : GraphPath T where
  source := root
  target := leaf
  walk :=
    ChekuriChuzhoyRootedTreePruning.rootPath hT root leaf
  isPath :=
    ChekuriChuzhoyRootedTreePruning.rootPath_isPath hT root leaf

@[simp] theorem supportTreePath_source
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    (root leaf : Fin n) :
    (supportTreePath T hT root leaf).source = root :=
  rfl

@[simp] theorem supportTreePath_target
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    (root leaf : Fin n) :
    (supportTreePath T hT root leaf).target = leaf :=
  rfl

@[simp] theorem supportTreePath_length
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    (root leaf : Fin n) :
    (supportTreePath T hT root leaf).walk.length = T.dist root leaf := by
  exact ChekuriChuzhoyRootedTreePruning.rootPath_length hT root leaf

/-- A strict internal vertex of a simple path has two distinct path
neighbors, so its degree cannot be one. -/
theorem graphPath_internal_vertex_not_degreeEquals_one
    {T : _root_.SimpleGraph (Fin n)}
    (P : GraphPath T) {a : Nat}
    (ha : a + 1 < P.walk.length) :
    ¬ DegreeEquals T (P.walk.getVert (a + 1)) 1 := by
  intro hdegreeOne
  rcases hdegreeOne with ⟨N, hN, hNcard⟩
  have hprev :
      T.Adj (P.walk.getVert (a + 1)) (P.walk.getVert a) :=
    (P.walk.adj_getVert_succ (i := a) (by omega)).symm
  have hnext :
      T.Adj (P.walk.getVert (a + 1)) (P.walk.getVert (a + 2)) := by
    simpa [Nat.add_assoc] using
      P.walk.adj_getVert_succ (i := a + 1) ha
  have hprevNext :
      P.walk.getVert a ≠ P.walk.getVert (a + 2) := by
    intro h
    have hindex :=
      P.isPath.getVert_injOn
        (by simp; omega)
        (by simp; omega)
        h
    omega
  have hpairSubset :
      ({P.walk.getVert a, P.walk.getVert (a + 2)} : Finset (Fin n)) ⊆ N := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (hN _).2 hprev
    · exact (hN _).2 hnext
  have htwo : 2 ≤ N.card := by
    have hcard := Finset.card_le_card hpairSubset
    simpa [hprevNext] using hcard
  omega

/-- Realize the canonical nontrivial root-to-leaf path of the support tree.
No explicit path or vertex-order datum remains in this interface. -/
theorem exists_directSelectedSupportPrefix_of_supportTreePath_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {Delta width cap routerDen m eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (root leaf : Fin n) (hrootLeaf : root ≠ leaf)
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ r : Fin (T.dist root leaf - 1),
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G
          (cluster
            ((supportTreePath T hT root leaf).walk.getVert (r.1 + 1)))
          cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate :
      ∀ r : Fin (T.dist root leaf - 1),
        Disjoint
          (cluster
            ((supportTreePath T hT root leaf).walk.getVert (r.1 + 1)))
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s))))
    (heta :
      1 + (T.dist root leaf - 1) * (routerDen + 1) ≤ eta) :
    ∃ previous : Fin n,
      Nonempty
        (DirectSelectedSupportPrefix S (cluster root)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          previous leaf width eta) := by
  have hdistPos : 0 < T.dist root leaf :=
    hT.connected.pos_dist_of_ne hrootLeaf
  have hlength :
      (supportTreePath T hT root leaf).walk.length =
        (T.dist root leaf - 1) + 1 := by
    rw [supportTreePath_length]
    omega
  simpa using
    exists_directSelectedSupportPrefix_of_graphPath_bounded
      S T hload hdegree hDelta B leafRouter
      (supportTreePath T hT root leaf) hlength
      hclusterDisjoint hband hcap hintermediate heta

/-- Root-to-leaf support-tree realization with internal-router avoidance
derived from the fact that every selected router is a degree-one tree vertex.
-/
theorem
    exists_directSelectedSupportPrefix_of_supportTreePath_leafFamily_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {Delta width cap routerDen m eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (hleaf : ∀ r, DegreeEquals T (leafRouter r) 1)
    (root : Fin n) (r : Fin m) (hrootLeaf : root ≠ leafRouter r)
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      1 + (T.dist root (leafRouter r) - 1) * (routerDen + 1) ≤ eta) :
    ∃ previous : Fin n,
      Nonempty
        (DirectSelectedSupportPrefix S (cluster root)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          previous (leafRouter r) width eta) := by
  let P := supportTreePath T hT root (leafRouter r)
  have hintermediate :
      ∀ a : Fin (T.dist root (leafRouter r) - 1),
        Disjoint
          (cluster (P.walk.getVert (a.1 + 1)))
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s))) := by
    intro a
    have hnotLeaf :
        ∀ s : Fin m, P.walk.getVert (a.1 + 1) ≠ leafRouter s := by
      intro s heq
      apply
        graphPath_internal_vertex_not_degreeEquals_one P (a := a.1)
      · rw [supportTreePath_length]
        omega
      · rw [heq]
        exact hleaf s
    rw [Finset.disjoint_left]
    intro v hvInternal hvSelected
    rcases
        ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mp
          hvSelected with
      ⟨s, hvLeaf⟩
    exact Finset.disjoint_left.mp
      (hclusterDisjoint (hnotLeaf s)) hvInternal hvLeaf
  exact
    exists_directSelectedSupportPrefix_of_supportTreePath_bounded
      S T hT hload hdegree hDelta B leafRouter root (leafRouter r)
      hrootLeaf hclusterDisjoint
      (fun _ => hband _) hcap hintermediate heta

/-! ## Simultaneous selected-leaf realization -/

/-- Simultaneously realize the canonical root path to every selected
degree-one leaf with one common congestion budget. -/
theorem exists_directSelectedSupportPrefixFamily_of_leafFamily_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {Delta width cap routerDen m eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (hleaf : ∀ r, DegreeEquals T (leafRouter r) 1)
    (root : Fin n)
    (hrootLeaf : ∀ r, root ≠ leafRouter r)
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      ∀ r,
        1 + (T.dist root (leafRouter r) - 1) * (routerDen + 1) ≤ eta) :
    ∃ previous : Fin m → Fin n,
      Nonempty
        (∀ r : Fin m,
          DirectSelectedSupportPrefix S (cluster root)
            (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
              (fun s => cluster (leafRouter s)))
            (previous r) (leafRouter r) width eta) := by
  classical
  have hpointwise :
      ∀ r : Fin m,
        ∃ previous : Fin n,
          Nonempty
            (DirectSelectedSupportPrefix S (cluster root)
              (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
                (fun s => cluster (leafRouter s)))
              previous (leafRouter r) width eta) := by
    intro r
    exact
      exists_directSelectedSupportPrefix_of_supportTreePath_leafFamily_bounded
        S T hT hload hdegree hDelta B leafRouter hleaf root r
        (hrootLeaf r) hclusterDisjoint hband hcap (heta r)
  let previous : Fin m → Fin n :=
    fun r => Classical.choose (hpointwise r)
  let family :
      ∀ r : Fin m,
        DirectSelectedSupportPrefix S (cluster root)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          (previous r) (leafRouter r) width eta :=
    fun r => Classical.choice (Classical.choose_spec (hpointwise r))
  exact ⟨previous, ⟨family⟩⟩

/-! ## Claim 5.14/5.15 endpoint from realized prefixes -/

/-- A family of realized prefixes may be integrated against any common
root-side target set containing all of their source boundaries. -/
theorem claim514_claim515_of_directSelectedSupportPrefixes_to_rootTarget
    {m width quota Delta eta : Nat}
    {rootRouter rootTarget : Finset V}
    {leafRouter previous : Fin m → Fin n}
    (S : RouterPathSkeleton G cluster)
    (family : ∀ r : Fin m,
      DirectSelectedSupportPrefix S rootRouter
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s)))
        (previous r) (leafRouter r) width eta)
    (hsourceTarget :
      ∀ r, (family r).sourceBoundary ⊆ rootTarget)
    (hrootTarget :
      Disjoint rootTarget
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r))))
    (hdegree : MaxDegreeAtMost G Delta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G (fun r => cluster (leafRouter r)))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota) rootTarget),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  have hterminalRouter :
      ∀ r, endpointSetAt S (leafRouter r) (family r).incomingSelected ⊆
        cluster (leafRouter r) := by
    intro r v hv
    rcases (mem_endpointSetAt S (leafRouter r)
      (family r).incomingSelected v).mp hv with ⟨e, he, rfl⟩
    exact
      (routerEndpointAt_mem_cluster_of_joins S
        (family r).previous_ne_current
        e ((family r).incomingJoins e he)).2
  have hrootTerminalDisjoint :
      ∀ r, Disjoint (family r).sourceBoundary
        (endpointSetAt S (leafRouter r) (family r).incomingSelected) := by
    intro r
    rw [Finset.disjoint_left]
    intro v hvRoot hvTerminal
    exact Finset.disjoint_left.mp hrootTarget
      (hsourceTarget r hvRoot)
      (ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mpr
        ⟨r, hterminalRouter r hvTerminal⟩)
  apply
    claim514_claim515_exists_integral_leaf_paths_of_varying_root_boundaryChains
      (chain := fun r => (family r).routing.chain)
      (rootTerminal := fun r => (family r).sourceBoundary)
      (terminal := fun r =>
        endpointSetAt S (leafRouter r) (family r).incomingSelected)
      (router := fun r => cluster (leafRouter r))
      (rootRouter := rootTarget)
      (quota := quota)
      (Delta := Delta)
  · exact hsourceTarget
  · exact hterminalRouter
  · exact hrootTarget
  · exact fun r => (family r).sourceBoundary_card
  · intro r
    exact
      (endpointSetAt_card S (leafRouter r) (family r).incomingSelected
        (family r).incomingInjCurrent).trans (family r).incomingCard
  · exact hrootTerminalDisjoint
  · exact fun r => (family r).routing.direct
  · exact hdegree
  · exact hc
  · exact hquotaPos
  · exact hquota
  · exact hcapacity

/-- A family of realized root-to-leaf prefixes supplies the complete,
paper-faithful Claim 5.14/5.15 integral packing. -/
theorem claim514_claim515_of_directSelectedSupportPrefixes
    {m width quota Delta eta : Nat}
    {rootRouter : Finset V}
    {leafRouter previous : Fin m → Fin n}
    (S : RouterPathSkeleton G cluster)
    (family : ∀ r : Fin m,
      DirectSelectedSupportPrefix S rootRouter
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s)))
        (previous r) (leafRouter r) width eta)
    (hrootRouter :
      Disjoint rootRouter
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r))))
    (hdegree : MaxDegreeAtMost G Delta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G (fun r => cluster (leafRouter r)))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota) rootRouter),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  have hterminalRouter :
      ∀ r, endpointSetAt S (leafRouter r) (family r).incomingSelected ⊆
        cluster (leafRouter r) := by
    intro r v hv
    rcases (mem_endpointSetAt S (leafRouter r)
      (family r).incomingSelected v).mp hv with ⟨e, he, rfl⟩
    exact
      (routerEndpointAt_mem_cluster_of_joins S
        (family r).previous_ne_current
        e ((family r).incomingJoins e he)).2
  have hrootTerminalDisjoint :
      ∀ r, Disjoint (family r).sourceBoundary
        (endpointSetAt S (leafRouter r) (family r).incomingSelected) := by
    intro r
    rw [Finset.disjoint_left]
    intro v hvRoot hvTerminal
    exact Finset.disjoint_left.mp hrootRouter
      ((family r).sourceBoundary_subset_root hvRoot)
      (ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mpr
        ⟨r, hterminalRouter r hvTerminal⟩)
  apply
    claim514_claim515_exists_integral_leaf_paths_of_varying_root_boundaryChains
      (chain := fun r => (family r).routing.chain)
      (rootTerminal := fun r => (family r).sourceBoundary)
      (terminal := fun r =>
        endpointSetAt S (leafRouter r) (family r).incomingSelected)
      (router := fun r => cluster (leafRouter r))
      (rootRouter := rootRouter)
      (quota := quota)
      (Delta := Delta)
  · exact fun r => (family r).sourceBoundary_subset_root
  · exact hterminalRouter
  · exact hrootRouter
  · exact fun r => (family r).sourceBoundary_card
  · intro r
    exact
      (endpointSetAt_card S (leafRouter r) (family r).incomingSelected
        (family r).incomingInjCurrent).trans (family r).incomingCard
  · exact hrootTerminalDisjoint
  · exact fun r => (family r).routing.direct
  · exact hdegree
  · exact hc
  · exact hquotaPos
  · exact hquota
  · exact hcapacity

/-- Complete Claims 5.14 and 5.15 directly from a support tree, its selected
degree-one leaf family, global router bandwidth, and the explicit numerical
capacity inequalities. -/
theorem claim514_claim515_of_supportTree_leafFamily
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {Delta width cap routerDen m eta quota : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (hleaf : ∀ r, DegreeEquals T (leafRouter r) 1)
    (root : Fin n)
    (hrootLeaf : ∀ r, root ≠ leafRouter r)
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      ∀ r,
        1 + (T.dist root (leafRouter r) - 1) * (routerDen + 1) ≤ eta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G (fun r => cluster (leafRouter r)))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota) (cluster root)),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  rcases exists_directSelectedSupportPrefixFamily_of_leafFamily_bounded
      S T hT hload hdegree hDelta B leafRouter hleaf root hrootLeaf
      hclusterDisjoint hband hcap heta with
    ⟨previous, ⟨family⟩⟩
  have hrootDisjoint :
      Disjoint (cluster root)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r))) := by
    rw [Finset.disjoint_left]
    intro v hvRoot hvSelected
    rcases
        ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mp
          hvSelected with
      ⟨r, hvLeaf⟩
    exact Finset.disjoint_left.mp
      (hclusterDisjoint (hrootLeaf r)) hvRoot hvLeaf
  exact
    claim514_claim515_of_directSelectedSupportPrefixes
      S family hrootDisjoint hdegree hc hquotaPos hquota hcapacity

/-- Claims 5.14 and 5.15 with the root-side target narrowed to the actual
interface of the root router.  This is the form consumed by the subsequent
Corollary 2.12 extraction. -/
theorem claim514_claim515_of_supportTree_leafFamily_interfaceRoot
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {Delta width cap routerDen m eta quota : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m → Fin n)
    (hleaf : ∀ r, DegreeEquals T (leafRouter r) 1)
    (root : Fin n)
    (hrootLeaf : ∀ r, root ≠ leafRouter r)
    (hclusterDisjoint :
      ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      ∀ r,
        1 + (T.dist root (leafRouter r) - 1) * (routerDen + 1) ≤ eta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G (fun r => cluster (leafRouter r)))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota)
          (ChekuriChuzhoySection5Clustering.interfaceVertices
            G (cluster root))),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  rcases exists_directSelectedSupportPrefixFamily_of_leafFamily_bounded
      S T hT hload hdegree hDelta B leafRouter hleaf root hrootLeaf
      hclusterDisjoint hband hcap heta with
    ⟨previous, ⟨family⟩⟩
  have hrootInterfaceDisjoint :
      Disjoint
        (ChekuriChuzhoySection5Clustering.interfaceVertices
          G (cluster root))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r))) := by
    rw [Finset.disjoint_left]
    intro v hvRoot hvSelected
    rcases
        ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mp
          hvSelected with
      ⟨r, hvLeaf⟩
    exact Finset.disjoint_left.mp
      (hclusterDisjoint (hrootLeaf r))
      (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
        G (cluster root) hvRoot)
      hvLeaf
  exact
    claim514_claim515_of_directSelectedSupportPrefixes_to_rootTarget
      S family
      (fun r => (family r).sourceBoundary_subset_interfaceRoot)
      hrootInterfaceDisjoint hdegree hc hquotaPos hquota hcapacity

end ChekuriChuzhoySection5Phase1Bundle
end SimpleGraph

end Lax17Proofs
