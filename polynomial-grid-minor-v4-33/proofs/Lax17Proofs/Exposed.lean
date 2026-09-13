import Lax17.EdgeMenger
import Lax17.CutMatchingTheorem
import Lax17.CrossbarOrPseudoGrid
import Lax17.CrossbarStitching
import Lax17.ExpanderGrid
import Lax17.ExponentTenCrossbarDichotomy
import Lax17.HairyPathOfSetsFromTreewidth
import Lax17.HindOellermann
import Lax17.LocalRoutingOrGrid
import Lax17.LowDegreeWellLinkedCore
import Lax17.Mader
import Lax17.NodeWellLinkedSetFromTreewidth
import Lax17.ParallelClusterSplitting
import Lax17.SinghLau
import Lax17.SmallLinkedSubsets
import Lax17.StrongPathExtraction
import Lax17.StrongPathOfSetsContainsGrid
import Lax17.StrongPathOfSetsFromTreewidth
import Lax17.StrongTreeOfSetsConstruction
import Lax17.TerminalElementMenger
import Lax17.TreewidthSparsifier
import Lax17.TreewidthMinorMonotonicity
import Lax17.VertexMenger
import Lax17.WellLinkednessBoosting
import Lax17Proofs.Public
import Lax17Proofs.Source.ChekuriChuzhoyWP6Complete
import Lax17Proofs.Source.ChekuriChuzhoyTheoremA2Inputs
import Lax17Proofs.Source.ChekuriChuzhoyStitchedRows
import Lax17Proofs.Source.EdgeMenger
import Lax17Proofs.Source.HairyPathOfSetsTheorem
import Lax17Proofs.Source.HairyCrossbarGridExpander
import Lax17Proofs.Source.HindOellermann
import Lax17Proofs.Source.GenericCutMatchingBudget
import Lax17Proofs.Source.Menger
import Lax17Proofs.Source.MaderTheorem
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.ReedNodeWellLinkedOracle
import Lax17Proofs.Source.SinghLauRounding
import Lax17Proofs.Source.Paths
import Lax17Proofs.Source.Theorem214Nonconstructive
import Lax17Proofs.Source.TreeOfSets
import Lax17Proofs.Source.TreewidthSparsifierTheorem11
import Lax17Proofs.Source.TreewidthSparsifierTheorem51
import Lax17Proofs.Source.TreewidthMinor
import Lax17Proofs.Source.Theorem41
import Lax17Proofs.Source.Section4Complete

/-!
# Public intermediate bridges

Only bridges whose proposition is stated directly in the public vocabulary
live here.  Source-native proof endpoints carry their `conclusion` metadata at
the declaration that actually proves them.
-/

namespace Lax17Proofs

universe u v

namespace Bridge

/-- Repackage an internal path in the public path vocabulary. -/
def pathToPublic {V : Type u} {G : SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    Lax17.Paths.Path G where
  source := P.source
  target := P.target
  walk := P.walk
  simple := P.isPath

/-- Repackage a public path in the internal proof vocabulary. -/
def pathToSource {V : Type u} {G : SimpleGraph V}
    (P : Lax17.Paths.Path G) :
    Lax17Proofs.SimpleGraph.GraphPath G where
  source := P.source
  target := P.target
  walk := P.walk
  isPath := P.simple

@[simp] theorem pathToPublic_vertices {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (pathToPublic P).vertices = P.vertexSet :=
  rfl

@[simp] theorem pathToPublic_edges {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (pathToPublic P).edges = P.edgeSet :=
  rfl

@[simp] theorem pathToSource_vertexSet {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (P : Lax17.Paths.Path G) :
    (pathToSource P).vertexSet = P.vertices :=
  rfl

@[simp] theorem pathToSource_edgeSet {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (P : Lax17.Paths.Path G) :
    (pathToSource P).edgeSet = P.edges :=
  rfl

/-- Reindex and orient an internal node-disjoint packing as a public
fixed-cardinality linkage. -/
noncomputable def pathPackingToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V}
    (P : Lax17Proofs.SimpleGraph.PathPacking G A B) (k : ℕ)
    (hcard : P.card = k) :
    Lax17.Paths.VertexLinkage G A B k := by
  let e : Fin k ≃ P.Index :=
    Fintype.equivOfCardEq (by
      simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using hcard.symm)
  exact {
    path := fun i =>
      pathToPublic ((P.path (e i)).orient (P.connects (e i)))
    connects := fun i =>
      ⟨Lax17Proofs.SimpleGraph.GraphPath.orient_source_mem
          (P.path (e i)) (P.connects (e i)),
        Lax17Proofs.SimpleGraph.GraphPath.orient_target_mem
          (P.path (e i)) (P.connects (e i))⟩
    vertex_disjoint := by
      intro i j hij
      have hne : e i ≠ e j := fun h => hij (e.injective h)
      simpa [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
        P.node_disjoint hne
  }

/-- Internal avoidance of a set is preserved by the reindexing and orientation
used to make a public linkage. -/
theorem pathPackingToPublic_internallyAvoids
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B C : Finset V}
    (P : Lax17Proofs.SimpleGraph.PathPacking G A B) (k : ℕ)
    (hcard : P.card = k)
    (havoid : P.InternallyDisjointFromSet C)
    (i : Fin k) :
    ((pathPackingToPublic P k hcard).path i).InternallyAvoids C := by
  let e : Fin k ≃ P.Index :=
    Fintype.equivOfCardEq (by
      simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using hcard.symm)
  intro v hv hC
  have hendpoint :
      ((P.path (e i)).orient (P.connects (e i))).IsEndpoint v :=
    (Lax17Proofs.SimpleGraph.GraphPath.orient_isEndpoint
      (P.path (e i)) (P.connects (e i))).2
        (havoid (e i) (by simpa [pathPackingToPublic, e] using hv) hC)
  simpa [pathPackingToPublic, e, Lax17.Paths.Path.InternallyAvoids,
    Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint] using hendpoint

/-- Pairwise source bridges survive the finite reindexing used by the public
linkage. -/
theorem pathPackingToPublic_hasPairwiseBridgesIn
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B C : Finset V}
    (P : Lax17Proofs.SimpleGraph.PathPacking G A B) (k : ℕ)
    (hcard : P.card = k)
    (hbridges : P.HasPairwiseBridgesIn C) :
    (pathPackingToPublic P k hcard).HasPairwiseBridgesIn C := by
  let e : Fin k ≃ P.Index :=
    Fintype.equivOfCardEq (by
      simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using hcard.symm)
  intro i j hij
  have heij : e i ≠ e j := fun h => hij (e.injective h)
  rcases hbridges heij with ⟨β, hβstay⟩
  refine ⟨{
    path := pathToPublic β.orientedPath
    source_on_first := by
      simpa [pathPackingToPublic, e] using
        β.orientedPath_source_mem_left
    target_on_second := by
      simpa [pathPackingToPublic, e] using
        β.orientedPath_target_mem_right
    internally_avoids_rows := ?_ }, ?_⟩
  · intro r v hv hrow
    have hvSource :
        v ∈ β.orientedPath.vertexSet := by
      simpa using hv
    have hrowSource :
        v ∈ (P.path (e r)).vertexSet := by
      simpa [pathPackingToPublic, e] using hrow
    have hpacking : v ∈ P.vertexSet :=
      (P.mem_vertexSet).2 ⟨e r, hrowSource⟩
    have hendpoint :=
      β.orientedPath_internallyDisjoint hvSource hpacking
    simpa [Lax17.Paths.Path.InternallyAvoids,
      Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint] using hendpoint
  · simpa [Lax17.Paths.Path.StaysIn] using hβstay

/-- Reindex and orient an internal edge-disjoint packing as a public
fixed-cardinality linkage. -/
noncomputable def edgePathPackingToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V}
    (P : Lax17Proofs.SimpleGraph.EdgePathPacking G A B) (k : ℕ)
    (hcard : P.card = k) :
    Lax17.Paths.EdgeLinkage G A B k := by
  let e : Fin k ≃ P.Index :=
    Fintype.equivOfCardEq (by
      simpa [Lax17Proofs.SimpleGraph.EdgePathPacking.card] using hcard.symm)
  exact {
    path := fun i =>
      pathToPublic ((P.path (e i)).orient (P.connects (e i)))
    connects := fun i =>
      ⟨Lax17Proofs.SimpleGraph.GraphPath.orient_source_mem
          (P.path (e i)) (P.connects (e i)),
        Lax17Proofs.SimpleGraph.GraphPath.orient_target_mem
          (P.path (e i)) (P.connects (e i))⟩
    edge_disjoint := by
      intro i j hij
      have hne : e i ≠ e j := fun h => hij (e.injective h)
      simpa [Lax17Proofs.SimpleGraph.GraphPath.EdgeDisjoint] using
        P.edge_disjoint hne
  }

/-- Regard a public vertex linkage as an internal finite path packing. -/
def vertexLinkageToSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} {k : ℕ}
    (P : Lax17.Paths.VertexLinkage G A B k) :
    Lax17Proofs.SimpleGraph.PathPacking G A B where
  Index := Fin k
  path i := pathToSource (P.path i)
  connects i := Or.inl (P.connects i)
  node_disjoint := by
    intro i j hij
    simpa [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
      P.vertex_disjoint hij

/-- Regard a public edge linkage as an internal finite edge-path packing. -/
def edgeLinkageToSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} {k : ℕ}
    (P : Lax17.Paths.EdgeLinkage G A B k) :
    Lax17Proofs.SimpleGraph.EdgePathPacking G A B where
  Index := Fin k
  path i := pathToSource (P.path i)
  connects i := Or.inl (P.connects i)
  edge_disjoint := by
    intro i j hij
    simpa [Lax17Proofs.SimpleGraph.GraphPath.EdgeDisjoint] using
      P.edge_disjoint hij

@[simp] theorem vertexLinkageToSource_card
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} {k : ℕ}
    (P : Lax17.Paths.VertexLinkage G A B k) :
    (vertexLinkageToSource P).card = k := by
  exact Fintype.card_fin k

/-- Public containment of every linkage path becomes containment of the
corresponding internal packing. -/
theorem vertexLinkageToSource_staysIn
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B C : Finset V} {k : ℕ}
    (P : Lax17.Paths.VertexLinkage G A B k)
    (hstay : ∀ i : Fin k, (P.path i).StaysIn C) :
    (vertexLinkageToSource P).StaysIn C := by
  intro i
  simpa [vertexLinkageToSource, pathToSource,
    Lax17.Paths.Path.StaysIn] using hstay i

/-- Public internal avoidance becomes internal avoidance for the corresponding
finite path packing. -/
theorem vertexLinkageToSource_internallyDisjoint
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B C : Finset V} {k : ℕ}
    (P : Lax17.Paths.VertexLinkage G A B k)
    (havoid : ∀ i : Fin k, (P.path i).InternallyAvoids C) :
    (vertexLinkageToSource P).InternallyDisjointFromSet C := by
  intro i v hv hC
  simpa [vertexLinkageToSource, pathToSource,
    Lax17.Paths.Path.InternallyAvoids,
    Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint] using
      havoid i v hv hC

/-- Public pairwise bridges give pairwise bridges for the corresponding
internal packing. -/
theorem vertexLinkageToSource_hasPairwiseBridgesIn
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B C : Finset V} {k : ℕ}
    (P : Lax17.Paths.VertexLinkage G A B k)
    (hbridges : P.HasPairwiseBridgesIn C) :
    (vertexLinkageToSource P).HasPairwiseBridgesIn C := by
  intro i j hij
  rcases hbridges hij with ⟨β, hβstay⟩
  let R := pathToSource β.path
  let βsource :
      (vertexLinkageToSource P).BridgeBetween i j :=
    Lax17Proofs.SimpleGraph.PathPacking.BridgeBetween.of_orientedPath
      (vertexLinkageToSource P) R
        (by
          simpa [R, vertexLinkageToSource, pathToSource] using
            β.source_on_first)
        (by
          simpa [R, vertexLinkageToSource, pathToSource] using
            β.target_on_second)
        (by
          intro v hv hpacking
          rcases
              ((vertexLinkageToSource P).mem_vertexSet).mp hpacking with
            ⟨r, hr⟩
          have hendpoint :=
            β.internally_avoids_rows r v
              (by simpa [R, pathToSource] using hv)
              (by simpa [vertexLinkageToSource, pathToSource] using hr)
          simpa [R, pathToSource,
            Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint] using hendpoint)
  refine ⟨βsource, ?_⟩
  simpa [βsource, R, pathToSource,
    Lax17.Paths.Path.StaysIn] using hβstay

@[simp] theorem edgeLinkageToSource_card
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} {k : ℕ}
    (P : Lax17.Paths.EdgeLinkage G A B k) :
    (edgeLinkageToSource P).card = k := by
  exact Fintype.card_fin k

/-- A fixed-cardinality public linkage using every vertex of two terminal
sets becomes the oriented perfect packing used internally. -/
noncomputable def vertexLinkageToPerfectSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} {k : ℕ}
    (P : Lax17.Paths.VertexLinkage G A B k)
    (hA : A.card = k) (hB : B.card = k) :
    Lax17Proofs.SimpleGraph.PerfectPathPacking G A B :=
  (vertexLinkageToSource P).toPerfectOfCardEq
    (by simpa [hA]) (by simpa [hB])

@[simp] theorem vertexLinkageToPerfectSource_path_vertexSet
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} {k : ℕ}
    (P : Lax17.Paths.VertexLinkage G A B k)
    (hA : A.card = k) (hB : B.card = k) (i : Fin k) :
    ((vertexLinkageToPerfectSource P hA hB).path i).vertexSet =
      (P.path i).vertices := by
  change
    (((vertexLinkageToSource P).orient.path i).vertexSet =
      (P.path i).vertices)
  rw [Lax17Proofs.SimpleGraph.PathPacking.orient_path_vertexSet]
  rfl

/-- Internal and public node-well-linkedness are equivalent. -/
theorem nodeWellLinkedIn_iff
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    (C X : Finset V) :
    Lax17Proofs.SimpleGraph.NodeWellLinkedIn G C X ↔
      Lax17.Linkedness.NodeWellLinkedIn G C X := by
  constructor
  · rintro ⟨hXC, hlinked⟩
    refine ⟨hXC, ?_⟩
    intro A B hA hB hAB
    rcases hlinked hA hB hAB with ⟨P, hcard, hstay⟩
    refine ⟨pathPackingToPublic P _ hcard, ?_⟩
    intro i
    change ((P.path _).orient _).vertexSet ⊆ C
    simpa using hstay _
  · rintro ⟨hXC, hlinked⟩
    refine ⟨hXC, ?_⟩
    intro A B hA hB hAB
    rcases hlinked hA hB hAB with ⟨P, hstay⟩
    refine ⟨vertexLinkageToSource P, by simp, ?_⟩
    intro i
    simpa [vertexLinkageToSource] using hstay i

/-- Internal and public node-linkedness are equivalent. -/
theorem nodeLinkedIn_iff
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    (C A B : Finset V) :
    Lax17Proofs.SimpleGraph.NodeLinkedIn G C A B ↔
      Lax17.Linkedness.NodeLinkedIn G C A B := by
  constructor
  · rintro ⟨hAC, hBC, hAB, hlinked⟩
    refine ⟨hAC, hBC, hAB, ?_⟩
    intro A' B' hA hB
    rcases hlinked hA hB with ⟨P, hcard, hstay⟩
    refine ⟨pathPackingToPublic P _ hcard, ?_⟩
    intro i
    change ((P.path _).orient _).vertexSet ⊆ C
    simpa using hstay _
  · rintro ⟨hAC, hBC, hAB, hlinked⟩
    refine ⟨hAC, hBC, hAB, ?_⟩
    intro A' B' hA hB
    rcases hlinked hA hB with ⟨P, hstay⟩
    refine ⟨vertexLinkageToSource P, by simp, ?_⟩
    intro i
    simpa [vertexLinkageToSource] using hstay i

/-- Internal and public edge-well-linkedness are equivalent. -/
theorem edgeWellLinkedIn_iff
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    (C X : Finset V) :
    Lax17Proofs.SimpleGraph.EdgeWellLinkedIn G C X ↔
      Lax17.Linkedness.EdgeWellLinkedIn G C X := by
  constructor
  · rintro ⟨hXC, hlinked⟩
    refine ⟨hXC, ?_⟩
    intro A B hA hB hAB
    rcases hlinked hA hB hAB with ⟨P, hcard, hstay⟩
    refine ⟨edgePathPackingToPublic P _ hcard, ?_⟩
    intro i
    change ((P.path _).orient _).vertexSet ⊆ C
    simpa using hstay _
  · rintro ⟨hXC, hlinked⟩
    refine ⟨hXC, ?_⟩
    intro A B hA hB hAB
    rcases hlinked hA hB hAB with ⟨P, hstay⟩
    refine ⟨edgeLinkageToSource P, by simp, ?_⟩
    intro i
    simpa [edgeLinkageToSource] using hstay i

/-- Translate the clean public strong path-of-sets structure to the structure
used by the detailed proof. -/
noncomputable def strongPathOfSetsToSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {ℓ w : ℕ}
    (P : Lax17.PathOfSets.StrongSystem G ℓ w) :
    Lax17Proofs.SimpleGraph.StrongPathOfSetsSystem G ℓ w where
  toPathOfSetsSystem :=
    { length_pos := P.length_pos
      width_pos := P.width_pos
      cluster := P.cluster
      cluster_connected := P.cluster_connected
      cluster_disjoint := P.cluster_disjoint
      left := P.left
      right := P.right
      left_subset_cluster := P.left_subset
      right_subset_cluster := P.right_subset
      left_right_disjoint := P.interfaces_disjoint
      left_card := P.left_card
      right_card := P.right_card
      connector := fun i hi =>
        vertexLinkageToPerfectSource (P.connector i hi)
          (P.right_card i) (P.left_card ⟨i.1 + 1, hi⟩)
      connector_card := by
        intro i hi
        exact Fintype.card_fin w
      connector_internally_disjoint_clusters := by
        intro i hi j a
        have hst := (P.connector i hi).connects a
        change
          ((vertexLinkageToSource (P.connector i hi)).path a).source ∈
              P.right i ∧
            ((vertexLinkageToSource (P.connector i hi)).path a).target ∈
              P.left ⟨i.1 + 1, hi⟩ at hst
        simpa [vertexLinkageToPerfectSource,
          Lax17Proofs.SimpleGraph.PathPacking.toPerfectOfCardEq,
          Lax17Proofs.SimpleGraph.PathPacking.orient,
          Lax17Proofs.SimpleGraph.GraphPath.orient,
          hst,
          Lax17Proofs.SimpleGraph.GraphPath.InternallyDisjointFromSet,
          Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint,
          Lax17.Paths.Path.InternallyAvoids] using
            P.connector_avoids_clusters i hi j a
      connector_mutually_nodeDisjoint := by
        intro i j hi hj hij a b
        simpa [vertexLinkageToPerfectSource,
          Lax17Proofs.SimpleGraph.PathPacking.toPerfectOfCardEq,
          Lax17Proofs.SimpleGraph.PathPacking.orient,
          Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
            P.connectors_disjoint hi hj hij a b }
  left_nodeWellLinked i :=
    (nodeWellLinkedIn_iff G (P.cluster i) (P.left i)).mpr
      (P.left_well_linked i)
  right_nodeWellLinked i :=
    (nodeWellLinkedIn_iff G (P.cluster i) (P.right i)).mpr
      (P.right_well_linked i)
  left_right_nodeLinked i :=
    (nodeLinkedIn_iff G (P.cluster i) (P.left i) (P.right i)).mpr
      (P.interfaces_linked i)

/-- Translate the detailed strong path-of-sets structure back to the clean
public structure. -/
noncomputable def strongPathOfSetsToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {ℓ w : ℕ}
    (P : Lax17Proofs.SimpleGraph.StrongPathOfSetsSystem G ℓ w) :
    Lax17.PathOfSets.StrongSystem G ℓ w where
  toSystem :=
    { length_pos := P.length_pos
      width_pos := P.width_pos
      cluster := P.cluster
      cluster_connected := P.cluster_connected
      cluster_disjoint := P.cluster_disjoint
      left := P.left
      right := P.right
      left_subset := P.left_subset_cluster
      right_subset := P.right_subset_cluster
      interfaces_disjoint := P.left_right_disjoint
      left_card := P.left_card
      right_card := P.right_card
      connector := fun i hi =>
        pathPackingToPublic (P.connector i hi).toPathPacking w
          (P.connector_card i hi)
      connector_avoids_clusters := by
        intro i hi j a
        exact pathPackingToPublic_internallyAvoids
          (P.connector i hi).toPathPacking w (P.connector_card i hi)
          (P.connector_internally_disjoint_clusters i hi j) a
      connectors_disjoint := by
        intro i j hi hj hij a b
        simpa [pathPackingToPublic,
          Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
            P.connector_mutually_nodeDisjoint hi hj hij
              ((Fintype.equivOfCardEq (by
                simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
                  (P.connector_card i hi).symm)) a)
              ((Fintype.equivOfCardEq (by
                simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
                  (P.connector_card j hj).symm)) b) }
  left_well_linked i :=
    (nodeWellLinkedIn_iff G (P.cluster i) (P.left i)).mp
      (P.left_nodeWellLinked i)
  right_well_linked i :=
    (nodeWellLinkedIn_iff G (P.cluster i) (P.right i)).mp
      (P.right_nodeWellLinked i)
  interfaces_linked i :=
    (nodeLinkedIn_iff G (P.cluster i) (P.left i) (P.right i)).mp
      (P.left_right_nodeLinked i)

/-- Translate the clean public strong tree-of-sets structure to the detailed
structure used by the extraction proof. -/
noncomputable def strongTreeOfSetsToSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {m w : ℕ}
    (T : Lax17.TreeOfSets.StrongSystem G m w) :
    Lax17Proofs.SimpleGraph.StrongTreeOfSetsSystem G m w where
  toTreeOfSetsSystem :=
    { clusterCount_pos := T.clusterCount_pos
      width_pos := T.width_pos
      metaTree := T.metaTree
      meta_isTree := T.meta_isTree
      meta_maxDegree_three := T.meta_subcubic
      cluster := T.cluster
      cluster_connected := T.cluster_connected
      cluster_disjoint := T.cluster_disjoint
      interface := T.interface
      interface_subset_cluster := T.interface_subset
      interface_card := T.interface_card
      interface_disjoint := T.incident_interfaces_disjoint
      connector := fun i j hij =>
        vertexLinkageToPerfectSource (T.connector i j hij)
          (T.interface_card i j hij)
          (T.interface_card j i (T.metaTree.symm hij))
      connector_card := by
        intro i j hij
        exact Fintype.card_fin w
      connector_internally_disjoint_clusters := by
        intro i j hij r a
        have hst := (T.connector i j hij).connects a
        change
          ((vertexLinkageToSource (T.connector i j hij)).path a).source ∈
              T.interface i j hij ∧
            ((vertexLinkageToSource (T.connector i j hij)).path a).target ∈
              T.interface j i (T.metaTree.symm hij) at hst
        simpa [vertexLinkageToPerfectSource,
          Lax17Proofs.SimpleGraph.PathPacking.toPerfectOfCardEq,
          Lax17Proofs.SimpleGraph.PathPacking.orient,
          Lax17Proofs.SimpleGraph.GraphPath.orient, hst,
          Lax17Proofs.SimpleGraph.GraphPath.InternallyDisjointFromSet,
          Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint,
          Lax17.Paths.Path.InternallyAvoids] using
            T.connector_avoids_clusters i j hij r a
      connector_mutually_nodeDisjoint := by
        intro i j hij p q hpq hedge a b
        simpa [vertexLinkageToPerfectSource,
          Lax17Proofs.SimpleGraph.PathPacking.toPerfectOfCardEq,
          Lax17Proofs.SimpleGraph.PathPacking.orient,
          Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
            T.connectors_disjoint i j hij p q hpq hedge a b }
  interface_nodeWellLinked i j hij :=
    (nodeWellLinkedIn_iff G (T.cluster i) (T.interface i j hij)).mpr
      (T.interface_well_linked i j hij)
  interface_pair_nodeLinked hij hik hjk :=
    (nodeLinkedIn_iff G _ _ _).mpr
      (T.incident_interfaces_linked hij hik hjk)

/-- Translate the detailed strong tree-of-sets structure back to the clean
public structure. -/
noncomputable def strongTreeOfSetsToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {m w : ℕ}
    (T : Lax17Proofs.SimpleGraph.StrongTreeOfSetsSystem G m w) :
    Lax17.TreeOfSets.StrongSystem G m w where
  toSystem :=
    { clusterCount_pos := T.clusterCount_pos
      width_pos := T.width_pos
      metaTree := T.metaTree
      meta_isTree := T.meta_isTree
      meta_subcubic := T.meta_maxDegree_three
      cluster := T.cluster
      cluster_connected := T.cluster_connected
      cluster_disjoint := T.cluster_disjoint
      interface := T.interface
      interface_subset := T.interface_subset_cluster
      interface_card := T.interface_card
      incident_interfaces_disjoint := T.interface_disjoint
      connector := fun i j hij =>
        pathPackingToPublic (T.connector i j hij).toPathPacking w
          (T.connector_card i j hij)
      connector_avoids_clusters := by
        intro i j hij r a
        exact pathPackingToPublic_internallyAvoids
          (T.connector i j hij).toPathPacking w
          (T.connector_card i j hij)
          (T.connector_internally_disjoint_cluster i j hij r) a
      connectors_disjoint := by
        intro i j hij p q hpq hedge a b
        simpa [pathPackingToPublic,
          Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
            T.connector_mutually_nodeDisjoint i j hij p q hpq hedge
              ((Fintype.equivOfCardEq (by
                simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
                  (T.connector_card i j hij).symm)) a)
              ((Fintype.equivOfCardEq (by
                simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
                  (T.connector_card p q hpq).symm)) b) }
  interface_well_linked i j hij :=
    (nodeWellLinkedIn_iff G (T.cluster i) (T.interface i j hij)).mp
      (T.interface_nodeWellLinked i j hij)
  incident_interfaces_linked hij hik hjk :=
    (nodeLinkedIn_iff G _ _ _).mp
      (T.interface_pair_nodeLinked hij hik hjk)

/-- Forget the additional source-side invariants of a hairy path-of-sets
system while retaining its clean public data. -/
noncomputable def hairyPathOfSetsToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {ℓ w : ℕ}
    (H : Lax17Proofs.SimpleGraph.HairyPathOfSetsSystem G ℓ w) :
    Lax17.PathOfSets.HairySystem G ℓ w where
  base := strongPathOfSetsToPublic H.base
  hairCluster := H.hairCluster
  hair_connected := H.hairCluster_connected
  hair_disjoint := H.hairCluster_disjoint
  hair_disjoint_base := H.hairCluster_disjoint_base
  hair_disjoint_connectors := by
    intro i j hj a
    rw [Finset.disjoint_left]
    intro v hvHair hvPath
    apply
      (Finset.disjoint_left.mp
        (H.hairCluster_disjoint_baseConnectors i j hj)) hvHair
    apply
      (H.base.connector j hj).toPathPacking.mem_vertexSet.mpr
    let e : Fin w ≃ (H.base.connector j hj).Index :=
      Fintype.equivOfCardEq (by
        simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
          (H.base.connector_card j hj).symm)
    exact
      ⟨e a, by
        simpa [Lax17Proofs.Bridge.strongPathOfSetsToPublic,
          pathPackingToPublic, e] using hvPath⟩
  baseEndpoint := H.x
  hairEndpoint := H.y
  baseEndpoint_subset := H.x_subset_cluster
  hairEndpoint_subset := H.y_subset_hairCluster
  baseEndpoint_card := H.x_card
  hairEndpoint_card := H.y_card
  baseEndpoint_avoids_interfaces := H.x_disjoint_nails
  hairEndpoint_well_linked i :=
    (nodeWellLinkedIn_iff G (H.hairCluster i) (H.y i)).mp
      (H.y_nodeWellLinked i)
  baseEndpoint_linked i :=
    (nodeLinkedIn_iff G (H.base.cluster i) (H.base.left i) (H.x i)).mp
      (H.left_x_nodeLinked i)
  hairLinkage i :=
    pathPackingToPublic (H.hairConnector i).toPathPacking w
      (H.hairConnector_card i)
  hair_linkages_disjoint := by
    intro i j hij a b
    simpa [pathPackingToPublic,
      Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
        H.hairConnector_mutually_nodeDisjoint hij
          ((Fintype.equivOfCardEq (by
            simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
              (H.hairConnector_card i).symm)) a)
          ((Fintype.equivOfCardEq (by
            simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
              (H.hairConnector_card j).symm)) b)
  hair_linkages_disjoint_connectors := by
    intro i j hj a b
    simpa [strongPathOfSetsToPublic, pathPackingToPublic,
      Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
        H.hairConnector_disjoint_baseConnectors i j hj
          ((Fintype.equivOfCardEq (by
            simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
              (H.hairConnector_card i).symm)) a)
          ((Fintype.equivOfCardEq (by
            simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
              (H.base.connector_card j hj).symm)) b)
  hair_linkages_avoid_base := by
    intro i j a
    exact pathPackingToPublic_internallyAvoids
      (H.hairConnector i).toPathPacking w (H.hairConnector_card i)
      (H.hairConnector_internally_disjoint_baseClusters i j) a
  hair_linkages_avoid_hair := by
    intro i j a
    exact pathPackingToPublic_internallyAvoids
      (H.hairConnector i).toPathPacking w (H.hairConnector_card i)
      (H.hairConnector_internally_disjoint_hairClusters i j) a

/-- Translate the detailed Appendix A.3 cluster split to its clean public
record. -/
noncomputable def hairyClusterSplitToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {C A B : Finset V} {w : ℕ}
    (D :
      Lax17Proofs.SimpleGraph.HairyPathOfSetsTheorem.AppendixA3ClusterSplitData
        G C A B w) :
    Lax17.PathOfSets.HairyClusterSplit G C A B w where
  baseCluster := D.baseCluster
  hairCluster := D.hairCluster
  left := D.left
  right := D.right
  baseEndpoint := D.x
  hairEndpoint := D.y
  base_subset := D.base_subset_cluster
  hair_subset := D.hair_subset_cluster
  base_connected := D.base_connected
  hair_connected := D.hair_connected
  clusters_disjoint := D.hair_disjoint_base.symm
  left_subset_base := D.left_subset_base
  right_subset_base := D.right_subset_base
  baseEndpoint_subset := D.x_subset_base
  hairEndpoint_subset := D.y_subset_hair
  left_subset_original := D.left_subset_old_left
  right_subset_original := D.right_subset_old_right
  left_card := D.left_card
  right_card := D.right_card
  baseEndpoint_card := D.x_card
  hairEndpoint_card := D.y_card
  interfaces_disjoint := D.left_right_disjoint
  baseEndpoint_disjoint_interfaces := D.x_disjoint_nails
  left_well_linked :=
    (nodeWellLinkedIn_iff G D.baseCluster D.left).mp
      D.left_nodeWellLinked
  right_well_linked :=
    (nodeWellLinkedIn_iff G D.baseCluster D.right).mp
      D.right_nodeWellLinked
  interfaces_linked :=
    (nodeLinkedIn_iff G D.baseCluster D.left D.right).mp
      D.left_right_nodeLinked
  left_baseEndpoint_linked :=
    (nodeLinkedIn_iff G D.baseCluster D.left D.x).mp
      D.left_x_nodeLinked
  hairEndpoint_well_linked :=
    (nodeWellLinkedIn_iff G D.hairCluster D.y).mp
      D.y_nodeWellLinked
  hairLinkage :=
    pathPackingToPublic D.hairConnector.toPathPacking w
      D.hairConnector_card
  hairLinkage_stays_in_cluster := by
    intro i
    simpa [pathPackingToPublic, Lax17.Paths.Path.StaysIn] using
      D.hairConnector_staysIn_cluster
        (Fintype.equivOfCardEq (by
          simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
            D.hairConnector_card.symm) i)
  hairLinkage_avoids_base := by
    intro i
    exact pathPackingToPublic_internallyAvoids
      D.hairConnector.toPathPacking w D.hairConnector_card
      D.hairConnector_internally_disjoint_base i
  hairLinkage_avoids_hair := by
    intro i
    exact pathPackingToPublic_internallyAvoids
      D.hairConnector.toPathPacking w D.hairConnector_card
      D.hairConnector_internally_disjoint_hair i

/-- Translate the clean public Appendix A.3 split back to the detailed local
split record consumed by Appendix A.4. -/
noncomputable def hairyClusterSplitToSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {C A B : Finset V} {w : ℕ}
    (D : Lax17.PathOfSets.HairyClusterSplit G C A B w) :
    Lax17Proofs.SimpleGraph.HairyPathOfSetsTheorem.AppendixA3ClusterSplitData
      G C A B w where
  baseCluster := D.baseCluster
  hairCluster := D.hairCluster
  left := D.left
  right := D.right
  x := D.baseEndpoint
  y := D.hairEndpoint
  base_subset_cluster := D.base_subset
  hair_subset_cluster := D.hair_subset
  base_connected := D.base_connected
  hair_connected := D.hair_connected
  hair_disjoint_base := D.clusters_disjoint.symm
  left_subset_base := D.left_subset_base
  right_subset_base := D.right_subset_base
  x_subset_base := D.baseEndpoint_subset
  y_subset_hair := D.hairEndpoint_subset
  left_subset_old_left := D.left_subset_original
  right_subset_old_right := D.right_subset_original
  left_card := D.left_card
  right_card := D.right_card
  x_card := D.baseEndpoint_card
  y_card := D.hairEndpoint_card
  left_right_disjoint := D.interfaces_disjoint
  x_disjoint_nails := D.baseEndpoint_disjoint_interfaces
  left_nodeWellLinked :=
    (nodeWellLinkedIn_iff G D.baseCluster D.left).mpr D.left_well_linked
  right_nodeWellLinked :=
    (nodeWellLinkedIn_iff G D.baseCluster D.right).mpr D.right_well_linked
  left_right_nodeLinked :=
    (nodeLinkedIn_iff G D.baseCluster D.left D.right).mpr
      D.interfaces_linked
  left_x_nodeLinked :=
    (nodeLinkedIn_iff G D.baseCluster D.left D.baseEndpoint).mpr
      D.left_baseEndpoint_linked
  y_nodeWellLinked :=
    (nodeWellLinkedIn_iff G D.hairCluster D.hairEndpoint).mpr
      D.hairEndpoint_well_linked
  hairConnector :=
    vertexLinkageToPerfectSource D.hairLinkage
      D.baseEndpoint_card D.hairEndpoint_card
  hairConnector_card := by
    exact Fintype.card_fin w
  hairConnector_staysIn_cluster := by
    change
      Lax17Proofs.SimpleGraph.PathPacking.StaysIn
        (vertexLinkageToSource D.hairLinkage).orient C
    exact
      Lax17Proofs.SimpleGraph.PathPacking.orient_staysIn
        (vertexLinkageToSource_staysIn D.hairLinkage
          D.hairLinkage_stays_in_cluster)
  hairConnector_internally_disjoint_base := by
    change
      Lax17Proofs.SimpleGraph.PathPacking.InternallyDisjointFromSet
        (vertexLinkageToSource D.hairLinkage).orient D.baseCluster
    exact
      Lax17Proofs.SimpleGraph.PathPacking.orient_internallyDisjointFromSet
        (vertexLinkageToSource_internallyDisjoint D.hairLinkage
          D.hairLinkage_avoids_base)
  hairConnector_internally_disjoint_hair := by
    change
      Lax17Proofs.SimpleGraph.PathPacking.InternallyDisjointFromSet
        (vertexLinkageToSource D.hairLinkage).orient D.hairCluster
    exact
      Lax17Proofs.SimpleGraph.PathPacking.orient_internallyDisjointFromSet
        (vertexLinkageToSource_internallyDisjoint D.hairLinkage
          D.hairLinkage_avoids_hair)

/-- The two endpoint formulations of “an edge lies inside `S`” agree. -/
theorem pairInside_iff
    {V : Type u} [DecidableEq V] (S : Finset V) (e : Sym2 V) :
    Lax17Proofs.SimpleGraph.SinghLau.PairInside S e ↔
      Lax17.SpanningTreeRounding.PairInside S e := by
  refine Sym2.inductionOn e ?_
  intro x y
  simp [Lax17Proofs.SimpleGraph.SinghLau.PairInside,
    Lax17.SpanningTreeRounding.PairInside, Finset.subset_iff]

/-- The canonical public edge enumeration is the usual graph edge finset. -/
theorem spanningEdges_eq
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Lax17.SpanningTreeRounding.edges G = G.edgeFinset := by
  ext e
  simp [Lax17.SpanningTreeRounding.edges]

/-- The internal-edge finsets used in the public and detailed formulations
are equal. -/
theorem spanningInternalEdges_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    Lax17Proofs.SimpleGraph.SinghLau.internalEdges G S =
      Lax17.SpanningTreeRounding.internalEdges G S := by
  ext e
  simp [Lax17Proofs.SimpleGraph.SinghLau.internalEdges,
    Lax17.SpanningTreeRounding.internalEdges, spanningEdges_eq,
    pairInside_iff]

/-- The incident-edge finsets used in the public and detailed formulations
are equal. -/
theorem spanningIncidentEdges_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    Lax17Proofs.SimpleGraph.SinghLau.incidentEdges G v =
      Lax17.SpanningTreeRounding.incidentEdges G v := by
  ext e
  simp [Lax17Proofs.SimpleGraph.SinghLau.incidentEdges,
    Lax17.SpanningTreeRounding.incidentEdges,
    Lax17.SpanningTreeRounding.edges]

/-- Translate a clean public feasible spanning-tree point to the detailed
Singh--Lau formulation. -/
noncomputable def feasiblePointToSource
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {B : ℕ}
    (x : Lax17.SpanningTreeRounding.FeasiblePoint G B) :
    Lax17Proofs.SimpleGraph.SinghLau.FeasibleBoundedDegreePoint G B where
  weight := x.weight
  nonnegative e he := x.nonnegative e (by
    rwa [spanningEdges_eq])
  total := by
    rw [← spanningEdges_eq]
    exact x.total
  forest S hS := by
    rw [spanningInternalEdges_eq]
    exact x.forest S hS
  degree v := by
    rw [spanningIncidentEdges_eq]
    exact x.degree v

/-- Forget the public namespace wrapper on a finite edge-indexed graph. -/
def edgeIndexedGraphToSource
    {V : Type u} (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V) :
    Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph V where
  Edge := H.Edge
  edgeFintype := H.edgeFintype
  edgeDecidableEq := H.edgeDecidableEq
  left := H.left
  right := H.right
  end_ne := H.end_ne

/-- Add the public namespace wrapper to a detailed edge-indexed graph. -/
def edgeIndexedGraphToPublic
    {V : Type u}
    (H :
      Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph V) :
    Lax17.TerminalConnectivity.EdgeIndexedGraph V where
  Edge := H.Edge
  edgeFintype := H.edgeFintype
  edgeDecidableEq := H.edgeDecidableEq
  left := H.left
  right := H.right
  end_ne := H.end_ne

/-- Public and detailed incidence finsets agree. -/
theorem terminalIncidentEdges_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V) (v : V) :
    (edgeIndexedGraphToSource H).incidentEdges v = H.incidentEdges v := by
  ext e
  rw [
    Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.mem_incidentEdges]
  constructor
  · intro he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩
  · intro he
    exact (Finset.mem_filter.mp he).2

/-- Public and detailed named-edge boundaries agree. -/
theorem terminalBoundary_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V) (S : Finset V) :
    (edgeIndexedGraphToSource H).boundary S = H.boundary S := by
  classical
  ext e
  rw [
    Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.mem_boundary]
  constructor
  · intro he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩
  · intro he
    exact (Finset.mem_filter.mp he).2

/-- Public and detailed available named-edge boundaries agree. -/
theorem terminalAvailableBoundary_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
    (removed side : Finset V) :
    (edgeIndexedGraphToSource H).availableBoundary removed side =
      H.availableBoundary removed side := by
  classical
  ext e
  rw [
    Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.mem_availableBoundary]
  constructor
  · rintro ⟨hcross, hleft, hright⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hleft, hright⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hcross⟩
  · intro he
    have havailable := Finset.mem_filter.mp he
    exact
      ⟨(Finset.mem_filter.mp havailable.1).2,
        havailable.2.1, havailable.2.2⟩

/-- Public and detailed terminal element-connectivity predicates agree. -/
theorem terminalElementConnectedAtLeast_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
    (terminals : Finset V) (k : ℕ) :
    (edgeIndexedGraphToSource H).TerminalElementConnectedAtLeast terminals k ↔
      H.TerminalElementConnectedAtLeast terminals k := by
  rw [
    Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.terminalElementConnectedAtLeast_iff_availableBoundary]
  constructor
  · intro h a ha b hb hab removed side hremoved haSide hbSide hside
    have hk :=
      h ha hb hab removed side hremoved haSide hbSide hside
    rwa [terminalAvailableBoundary_eq] at hk
  · intro h a ha b hb hab removed side hremoved haSide hbSide hside
    have hk :=
      h ha hb hab removed side hremoved haSide hbSide hside
    rwa [terminalAvailableBoundary_eq]

/-- The canonical contraction graph, presented in the public vocabulary. -/
noncomputable def contractionGraphToPublic
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V) (e₀ : H.Edge) :
    Lax17.TerminalConnectivity.EdgeIndexedGraph
      (Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.ContractVertex
        V (H.left e₀) (H.right e₀)) :=
  edgeIndexedGraphToPublic ((edgeIndexedGraphToSource H).contractEdge e₀)

/-- The canonical quotient really contracts precisely the endpoints of `e₀`. -/
noncomputable def canonicalContractionModel
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V) (e₀ : H.Edge) :
    H.IsContraction e₀ (contractionGraphToPublic H e₀)
      (Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.ContractVertex.projection
          (p := H.left e₀) (q := H.right e₀)) where
  vertex_surjective :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.ContractVertex.projection_surjective
  endpoints_identified := by simp
  fibres := by
    intro x y hxy
    rcases
        Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.ContractVertex.eq_or_both_endpoints_of_projection_eq
          hxy with
      h | ⟨hx, hy⟩
    · exact Or.inl h
    · rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (hx.trans hy.symm)
      · exact Or.inr (Or.inl ⟨hx, hy⟩)
      · exact Or.inr (Or.inr ⟨hx, hy⟩)
      · exact Or.inl (hx.trans hy.symm)
  edgeEquiv :=
    { toFun := fun e => ⟨e.1, e.2.2⟩
      invFun := fun e =>
        ⟨e.1, by
          intro he
          apply e.2
          unfold
            Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.SurvivesContraction
          rw [he]
          simp, e.2⟩
      left_inv := by
        intro e
        exact Subtype.ext rfl
      right_inv := by
        intro e
        exact Subtype.ext rfl }
  edge_endpoints := by
    intro e
    exact Or.inl ⟨rfl, rfl⟩

/-- Translate a public split pair to the detailed split-off vocabulary. -/
def splitPairToSource
    {V : Type u} {H : Lax17.TerminalConnectivity.EdgeIndexedGraph V}
    {s : V} (p : H.SplitPair s) :
    (edgeIndexedGraphToSource H).MaderSplitPair s where
  first := p.first
  second := p.second
  edge_ne := p.edge_ne
  firstOther := p.firstOther
  secondOther := p.secondOther
  first_ends := p.first_ends
  second_ends := p.second_ends

/-- Translate a detailed split pair back to the public vocabulary. -/
def splitPairToPublic
    {V : Type u} {H : Lax17.TerminalConnectivity.EdgeIndexedGraph V}
    {s : V} (p : (edgeIndexedGraphToSource H).MaderSplitPair s) :
    H.SplitPair s where
  first := p.first
  second := p.second
  edge_ne := p.edge_ne
  firstOther := p.firstOther
  secondOther := p.secondOther
  first_ends := p.first_ends
  second_ends := p.second_ends

/-- Translating before or after a split gives the same named-edge boundary. -/
theorem maderSplitBoundary_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {H : Lax17.TerminalConnectivity.EdgeIndexedGraph V} {s : V}
    (p : (edgeIndexedGraphToSource H).MaderSplitPair s)
    (S : Finset V) :
    ((edgeIndexedGraphToSource H).maderSplit p).boundary S =
      (edgeIndexedGraphToSource
        (H.splitOff (splitPairToPublic p))).boundary S := by
  ext e
  constructor
  · intro he
    have hcross :=
      (((edgeIndexedGraphToSource H).maderSplit p).mem_boundary S e).mp he
    apply
      ((edgeIndexedGraphToSource
        (H.splitOff (splitPairToPublic p))).mem_boundary S e).mpr
    rcases e with e | e <;>
      simpa [Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.Crosses,
        Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.maderSplit,
        Lax17.TerminalConnectivity.EdgeIndexedGraph.splitOff,
        edgeIndexedGraphToSource, splitPairToPublic] using hcross
  · intro he
    have hcross :=
      ((edgeIndexedGraphToSource
        (H.splitOff (splitPairToPublic p))).mem_boundary S e).mp he
    apply
      (((edgeIndexedGraphToSource H).maderSplit p).mem_boundary S e).mpr
    rcases e with e | e <;>
      simpa [Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.Crosses,
        Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.maderSplit,
        Lax17.TerminalConnectivity.EdgeIndexedGraph.splitOff,
        edgeIndexedGraphToSource, splitPairToPublic] using hcross

/-- Public and detailed local edge-connectivity thresholds agree. -/
theorem pairEdgeConnectedAtLeast_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
    (x y : V) (k : ℕ) :
    (edgeIndexedGraphToSource H).PairwiseEdgeConnectedAtLeast x y k ↔
      H.PairEdgeConnectedAtLeast x y k := by
  constructor
  · intro h S hx hy
    rw [← terminalBoundary_eq]
    exact h S hx hy
  · intro h S hx hy
    rw [terminalBoundary_eq]
    exact h S hx hy

/-- Local edge-connectivity is unchanged by the order in which a split and
the public/source translation are performed. -/
theorem maderSplitPairEdgeConnectedAtLeast_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    {H : Lax17.TerminalConnectivity.EdgeIndexedGraph V} {s : V}
    (p : (edgeIndexedGraphToSource H).MaderSplitPair s)
    (x y : V) (k : ℕ) :
    ((edgeIndexedGraphToSource H).maderSplit p).PairwiseEdgeConnectedAtLeast
        x y k ↔
      (edgeIndexedGraphToSource
        (H.splitOff (splitPairToPublic p))).PairwiseEdgeConnectedAtLeast
          x y k := by
  constructor
  · intro h S hx hy
    rw [← maderSplitBoundary_eq]
    exact h S hx hy
  · intro h S hx hy
    rw [maderSplitBoundary_eq]
    exact h S hx hy

/-- A detailed Mader-admissibility certificate is a public one. -/
theorem maderAdmissibleToPublic
    {V : Type u} [Fintype V] [DecidableEq V]
    {H : Lax17.TerminalConnectivity.EdgeIndexedGraph V} {s : V}
    (p : (edgeIndexedGraphToSource H).MaderSplitPair s)
    (hp : (edgeIndexedGraphToSource H).MaderAdmissible p) :
    H.IsMaderAdmissible (splitPairToPublic p) := by
  intro x y hxs hys hxy k
  rw [← pairEdgeConnectedAtLeast_iff]
  rw [← pairEdgeConnectedAtLeast_iff]
  rw [← maderSplitPairEdgeConnectedAtLeast_iff]
  exact hp x y hxs hys hxy k

/-- Turn a public set-valued minor model of a finite host into the finite
branch-set model used by the proof. -/
noncomputable def minorModelToSource
    {W : Type u} {V : Type v}
    [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : Lax17.Minor.Model H G) :
    Lax17Proofs.SimpleGraph.MinorModel H G where
  branchSet w := (M.branchSet w).toFinite.toFinset
  branch_nonempty w := by
    rcases M.branch_nonempty w with ⟨x, hx⟩
    exact ⟨x, by simpa⟩
  branch_connected w := by
    rw [show
      {x : V | x ∈ (M.branchSet w).toFinite.toFinset} = M.branchSet w by
        ext x
        simp]
    exact M.branch_connected w
  branch_disjoint := by
    intro x y hxy
    rw [Finset.disjoint_left]
    intro z hzx hzy
    exact Set.disjoint_left.1 (M.branch_disjoint hxy)
      (by simpa using hzx) (by simpa using hzy)
  adjacent := by
    intro x y hxy
    rcases M.adjacent hxy with ⟨a, ha, b, hb, hab⟩
    exact ⟨a, by simpa, b, by simpa, hab⟩

/-- Public and internal minor predicates agree for a finite host. -/
theorem isMinorToSource
    {W : Type u} {V : Type v}
    [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (h : Lax17.Minor.IsMinor H G) :
    Lax17Proofs.SimpleGraph.IsMinor H G := by
  rcases h with ⟨M⟩
  exact ⟨minorModelToSource M⟩

/-- A canonical public grid-minor witness is also a grid-minor witness in the
detailed proof vocabulary. -/
theorem containsGridMinorToSource
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {g : ℕ}
    (h : Lax17.GridMinor.ContainsGridMinor G g) :
    Lax17Proofs.SimpleGraph.ContainsGridMinor G g := by
  have hcanonical :
      Lax17Proofs.SimpleGraph.IsMinor
        (Lax17Proofs.SimpleGraph.gridGraph g) G := by
    apply isMinorToSource
    rw [← Lax17Proofs.Bridge.squareGrid_eq_gridGraph]
    exact h
  exact
    ⟨Lax17Proofs.SimpleGraph.GridVertexULift.{u} g,
      inferInstance, inferInstance,
      Lax17Proofs.SimpleGraph.gridGraphULift.{u} g,
      Lax17Proofs.SimpleGraph.gridGraphULift_isGridGraph.{u} g,
      Lax17Proofs.SimpleGraph.IsMinor.of_iso_left
        (Lax17Proofs.SimpleGraph.gridGraphULiftIso.{u} g) hcanonical⟩

/-- Repackage a public balanced separator for the detailed expander theorem. -/
def balancedSeparatorToSource
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B S : Finset V}
    (h : Lax17.Expansion.BalancedSeparator G A B S) :
    Lax17Proofs.SimpleGraph.BalancedSeparator G A B S where
  cover := h.cover
  disjoint_left_right := h.left_right_disjoint
  disjoint_left_separator := h.left_separator_disjoint
  disjoint_right_separator := h.right_separator_disjoint
  left_card_le_right_card := h.left_card_le_right_card
  right_balanced := h.right_balanced
  no_edge_left_right := h.no_edge_left_right

/-- The public and detailed no-small-balanced-separator predicates agree in
the direction needed by Theorem 8.1. -/
theorem noSmallBalancedSeparatorToSource
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ}
    (h : Lax17.Expansion.NoSmallBalancedSeparator G d) :
    Lax17Proofs.SimpleGraph.NoSmallBalancedSeparator G d := by
  intro A B S hseparator
  exact h {
    cover := hseparator.cover
    left_right_disjoint := hseparator.disjoint_left_right
    left_separator_disjoint := hseparator.disjoint_left_separator
    right_separator_disjoint := hseparator.disjoint_right_separator
    left_card_le_right_card := hseparator.left_card_le_right_card
    right_balanced := hseparator.right_balanced
    no_edge_left_right := hseparator.no_edge_left_right }

/-- Forget the internal random-walk view of a cut-matching round while
retaining exactly its bisection and matching. -/
def matchingRoundToPublic
    {V : Type u} [Fintype V] [DecidableEq V]
    (R : Lax17Proofs.SimpleGraph.CutMatchingGame.LazyRound V) :
    Lax17.Expansion.MatchingRound V where
  left := R.cut.left
  right := R.cut.right
  sides_disjoint := R.cut.disjoint
  sides_equipotent := R.cut.card_eq
  sides_cover := R.cut.cover
  partner := R.matching.toEquiv

/-- The public and source edge-boundary finsets agree. -/
theorem pathsEdgeBoundary_eq_section44
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Finset V) :
    Lax17.Paths.edgeBoundary G X Y =
      Lax17Proofs.SimpleGraph.Section44.edgeBoundary G X Y := by
  classical
  ext e
  simp [Lax17.Paths.edgeBoundary,
    Lax17Proofs.SimpleGraph.Section44.edgeBoundary]

/-- The source and public scaled cut definitions have the same mathematical
content. -/
theorem scaledWellLinkedToPublic
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {T : Finset V}
    {numerator denominator : ℕ}
    (h :
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.ScaledWellLinked
        G T numerator denominator) :
    Lax17.Linkedness.ScaledEdgeWellLinked
      G T numerator denominator := by
  rcases h with ⟨hpositive, hratio, hcuts⟩
  refine ⟨hpositive, hratio, ?_⟩
  intro X Y hcover hdisjoint
  rw [pathsEdgeBoundary_eq_section44]
  exact hcuts X Y hcover hdisjoint

/-- Reindex an internal crossbar by its stated width and expose its paths and
attachment vertices in the public vocabulary. -/
noncomputable def crossbarToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B X : Finset V} {width : ℕ}
    (C : Lax17Proofs.SimpleGraph.Crossbar G A B X width) :
    Lax17.Crossbar.System G A B X width := by
  let C' := C.finReindex
  exact {
    mainPath := fun i =>
      pathToPublic ((C'.mainPath i).orient (C'.main_connects i))
    main_connects := by
      intro i
      exact
        ⟨Lax17Proofs.SimpleGraph.GraphPath.orient_source_mem
            (C'.mainPath i) (C'.main_connects i),
          Lax17Proofs.SimpleGraph.GraphPath.orient_target_mem
            (C'.mainPath i) (C'.main_connects i)⟩
    main_disjoint := by
      intro i j hij
      rw [pathToPublic_vertices, pathToPublic_vertices,
        Lax17Proofs.SimpleGraph.GraphPath.orient_vertexSet,
        Lax17Proofs.SimpleGraph.GraphPath.orient_vertexSet]
      exact C'.main_nodeDisjoint hij
    spokePath := fun i => pathToPublic (C'.spokePath i)
    spoke_disjoint := by
      intro i j hij
      rw [pathToPublic_vertices, pathToPublic_vertices]
      exact C'.spoke_nodeDisjoint hij
    attachment := fun i =>
      Classical.choose (C'.spoke_exits_own_main i)
    attachment_on_main := by
      intro i
      let v := Classical.choose (C'.spoke_exits_own_main i)
      have hmeet :=
        (Classical.choose_spec (C'.spoke_exits_own_main i)).2.1
      have hv :
          v ∈ (C'.mainPath i).vertexSet ∩
            (C'.spokePath i).vertexSet := by
        rw [hmeet]
        simp [v]
      change
        v ∈
          (pathToPublic
            ((C'.mainPath i).orient (C'.main_connects i))).vertices
      rw [pathToPublic_vertices,
        Lax17Proofs.SimpleGraph.GraphPath.orient_vertexSet]
      exact (Finset.mem_inter.mp hv).1
    attachment_on_spoke := by
      intro i
      let v := Classical.choose (C'.spoke_exits_own_main i)
      have hmeet :=
        (Classical.choose_spec (C'.spoke_exits_own_main i)).2.1
      have hv :
          v ∈ (C'.mainPath i).vertexSet ∩
            (C'.spokePath i).vertexSet := by
        rw [hmeet]
        simp [v]
      change v ∈ (pathToPublic (C'.spokePath i)).vertices
      rw [pathToPublic_vertices]
      exact (Finset.mem_inter.mp hv).2
    exact_attachment := by
      intro i
      rw [pathToPublic_vertices, pathToPublic_vertices,
        Lax17Proofs.SimpleGraph.GraphPath.orient_vertexSet]
      exact (Classical.choose_spec (C'.spoke_exits_own_main i)).2.1
    exit := fun i =>
      (C'.spokePath i).otherEndpoint
        (Classical.choose (C'.spoke_exits_own_main i))
    attachment_is_endpoint := by
      intro i
      exact (Classical.choose_spec (C'.spoke_exits_own_main i)).1
    exit_is_other_endpoint := by
      intro i
      rfl
    exit_in_X := by
      intro i
      exact (Classical.choose_spec (C'.spoke_exits_own_main i)).2.2.1
    exit_off_main := by
      intro i
      change
        (C'.spokePath i).otherEndpoint
            (Classical.choose (C'.spoke_exits_own_main i)) ∉
          (pathToPublic
            ((C'.mainPath i).orient (C'.main_connects i))).vertices
      rw [pathToPublic_vertices,
        Lax17Proofs.SimpleGraph.GraphPath.orient_vertexSet]
      exact (Classical.choose_spec (C'.spoke_exits_own_main i)).2.2.2
    spoke_avoids_other_main := by
      intro i j hij
      have hsource :=
        C'.spoke_disjoint_other_main (i := j) (j := i) hij.symm
      rw [pathToPublic_vertices, pathToPublic_vertices,
        Lax17Proofs.SimpleGraph.GraphPath.orient_vertexSet]
      exact hsource.symm
  }

/-- Forget the proof-internal provenance of a pseudo-grid while retaining its
rows, selected columns, and properties P1 and P2. -/
noncomputable def pseudoGridToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B X : Finset V} {g D κ : ℕ}
    {P : Lax17Proofs.SimpleGraph.PerfectPathPacking G A B}
    {Q : Lax17Proofs.SimpleGraph.PerfectPathPacking G A X}
    (hPcard : P.card = κ)
    (Γ : Lax17Proofs.SimpleGraph.PseudoGrid G A B X g D P Q) :
    Lax17.Crossbar.PseudoGrid G A B X g D κ := by
  classical
  exact {
    RowIndex := P.Index
    row_count := hPcard
    row := fun i => pathToPublic (P.path i)
    row_connects := fun i => ⟨P.source_mem i, P.target_mem i⟩
    rows_disjoint := by
      intro i j hij
      simpa [pathToPublic,
        Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
          P.node_disjoint hij
    depth_pos := Γ.depth_pos
    reserved := Γ.reserved
    reserved_card_le := Γ.reserved_card_le
    reserved_disjoint := Γ.reserved_disjoint
    ColumnIndex := Γ.QIndex
    column_count := by
      simpa [hPcard] using Γ.q_card
    column := fun j => pathToPublic (Γ.qPath j)
    columns_disjoint := by
      intro i j hij
      simpa [pathToPublic,
        Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
          Γ.qPath_nodeDisjoint hij
    column_reaches_X_cleanly := by
      intro j
      simpa [pathToPublic,
        Lax17Proofs.SimpleGraph.GraphPath.ExactlyOneEndpointIn,
        Lax17Proofs.SimpleGraph.GraphPath.InternallyDisjointFromSet,
        Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint,
        Lax17.Paths.Path.InternallyAvoids] using
          Γ.qPath_exactly_one_endpoint_in_X j
    unreserved_row_avoids_columns := by
      intro p hp j
      have hpRemaining :
          p ∈ Lax17Proofs.SimpleGraph.pseudoGridRemaining Γ.reserved := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ p, ?_⟩
        intro hpUnion
        rcases Finset.mem_biUnion.mp hpUnion with ⟨i, _hi, hpi⟩
        exact hp i hpi
      simpa [pathToPublic,
        Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
          Γ.remaining_disjoint_qPath p hpRemaining j
    few_columns_miss_reserved := by
      intro i
      rcases Γ.few_qPath_miss_reserved i with ⟨miss, hmissCard, hmiss⟩
      refine ⟨miss, hmissCard, ?_⟩
      intro j hj
      have hintersects :
          Lax17Proofs.SimpleGraph.pseudoGridIntersectsRow
            P Γ.reserved Γ.qPath i j := by
        by_contra hnot
        exact hj (hmiss j hnot)
      rcases hintersects with ⟨p, hp, hmeet⟩
      exact ⟨p, hp, by
        simpa [pathToPublic,
          Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using hmeet⟩
  }

/-- An internal strong path-of-sets minor witness gives the public minor
witness. -/
theorem strongPathOfSetsMinorToPublic
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {length width : ℕ}
    (h :
      Lax17Proofs.SimpleGraph.CrossbarContract.HasStrongPathOfSetsMinor
        G length width) :
    Lax17.Crossbar.HasStrongPathOfSetsMinor G length width := by
  rcases h with ⟨W, hWfinite, hWdecidable, H, ⟨M⟩, ⟨P⟩⟩
  letI : Fintype W := hWfinite
  letI : DecidableEq W := hWdecidable
  exact
    ⟨W, hWfinite, hWdecidable, H,
      ⟨Lax17Proofs.Bridge.minorModelToPublic M⟩,
      ⟨strongPathOfSetsToPublic P⟩⟩

/-- Translate a clean public hairy path-of-sets system to the detailed
structure used by the composition theorem. -/
noncomputable def hairyPathOfSetsToSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {ℓ w : ℕ}
    (H : Lax17.PathOfSets.HairySystem G ℓ w) :
    Lax17Proofs.SimpleGraph.HairyPathOfSetsSystem G ℓ w where
  base := strongPathOfSetsToSource H.base
  hairCluster := H.hairCluster
  hairCluster_connected := H.hair_connected
  hairCluster_disjoint := H.hair_disjoint
  hairCluster_disjoint_base := H.hair_disjoint_base
  hairCluster_disjoint_baseConnectors := by
    intro i j hj
    rw [Finset.disjoint_left]
    intro v hvHair hvConnector
    rcases
        ((strongPathOfSetsToSource H.base).connector j hj).toPathPacking
          |>.mem_vertexSet.mp hvConnector with
      ⟨a, ha⟩
    dsimp [strongPathOfSetsToSource] at a ha
    rw [vertexLinkageToPerfectSource_path_vertexSet] at ha
    exact
      Finset.disjoint_left.mp (H.hair_disjoint_connectors i j hj a)
        hvHair ha
  x := H.baseEndpoint
  y := H.hairEndpoint
  x_subset_cluster := H.baseEndpoint_subset
  y_subset_hairCluster := H.hairEndpoint_subset
  x_card := H.baseEndpoint_card
  y_card := H.hairEndpoint_card
  x_disjoint_nails := H.baseEndpoint_avoids_interfaces
  y_nodeWellLinked i :=
    (nodeWellLinkedIn_iff G (H.hairCluster i) (H.hairEndpoint i)).mpr
      (H.hairEndpoint_well_linked i)
  left_x_nodeLinked i :=
    (nodeLinkedIn_iff G (H.base.cluster i) (H.base.left i)
      (H.baseEndpoint i)).mpr (H.baseEndpoint_linked i)
  hairConnector i :=
    vertexLinkageToPerfectSource (H.hairLinkage i)
      (H.baseEndpoint_card i) (H.hairEndpoint_card i)
  hairConnector_card i := by
    exact Fintype.card_fin w
  hairConnector_mutually_nodeDisjoint := by
    intro i j hij a b
    rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint,
      vertexLinkageToPerfectSource_path_vertexSet,
      vertexLinkageToPerfectSource_path_vertexSet]
    exact H.hair_linkages_disjoint hij a b
  hairConnector_disjoint_baseConnectors := by
    intro i j hj a b
    dsimp [strongPathOfSetsToSource] at b ⊢
    rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint,
      vertexLinkageToPerfectSource_path_vertexSet,
      vertexLinkageToPerfectSource_path_vertexSet]
    exact H.hair_linkages_disjoint_connectors i j hj a b
  hairConnector_internally_disjoint_baseClusters := by
    intro i j
    change
      Lax17Proofs.SimpleGraph.PathPacking.InternallyDisjointFromSet
        ((vertexLinkageToSource (H.hairLinkage i)).orient)
        (H.base.cluster j)
    exact
      Lax17Proofs.SimpleGraph.PathPacking.orient_internallyDisjointFromSet
        (vertexLinkageToSource_internallyDisjoint (H.hairLinkage i)
          (H.hair_linkages_avoid_base i j))
  hairConnector_internally_disjoint_hairClusters := by
    intro i j
    change
      Lax17Proofs.SimpleGraph.PathPacking.InternallyDisjointFromSet
        ((vertexLinkageToSource (H.hairLinkage i)).orient)
        (H.hairCluster j)
    exact
      Lax17Proofs.SimpleGraph.PathPacking.orient_internallyDisjointFromSet
        (vertexLinkageToSource_internallyDisjoint (H.hairLinkage i)
          (H.hair_linkages_avoid_hair i j))

/-- Translate a public crossbar back to the detailed finite-index
representation used by the Section 4 composition. -/
noncomputable def crossbarToSource
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B X : Finset V} {width : ℕ}
    (C : Lax17.Crossbar.System G A B X width) :
    Lax17Proofs.SimpleGraph.Crossbar G A B X width where
  Index := Fin width
  card_index := Fintype.card_fin width
  mainPath i := pathToSource (C.mainPath i)
  main_connects i := Or.inl (C.main_connects i)
  main_nodeDisjoint := by
    intro i j hij
    simpa [pathToSource,
      Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
        C.main_disjoint hij
  spokePath i := pathToSource (C.spokePath i)
  spoke_connects := by
    intro i
    by_cases hsource : (C.spokePath i).source = C.attachment i
    · left
      refine ⟨?_, ?_⟩
      · simpa [pathToSource, hsource] using C.attachment_on_main i
      · have hexit := C.exit_is_other_endpoint i
        simp [hsource] at hexit
        simpa [pathToSource, ← hexit] using C.exit_in_X i
    · right
      have htarget : C.attachment i = (C.spokePath i).target :=
        (C.attachment_is_endpoint i).resolve_left
          (fun h => hsource h.symm)
      refine ⟨?_, ?_⟩
      · simpa [pathToSource, htarget] using C.attachment_on_main i
      · have hexit := C.exit_is_other_endpoint i
        simp [hsource] at hexit
        simpa [pathToSource, ← hexit] using C.exit_in_X i
  spoke_nodeDisjoint := by
    intro i j hij
    simpa [pathToSource,
      Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
        C.spoke_disjoint hij
  spoke_meets_own_main := by
    intro i
    refine ⟨C.attachment i, ?_, ?_⟩
    · simpa [pathToSource,
        Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint] using
          C.attachment_is_endpoint i
    · simpa [pathToSource,
        Lax17Proofs.SimpleGraph.GraphPath.MeetsExactlyAt] using
          C.exact_attachment i
  spoke_exits_own_main := by
    intro i
    refine ⟨C.attachment i, ?_, ?_, ?_, ?_⟩
    · simpa [pathToSource,
        Lax17Proofs.SimpleGraph.GraphPath.IsEndpoint] using
          C.attachment_is_endpoint i
    · simpa [pathToSource,
        Lax17Proofs.SimpleGraph.GraphPath.MeetsExactlyAt] using
          C.exact_attachment i
    · simpa [pathToSource,
        Lax17Proofs.SimpleGraph.GraphPath.otherEndpoint,
        ← C.exit_is_other_endpoint i] using C.exit_in_X i
    · simpa [pathToSource,
        Lax17Proofs.SimpleGraph.GraphPath.otherEndpoint,
        ← C.exit_is_other_endpoint i] using C.exit_off_main i
  spoke_disjoint_other_main := by
    intro i j hij
    simpa [pathToSource,
      Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint] using
        (C.spoke_avoids_other_main hij.symm).symm

/-- Translate a public strong path-of-sets minor witness to the detailed
composition vocabulary. -/
theorem strongPathOfSetsMinorToSource
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {length width : ℕ}
    (h : Lax17.Crossbar.HasStrongPathOfSetsMinor G length width) :
    Lax17Proofs.SimpleGraph.CrossbarContract.HasStrongPathOfSetsMinor
      G length width := by
  rcases h with ⟨W, hWfinite, hWdecidable, H, hminor, ⟨P⟩⟩
  letI : Fintype W := hWfinite
  letI : DecidableEq W := hWdecidable
  exact
    ⟨W, hWfinite, hWdecidable, H, isMinorToSource hminor,
      ⟨strongPathOfSetsToSource P⟩⟩

end Bridge

namespace Exposed

/-- Keep the paper-level theorem boundary visible when the clean public
statement and its detailed source-native realization have separate APIs. -/
private theorem rebuildFrom {P Q : Prop} (_dependency : Q) (result : P) : P :=
  result

/--
---
conclusion: Lax17.NodeWellLinkedSetFromTreewidth.nodeWellLinkedSetFromTreewidth
---
Treewidth supplies a proportionally large node-well-linked set.
-/
theorem nodeWellLinkedSetFromTreewidth :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {k : ℕ},
          c * k ≤ Lax17.Treewidth.treewidth G →
            ∃ X : Finset V,
              k ≤ X.card ∧
                Lax17.Linkedness.NodeWellLinkedIn G Finset.univ X := by
  refine ⟨9, by decide, ?_⟩
  intro V _ _ G k hlarge
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.exists_nodeWellLinked_treewidth_le_nine_mul_card
        G with
    ⟨X, hlinked, hcontrol⟩
  refine ⟨X, ?_, (Bridge.nodeWellLinkedIn_iff G Finset.univ X).mp hlinked⟩
  rw [← Bridge.treewidth_eq] at hlarge
  omega

/--
---
conclusion: Lax17.TreewidthMinorMonotonicity.treewidth_mono_minor
---
Taking a minor cannot increase treewidth.
-/
theorem treewidth_mono_minor :
    ∀ {V W : Type u} [Fintype V] [DecidableEq V]
      [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (H : SimpleGraph W),
        Lax17.Minor.IsMinor H G →
          Lax17.Treewidth.treewidth H ≤ Lax17.Treewidth.treewidth G := by
  intro V W _ _ _ _ G H hminor
  rw [← Bridge.treewidth_eq, ← Bridge.treewidth_eq]
  exact Lax17Proofs.SimpleGraph.treewidth_le_of_minor
    (Bridge.isMinorToSource hminor)

/--
---
conclusion: Lax17.SmallLinkedSubsets.smallLinkedSubsets
---
Disjoint subsets of a node-well-linked set are linked.
-/
theorem smallLinkedSubsets :
    ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V)
      (C X A B : Finset V),
        Lax17.Linkedness.NodeWellLinkedIn G C X →
          A ⊆ X → B ⊆ X → Disjoint A B → A.card = B.card →
            Lax17.Linkedness.NodeLinkedIn G C A B := by
  intro V _ G C X A B hX hA hB hAB _hcard
  refine ⟨hA.trans hX.1, hB.trans hX.1, hAB, ?_⟩
  intro A' B' hA' hB'
  exact hX.2 (hA'.trans hA) (hB'.trans hB) (hAB.mono hA' hB')

/--
---
conclusion: Lax17.WellLinkednessBoosting.wellLinkednessBoosting
---
Bounded-degree edge-well-linkedness contains a large node-well-linked core.
-/
theorem wellLinkednessBoosting :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (C T : Finset V) (Δ κ : ℕ),
        Lax17.PathOfSets.IsCluster G C →
          Lax17.Degree.MaximumAtMost G Δ →
            3 ≤ Δ →
              T.card = κ →
                Lax17.Linkedness.EdgeWellLinkedIn G C T →
                  ∃ T' : Finset V,
                    T' ⊆ T ∧ κ / (4 * Δ) ≤ T'.card ∧
                      Lax17.Linkedness.NodeWellLinkedIn G C T' := by
  apply rebuildFrom (@Lax17.SmallLinkedSubsets.smallLinkedSubsets.{u})
  apply rebuildFrom (@Lax17.VertexMenger.vertexMenger.{u})
  apply rebuildFrom (@Lax17.EdgeMenger.edgeMenger.{u})
  intro V _ _ G C T Δ κ hcluster hdegree hDelta hcard hwell
  have hsource :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_of_edgeWellLinked_floor
        (G := G) (C := C) (T := T) (Δ := Δ) (κ := κ)
        hcluster hdegree hDelta hcard
        ((Bridge.edgeWellLinkedIn_iff G C T).mpr hwell)
  rcases hsource with ⟨T', hsubset, hsize, hlinked⟩
  exact
    ⟨T', hsubset, hsize,
      (Bridge.nodeWellLinkedIn_iff G C T').mp hlinked⟩

/--
---
conclusion: Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid
---
A sufficiently long and wide strong path-of-sets system contains a grid.
-/
theorem strongPathOfSetsContainsGrid :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w g : ℕ},
        Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w) →
          2 ≤ g →
            2 * g * (g - 1) ≤ ℓ →
              16 * g ^ 2 + 10 * g ≤ w →
                Lax17.GridMinor.ContainsGridMinor G g := by
  apply rebuildFrom (@Lax17.LocalRoutingOrGrid.localRoutingOrGrid.{u})
  apply rebuildFrom (@Lax17.CrossbarStitching.crossbarStitching.{u})
  intro V _ _ G ℓ w g hsystem hg hlength hwidth
  rcases hsystem with ⟨P⟩
  exact Lax17Proofs.Bridge.containsGridMinorToPublic
    (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.strongPathOfSets_containsGridMinor_proved
      G hg hlength hwidth (Bridge.strongPathOfSetsToSource P))

/--
---
conclusion: Lax17.TreewidthSparsifier.degreeThreeTreewidthSparsifier
---
Treewidth has a degree-three spanning sparsifier with polylogarithmic loss.
-/
theorem degreeThreeTreewidthSparsifier :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {k : ℕ},
          1 < k →
            k ≤ Lax17.Treewidth.treewidth G →
              ∃ H : SimpleGraph V,
                H ≤ G ∧
                  Lax17.Degree.MaximumAtMost H 3 ∧
                    k ≤ c * Lax17.Treewidth.treewidth H *
                      (Nat.log 2 k) ^ d := by
  apply rebuildFrom
    (@Lax17.StrongPathOfSetsFromTreewidth.strongPathOfSetsFromTreewidth.{u})
  apply rebuildFrom
    (@Lax17.LowDegreeWellLinkedCore.lowDegreeWellLinkedCore.{u})
  apply rebuildFrom
    (@Lax17.TreewidthMinorMonotonicity.treewidth_mono_minor.{u})
  rcases
      Lax17Proofs.SimpleGraph.DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifierOmega_proved.{u} with
    ⟨c, d, hc, hd, hsparse⟩
  refine ⟨c, d, hc, hd, ?_⟩
  intro V _ _ G k hk htreewidth
  rw [← Bridge.treewidth_eq] at htreewidth
  rcases hsparse G hk htreewidth with ⟨H, hHG, hdegree, hbound⟩
  refine ⟨H, hHG, ?_, ?_⟩
  · exact hdegree
  · rwa [Bridge.treewidth_eq] at hbound

/--
---
conclusion: Lax17.VertexMenger.vertexMenger
---
Finite vertex-Menger in exact packing-or-separator form.
-/
theorem vertexMenger :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A B : Finset V) (k : ℕ),
        Nonempty (Lax17.Paths.VertexLinkage G A B k) ∨
          ∃ X : Finset V,
            X.card < k ∧ Lax17.Paths.IsVertexSeparator G A B X := by
  intro V _ _ G A B k
  rcases Lax17Proofs.SimpleGraph.Menger.finite_vertex_menger_sharp
      G A B k with hpaths | hseparator
  · rcases
        Lax17Proofs.SimpleGraph.HasAtLeastDisjointPaths.exists_exact hpaths with
      ⟨P, hcard⟩
    exact Or.inl ⟨Bridge.pathPackingToPublic P k hcard⟩
  · rcases hseparator with ⟨X, hcard, hseparator⟩
    refine Or.inr ⟨X, hcard, ?_⟩
    intro P hconnects
    rcases hseparator (Bridge.pathToSource P) (Or.inl hconnects) with
      ⟨v, hvpath, hvX⟩
    exact ⟨v, by simpa using hvpath, hvX⟩

/--
---
conclusion: Lax17.EdgeMenger.edgeMenger
---
Finite edge-Menger in exact packing-or-cut form.
-/
theorem edgeMenger :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (C A B : Finset V) (k : ℕ),
        A ⊆ C →
          B ⊆ C →
            Disjoint A B →
              (∃ P : Lax17.Paths.EdgeLinkage G A B k,
                ∀ i : Fin k, (P.path i).StaysIn C) ∨
                Nonempty (Lax17.Paths.EdgeCutPartition G C A B k) := by
  intro V _ _ G C A B k hA hB hAB
  by_cases hpaths :
      Lax17Proofs.SimpleGraph.EdgeMenger.HasEdgeDisjointPathsIn
        G C A B k
  · rcases
        Lax17Proofs.SimpleGraph.EdgeMenger.exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn
          hpaths with
      ⟨P, hcard, hstay⟩
    let Q := Bridge.edgePathPackingToPublic P k hcard
    refine Or.inl ⟨Q, ?_⟩
    intro i
    simpa [Q, Bridge.edgePathPackingToPublic,
      Lax17.Paths.Path.StaysIn] using hstay
        (Fintype.equivOfCardEq (by
          simpa [Lax17Proofs.SimpleGraph.EdgePathPacking.card] using
            hcard.symm) i)
  · rcases
        Lax17Proofs.SimpleGraph.EdgeMenger.edge_menger_cut
          G C A B k hA hB hAB hpaths with
      ⟨cut⟩
    refine Or.inr ⟨{
      left := cut.X
      right := cut.Y
      cover := cut.cover
      disjoint := cut.disjoint
      left_terminals := cut.left_subset
      right_terminals := cut.right_subset
      boundary_small := ?_ }⟩
    have hboundary :
        Lax17.Paths.edgeBoundary G cut.X cut.Y =
          Lax17Proofs.SimpleGraph.EdgeMenger.edgeBoundary G cut.X cut.Y := by
      ext e
      simp [Lax17.Paths.edgeBoundary,
        Lax17Proofs.SimpleGraph.EdgeMenger.edgeBoundary]
    rw [hboundary]
    exact cut.boundary_lt

/--
---
conclusion: Lax17.SinghLau.singhLauBoundedDegreeSpanningTree
---
Singh--Lau additive-one bounded-degree spanning-tree rounding.
-/
theorem singhLauBoundedDegreeSpanningTree :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (B : ℕ),
        1 < Fintype.card V →
          Lax17.SpanningTreeRounding.FeasiblePoint G B →
            ∃ T : SimpleGraph V,
              T ≤ G ∧ T.IsTree ∧ Lax17.Degree.MaximumAtMost T (B + 1) := by
  intro V _ _ G B hcard hx
  exact
    Lax17Proofs.SimpleGraph.SinghLau.boundedDegreeSpanningTree_proved
      G B hcard (Bridge.feasiblePointToSource hx)

/--
---
conclusion: Lax17.Mader.maderAdmissibleSplitOff
---
Mader's admissible split-off theorem for named-edge multigraphs.
-/
theorem maderAdmissibleSplitOff :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V) (s : V),
        2 ≤ H.degree s → H.degree s ≠ 3 → H.NoIncidentCutEdge s →
          ∃ p : H.SplitPair s, H.IsMaderAdmissible p := by
  intro V _ _ H s hdegree hthree hno
  have hdegreeEq :
      (Bridge.edgeIndexedGraphToSource H).degree s = H.degree s := by
    exact congrArg Finset.card (Bridge.terminalIncidentEdges_eq H s)
  have hnoSource :
      (Bridge.edgeIndexedGraphToSource H).NoIncidentCutEdge s := by
    intro e he hcut
    apply hno e
    · rw [← Bridge.terminalIncidentEdges_eq]
      exact he
    · rcases hcut with ⟨S, hS⟩
      refine ⟨S, ?_⟩
      rw [← Bridge.terminalBoundary_eq]
      exact hS
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.maderAdmissiblePair
        (Bridge.edgeIndexedGraphToSource H) s
        (by rwa [hdegreeEq]) (by rwa [hdegreeEq]) hnoSource with
    ⟨p, hp⟩
  exact ⟨Bridge.splitPairToPublic p,
    Bridge.maderAdmissibleToPublic p hp⟩

/--
---
conclusion: Lax17.TerminalElementMenger.terminalElementMenger
---
Canonical and arbitrary-cut formulations of terminal element connectivity
agree.
-/
theorem terminalElementMenger :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
      (terminals : Finset V) (k : ℕ),
        H.TerminalElementConnectedAtLeast terminals k ↔
          ∀ ⦃a : V⦄, a ∈ terminals →
            ∀ ⦃b : V⦄, b ∈ terminals → a ≠ b →
              ∀ C : H.ElementCut terminals a b, k ≤ C.order := by
  intro V _ _ H terminals k
  classical
  constructor
  · intro h a ha b hb hab C
    have hcanonical :=
      h ha hb hab C.removedVertices C.side
        C.removedVertices_nonterminal C.source_mem C.target_not_mem
        C.side_disjoint_removed
    have hsubset :
        H.availableBoundary C.removedVertices C.side ⊆ C.removedEdges := by
      intro e he
      have havailable := Finset.mem_filter.mp he
      have hcross := (Finset.mem_filter.mp havailable.1).2
      exact C.crossing_removed e havailable.2.1 havailable.2.2 hcross
    exact hcanonical.trans
      (Nat.add_le_add_left (Finset.card_le_card hsubset) _)
  · intro h a ha b hb hab removed side hnonterminal
      haSide hbSide hdisjoint
    let C : H.ElementCut terminals a b :=
      { removedVertices := removed
        removedVertices_nonterminal := hnonterminal
        removedEdges := H.availableBoundary removed side
        side := side
        source_mem := haSide
        target_not_mem := hbSide
        side_disjoint_removed := hdisjoint
        crossing_removed := by
          intro e hleft hright hcross
          apply Finset.mem_filter.mpr
          refine ⟨?_, hleft, hright⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hcross⟩ }
    simpa [C, Lax17.TerminalConnectivity.EdgeIndexedGraph.ElementCut.order]
      using h ha hb hab C

/--
---
conclusion: Lax17.HindOellermann.hindOellermannDeletionContraction
---
Hind--Oellermann deletion--contraction for terminal element connectivity.
-/
theorem hindOellermannDeletionContraction :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
      (terminals : Finset V) (k : ℕ) (e₀ : H.Edge),
        H.left e₀ ∉ terminals → H.right e₀ ∉ terminals →
          H.TerminalElementConnectedAtLeast terminals k →
            (H.deleteEdge e₀).TerminalElementConnectedAtLeast terminals k ∨
              ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
                (K : Lax17.TerminalConnectivity.EdgeIndexedGraph W)
                (mapVertex : V → W),
                  Nonempty (H.IsContraction e₀ K mapVertex) ∧
                    K.TerminalElementConnectedAtLeast
                      (Lax17.TerminalConnectivity.EdgeIndexedGraph.terminalImage
                      mapVertex terminals) k := by
  apply rebuildFrom
    (@Lax17.TerminalElementMenger.terminalElementMenger.{u})
  intro V _ _ H terminals k e₀ hleft hright hconnected
  have hsource :=
    (Bridge.terminalElementConnectedAtLeast_iff H terminals k).mpr hconnected
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.hindOellermannDeletionContraction
        (Bridge.edgeIndexedGraphToSource H) terminals k e₀
        hleft hright hsource with
    hdelete | hcontract
  · left
    apply
      (Bridge.terminalElementConnectedAtLeast_iff
        (H.deleteEdge e₀) terminals k).mp
    exact hdelete
  · right
    let W :=
      Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.ContractVertex
        V (H.left e₀) (H.right e₀)
    let mapVertex : V → W :=
      Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.ContractVertex.projection
        (p := H.left e₀) (q := H.right e₀)
    let K : Lax17.TerminalConnectivity.EdgeIndexedGraph W :=
      Bridge.contractionGraphToPublic H e₀
    refine ⟨W, inferInstance, inferInstance, K, mapVertex, ?_, ?_⟩
    · exact ⟨Bridge.canonicalContractionModel H e₀⟩
    · apply
        (Bridge.terminalElementConnectedAtLeast_iff K
          (Lax17.TerminalConnectivity.EdgeIndexedGraph.terminalImage
            mapVertex terminals) k).mp
      exact hcontract

/--
---
conclusion: Lax17.StrongPathExtraction.strongPathExtraction
---
A buffered meta-tree path yields a strong path-of-sets system.
-/
theorem strongPathExtraction :
    ∀ {V : Type u} [DecidableEq V] {G : SimpleGraph V}
      {m w ℓ : ℕ} (T : Lax17.TreeOfSets.StrongSystem G m w),
        0 < ℓ →
          Lax17.TreeOfSets.HasMetaPath T (ℓ + 2) →
            Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w) := by
  intro V _ G m w ℓ T hℓ hpath
  let Tsource := Bridge.strongTreeOfSetsToSource T
  have hbuffered :
      Tsource.HasBufferedMetaPath ℓ := by
    rcases hpath with ⟨order, hinjective, hadjacent⟩
    refine ⟨order, hinjective, ?_⟩
    intro r
    have hr := r.isLt
    have hr0 : r.1 < ℓ + 2 := by omega
    have hr1 : r.1 + 1 < ℓ + 2 := by omega
    exact hadjacent ⟨r.1, hr0⟩ hr1
  rcases
      Tsource.exists_strongPathOfSetsSystem_of_hasBufferedMetaPath
        hℓ hbuffered with
    ⟨P⟩
  exact ⟨Bridge.strongPathOfSetsToPublic P⟩

/--
---
conclusion: Lax17.StrongPathOfSetsFromTreewidth.strongPathOfSetsFromTreewidth
---
Large treewidth produces a strong path-of-sets system.
-/
theorem strongPathOfSetsFromTreewidth :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {ℓ w k : ℕ},
          1 < ℓ →
            1 < w →
              1 < k →
                k ≤ Lax17.Treewidth.treewidth G →
                  c * w * ℓ ^ 50 * (Nat.log 2 k) ^ d < k →
                    Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w) := by
  apply rebuildFrom
    (@Lax17.NodeWellLinkedSetFromTreewidth.nodeWellLinkedSetFromTreewidth.{u})
  apply rebuildFrom
    (@Lax17.StrongTreeOfSetsConstruction.strongTreeOfSetsConstruction.{u})
  apply rebuildFrom
    (@Lax17.StrongPathExtraction.strongPathExtraction.{u})
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.exists_strongPathOfSets_of_treewidth_from_theoremA2SourceInputs
        Lax17Proofs.SimpleGraph.ChekuriChuzhoy.theoremA2SourceInputs_proved.{u} with
    ⟨c, d, hc, hd, hpath⟩
  refine ⟨c, d, hc, hd, ?_⟩
  intro V _ _ G ℓ w k hℓ hw hk htree hlarge
  rw [← Bridge.treewidth_eq] at htree
  rcases hpath G hℓ hw hk htree hlarge with ⟨P⟩
  exact ⟨Bridge.strongPathOfSetsToPublic P⟩

/--
---
conclusion: Lax17.StrongTreeOfSetsConstruction.strongTreeOfSetsConstruction
---
A bounded-degree node-well-linked core supports a strong tree-of-sets system.
-/
theorem strongTreeOfSetsConstruction :
    ∃ c d p : ℕ, 0 < c ∧ 0 < d ∧ 0 < p ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (X : Finset V) {m w x Δ : ℕ},
          1 < m →
            1 < w →
              1 < x →
                Lax17.Degree.MaximumAtMost G Δ →
                  X.card = x →
                    Lax17.Linkedness.NodeWellLinkedIn G Finset.univ X →
                      c * w * m ^ 24 * Δ ^ p *
                          (Nat.log 2 x) ^ d < x →
                        Nonempty (Lax17.TreeOfSets.StrongSystem G m w) := by
  apply rebuildFrom (@Lax17.Mader.maderAdmissibleSplitOff.{u})
  apply rebuildFrom
    (@Lax17.HindOellermann.hindOellermannDeletionContraction.{u})
  apply rebuildFrom
    (@Lax17.WellLinkednessBoosting.wellLinkednessBoosting.{u})
  apply rebuildFrom (@Lax17.EdgeMenger.edgeMenger.{u})
  apply rebuildFrom (@Lax17.VertexMenger.vertexMenger.{u})
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.strongTreeOfSetsCoreFromNodeWellLinkedCore_proved.{u} with
    ⟨hc, hd, hp, hbuild⟩
  refine
    ⟨Lax17Proofs.SimpleGraph.ChekuriChuzhoySection5Arithmetic.buildConstant24,
      5, 10, hc, hd, hp, ?_⟩
  intro V _ _ G X m w x Δ hm hw hx hdegree hcard hlinked hlarge
  rcases
      hbuild G X hm hw hx hdegree hcard
        ((Bridge.nodeWellLinkedIn_iff G Finset.univ X).mpr hlinked)
        hlarge with
    ⟨T⟩
  exact ⟨Bridge.strongTreeOfSetsToPublic T⟩

/-- Repackage the exposed sparsifier theorem as the Omega-form source input
used by the hairy-system assembly. -/
private theorem degreeThreeSparsifierOmegaFromPublic :
    ∃ cSparse cSparseLog : ℕ,
      0 < cSparse ∧ 0 < cSparseLog ∧
        Lax17Proofs.SimpleGraph.DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
          cSparse cSparseLog := by
  rcases
      Lax17.TreewidthSparsifier.degreeThreeTreewidthSparsifier.{u} with
    ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, hsparse⟩
  refine ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, ?_⟩
  intro V _ _ G k hk htree
  rw [Bridge.treewidth_eq] at htree
  rcases hsparse G hk htree with ⟨H, hHG, hdegree, hbound⟩
  refine ⟨H, hHG, hdegree, ?_⟩
  rwa [← Bridge.treewidth_eq] at hbound

/-- Repackage the exposed strong tree-of-sets construction as the source
input consumed by the hairy-system assembly. -/
private theorem strongTreeInputFromPublic :
    ∃ cBuild cBuildLog cDeltaPow : ℕ,
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
        cBuild cBuildLog cDeltaPow := by
  rcases
      Lax17.StrongTreeOfSetsConstruction.strongTreeOfSetsConstruction.{u} with
    ⟨cBuild, cBuildLog, cDeltaPow,
      hcBuild, hcBuildLog, hcDeltaPow, hbuild⟩
  refine
    ⟨cBuild, cBuildLog, cDeltaPow,
      hcBuild, hcBuildLog, hcDeltaPow, ?_⟩
  intro V _ _ G m width x delta X hm hwidth hx hdegree hcard
    hlinked hlarge
  rcases
      hbuild G X hm hwidth hx hdegree hcard
        ((Bridge.nodeWellLinkedIn_iff G Finset.univ X).mp hlinked)
        hlarge with
    ⟨T⟩
  exact ⟨Bridge.strongTreeOfSetsToSource T⟩

/-- Repackage the exposed local split theorem as the source Appendix A.3
input, then lift it pointwise to Appendix A.4. -/
private theorem appendixA4InputFromPublic :
    ∃ cSplit : ℕ, 0 < cSplit ∧
      Lax17Proofs.SimpleGraph.HairyPathOfSetsTheorem.AppendixA4SplitInput.{u}
        cSplit := by
  rcases
      Lax17.ParallelClusterSplitting.parallelClusterSplitting.{u} with
    ⟨cSplit, hcSplit, hsplit⟩
  have hA3 :
      Lax17Proofs.SimpleGraph.HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u}
        cSplit := by
    refine ⟨hcSplit, ?_⟩
    intro V _ _ G C A B w hw hdegree hcluster hA hB hAcard hBcard
      hAB hAwell hBwell hlinked
    rcases
        hsplit G hw hdegree hcluster hA hB hAcard hBcard hAB
          ((Bridge.nodeWellLinkedIn_iff G C A).mp hAwell)
          ((Bridge.nodeWellLinkedIn_iff G C B).mp hBwell)
          ((Bridge.nodeLinkedIn_iff G C A B).mp hlinked) with
      ⟨D⟩
    exact ⟨Bridge.hairyClusterSplitToSource D⟩
  exact
    ⟨cSplit, hcSplit,
      Lax17Proofs.SimpleGraph.HairyPathOfSetsTheorem.appendixA4SplitInput_of_appendixA3ClusterSplitInput
        hA3⟩

/--
---
conclusion: Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth
assumptions:
  - Lax17.ParallelClusterSplitting.parallelClusterSplitting
  - Lax17.StrongTreeOfSetsConstruction.strongTreeOfSetsConstruction
  - Lax17.TreewidthSparsifier.degreeThreeTreewidthSparsifier
---
Large treewidth produces a subcubic subgraph carrying a hairy path-of-sets
system.
-/
theorem hairyPathOfSetsFromTreewidth :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {ℓ w k : ℕ},
          1 < ℓ →
            1 < w →
              1 < k →
                k ≤ Lax17.Treewidth.treewidth G →
                  c * w * ℓ ^ 50 * (Nat.log 2 k) ^ d < k →
                    ∃ H : SimpleGraph V,
                      H ≤ G ∧
                        Lax17.Degree.MaximumAtMost H 3 ∧
                          Nonempty (Lax17.PathOfSets.HairySystem H ℓ w) := by
  rcases
      Lax17Proofs.SimpleGraph.HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_and_appendixA4
        degreeThreeSparsifierOmegaFromPublic
        Lax17Proofs.SimpleGraph.ChekuriChuzhoy.exists_routableSetFromTreewidth_proved.{u}
        Lax17Proofs.SimpleGraph.ChekuriChuzhoy.exists_cutWellLinkedCoreFromRoutableSet_proved.{u}
        strongTreeInputFromPublic
        Lax17Proofs.SimpleGraph.ChekuriChuzhoy.strongPathOfSetsFromLeafyStrongTreeOfSets_proved.{u}
        appendixA4InputFromPublic with
    ⟨c, d, hc, hd, hhairy⟩
  refine ⟨c, d, hc, hd, ?_⟩
  intro V _ _ G ℓ w k hℓ hw hk htree hlarge
  rw [← Bridge.treewidth_eq] at htree
  rcases hhairy G hℓ hw hk htree hlarge with
    ⟨H, hHG, hdegree, ⟨S⟩⟩
  exact ⟨H, hHG, hdegree, ⟨Bridge.hairyPathOfSetsToPublic S⟩⟩

/--
---
conclusion: Lax17.LocalRoutingOrGrid.localRoutingOrGrid
---
Linked terminal sets in a connected cluster admit bridged local routes unless
the target grid is already a minor.
-/
theorem localRoutingOrGrid :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
        1 < h →
          1 < q →
            Lax17.PathOfSets.IsCluster G C →
              Lax17.Linkedness.NodeLinkedIn G C A B →
                A.card = w →
                  B.card = w →
                    (16 * h + 10) * q ≤ w →
                      Lax17.GridMinor.ContainsGridMinor G h ∨
                        ∃ Q : Lax17.Paths.VertexLinkage G A B q,
                          (∀ i : Fin q, (Q.path i).StaysIn C) ∧
                            Q.HasPairwiseBridgesIn C := by
  apply rebuildFrom (@Lax17.VertexMenger.vertexMenger.{u})
  intro V _ _ G C A B h q w hh hq hcluster hlinked hA hB hwidth
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.localRoutingClusterInput_proved
        G hh hq hcluster
        ((Bridge.nodeLinkedIn_iff G C A B).mpr hlinked)
        hA hB hwidth with
    hgrid | hroutes
  · exact Or.inl (Lax17Proofs.Bridge.containsGridMinorToPublic hgrid)
  · rcases hroutes with ⟨P, hcard, hstay, hbridges⟩
    let Q := Bridge.pathPackingToPublic P q hcard
    refine Or.inr ⟨Q, ?_, ?_⟩
    · intro i
      simpa [Q, Bridge.pathPackingToPublic,
        Lax17.Paths.Path.StaysIn] using hstay
          (Fintype.equivOfCardEq (by
            simpa [Lax17Proofs.SimpleGraph.PathPacking.card] using
              hcard.symm) i)
    · exact Bridge.pathPackingToPublic_hasPairwiseBridgesIn
        P q hcard hbridges

/--
---
conclusion: Lax17.ParallelClusterSplitting.parallelClusterSplitting
---
A degree-three cluster with two linked interfaces splits into a base cluster
and a disjoint hair cluster.
-/
theorem parallelClusterSplitting :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {C A B : Finset V} {w : ℕ},
          0 < w →
            Lax17.Degree.MaximumAtMost G 3 →
              Lax17.PathOfSets.IsCluster G C →
                A ⊆ C →
                  B ⊆ C →
                    A.card = c * w →
                      B.card = c * w →
                        Disjoint A B →
                          Lax17.Linkedness.NodeWellLinkedIn G C A →
                            Lax17.Linkedness.NodeWellLinkedIn G C B →
                              Lax17.Linkedness.NodeLinkedIn G C A B →
                                Nonempty
                                  (Lax17.PathOfSets.HairyClusterSplit
                                    G C A B w) := by
  let c := Lax17Proofs.SimpleGraph.AppendixA3Complete.cSplit
  refine
    ⟨c, Lax17Proofs.SimpleGraph.AppendixA3Complete.cSplit_pos, ?_⟩
  intro V _ _ G C A B w hw hdegree hcluster hA hB hAcard hBcard
    hAB hAwell hBwell hlinked
  rcases
      Lax17Proofs.SimpleGraph.AppendixA3Complete.exists_clusterSplitData
        G hw hdegree hcluster hA hB hAcard hBcard hAB
        ((Bridge.nodeWellLinkedIn_iff G C A).mpr hAwell)
        ((Bridge.nodeWellLinkedIn_iff G C B).mpr hBwell)
        ((Bridge.nodeLinkedIn_iff G C A B).mpr hlinked) with
    ⟨D⟩
  exact ⟨Bridge.hairyClusterSplitToPublic D⟩

/--
---
conclusion: Lax17.ExpanderGrid.expanderContainsGrid
---
Theorem 8.1 turns separator expansion into a square grid minor.
-/
theorem expanderContainsGrid :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (d g : ℕ),
        2 ≤ Fintype.card V →
          Lax17.Expansion.NoSmallBalancedSeparator G d →
            ((3 * (d + 1) * (15 * (d + 1))) * 8) *
                (5 * g ^ 2) * Nat.log 2 (Fintype.card V) ≤
                  Fintype.card V →
              Lax17.GridMinor.ContainsGridMinor G g := by
  intro V _ _ G d g hcard hnoseparator hbudget
  classical
  let targetScale := (3 * (d + 1) * (15 * (d + 1))) * 8
  have hcomplex :
      Lax17Proofs.SimpleGraph.targetComplexity
          (Lax17Proofs.SimpleGraph.gridGraphULift.{u} g) ≤
        5 * g ^ 2 :=
    Lax17Proofs.SimpleGraph.targetComplexity_gridGraphULift_le_five_mul_sq g
  have hsmall :
      Lax17Proofs.SimpleGraph.TargetSmallForHost
        (V := V) (Lax17Proofs.SimpleGraph.gridGraphULift.{u} g)
          targetScale := by
    unfold Lax17Proofs.SimpleGraph.TargetSmallForHost
    exact
      (Nat.mul_le_mul_right (Nat.log 2 (Fintype.card V))
        (Nat.mul_le_mul_left targetScale hcomplex)).trans
          (by simpa [targetScale] using hbudget)
  exact
    Lax17Proofs.Bridge.containsGridMinorToPublic
      (Lax17Proofs.SimpleGraph.containsGridMinor_of_expanderTheorem81_of_noSmallBalancedSeparator
        G hcard (Bridge.noSmallBalancedSeparatorToSource hnoseparator)
        hsmall)

/--
---
conclusion: Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion
---
Every finite even set has a logarithmic cut-matching transcript with
half-expansion, counting matching edges with their round multiplicity.
-/
theorem logarithmicCutMatchingExpansion :
    ∃ c : ℕ, 0 < c ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V],
        2 ≤ Fintype.card V →
          (∃ half : ℕ, Fintype.card V = 2 * half) →
            ∃ T : Lax17.Expansion.CutMatchingTranscript V,
              T.length ≤ c * Nat.log 2 (Fintype.card V) ∧
                T.IsHalfEdgeExpander := by
  rcases
      Lax17Proofs.SimpleGraph.CutMatchingGame.exists_generic_log_round_halfExpander_with_followsResponder with
    ⟨c, hc, htranscript⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ hcard ⟨half, hhalf⟩
  let responder :
      Lax17Proofs.SimpleGraph.CutMatchingGame.SequentialResponder V :=
    fun _ B =>
      { toEquiv := Fintype.equivOfCardEq (by
          simpa using B.card_eq) }
  have heven : Even (Fintype.card V) := by
    refine ⟨half, ?_⟩
    omega
  rcases
      htranscript (X := V) (k := Fintype.card V)
        (by omega) (by omega) heven le_rfl responder with
    ⟨rounds, hlength, hexpands, _⟩
  let T : Lax17.Expansion.CutMatchingTranscript V :=
    rounds.map Bridge.matchingRoundToPublic
  refine ⟨T, ?_, ?_⟩
  · simpa [T] using hlength
  · intro S hS hsmall
    have hboundary :=
      (Lax17Proofs.SimpleGraph.CutMatchingGame.isHalfEdgeExpander_iff
        rounds).mp hexpands S hS hsmall
    simpa [T, Lax17.Expansion.CutMatchingTranscript.edgeBoundaryCount,
      Lax17.Expansion.MatchingRound.boundary,
      Lax17.Expansion.MatchingRound.Crosses,
      Bridge.matchingRoundToPublic,
      Lax17Proofs.SimpleGraph.CutMatchingGame.edgeBoundaryCount,
      Lax17Proofs.SimpleGraph.CutMatchingGame.LazyRound.edgeBoundary,
      Lax17Proofs.SimpleGraph.CutMatchingGame.LazyRound.edgeCrosses] using
        hboundary

/--
---
conclusion: Lax17.LowDegreeWellLinkedCore.lowDegreeWellLinkedCore
---
A sufficiently long strong path-of-sets system yields a subcubic subgraph in
which its first left interface is still polylogarithmically well-linked.
-/
theorem lowDegreeWellLinkedCore :
    ∃ cLength logLength cWellLinked logWellLinked : ℕ,
      0 < cLength ∧ 0 < logLength ∧
        0 < cWellLinked ∧ 0 < logWellLinked ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} {length width : ℕ}
        (P : Lax17.PathOfSets.StrongSystem G length width),
          1 < width →
            (∃ half : ℕ, width = 2 * half) →
              cLength * (Nat.log 2 width) ^ logLength ≤ length →
                ∃ H : SimpleGraph V,
                  H ≤ G ∧
                    Lax17.Degree.MaximumAtMost H 3 ∧
                      Lax17.Linkedness.ScaledEdgeWellLinked H
                        (P.left ⟨0, P.length_pos⟩) 1
                          (cWellLinked *
                            (Nat.log 2 width) ^ logWellLinked) := by
  apply rebuildFrom
    (@Lax17.SinghLau.singhLauBoundedDegreeSpanningTree.{u})
  rcases
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.Theorem51.theorem51_degree3_wellLinked_subgraph_from_localStrongPathOfSets with
    ⟨cLength, logLength, cWellLinked, logWellLinked,
      hcLength, hlogLength, hcWellLinked, hlogWellLinked, hcore⟩
  refine
    ⟨cLength, logLength, cWellLinked, logWellLinked,
      hcLength, hlogLength, hcWellLinked, hlogWellLinked, ?_⟩
  intro V _ _ G length width P hwidth ⟨half, hhalf⟩ hlength
  have heven : Even width := by
    refine ⟨half, ?_⟩
    omega
  rcases
      hcore (P := Bridge.strongPathOfSetsToSource P)
        hwidth heven hlength with
    ⟨H, hHG, hdegree, hwellLinked⟩
  refine ⟨H, hHG, hdegree, ?_⟩
  simpa [Bridge.strongPathOfSetsToSource,
    Lax17Proofs.SimpleGraph.PathOfSetsSystem.firstIndex] using
      Bridge.scaledWellLinkedToPublic hwellLinked

/--
---
conclusion: Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid
---
Theorem 4.1 produces either a width-`g²` crossbar or a depth-`D`
pseudo-grid satisfying P1 and P2.
-/
theorem crossbarOrPseudoGrid :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {A B X : Finset V} {g κ D : ℕ},
        2 ≤ g →
          Lax17.Crossbar.IsPowerOfTwo g →
            A.card = κ → B.card = κ → X.card = κ →
              Disjoint A B → Disjoint A X → Disjoint B X →
                (∀ x ∈ X, Lax17.Degree.Exactly G x 1) →
                  Lax17.Paths.VertexLinkage G A B κ →
                    Lax17.Paths.VertexLinkage G A X κ →
                      1 ≤ D → D ≤ κ / (2 * g ^ 2) →
                        Nonempty
                            (Lax17.Crossbar.System
                              G A B X (g ^ 2)) ∨
                          Nonempty
                            (Lax17.Crossbar.PseudoGrid
                              G A B X g D κ) := by
  apply rebuildFrom (@Lax17.VertexMenger.vertexMenger.{u})
  apply rebuildFrom (@Lax17.EdgeMenger.edgeMenger.{u})
  intro V _ _ G A B X g κ D hg hpower hA hB hX hAB hAX hBX
    hdegree Pab Pax hDpositive hDbound
  have hpowerSource :
      Lax17Proofs.SimpleGraph.CrossbarContract.IsPowerOfTwo g := by
    simpa [Lax17.Crossbar.IsPowerOfTwo,
      Lax17Proofs.SimpleGraph.CrossbarContract.IsPowerOfTwo] using hpower
  have hdegreeSource :
      ∀ x ∈ X, Lax17Proofs.SimpleGraph.DegreeEquals G x 1 := by
    simpa [Lax17.Degree.Exactly, Lax17.Degree.IsNeighbourhood,
      Lax17Proofs.SimpleGraph.DegreeEquals,
      Lax17Proofs.SimpleGraph.IsNeighborFinset] using hdegree
  rcases
      Lax17Proofs.SimpleGraph.theorem_four_one_of_pathPackings
        G hg hpowerSource hA hB hX hAB hAX hBX hdegreeSource
        (Bridge.vertexLinkageToSource Pab)
        (Bridge.vertexLinkageToSource_card Pab)
        (Bridge.vertexLinkageToSource Pax)
        (Bridge.vertexLinkageToSource_card Pax)
        hDpositive hDbound with
    ⟨P, Q, hPcard, _hQcard, _hminimum, hconclusion⟩
  rcases hconclusion with hcrossbar | hpseudoGrid
  · rcases hcrossbar with ⟨C⟩
    exact Or.inl ⟨Bridge.crossbarToPublic C⟩
  · rcases hpseudoGrid with ⟨Γ⟩
    exact Or.inr ⟨Bridge.pseudoGridToPublic hPcard Γ⟩

/--
---
conclusion: Lax17.ExponentTenCrossbarDichotomy.exponentTenCrossbarDichotomy
---
At the exponent-ten threshold, either a large crossbar exists or a minor
carries a proportionally large strong path-of-sets system.
-/
theorem exponentTenCrossbarDichotomy :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {A B X : Finset V} {g κ : ℕ},
          2 ≤ g →
            Lax17.Crossbar.IsPowerOfTwo g →
              A.card = κ → B.card = κ → X.card = κ →
                Disjoint A B → Disjoint A X → Disjoint B X →
                  2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ κ →
                    (∀ x ∈ X, Lax17.Degree.Exactly G x 1) →
                      Lax17.Paths.VertexLinkage G A B κ →
                        Lax17.Paths.VertexLinkage G A X κ →
                          Nonempty
                              (Lax17.Crossbar.System
                                G A B X (g ^ 2)) ∨
                            ∃ length width : ℕ,
                              g ^ 2 ≤ c * length ∧
                                g ^ 2 ≤ c * width ∧
                                  Lax17.Crossbar.HasStrongPathOfSetsMinor
                                    G length width := by
  apply rebuildFrom
    (@Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid.{u})
  rcases
      Lax17Proofs.SimpleGraph.CrossbarTheorem.crossbar_or_strong_pathOfSets_minor_degree10_proved with
    ⟨c, hc, hdichotomy⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G A B X g κ hg hpower hA hB hX hAB hAX hBX
    hlarge hdegree Pab Pax
  have hpowerSource :
      Lax17Proofs.SimpleGraph.CrossbarContract.IsPowerOfTwo g := by
    simpa [Lax17.Crossbar.IsPowerOfTwo,
      Lax17Proofs.SimpleGraph.CrossbarContract.IsPowerOfTwo] using hpower
  have hdegreeSource :
      ∀ x ∈ X, Lax17Proofs.SimpleGraph.DegreeEquals G x 1 := by
    simpa [Lax17.Degree.Exactly, Lax17.Degree.IsNeighbourhood,
      Lax17Proofs.SimpleGraph.DegreeEquals,
      Lax17Proofs.SimpleGraph.IsNeighborFinset] using hdegree
  rcases
      hdichotomy G hg hpowerSource hA hB hX hAB hAX hBX hlarge
        hdegreeSource
        (Bridge.vertexLinkageToSource Pab)
        (Bridge.vertexLinkageToSource_card Pab)
        (Bridge.vertexLinkageToSource Pax)
        (Bridge.vertexLinkageToSource_card Pax) with
    hcrossbar | hpath
  · rcases hcrossbar with ⟨C⟩
    exact Or.inl ⟨Bridge.crossbarToPublic C⟩
  · rcases hpath with ⟨length, width, hlength, hwidth, hminor⟩
    exact
      Or.inr
        ⟨length, width, hlength, hwidth,
          Bridge.strongPathOfSetsMinorToPublic hminor⟩

/--
---
conclusion: Lax17.CrossbarStitching.crossbarStitching
---
Compatible locally bridged row families stitch into global first-to-last
rows, retaining the bridges in every designated even cluster.
-/
theorem crossbarStitching :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {g : ℕ}
      (P : Lax17.PathOfSets.StrongSystem G
        (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)),
        2 ≤ g →
          (∀ i : Fin (2 * g * (g - 1)),
            ∃ localRows :
                Lax17.Paths.VertexLinkage G
                  (P.left i) (P.right i) g,
              (∀ row : Fin g,
                (localRows.path row).StaysIn (P.cluster i)) ∧
                  localRows.HasPairwiseBridgesIn (P.cluster i)) →
            ∃ rows :
                Lax17.Paths.VertexLinkage G
                  (P.left P.toSystem.firstIndex)
                  (P.right P.toSystem.lastIndex) g,
              ∀ i : Fin (g * (g - 1)),
                ∃ clusterIndex : Fin (2 * g * (g - 1)),
                  clusterIndex.1 = 2 * i.1 + 1 ∧
                    rows.HasPairwiseBridgesIn
                      (P.cluster clusterIndex) := by
  intro V _ _ G g P hg hlocal
  classical
  choose localRows localRowsStay localRowsBridges using hlocal
  let Psource := Bridge.strongPathOfSetsToSource P
  let E :
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.EvenClusterOutputs
        Psource.toPathOfSetsSystem g :=
    { output := fun i =>
        let clusterIndex :=
          Lax17Proofs.SimpleGraph.ChekuriChuzhoy.evenClusterIndex g i
        let Q := localRows clusterIndex
        { paths := Bridge.vertexLinkageToSource Q
          paths_card := Bridge.vertexLinkageToSource_card Q
          paths_staysIn := by
            simpa [Q, clusterIndex, Psource,
              Bridge.strongPathOfSetsToSource] using
                Bridge.vertexLinkageToSource_staysIn Q
                  (localRowsStay clusterIndex)
          pairwise_bridges := by
            simpa [Q, clusterIndex, Psource,
              Bridge.strongPathOfSetsToSource] using
                Bridge.vertexLinkageToSource_hasPairwiseBridgesIn Q
                  (localRowsBridges clusterIndex) } }
  let K :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.StitchingPieces.canonicalOfTwoLe
      Psource E hg
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.stitchingInput_proved
        G hg Psource E K with
    ⟨S⟩
  let rows :
      Lax17.Paths.VertexLinkage G
        (P.left P.toSystem.firstIndex)
        (P.right P.toSystem.lastIndex) g := by
    simpa [Psource, Bridge.strongPathOfSetsToSource,
      Lax17.PathOfSets.System.firstIndex,
      Lax17.PathOfSets.System.lastIndex,
      Lax17Proofs.SimpleGraph.PathOfSetsSystem.firstIndex,
      Lax17Proofs.SimpleGraph.PathOfSetsSystem.lastIndex] using
        Bridge.pathPackingToPublic S.rows g S.rows_card
  refine ⟨rows, ?_⟩
  intro i
  let clusterIndex :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.evenClusterIndex g i
  refine
    ⟨clusterIndex,
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.evenClusterIndex_val g i,
      ?_⟩
  have hbridges :=
    Bridge.pathPackingToPublic_hasPairwiseBridgesIn
      S.rows g S.rows_card (S.bridge_in_even_cluster i)
  simpa [rows, clusterIndex, Psource,
    Bridge.strongPathOfSetsToSource,
    Lax17.PathOfSets.System.firstIndex,
    Lax17.PathOfSets.System.lastIndex,
    Lax17Proofs.SimpleGraph.PathOfSetsSystem.firstIndex,
    Lax17Proofs.SimpleGraph.PathOfSetsSystem.lastIndex] using hbridges

end Exposed

end Lax17Proofs
