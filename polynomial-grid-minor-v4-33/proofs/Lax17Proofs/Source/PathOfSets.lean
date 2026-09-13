import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Path-of-sets systems

This file formalizes the Path-of-Sets System definitions from Section 2 of
Chuzhoy--Tan's proof of the polynomial grid-minor theorem.  The structures are
definition-only infrastructure for the later proof: a path-of-sets system is a
sequence of connected clusters with equal-size left and right nail sets and
node-disjoint connector path packings between consecutive clusters.
-/

namespace SimpleGraph

/-- A finite vertex set is a cluster when it induces a connected subgraph. -/
def IsCluster {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C : Finset V) : Prop :=
  (G.induce {v : V | v ∈ C}).Connected

namespace IsCluster

variable {V : Type*} [DecidableEq V]

/-- Cluster connectedness is preserved when edges are added to the ambient
graph. -/
theorem mono_graph {G G' : _root_.SimpleGraph V} {C : Finset V}
    (hC : IsCluster G C) (hGG' : G ≤ G') :
    IsCluster G' C := by
  apply hC.mono
  intro u v huv
  exact hGG' huv

end IsCluster

/-- A Path-of-Sets System of length `ell` and width `w`.

The paper assumes positive `ell` and `w`; these are stored as fields.  Connector
`i` runs from the right nail set of cluster `i` to the left nail set of cluster
`i + 1`, is internally disjoint from all clusters, and connector families for
different indices are mutually node-disjoint.
-/
structure PathOfSetsSystem {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (ell w : ℕ) where
  /-- The number of clusters is positive. -/
  length_pos : 0 < ell
  /-- The width is positive. -/
  width_pos : 0 < w
  /-- The ordered cluster sequence. -/
  cluster : Fin ell → Finset V
  /-- Each cluster is connected. -/
  cluster_connected : ∀ i : Fin ell, IsCluster G (cluster i)
  /-- Distinct clusters are disjoint. -/
  cluster_disjoint :
    ∀ ⦃i j : Fin ell⦄, i ≠ j → Disjoint (cluster i) (cluster j)
  /-- Left nail sets. -/
  left : Fin ell → Finset V
  /-- Right nail sets. -/
  right : Fin ell → Finset V
  /-- Left nails lie in their cluster. -/
  left_subset_cluster : ∀ i : Fin ell, left i ⊆ cluster i
  /-- Right nails lie in their cluster. -/
  right_subset_cluster : ∀ i : Fin ell, right i ⊆ cluster i
  /-- The two nail sets of a cluster are disjoint. -/
  left_right_disjoint : ∀ i : Fin ell, Disjoint (left i) (right i)
  /-- Each left nail set has cardinality `w`. -/
  left_card : ∀ i : Fin ell, (left i).card = w
  /-- Each right nail set has cardinality `w`. -/
  right_card : ∀ i : Fin ell, (right i).card = w
  /-- Connector path packings between consecutive clusters. -/
  connector :
    (i : Fin ell) → (hi : i.1 + 1 < ell) →
      PerfectPathPacking G (right i) (left ⟨i.1 + 1, hi⟩)
  /-- Each connector family has cardinality `w`. -/
  connector_card :
    ∀ (i : Fin ell) (hi : i.1 + 1 < ell),
      (connector i hi).card = w
  /-- Connector paths are internally disjoint from every cluster. -/
  connector_internally_disjoint_clusters :
    ∀ (i : Fin ell) (hi : i.1 + 1 < ell) (j : Fin ell),
      (connector i hi).toPathPacking.InternallyDisjointFromSet (cluster j)
  /-- Connector families for different gaps are mutually node-disjoint. -/
  connector_mutually_nodeDisjoint :
    ∀ ⦃i j : Fin ell⦄ (hi : i.1 + 1 < ell) (hj : j.1 + 1 < ell),
      i ≠ j →
        (connector i hi).toPathPacking.MutuallyNodeDisjoint
          (connector j hj).toPathPacking

namespace PathOfSetsSystem

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {ell w : ℕ}

/-- View a path-of-sets system inside a same-vertex supergraph. -/
def mapLe (P : PathOfSetsSystem G ell w) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') : PathOfSetsSystem G' ell w where
  length_pos := P.length_pos
  width_pos := P.width_pos
  cluster := P.cluster
  cluster_connected := fun i => (P.cluster_connected i).mono_graph hGG'
  cluster_disjoint := P.cluster_disjoint
  left := P.left
  right := P.right
  left_subset_cluster := P.left_subset_cluster
  right_subset_cluster := P.right_subset_cluster
  left_right_disjoint := P.left_right_disjoint
  left_card := P.left_card
  right_card := P.right_card
  connector := fun i hi => (P.connector i hi).mapLe hGG'
  connector_card := by
    intro i hi
    simpa using P.connector_card i hi
  connector_internally_disjoint_clusters := by
    intro i hi j a
    change (((P.connector i hi).path a).mapLe hGG').InternallyDisjointFromSet
      (P.cluster j)
    simpa [GraphPath.InternallyDisjointFromSet, GraphPath.IsEndpoint] using
      P.connector_internally_disjoint_clusters i hi j a
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij a b
    change GraphPath.NodeDisjoint
      (((P.connector i hi).path a).mapLe hGG')
      (((P.connector j hj).path b).mapLe hGG')
    simpa [GraphPath.NodeDisjoint] using
      P.connector_mutually_nodeDisjoint hi hj hij a b

/-- The first cluster index of a path-of-sets system. -/
def firstIndex (P : PathOfSetsSystem G ell w) : Fin ell :=
  ⟨0, P.length_pos⟩

/-- The last cluster index of a path-of-sets system. -/
def lastIndex (P : PathOfSetsSystem G ell w) : Fin ell :=
  ⟨ell - 1, Nat.sub_lt P.length_pos (by decide : 0 < 1)⟩

@[simp] theorem firstIndex_val (P : PathOfSetsSystem G ell w) :
    (P.firstIndex).1 = 0 := rfl

@[simp] theorem lastIndex_val (P : PathOfSetsSystem G ell w) :
    (P.lastIndex).1 = ell - 1 := rfl

/-- The finite set of all nails in a path-of-sets system. -/
noncomputable def nails (P : PathOfSetsSystem G ell w) : Finset V :=
  Finset.univ.biUnion fun i : Fin ell => P.left i ∪ P.right i

theorem left_subset_nails (P : PathOfSetsSystem G ell w)
    (i : Fin ell) : P.left i ⊆ P.nails := by
  classical
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, Finset.mem_union_left _ hv⟩

theorem right_subset_nails (P : PathOfSetsSystem G ell w)
    (i : Fin ell) : P.right i ⊆ P.nails := by
  classical
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, Finset.mem_union_right _ hv⟩

/-- The previous index of a non-first cluster. -/
def prevIndex (i : Fin ell) (_h : 0 < i.1) : Fin ell :=
  ⟨i.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.1 1) i.2⟩

/-- The predecessor of a non-first cluster is followed by that cluster. -/
theorem prevIndex_succ_lt (i : Fin ell) (h : 0 < i.1) :
    (prevIndex i h).1 + 1 < ell := by
  have hone : 1 ≤ i.1 := Nat.succ_le_of_lt h
  simp [prevIndex, Nat.sub_add_cancel hone, i.2]

@[simp] theorem next_prevIndex_eq (i : Fin ell) (h : 0 < i.1) :
    (⟨(prevIndex i h).1 + 1, prevIndex_succ_lt i h⟩ : Fin ell) = i := by
  apply Fin.ext
  have hone : 1 ≤ i.1 := Nat.succ_le_of_lt h
  simp [prevIndex, Nat.sub_add_cancel hone]

/-- An arbitrary `w'`-element subset of the left nails of one cluster. -/
noncomputable def leftSubsetOfCard (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) : Finset V :=
  Classical.choose (Finset.exists_subset_card_eq (by
    simpa [P.left_card i] using hle : w' ≤ (P.left i).card))

theorem leftSubsetOfCard_subset (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    P.leftSubsetOfCard hle i ⊆ P.left i :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (by
    simpa [P.left_card i] using hle : w' ≤ (P.left i).card))).1

theorem leftSubsetOfCard_card (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    (P.leftSubsetOfCard hle i).card = w' :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (by
    simpa [P.left_card i] using hle : w' ≤ (P.left i).card))).2

/-- An arbitrary `w'`-element subset of the right nails of one cluster. -/
noncomputable def rightSubsetOfCard (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) : Finset V :=
  Classical.choose (Finset.exists_subset_card_eq (by
    simpa [P.right_card i] using hle : w' ≤ (P.right i).card))

theorem rightSubsetOfCard_subset (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    P.rightSubsetOfCard hle i ⊆ P.right i :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (by
    simpa [P.right_card i] using hle : w' ≤ (P.right i).card))).1

theorem rightSubsetOfCard_card (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    (P.rightSubsetOfCard hle i).card = w' :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (by
    simpa [P.right_card i] using hle : w' ≤ (P.right i).card))).2

/-- A chosen `w'`-element subset of the connector paths across a gap. -/
noncomputable def connectorIndexSet (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) (hi : i.1 + 1 < ell) :
    Finset (P.connector i hi).Index :=
  Classical.choose ((P.connector i hi).exists_indexSet_card_eq (by
    simpa [P.connector_card i hi] using hle))

theorem connectorIndexSet_card (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) (hi : i.1 + 1 < ell) :
    (P.connectorIndexSet hle i hi).card = w' :=
  (Classical.choose_spec ((P.connector i hi).exists_indexSet_card_eq (by
    simpa [P.connector_card i hi] using hle))).1

/-- Trimmed left nails for a width restriction.  The first cluster uses an
arbitrary subset; every later cluster uses the target endpoints of the selected
connector paths from the previous gap. -/
noncomputable def leftTrim (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) : Finset V :=
  if h : 0 < i.1 then
    (P.connector (prevIndex i h) (prevIndex_succ_lt i h)).targetSet
      (P.connectorIndexSet hle (prevIndex i h) (prevIndex_succ_lt i h))
  else
    P.leftSubsetOfCard hle i

/-- Trimmed right nails for a width restriction.  All non-last clusters use
the source endpoints of the selected connector paths to the next cluster; the
last cluster uses an arbitrary subset. -/
noncomputable def rightTrim (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) : Finset V :=
  if hi : i.1 + 1 < ell then
    (P.connector i hi).sourceSet (P.connectorIndexSet hle i hi)
  else
    P.rightSubsetOfCard hle i

@[simp] theorem rightTrim_of_gap (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) (hi : i.1 + 1 < ell) :
    P.rightTrim hle i =
      (P.connector i hi).sourceSet (P.connectorIndexSet hle i hi) := by
  simp [rightTrim, hi]

@[simp] theorem leftTrim_of_first (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) (hfirst : ¬ 0 < i.1) :
    P.leftTrim hle i = P.leftSubsetOfCard hle i := by
  simp [leftTrim, hfirst]

@[simp] theorem leftTrim_of_next (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) (hi : i.1 + 1 < ell) :
    P.leftTrim hle ⟨i.1 + 1, hi⟩ =
      (P.connector i hi).targetSet (P.connectorIndexSet hle i hi) := by
  have hpos : 0 < (⟨i.1 + 1, hi⟩ : Fin ell).1 := Nat.succ_pos i.1
  simp [leftTrim, hpos, prevIndex]

theorem leftTrim_subset_left (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    P.leftTrim hle i ⊆ P.left i := by
  by_cases h : 0 < i.1
  · intro v hv
    have htarget :
        (P.connector (prevIndex i h) (prevIndex_succ_lt i h)).targetSet
            (P.connectorIndexSet hle (prevIndex i h)
              (prevIndex_succ_lt i h)) ⊆
          P.left ⟨(prevIndex i h).1 + 1, prevIndex_succ_lt i h⟩ :=
      (P.connector (prevIndex i h) (prevIndex_succ_lt i h)).targetSet_subset_right
        (P.connectorIndexSet hle (prevIndex i h) (prevIndex_succ_lt i h))
    have hv' : v ∈
        P.left ⟨(prevIndex i h).1 + 1, prevIndex_succ_lt i h⟩ :=
      htarget (by simpa [leftTrim, h] using hv)
    simpa [next_prevIndex_eq i h] using hv'
  · intro v hv
    exact P.leftSubsetOfCard_subset hle i (by simpa [leftTrim, h] using hv)

theorem rightTrim_subset_right (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    P.rightTrim hle i ⊆ P.right i := by
  by_cases hi : i.1 + 1 < ell
  · intro v hv
    exact (P.connector i hi).sourceSet_subset_left
      (P.connectorIndexSet hle i hi) (by simpa [rightTrim, hi] using hv)
  · intro v hv
    exact P.rightSubsetOfCard_subset hle i (by simpa [rightTrim, hi] using hv)

theorem leftTrim_card (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    (P.leftTrim hle i).card = w' := by
  by_cases h : 0 < i.1
  · simpa [leftTrim, h] using
      P.connectorIndexSet_card hle (prevIndex i h) (prevIndex_succ_lt i h)
  · simpa [leftTrim, h] using P.leftSubsetOfCard_card hle i

theorem rightTrim_card (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    (P.rightTrim hle i).card = w' := by
  by_cases hi : i.1 + 1 < ell
  · simpa [rightTrim, hi] using
      P.connectorIndexSet_card hle i hi
  · simpa [rightTrim, hi] using P.rightSubsetOfCard_card hle i

/-- Restrict the width of a path-of-sets system by selecting `w'` connector
paths across every gap and keeping the induced endpoint sets. -/
noncomputable def restrictWidth (P : PathOfSetsSystem G ell w)
    {w' : ℕ} (hpos : 0 < w') (hle : w' ≤ w) :
    PathOfSetsSystem G ell w' where
  length_pos := P.length_pos
  width_pos := hpos
  cluster := P.cluster
  cluster_connected := P.cluster_connected
  cluster_disjoint := P.cluster_disjoint
  left := P.leftTrim hle
  right := P.rightTrim hle
  left_subset_cluster := by
    intro i v hv
    exact P.left_subset_cluster i (P.leftTrim_subset_left hle i hv)
  right_subset_cluster := by
    intro i v hv
    exact P.right_subset_cluster i (P.rightTrim_subset_right hle i hv)
  left_right_disjoint := by
    intro i
    rw [Finset.disjoint_left]
    intro v hvleft hvright
    exact Finset.disjoint_left.mp (P.left_right_disjoint i)
      (P.leftTrim_subset_left hle i hvleft)
      (P.rightTrim_subset_right hle i hvright)
  left_card := P.leftTrim_card hle
  right_card := P.rightTrim_card hle
  connector := by
    intro i hi
    exact ((P.connector i hi).restrictIndexSet
      (P.connectorIndexSet hle i hi)).copyTerminals
        (by simp [rightTrim, hi])
        (by simp [leftTrim_of_next])
  connector_card := by
    intro i hi
    rw [PerfectPathPacking.copyTerminals_card]
    rw [(P.connector i hi).restrictIndexSet_card (P.connectorIndexSet hle i hi)]
    exact P.connectorIndexSet_card hle i hi
  connector_internally_disjoint_clusters := by
    intro i hi j a
    simpa [rightTrim, hi, leftTrim_of_next, PerfectPathPacking.copyTerminals] using
      P.connector_internally_disjoint_clusters i hi j a.1
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij a b
    simpa [rightTrim, hi, hj, leftTrim_of_next,
      PerfectPathPacking.copyTerminals, GraphPath.NodeDisjoint] using
      P.connector_mutually_nodeDisjoint hi hj hij a.1 b.1

/-- Restrict a path-of-sets system to its first `ell'` clusters.

This is the length-thinning operation used when a downstream theorem requires
an exact length but the construction supplies a longer system.  The width is
unchanged, and each connector is the corresponding connector in the original
system under the order embedding `Fin ell' → Fin ell`.
-/
noncomputable def restrictLength (P : PathOfSetsSystem G ell w)
    {ell' : ℕ} (hpos : 0 < ell') (hle : ell' ≤ ell) :
    PathOfSetsSystem G ell' w where
  length_pos := hpos
  width_pos := P.width_pos
  cluster := fun i => P.cluster (Fin.castLE hle i)
  cluster_connected := fun i => P.cluster_connected (Fin.castLE hle i)
  cluster_disjoint := by
    intro i j hij
    apply P.cluster_disjoint
    intro h
    apply hij
    exact Fin.ext (by simpa [Fin.val_castLE] using congrArg Fin.val h)
  left := fun i => P.left (Fin.castLE hle i)
  right := fun i => P.right (Fin.castLE hle i)
  left_subset_cluster := fun i => P.left_subset_cluster (Fin.castLE hle i)
  right_subset_cluster := fun i => P.right_subset_cluster (Fin.castLE hle i)
  left_right_disjoint := fun i => P.left_right_disjoint (Fin.castLE hle i)
  left_card := fun i => P.left_card (Fin.castLE hle i)
  right_card := fun i => P.right_card (Fin.castLE hle i)
  connector := by
    intro i hi
    have hi' : (Fin.castLE hle i).1 + 1 < ell := by
      simpa [Fin.val_castLE] using lt_of_lt_of_le hi hle
    simpa [Fin.val_castLE] using P.connector (Fin.castLE hle i) hi'
  connector_card := by
    intro i hi
    have hi' : (Fin.castLE hle i).1 + 1 < ell := by
      simpa [Fin.val_castLE] using lt_of_lt_of_le hi hle
    simpa [Fin.val_castLE] using P.connector_card (Fin.castLE hle i) hi'
  connector_internally_disjoint_clusters := by
    intro i hi j
    have hi' : (Fin.castLE hle i).1 + 1 < ell := by
      simpa [Fin.val_castLE] using lt_of_lt_of_le hi hle
    simpa [Fin.val_castLE] using
      P.connector_internally_disjoint_clusters
        (Fin.castLE hle i) hi' (Fin.castLE hle j)
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij
    have hi' : (Fin.castLE hle i).1 + 1 < ell := by
      simpa [Fin.val_castLE] using lt_of_lt_of_le hi hle
    have hj' : (Fin.castLE hle j).1 + 1 < ell := by
      simpa [Fin.val_castLE] using lt_of_lt_of_le hj hle
    apply P.connector_mutually_nodeDisjoint hi' hj'
    intro h
    apply hij
    exact Fin.ext (by simpa [Fin.val_castLE] using congrArg Fin.val h)

end PathOfSetsSystem

/-- A weak Path-of-Sets System: within each cluster the union of the two nail
sets is edge-well-linked. -/
structure WeakPathOfSetsSystem {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (ell w : ℕ)
    extends PathOfSetsSystem G ell w where
  /-- The nails in each cluster are edge-well-linked in that cluster. -/
  nails_edgeWellLinked :
    ∀ i : Fin ell, EdgeWellLinkedIn G (cluster i) (left i ∪ right i)

namespace WeakPathOfSetsSystem

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {ell w : ℕ}

/-- View a weak path-of-sets system inside a same-vertex supergraph. -/
def mapLe (P : WeakPathOfSetsSystem G ell w) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') : WeakPathOfSetsSystem G' ell w where
  toPathOfSetsSystem := P.toPathOfSetsSystem.mapLe hGG'
  nails_edgeWellLinked := by
    intro i
    exact EdgeWellLinkedIn.mono_graph (P.nails_edgeWellLinked i) hGG'

/-- Restrict a weak path-of-sets system to its first `ell'` clusters. -/
noncomputable def restrictLength (P : WeakPathOfSetsSystem G ell w)
    {ell' : ℕ} (hpos : 0 < ell') (hle : ell' ≤ ell) :
    WeakPathOfSetsSystem G ell' w where
  toPathOfSetsSystem := P.toPathOfSetsSystem.restrictLength hpos hle
  nails_edgeWellLinked := by
    intro i
    simpa [PathOfSetsSystem.restrictLength] using
      P.nails_edgeWellLinked (Fin.castLE hle i)

/-- Restrict the width of a weak path-of-sets system. -/
noncomputable def restrictWidth (P : WeakPathOfSetsSystem G ell w)
    {w' : ℕ} (hpos : 0 < w') (hle : w' ≤ w) :
    WeakPathOfSetsSystem G ell w' where
  toPathOfSetsSystem := P.toPathOfSetsSystem.restrictWidth hpos hle
  nails_edgeWellLinked := by
    intro i
    apply (P.nails_edgeWellLinked i).mono_terminals
    intro v hv
    rcases Finset.mem_union.mp hv with hvleft | hvright
    · exact Finset.mem_union_left _ <|
        P.toPathOfSetsSystem.leftTrim_subset_left hle i hvleft
    · exact Finset.mem_union_right _ <|
        P.toPathOfSetsSystem.rightTrim_subset_right hle i hvright

end WeakPathOfSetsSystem

/-- A strong Path-of-Sets System: each nail side is node-well-linked and the two
sides are linked inside every cluster. -/
structure StrongPathOfSetsSystem {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (ell w : ℕ)
    extends PathOfSetsSystem G ell w where
  /-- The left nails are node-well-linked in their cluster. -/
  left_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (cluster i) (left i)
  /-- The right nails are node-well-linked in their cluster. -/
  right_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (cluster i) (right i)
  /-- The left and right nail sets are linked in their cluster. -/
  left_right_nodeLinked :
    ∀ i : Fin ell, NodeLinkedIn G (cluster i) (left i) (right i)

namespace StrongPathOfSetsSystem

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {ell w : ℕ}

/-- View a strong path-of-sets system inside a same-vertex supergraph. -/
def mapLe (P : StrongPathOfSetsSystem G ell w) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') : StrongPathOfSetsSystem G' ell w where
  toPathOfSetsSystem := P.toPathOfSetsSystem.mapLe hGG'
  left_nodeWellLinked := by
    intro i
    exact NodeWellLinkedIn.mono_graph (P.left_nodeWellLinked i) hGG'
  right_nodeWellLinked := by
    intro i
    exact NodeWellLinkedIn.mono_graph (P.right_nodeWellLinked i) hGG'
  left_right_nodeLinked := by
    intro i
    exact NodeLinkedIn.mono_graph (P.left_right_nodeLinked i) hGG'

/-- The left and right nails in each strong cluster have the same cardinality. -/
theorem left_card_eq_right_card
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    (P.left i).card = (P.right i).card := by
  rw [P.left_card i, P.right_card i]

/-- The strong linkage field supplies a full-width path packing from the left
nails to the right nails inside each cluster. -/
theorem exists_left_right_linkage
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ Q : PathPacking G (P.left i) (P.right i),
      Q.card = w ∧ Q.StaysIn (P.cluster i) := by
  rcases NodeLinkedIn.exists_pathPacking (P.left_right_nodeLinked i) with
    ⟨Q, hcard, hstay⟩
  refine ⟨Q, ?_, hstay⟩
  simpa [P.left_card i, P.right_card i] using hcard

/-- The strong linkage field supplies an oriented perfect full-width packing
from the left nails to the right nails inside each cluster. -/
theorem exists_left_right_perfect_linkage
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ Q : PerfectPathPacking G (P.left i) (P.right i),
      Q.card = w ∧ Q.toPathPacking.StaysIn (P.cluster i) := by
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      (P.left_right_nodeLinked i) (P.left_card_eq_right_card i) with
    ⟨Q, hQcard, hstay⟩
  exact ⟨Q, hQcard.trans (P.left_card i), hstay⟩

/-- A cluster-internal left-to-right path can be concatenated with the connector
to the next cluster without repeating vertices. -/
theorem left_right_connector_concat_isPath
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i)) :
    ∀ a : Q.Index,
      ((Q.path a).walk.append
        (((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) a) rfl)).IsPath := by
  intro a
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (Q.path a)
    ((P.connector i hi).path
      (Q.indexOfSourceTarget (P.connector i hi) a))
    (PerfectPathPacking.source_indexOfSourceTarget Q
      (P.connector i hi) a).symm ?_
  intro v hvQ hvConn
  have hv_cluster : v ∈ P.cluster i := hQstay a hvQ
  have hendpoint :=
    P.connector_internally_disjoint_clusters i hi i
      (Q.indexOfSourceTarget (P.connector i hi) a) hvConn hv_cluster
  rcases hendpoint with hsource | htarget
  · exact hsource.trans
      (PerfectPathPacking.source_indexOfSourceTarget Q
        (P.connector i hi) a)
  · have htarget_cluster :
        ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) a)).target ∈
            P.cluster ⟨i.1 + 1, hi⟩ :=
      P.left_subset_cluster ⟨i.1 + 1, hi⟩
        ((P.connector i hi).target_mem
          (Q.indexOfSourceTarget (P.connector i hi) a))
    have hnext_ne : (⟨i.1 + 1, hi⟩ : Fin ell) ≠ i := by
      intro h
      have hval := congrArg Fin.val h
      exact Nat.succ_ne_self i.1 hval
    exact False.elim
      (Finset.disjoint_left.mp (P.cluster_disjoint hnext_ne)
        htarget_cluster (by simpa [htarget] using hv_cluster))

/-- The concatenated paths from a cluster-internal linkage followed by the next
connector remain pairwise node-disjoint. -/
theorem left_right_connector_concat_nodeDisjoint
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i))
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath) :
    Pairwise fun a b =>
      GraphPath.NodeDisjoint
        ((Q.path a).appendWithEq
          ((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a))
          (PerfectPathPacking.source_indexOfSourceTarget Q
            (P.connector i hi) a).symm
          (hpath a))
        ((Q.path b).appendWithEq
          ((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) b))
          (PerfectPathPacking.source_indexOfSourceTarget Q
            (P.connector i hi) b).symm
          (hpath b)) := by
  classical
  have hcross :
      ∀ ⦃a b : Q.Index⦄, a ≠ b → ∀ ⦃v : V⦄,
        v ∈ (Q.path a).vertexSet →
        v ∈ ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) b)).vertexSet →
        False := by
    intro a b hab v hvQ hvConn
    have hv_cluster : v ∈ P.cluster i := hQstay a hvQ
    have hendpoint :=
      P.connector_internally_disjoint_clusters i hi i
        (Q.indexOfSourceTarget (P.connector i hi) b) hvConn hv_cluster
    rcases hendpoint with hsource | htarget
    · have hv_eq_target : v = (Q.path b).target := by
        exact hsource.trans
          (PerfectPathPacking.source_indexOfSourceTarget Q
            (P.connector i hi) b)
      have hvQb : v ∈ (Q.path b).vertexSet := by
        simp [hv_eq_target]
      exact Finset.disjoint_left.mp (Q.toPathPacking.node_disjoint hab)
        hvQ hvQb
    · have htarget_cluster :
          ((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) b)).target ∈
              P.cluster ⟨i.1 + 1, hi⟩ :=
        P.left_subset_cluster ⟨i.1 + 1, hi⟩
          ((P.connector i hi).target_mem
            (Q.indexOfSourceTarget (P.connector i hi) b))
      have hnext_ne : (⟨i.1 + 1, hi⟩ : Fin ell) ≠ i := by
        intro h
        have hval := congrArg Fin.val h
        exact Nat.succ_ne_self i.1 hval
      exact Finset.disjoint_left.mp (P.cluster_disjoint hnext_ne)
        htarget_cluster (by simpa [htarget] using hv_cluster)
  intro a b hab
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvA hvB
  have hvA_union :
      v ∈ (Q.path a).vertexSet ∨
        v ∈ ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) a)).vertexSet := by
    have hsubset :=
      GraphPath.appendWithEq_vertexSet_subset
        (Q.path a)
        ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) a))
        (PerfectPathPacking.source_indexOfSourceTarget Q
          (P.connector i hi) a).symm
        (hpath a) hvA
    simpa [Finset.mem_union] using hsubset
  have hvB_union :
      v ∈ (Q.path b).vertexSet ∨
        v ∈ ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) b)).vertexSet := by
    have hsubset :=
      GraphPath.appendWithEq_vertexSet_subset
        (Q.path b)
        ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) b))
        (PerfectPathPacking.source_indexOfSourceTarget Q
          (P.connector i hi) b).symm
        (hpath b) hvB
    simpa [Finset.mem_union] using hsubset
  rcases hvA_union with hvQa | hvConna
  · rcases hvB_union with hvQb | hvConnb
    · exact Finset.disjoint_left.mp (Q.toPathPacking.node_disjoint hab)
        hvQa hvQb
    · exact hcross hab hvQa hvConnb
  · rcases hvB_union with hvQb | hvConnb
    · exact hcross hab.symm hvQb hvConna
    · have hconn_ne :
          Q.indexOfSourceTarget (P.connector i hi) a ≠
            Q.indexOfSourceTarget (P.connector i hi) b := by
        intro hconn
        have htargets : (Q.path a).target = (Q.path b).target := by
          have hs :=
            congrArg (fun q => ((P.connector i hi).path q).source) hconn
          exact (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) a).symm.trans
            (hs.trans
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) b))
        exact hab (Q.target_bijective.1 (Subtype.ext htargets))
      exact Finset.disjoint_left.mp
        ((P.connector i hi).toPathPacking.node_disjoint hconn_ne)
        hvConna hvConnb

/-- Each concatenated left-to-next path stays inside the current cluster plus
the connector path set across the next gap. -/
theorem left_right_connector_append_vertexSet_subset
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i))
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath)
    (a : Q.Index) :
    ((Q.path a).appendWithEq
      ((P.connector i hi).path
        (Q.indexOfSourceTarget (P.connector i hi) a))
      (PerfectPathPacking.source_indexOfSourceTarget Q
        (P.connector i hi) a).symm
      (hpath a)).vertexSet ⊆
        P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet := by
  classical
  intro v hv
  have hsubset :=
    GraphPath.appendWithEq_vertexSet_subset
      (Q.path a)
      ((P.connector i hi).path
        (Q.indexOfSourceTarget (P.connector i hi) a))
      (PerfectPathPacking.source_indexOfSourceTarget Q
        (P.connector i hi) a).symm
      (hpath a) hv
  rcases Finset.mem_union.mp hsubset with hvQ | hvConn
  · exact Finset.mem_union_left _ (hQstay a hvQ)
  · exact Finset.mem_union_right _ (by
      exact Finset.mem_biUnion.mpr
        ⟨Q.indexOfSourceTarget (P.connector i hi) a, by simp, hvConn⟩)

/-- The trace of a one-step left-to-next path in its source cluster is exactly
the internal left-to-right linkage used to construct it. -/
theorem left_right_connector_append_inter_current_cluster_eq
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i))
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath)
    (a : Q.Index) :
    ((Q.path a).appendWithEq
        ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) a))
        (PerfectPathPacking.source_indexOfSourceTarget Q
          (P.connector i hi) a).symm
        (hpath a)).vertexSet ∩ P.cluster i =
      (Q.path a).vertexSet := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvAppend, hvCluster⟩
    have hsubset :=
      GraphPath.appendWithEq_vertexSet_subset
        (Q.path a)
        ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) a))
        (PerfectPathPacking.source_indexOfSourceTarget Q
          (P.connector i hi) a).symm
        (hpath a) hvAppend
    rcases Finset.mem_union.mp hsubset with hvQ | hvConnector
    · exact hvQ
    · have hendpoint :=
        P.connector_internally_disjoint_clusters i hi i
          (Q.indexOfSourceTarget (P.connector i hi) a)
          hvConnector hvCluster
      rcases hendpoint with hsource | htarget
      · have hglue :
          ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) a)).source =
            (Q.path a).target :=
        PerfectPathPacking.source_indexOfSourceTarget Q
          (P.connector i hi) a
        simpa [hsource, hglue] using
          GraphPath.target_mem_vertexSet (Q.path a)
      · have htargetCluster :
          ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) a)).target ∈
            P.cluster ⟨i.1 + 1, hi⟩ :=
        P.left_subset_cluster ⟨i.1 + 1, hi⟩
          ((P.connector i hi).target_mem
            (Q.indexOfSourceTarget (P.connector i hi) a))
        have hne : i ≠ (⟨i.1 + 1, hi⟩ : Fin ell) := by
          intro h
          have hval := congrArg Fin.val h
          exact Nat.succ_ne_self i.1 hval.symm
        exact False.elim
          (Finset.disjoint_left.mp (P.cluster_disjoint hne)
            hvCluster (by simpa [htarget] using htargetCluster))
  · intro v hvQ
    exact Finset.mem_inter.mpr
      ⟨GraphPath.left_vertexSet_subset_appendWithEq
          (Q.path a)
          ((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a))
          (PerfectPathPacking.source_indexOfSourceTarget Q
            (P.connector i hi) a).symm
          (hpath a) hvQ,
        hQstay a hvQ⟩

/-- A one-step concatenated path meets the next cluster only at its target. -/
theorem left_right_connector_append_meets_next_cluster_only_at_target
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i))
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath)
    (a : Q.Index) :
    ∀ ⦃v : V⦄,
      v ∈ ((Q.path a).appendWithEq
        ((P.connector i hi).path
          (Q.indexOfSourceTarget (P.connector i hi) a))
        (PerfectPathPacking.source_indexOfSourceTarget Q
          (P.connector i hi) a).symm
        (hpath a)).vertexSet →
      v ∈ P.cluster ⟨i.1 + 1, hi⟩ →
        v =
          ((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).target := by
  intro v hvAppend hvNext
  have hnext_ne_i : i ≠ (⟨i.1 + 1, hi⟩ : Fin ell) := by
    intro h
    have hval := congrArg Fin.val h
    exact Nat.succ_ne_self i.1 hval.symm
  have hsubset :=
    GraphPath.appendWithEq_vertexSet_subset
      (Q.path a)
      ((P.connector i hi).path
        (Q.indexOfSourceTarget (P.connector i hi) a))
      (PerfectPathPacking.source_indexOfSourceTarget Q
        (P.connector i hi) a).symm
      (hpath a) hvAppend
  rcases Finset.mem_union.mp hsubset with hvQ | hvConn
  · have hv_i : v ∈ P.cluster i := hQstay a hvQ
    exact False.elim
      (Finset.disjoint_left.mp (P.cluster_disjoint hnext_ne_i)
        hv_i hvNext)
  · have hendpoint :=
      P.connector_internally_disjoint_clusters i hi ⟨i.1 + 1, hi⟩
        (Q.indexOfSourceTarget (P.connector i hi) a) hvConn hvNext
    rcases hendpoint with hsource | htarget
    · have hsource_cluster :
          ((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).source ∈
              P.cluster i :=
        P.right_subset_cluster i
          ((P.connector i hi).source_mem
            (Q.indexOfSourceTarget (P.connector i hi) a))
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hnext_ne_i)
          hsource_cluster (by simpa [hsource] using hvNext))
    · exact htarget

/-- The perfect packing obtained by concatenating a cluster-internal linkage
with the next connector stays in the current cluster plus that connector
family. -/
theorem left_right_connector_concat_staysIn
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i))
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath)
    (hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((Q.path a).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) a))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) a).symm
            (hpath a))
          ((Q.path b).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) b))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) b).symm
    (hpath b))) :
    (Q.concat (P.connector i hi) hpath hnode).toPathPacking.StaysIn
      (P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet) := by
  intro a
  exact P.left_right_connector_append_vertexSet_subset i hi Q hQstay hpath a

/-- The one-step perfect packing is internally disjoint from the next cluster:
the only vertices it uses in that cluster are the target endpoints. -/
theorem left_right_connector_concat_internallyDisjoint_nextCluster
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i))
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath)
    (hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((Q.path a).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) a))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) a).symm
            (hpath a))
          ((Q.path b).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) b))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) b).symm
            (hpath b))) :
    PathPacking.InternallyDisjointFromSet
      ((Q.concat (P.connector i hi) hpath hnode).toPathPacking)
      (P.cluster ⟨i.1 + 1, hi⟩) := by
  intro a v hv hvNext
  right
  exact P.left_right_connector_append_meets_next_cluster_only_at_target
    i hi Q hQstay hpath a hv hvNext

/-- A connector across the gap `i -> i + 1` is node-disjoint from every
non-incident cluster. -/
theorem connector_vertexSet_disjoint_cluster_of_ne
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) (j : Fin ell)
    (hji : j ≠ i) (hjn : j ≠ ⟨i.1 + 1, hi⟩) :
    Disjoint (P.connector i hi).toPathPacking.vertexSet (P.cluster j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvConn hvCluster
  have hvConn' :
      v ∈ Finset.univ.biUnion fun a : (P.connector i hi).Index =>
        ((P.connector i hi).path a).vertexSet := by
    simpa [PathPacking.vertexSet] using hvConn
  rcases Finset.mem_biUnion.mp hvConn' with ⟨a, _ha, hvPath⟩
  have hendpoint :=
    P.connector_internally_disjoint_clusters i hi j a hvPath hvCluster
  rcases hendpoint with hsource | htarget
  · have hsource_cluster :
        ((P.connector i hi).path a).source ∈ P.cluster i :=
      P.right_subset_cluster i ((P.connector i hi).source_mem a)
    have hij : i ≠ j := fun h => hji h.symm
    exact Finset.disjoint_left.mp (P.cluster_disjoint hij)
      hsource_cluster (by simpa [hsource] using hvCluster)
  · have htarget_cluster :
        ((P.connector i hi).path a).target ∈ P.cluster ⟨i.1 + 1, hi⟩ :=
      P.left_subset_cluster ⟨i.1 + 1, hi⟩
        ((P.connector i hi).target_mem a)
    have hnextj : (⟨i.1 + 1, hi⟩ : Fin ell) ≠ j := fun h => hjn h.symm
    exact Finset.disjoint_left.mp (P.cluster_disjoint hnextj)
      htarget_cluster (by simpa [htarget] using hvCluster)

/-- Concatenating a perfect left-to-right linkage in cluster `i` with the
connector across the next gap gives a perfect packing from the left nails of
cluster `i` to the left nails of cluster `i + 1`. -/
theorem exists_left_next_perfect_linkage_of_concat
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQcard : Q.card = w)
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath)
    (hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((Q.path a).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) a))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) a).symm
            (hpath a))
          ((Q.path b).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) b))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) b).symm
            (hpath b))) :
    ∃ R : PerfectPathPacking G (P.left i) (P.left ⟨i.1 + 1, hi⟩),
      R.card = w := by
  refine ⟨Q.concat (P.connector i hi) hpath hnode, ?_⟩
  simpa using hQcard

/-- Version of `exists_left_next_perfect_linkage_of_concat` that records where
the concatenated paths live. -/
theorem exists_left_next_perfect_linkage_of_concat_with_staysIn
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (Q : PerfectPathPacking G (P.left i) (P.right i))
    (hQcard : Q.card = w)
    (hQstay : Q.toPathPacking.StaysIn (P.cluster i))
    (hpath :
      ∀ a : Q.Index,
        ((Q.path a).walk.append
          (((P.connector i hi).path
            (Q.indexOfSourceTarget (P.connector i hi) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget Q
                (P.connector i hi) a) rfl)).IsPath)
    (hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((Q.path a).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) a))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) a).symm
            (hpath a))
          ((Q.path b).appendWithEq
            ((P.connector i hi).path
              (Q.indexOfSourceTarget (P.connector i hi) b))
            (PerfectPathPacking.source_indexOfSourceTarget Q
              (P.connector i hi) b).symm
            (hpath b))) :
    ∃ R : PerfectPathPacking G (P.left i) (P.left ⟨i.1 + 1, hi⟩),
      R.card = w ∧
        R.toPathPacking.StaysIn
          (P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet) := by
  refine ⟨Q.concat (P.connector i hi) hpath hnode, ?_, ?_⟩
  · simpa using hQcard
  · exact P.left_right_connector_concat_staysIn i hi Q hQstay hpath hnode

/-- A strong path-of-sets system supplies a full-width perfect packing from the
left nails of a cluster to the left nails of the next cluster. -/
theorem exists_left_next_perfect_linkage
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    ∃ R : PerfectPathPacking G (P.left i) (P.left ⟨i.1 + 1, hi⟩),
      R.card = w := by
  rcases P.exists_left_right_perfect_linkage i with ⟨Q, hQcard, hQstay⟩
  let hpath := P.left_right_connector_concat_isPath i hi Q hQstay
  exact P.exists_left_next_perfect_linkage_of_concat i hi Q hQcard hpath
    (P.left_right_connector_concat_nodeDisjoint i hi Q hQstay hpath)

/-- Region-aware version of `exists_left_next_perfect_linkage`. -/
theorem exists_left_next_perfect_linkage_with_staysIn
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    ∃ R : PerfectPathPacking G (P.left i) (P.left ⟨i.1 + 1, hi⟩),
      R.card = w ∧
        R.toPathPacking.StaysIn
          (P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet) := by
  rcases P.exists_left_right_perfect_linkage i with ⟨Q, hQcard, hQstay⟩
  let hpath := P.left_right_connector_concat_isPath i hi Q hQstay
  let hnode := P.left_right_connector_concat_nodeDisjoint i hi Q hQstay hpath
  exact P.exists_left_next_perfect_linkage_of_concat_with_staysIn i hi Q
    hQcard hQstay hpath hnode

/-- One-step left-to-next linkage with both region and next-cluster
intersection invariants exposed. -/
theorem exists_left_next_perfect_linkage_with_invariants
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    ∃ R : PerfectPathPacking G (P.left i) (P.left ⟨i.1 + 1, hi⟩),
      R.card = w ∧
        R.toPathPacking.StaysIn
          (P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet) ∧
        R.toPathPacking.InternallyDisjointFromSet
          (P.cluster ⟨i.1 + 1, hi⟩) := by
  rcases P.exists_left_right_perfect_linkage i with ⟨Q, hQcard, hQstay⟩
  let hpath := P.left_right_connector_concat_isPath i hi Q hQstay
  let hnode := P.left_right_connector_concat_nodeDisjoint i hi Q hQstay hpath
  refine ⟨Q.concat (P.connector i hi) hpath hnode, ?_, ?_, ?_⟩
  · simpa using hQcard
  · exact P.left_right_connector_concat_staysIn i hi Q hQstay hpath hnode
  · exact P.left_right_connector_concat_internallyDisjoint_nextCluster
      i hi Q hQstay hpath hnode

/-- A chosen one-step perfect packing from the left nails of cluster `i` to the
left nails of cluster `i + 1`.  The accompanying lemmas expose the cardinality
and separation invariants supplied by
`exists_left_next_perfect_linkage_with_invariants`. -/
noncomputable def leftNextPacking
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    PerfectPathPacking G (P.left i) (P.left ⟨i.1 + 1, hi⟩) :=
  Classical.choose (P.exists_left_next_perfect_linkage_with_invariants i hi)

@[simp] theorem leftNextPacking_card
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    (P.leftNextPacking i hi).card = w :=
  (Classical.choose_spec
    (P.exists_left_next_perfect_linkage_with_invariants i hi)).1

/-- The chosen one-step packing stays inside the current cluster plus the
connector path family crossing to the next cluster. -/
theorem leftNextPacking_staysIn
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    (P.leftNextPacking i hi).toPathPacking.StaysIn
      (P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet) :=
  (Classical.choose_spec
    (P.exists_left_next_perfect_linkage_with_invariants i hi)).2.1

/-- The chosen one-step packing meets the next cluster only at its terminal
endpoints. -/
theorem leftNextPacking_internallyDisjoint_nextCluster
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    (P.leftNextPacking i hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster ⟨i.1 + 1, hi⟩) :=
  (Classical.choose_spec
    (P.exists_left_next_perfect_linkage_with_invariants i hi)).2.2

/-- The chosen one-step packing across gap `i` is disjoint from the connector
across the following gap. -/
theorem leftNextPacking_vertexSet_disjoint_nextConnector
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell) :
    Disjoint (P.leftNextPacking i hi).toPathPacking.vertexSet
      (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvThread hvNextConnector
  have hv_region :=
    PathPacking.vertexSet_subset_of_staysIn
      (P := (P.leftNextPacking i hi).toPathPacking)
      (P.leftNextPacking_staysIn i hi) hvThread
  rcases Finset.mem_union.mp hv_region with hvCluster | hvConnector
  · have hcluster_disj :
        Disjoint (P.cluster i)
          (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet := by
      exact (P.connector_vertexSet_disjoint_cluster_of_ne
        ⟨i.1 + 1, hi⟩ hnext i
        (by
          intro h
          have hval := congrArg Fin.val h
          simp at hval)
        (by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
          omega)).symm
    exact Finset.disjoint_left.mp hcluster_disj hvCluster hvNextConnector
  · have hconnector_disj :
        Disjoint (P.connector i hi).toPathPacking.vertexSet
          (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet := by
      exact PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (P.connector_mutually_nodeDisjoint hi hnext (by
          intro h
          have hval := congrArg Fin.val h
          simp at hval))
    exact Finset.disjoint_left.mp hconnector_disj hvConnector hvNextConnector

/-- The chosen one-step packing across gap `i` can be concatenated with the
chosen one-step packing across the following gap without repeating vertices. -/
theorem leftNext_leftNext_concat_isPath
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell) :
    ∀ a : (P.leftNextPacking i hi).Index,
      (((P.leftNextPacking i hi).path a).walk.append
        (((P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext).path
          ((P.leftNextPacking i hi).indexOfSourceTarget
            (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a)).walk.copy
            (PerfectPathPacking.source_indexOfSourceTarget
              (P.leftNextPacking i hi)
              (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a) rfl)).IsPath := by
  intro a
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    ((P.leftNextPacking i hi).path a)
    ((P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext).path
      ((P.leftNextPacking i hi).indexOfSourceTarget
        (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a))
    (PerfectPathPacking.source_indexOfSourceTarget
      (P.leftNextPacking i hi)
      (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a).symm ?_
  intro v hvFirst hvSecond
  let i₁ : Fin ell := ⟨i.1 + 1, hi⟩
  let Q := P.leftNextPacking i₁ hnext
  let b := (P.leftNextPacking i hi).indexOfSourceTarget Q a
  have hvSecond_total : v ∈ Q.toPathPacking.vertexSet :=
    Q.toPathPacking.path_vertexSet_subset_vertexSet b (by simpa [Q, b, i₁] using hvSecond)
  have hvSecond_region :
      v ∈ P.cluster i₁ ∪ (P.connector i₁ hnext).toPathPacking.vertexSet :=
    PathPacking.vertexSet_subset_of_staysIn
      (P := Q.toPathPacking)
      (by
        simpa [Q, i₁] using P.leftNextPacking_staysIn i₁ hnext)
      hvSecond_total
  rcases Finset.mem_union.mp hvSecond_region with hvCluster | hvConnector
  · have hendpoint :=
      P.leftNextPacking_internallyDisjoint_nextCluster i hi a hvFirst
        (by simpa [i₁] using hvCluster)
    rcases hendpoint with hsource | htarget
    · have hsource_cluster :
          ((P.leftNextPacking i hi).path a).source ∈ P.cluster i :=
        P.left_subset_cluster i ((P.leftNextPacking i hi).source_mem a)
      have hi_ne_i₁ : i ≠ i₁ := by
        intro h
        have hval := congrArg Fin.val h
        simp [i₁] at hval
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hi_ne_i₁)
          hsource_cluster (by simpa [hsource, i₁] using hvCluster))
    · exact htarget
  · have hvFirst_total :
        v ∈ (P.leftNextPacking i hi).toPathPacking.vertexSet :=
      (P.leftNextPacking i hi).toPathPacking.path_vertexSet_subset_vertexSet a
        hvFirst
    exact False.elim
      (Finset.disjoint_left.mp
        (P.leftNextPacking_vertexSet_disjoint_nextConnector i hi hnext)
        hvFirst_total (by simpa [i₁] using hvConnector))

/-- The two-step concatenations of adjacent chosen one-step packings are
pairwise node-disjoint. -/
theorem leftNext_leftNext_concat_nodeDisjoint
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell)
    (hpath :
      ∀ a : (P.leftNextPacking i hi).Index,
        (((P.leftNextPacking i hi).path a).walk.append
          (((P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext).path
            ((P.leftNextPacking i hi).indexOfSourceTarget
              (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget
                (P.leftNextPacking i hi)
                (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a) rfl)).IsPath) :
    Pairwise fun a b =>
      GraphPath.NodeDisjoint
        (((P.leftNextPacking i hi).path a).appendWithEq
          ((P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext).path
            ((P.leftNextPacking i hi).indexOfSourceTarget
              (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a))
          (PerfectPathPacking.source_indexOfSourceTarget
            (P.leftNextPacking i hi)
            (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) a).symm
          (hpath a))
        (((P.leftNextPacking i hi).path b).appendWithEq
          ((P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext).path
            ((P.leftNextPacking i hi).indexOfSourceTarget
              (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) b))
          (PerfectPathPacking.source_indexOfSourceTarget
            (P.leftNextPacking i hi)
            (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) b).symm
          (hpath b)) := by
  classical
  let R := P.leftNextPacking i hi
  let i₁ : Fin ell := ⟨i.1 + 1, hi⟩
  let Q := P.leftNextPacking i₁ hnext
  have hcross :
      ∀ ⦃a b : R.Index⦄, a ≠ b → ∀ ⦃v : V⦄,
        v ∈ (R.path a).vertexSet →
        v ∈ (Q.path (R.indexOfSourceTarget Q b)).vertexSet →
        False := by
    intro a b hab v hvR hvQ
    have hvQ_total : v ∈ Q.toPathPacking.vertexSet :=
      Q.toPathPacking.path_vertexSet_subset_vertexSet
        (R.indexOfSourceTarget Q b) hvQ
    have hvQ_region :
        v ∈ P.cluster i₁ ∪ (P.connector i₁ hnext).toPathPacking.vertexSet :=
      PathPacking.vertexSet_subset_of_staysIn
        (P := Q.toPathPacking)
        (by simpa [Q, i₁] using P.leftNextPacking_staysIn i₁ hnext)
        hvQ_total
    rcases Finset.mem_union.mp hvQ_region with hvCluster | hvConnector
    · have hendpoint :=
        P.leftNextPacking_internallyDisjoint_nextCluster i hi a
          (by simpa [R] using hvR) (by simpa [i₁] using hvCluster)
      rcases hendpoint with hsource | htarget
      · have hsource_cluster :
            (R.path a).source ∈ P.cluster i :=
          P.left_subset_cluster i (by simpa [R] using R.source_mem a)
        have hi_ne_i₁ : i ≠ i₁ := by
          intro h
          have hval := congrArg Fin.val h
          simp [i₁] at hval
        exact Finset.disjoint_left.mp (P.cluster_disjoint hi_ne_i₁)
          hsource_cluster (by simpa [R, hsource, i₁] using hvCluster)
      · have hv_left : v ∈ P.left i₁ := by
          simpa [R, htarget, i₁] using R.target_mem a
        have hv_source_Q :
            v = (Q.path (R.indexOfSourceTarget Q b)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (R.indexOfSourceTarget Q b) (by simpa [Q, i₁] using hv_left) hvQ
        have htargets : (R.path a).target = (R.path b).target := by
          calc
            (R.path a).target = v := by simpa [R] using htarget.symm
            _ = (Q.path (R.indexOfSourceTarget Q b)).source := hv_source_Q
            _ = (R.path b).target :=
              (PerfectPathPacking.source_indexOfSourceTarget R Q b)
        exact hab (R.target_bijective.1 (Subtype.ext htargets))
    · have hvR_total : v ∈ R.toPathPacking.vertexSet :=
        R.toPathPacking.path_vertexSet_subset_vertexSet a hvR
      exact Finset.disjoint_left.mp
        (by simpa [R, Q, i₁] using
          P.leftNextPacking_vertexSet_disjoint_nextConnector i hi hnext)
        hvR_total (by simpa [Q, i₁] using hvConnector)
  intro a b hab
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvA hvB
  have hvA_union :
      v ∈ (R.path a).vertexSet ∨
        v ∈ (Q.path (R.indexOfSourceTarget Q a)).vertexSet := by
    have hsubset :=
      GraphPath.appendWithEq_vertexSet_subset
        (R.path a) (Q.path (R.indexOfSourceTarget Q a))
        (PerfectPathPacking.source_indexOfSourceTarget R Q a).symm
        (by simpa [R, Q, i₁] using hpath a) hvA
    simpa [Finset.mem_union, R, Q, i₁] using hsubset
  have hvB_union :
      v ∈ (R.path b).vertexSet ∨
        v ∈ (Q.path (R.indexOfSourceTarget Q b)).vertexSet := by
    have hsubset :=
      GraphPath.appendWithEq_vertexSet_subset
        (R.path b) (Q.path (R.indexOfSourceTarget Q b))
        (PerfectPathPacking.source_indexOfSourceTarget R Q b).symm
        (by simpa [R, Q, i₁] using hpath b) hvB
    simpa [Finset.mem_union, R, Q, i₁] using hsubset
  rcases hvA_union with hvRa | hvQa
  · rcases hvB_union with hvRb | hvQb
    · exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hab)
        hvRa hvRb
    · exact hcross hab hvRa hvQb
  · rcases hvB_union with hvRb | hvQb
    · exact hcross hab.symm hvRb hvQa
    · have hq_ne :
          R.indexOfSourceTarget Q a ≠ R.indexOfSourceTarget Q b := by
        intro hq
        have htargets : (R.path a).target = (R.path b).target := by
          have hs :=
            congrArg (fun q => (Q.path q).source) hq
          exact (PerfectPathPacking.source_indexOfSourceTarget R Q a).symm.trans
            (hs.trans (PerfectPathPacking.source_indexOfSourceTarget R Q b))
        exact hab (R.target_bijective.1 (Subtype.ext htargets))
      exact Finset.disjoint_left.mp (Q.toPathPacking.node_disjoint hq_ne)
        hvQa hvQb

/-- Two adjacent chosen one-step packings compose to a two-step perfect
threading from the left nails of cluster `i` to the left nails of cluster
`i + 2`. -/
noncomputable def leftTwoStepPacking
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell) :
    PerfectPathPacking G (P.left i)
      (P.left ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩) :=
  let hpath := P.leftNext_leftNext_concat_isPath i hi hnext
  let hnode := P.leftNext_leftNext_concat_nodeDisjoint i hi hnext hpath
  (P.leftNextPacking i hi).concat
    (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext) hpath hnode

@[simp] theorem leftTwoStepPacking_card
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell) :
    (P.leftTwoStepPacking i hi hnext).card = w := by
  simp [leftTwoStepPacking]

/-- The two-step packing stays inside the union of the two one-step regions. -/
theorem leftTwoStepPacking_staysIn
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell) :
    (P.leftTwoStepPacking i hi hnext).toPathPacking.StaysIn
      ((P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet) ∪
        (P.cluster ⟨i.1 + 1, hi⟩ ∪
          (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet)) := by
  change
    (((P.leftNextPacking i hi).concat
      (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext)
      (P.leftNext_leftNext_concat_isPath i hi hnext)
      (P.leftNext_leftNext_concat_nodeDisjoint i hi hnext
        (P.leftNext_leftNext_concat_isPath i hi hnext))).toPathPacking).StaysIn
      ((P.cluster i ∪ (P.connector i hi).toPathPacking.vertexSet) ∪
        (P.cluster ⟨i.1 + 1, hi⟩ ∪
          (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet))
  exact PerfectPathPacking.concat_staysIn_union
    (P.leftNextPacking i hi)
    (P.leftNextPacking ⟨i.1 + 1, hi⟩ hnext)
    (P.leftNext_leftNext_concat_isPath i hi hnext)
    (P.leftNext_leftNext_concat_nodeDisjoint i hi hnext
      (P.leftNext_leftNext_concat_isPath i hi hnext))
    (P.leftNextPacking_staysIn i hi)
    (P.leftNextPacking_staysIn ⟨i.1 + 1, hi⟩ hnext)

/-- Stitching data across two consecutive gaps, with prescribed endpoint
subsets on the outside odd clusters.

This is the local, proof-facing core of Chekuri--Chuzhoy Appendix C: restrict
the first connector to the chosen right endpoints of cluster `i`, restrict the
second connector to the chosen left endpoints of cluster `i+2`, and use
linkedness in the middle cluster to connect the two induced terminal sets.  The
theorem deliberately returns the three pieces separately; later assembly can
concatenate them or use their regions independently. -/
theorem exists_twoGap_stitchingPieces_between_subsets
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell)
    {R L : Finset V}
    (hR : R ⊆ P.right i)
    (hL : L ⊆ P.left ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩)
    (hcard : R.card = L.card) :
    ∃ Lmid Rmid : Finset V,
      ∃ Q₁ : PerfectPathPacking G R Lmid,
        ∃ Q₂ : PerfectPathPacking G Lmid Rmid,
          ∃ Q₃ : PerfectPathPacking G Rmid L,
            Q₁.card = R.card ∧
              Q₂.card = R.card ∧
                Q₃.card = L.card ∧
                  Lmid ⊆ P.left ⟨i.1 + 1, hi⟩ ∧
                    Rmid ⊆ P.right ⟨i.1 + 1, hi⟩ ∧
                      Q₁.toPathPacking.StaysIn
                        (P.connector i hi).toPathPacking.vertexSet ∧
                        Q₂.toPathPacking.StaysIn
                          (P.cluster ⟨i.1 + 1, hi⟩) ∧
                          Q₃.toPathPacking.StaysIn
                            (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet := by
  classical
  let i₁ : Fin ell := ⟨i.1 + 1, hi⟩
  let i₂ : Fin ell := ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩
  let C₁ := P.connector i hi
  let C₂ := P.connector i₁ hnext
  let Lmid : Finset V := C₁.targetSet (C₁.sourceIndexSetOfSubset R)
  let Rmid : Finset V := C₂.sourceSet (C₂.targetIndexSetOfSubset L)
  let Q₁ : PerfectPathPacking G R Lmid := C₁.restrictSourceSet R hR
  have hL₂ : L ⊆ P.left i₂ := hL
  let Q₃ : PerfectPathPacking G Rmid L := C₂.restrictTargetSet L hL₂
  have hLmid_subset : Lmid ⊆ P.left i₁ := by
    simpa [Lmid, C₁, i₁] using
      C₁.targetSet_subset_right (C₁.sourceIndexSetOfSubset R)
  have hRmid_subset : Rmid ⊆ P.right i₁ := by
    simpa [Rmid, C₂, i₁] using
      C₂.sourceSet_subset_left (C₂.targetIndexSetOfSubset L)
  have hQ₁card : Q₁.card = R.card := by
    simp [Q₁, C₁]
  have hQ₃card : Q₃.card = L.card := by
    simp [Q₃, C₂]
  have hLmid_card : Lmid.card = R.card := by
    exact (Q₁.card_eq_right_card).symm.trans hQ₁card
  have hRmid_card : Rmid.card = L.card := by
    exact (Q₃.card_eq_left_card).symm.trans hQ₃card
  have hmid_card : Lmid.card = Rmid.card := by
    exact hLmid_card.trans (hcard.trans hRmid_card.symm)
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      ((P.left_right_nodeLinked i₁).mono_terminals hLmid_subset hRmid_subset)
      hmid_card with
    ⟨Q₂, hQ₂cardLmid, hQ₂stay⟩
  have hQ₂card : Q₂.card = R.card :=
    hQ₂cardLmid.trans hLmid_card
  refine ⟨Lmid, Rmid, Q₁, Q₂, Q₃, hQ₁card, hQ₂card, hQ₃card,
    hLmid_subset, hRmid_subset, ?_, hQ₂stay, ?_⟩
  · simpa [Q₁, C₁] using C₁.restrictSourceSet_staysIn_vertexSet R hR
  · simpa [Q₃, C₂, i₁, i₂] using
      C₂.restrictTargetSet_staysIn_vertexSet L hL₂

/-- Stitching data across two consecutive gaps, including the separation
properties needed by the eventual concatenation proof.

The first restricted connector may meet the middle cluster only at its target,
the third restricted connector may meet the middle cluster only at its source,
and the two connector restrictions are mutually node-disjoint because they come
from different connector families of the path-of-sets system. -/
theorem exists_twoGap_stitchingPieces_between_subsets_with_separation
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell)
    {R L : Finset V}
    (hR : R ⊆ P.right i)
    (hL : L ⊆ P.left ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩)
    (hcard : R.card = L.card) :
    ∃ Lmid Rmid : Finset V,
      ∃ Q₁ : PerfectPathPacking G R Lmid,
        ∃ Q₂ : PerfectPathPacking G Lmid Rmid,
          ∃ Q₃ : PerfectPathPacking G Rmid L,
            Q₁.card = R.card ∧
              Q₂.card = R.card ∧
                Q₃.card = L.card ∧
                  Lmid ⊆ P.left ⟨i.1 + 1, hi⟩ ∧
                    Rmid ⊆ P.right ⟨i.1 + 1, hi⟩ ∧
                      Q₁.toPathPacking.StaysIn
                        (P.connector i hi).toPathPacking.vertexSet ∧
                        Q₂.toPathPacking.StaysIn
                          (P.cluster ⟨i.1 + 1, hi⟩) ∧
                          Q₃.toPathPacking.StaysIn
                            (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet ∧
                            Q₁.toPathPacking.InternallyDisjointFromSet
                              (P.cluster ⟨i.1 + 1, hi⟩) ∧
                              Q₃.toPathPacking.InternallyDisjointFromSet
                                (P.cluster ⟨i.1 + 1, hi⟩) ∧
                                Q₁.toPathPacking.MutuallyNodeDisjoint
                                  Q₃.toPathPacking ∧
                                  Q₁.toPathPacking.InternallyDisjointFromSet
                                    (P.cluster i) ∧
                                    Q₃.toPathPacking.InternallyDisjointFromSet
                                      (P.cluster
                                        ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1,
                                          hnext⟩) := by
  classical
  let i₁ : Fin ell := ⟨i.1 + 1, hi⟩
  let i₂ : Fin ell := ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩
  let C₁ := P.connector i hi
  let C₂ := P.connector i₁ hnext
  let Lmid : Finset V := C₁.targetSet (C₁.sourceIndexSetOfSubset R)
  let Rmid : Finset V := C₂.sourceSet (C₂.targetIndexSetOfSubset L)
  let Q₁ : PerfectPathPacking G R Lmid := C₁.restrictSourceSet R hR
  have hL₂ : L ⊆ P.left i₂ := hL
  let Q₃ : PerfectPathPacking G Rmid L := C₂.restrictTargetSet L hL₂
  have hLmid_subset : Lmid ⊆ P.left i₁ := by
    simpa [Lmid, C₁, i₁] using
      C₁.targetSet_subset_right (C₁.sourceIndexSetOfSubset R)
  have hRmid_subset : Rmid ⊆ P.right i₁ := by
    simpa [Rmid, C₂, i₁] using
      C₂.sourceSet_subset_left (C₂.targetIndexSetOfSubset L)
  have hQ₁card : Q₁.card = R.card := by
    simp [Q₁, C₁]
  have hQ₃card : Q₃.card = L.card := by
    simp [Q₃, C₂]
  have hLmid_card : Lmid.card = R.card := by
    exact (Q₁.card_eq_right_card).symm.trans hQ₁card
  have hRmid_card : Rmid.card = L.card := by
    exact (Q₃.card_eq_left_card).symm.trans hQ₃card
  have hmid_card : Lmid.card = Rmid.card := by
    exact hLmid_card.trans (hcard.trans hRmid_card.symm)
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      ((P.left_right_nodeLinked i₁).mono_terminals hLmid_subset hRmid_subset)
      hmid_card with
    ⟨Q₂, hQ₂cardLmid, hQ₂stay⟩
  have hQ₂card : Q₂.card = R.card :=
    hQ₂cardLmid.trans hLmid_card
  have hQ₁stay :
      Q₁.toPathPacking.StaysIn (P.connector i hi).toPathPacking.vertexSet := by
    simpa [Q₁, C₁] using C₁.restrictSourceSet_staysIn_vertexSet R hR
  have hQ₃stay :
      Q₃.toPathPacking.StaysIn (P.connector i₁ hnext).toPathPacking.vertexSet := by
    simpa [Q₃, C₂, i₁, i₂] using
      C₂.restrictTargetSet_staysIn_vertexSet L hL₂
  have hQ₁middle :
      Q₁.toPathPacking.InternallyDisjointFromSet (P.cluster i₁) := by
    intro a
    simpa [Q₁, C₁, i₁, PerfectPathPacking.restrictSourceSet,
      PerfectPathPacking.copyTerminals, PerfectPathPacking.restrictIndexSet] using
      P.connector_internally_disjoint_clusters i hi i₁ a.1
  have hQ₃middle :
      Q₃.toPathPacking.InternallyDisjointFromSet (P.cluster i₁) := by
    intro a
    simpa [Q₃, C₂, i₁, i₂, PerfectPathPacking.restrictTargetSet,
      PerfectPathPacking.copyTerminals, PerfectPathPacking.restrictIndexSet] using
      P.connector_internally_disjoint_clusters i₁ hnext i₁ a.1
  have hQ₁first :
      Q₁.toPathPacking.InternallyDisjointFromSet (P.cluster i) := by
    intro a
    simpa [Q₁, C₁, PerfectPathPacking.restrictSourceSet,
      PerfectPathPacking.copyTerminals, PerfectPathPacking.restrictIndexSet] using
      P.connector_internally_disjoint_clusters i hi i a.1
  have hQ₃last :
      Q₃.toPathPacking.InternallyDisjointFromSet (P.cluster i₂) := by
    intro a
    simpa [Q₃, C₂, i₁, i₂, PerfectPathPacking.restrictTargetSet,
      PerfectPathPacking.copyTerminals, PerfectPathPacking.restrictIndexSet] using
      P.connector_internally_disjoint_clusters i₁ hnext i₂ a.1
  have hi_ne_i₁ : i ≠ i₁ := by
    intro h
    have hval := congrArg Fin.val h
    simp [i₁] at hval
  have hQ₁Q₃ :
      Q₁.toPathPacking.MutuallyNodeDisjoint Q₃.toPathPacking := by
    intro a b
    simpa [Q₁, Q₃, C₁, C₂, i₁, i₂, PerfectPathPacking.restrictSourceSet,
      PerfectPathPacking.restrictTargetSet, PerfectPathPacking.copyTerminals,
      PerfectPathPacking.restrictIndexSet] using
      P.connector_mutually_nodeDisjoint hi hnext hi_ne_i₁ a.1 b.1
  refine ⟨Lmid, Rmid, Q₁, Q₂, Q₃, hQ₁card, hQ₂card, hQ₃card,
    hLmid_subset, hRmid_subset, hQ₁stay, hQ₂stay, ?_, ?_, ?_, hQ₁Q₃,
    ?_, ?_⟩
  · simpa [i₁] using hQ₃stay
  · simpa [i₁] using hQ₁middle
  · simpa [i₁] using hQ₃middle
  · exact hQ₁first
  · simpa [i₂] using hQ₃last

/-- The two-gap stitching pieces can already be collapsed on either side of
the middle cluster.  The first concatenation runs from the prescribed right
endpoints in cluster `i` to the chosen right endpoints of the middle cluster;
the second runs from the chosen left endpoints of the middle cluster to the
prescribed left endpoints in cluster `i+2`.

This is the main reusable API before the final three-piece concatenation: it
turns the path-splicing step of Chekuri--Chuzhoy Appendix C from a raw existence
statement into actual perfect packings with region-containment certificates. -/
theorem exists_twoGap_partialConcatPackings_between_subsets
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell)
    {R L : Finset V}
    (hR : R ⊆ P.right i)
    (hL : L ⊆ P.left ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩)
    (hcard : R.card = L.card) :
    ∃ Lmid Rmid : Finset V,
      ∃ Q₁ : PerfectPathPacking G R Lmid,
        ∃ Q₂ : PerfectPathPacking G Lmid Rmid,
          ∃ Q₃ : PerfectPathPacking G Rmid L,
            ∃ Q₁₂ : PerfectPathPacking G R Rmid,
              ∃ Q₂₃ : PerfectPathPacking G Lmid L,
                Q₁.card = R.card ∧
                  Q₂.card = R.card ∧
                    Q₃.card = L.card ∧
                      Q₁₂.card = R.card ∧
                        Q₂₃.card = R.card ∧
                          Lmid ⊆ P.left ⟨i.1 + 1, hi⟩ ∧
                            Rmid ⊆ P.right ⟨i.1 + 1, hi⟩ ∧
                              Q₁₂.toPathPacking.StaysIn
                                ((P.connector i hi).toPathPacking.vertexSet ∪
                                  P.cluster ⟨i.1 + 1, hi⟩) ∧
                                Q₂₃.toPathPacking.StaysIn
                                  (P.cluster ⟨i.1 + 1, hi⟩ ∪
                                    (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet) ∧
                                  Q₁.toPathPacking.MutuallyNodeDisjoint Q₃.toPathPacking := by
  classical
  let i₁ : Fin ell := ⟨i.1 + 1, hi⟩
  let i₂ : Fin ell := ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩
  rcases P.exists_twoGap_stitchingPieces_between_subsets_with_separation
      i hi hnext hR hL hcard with
    ⟨Lmid, Rmid, Q₁, Q₂, Q₃, hQ₁card, hQ₂card, hQ₃card,
      hLmid, hRmid, hQ₁stay, hQ₂stay, hQ₃stay,
      hQ₁middle, hQ₃middle, hQ₁Q₃, _hQ₁first, _hQ₃last⟩
  have hi_ne_i₁ : i ≠ i₁ := by
    intro h
    have hval := congrArg Fin.val h
    simp [i₁] at hval
  have hRdisj : Disjoint R (P.cluster i₁) := by
    rw [Finset.disjoint_left]
    intro v hvR hvMiddle
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi_ne_i₁)
      (P.right_subset_cluster i (hR hvR)) hvMiddle
  have hi₂_ne_i₁ : i₂ ≠ i₁ := by
    intro h
    have hval := congrArg Fin.val h
    simp [i₁, i₂] at hval
  have hLdisj : Disjoint L (P.cluster i₁) := by
    rw [Finset.disjoint_left]
    intro v hvL hvMiddle
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi₂_ne_i₁)
      (P.left_subset_cluster i₂ (by simpa [i₂] using hL hvL)) hvMiddle
  let Q₁₂ : PerfectPathPacking G R Rmid :=
    Q₁.concatOfFirstInternallyDisjointSecondStaysIn Q₂
      (by simpa [i₁] using hQ₁middle) (by simpa [i₁] using hQ₂stay)
      (by simpa [i₁] using hRdisj)
  let Q₂₃ : PerfectPathPacking G Lmid L :=
    Q₂.concatOfFirstStaysInSecondInternallyDisjoint Q₃
      (by simpa [i₁] using hQ₂stay) (by simpa [i₁] using hQ₃middle)
      (by simpa [i₁] using hLdisj)
  have hQ₁₂card : Q₁₂.card = R.card := by
    simpa [Q₁₂] using hQ₁card
  have hQ₂₃card : Q₂₃.card = R.card := by
    simpa [Q₂₃] using hQ₂card
  have hQ₁₂stay :
      Q₁₂.toPathPacking.StaysIn
        ((P.connector i hi).toPathPacking.vertexSet ∪ P.cluster i₁) := by
    simpa [Q₁₂, i₁] using
      Q₁.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union Q₂
        (by simpa [i₁] using hQ₁middle) (by simpa [i₁] using hQ₂stay)
        (by simpa [i₁] using hRdisj) hQ₁stay
  have hQ₂₃stay :
      Q₂₃.toPathPacking.StaysIn
        (P.cluster i₁ ∪ (P.connector i₁ hnext).toPathPacking.vertexSet) := by
    simpa [Q₂₃, i₁] using
      Q₂.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union Q₃
        (by simpa [i₁] using hQ₂stay) (by simpa [i₁] using hQ₃middle)
        (by simpa [i₁] using hLdisj) (by simpa [i₁] using hQ₃stay)
  refine ⟨Lmid, Rmid, Q₁, Q₂, Q₃, Q₁₂, Q₂₃,
    hQ₁card, hQ₂card, hQ₃card, hQ₁₂card, hQ₂₃card,
    ?_, ?_, ?_, ?_, hQ₁Q₃⟩
  · simpa [i₁] using hLmid
  · simpa [i₁] using hRmid
  · simpa [i₁] using hQ₁₂stay
  · simpa [i₁] using hQ₂₃stay

/-- If the first path in a perfect-packing concatenation is internally
disjoint from `A` and its source terminal is outside `A`, intersecting the
concatenated path with `A` discards exactly the first-path prefix. -/
private theorem concat_path_inter_eq_right_inter
    {S T U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ a : P.Index,
        ((P.path a).walk.append
          ((Q.path (P.indexOfSourceTarget Q a)).walk.copy
            (PerfectPathPacking.source_indexOfSourceTarget P Q a) rfl)).IsPath)
    (hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((P.path a).appendWithEq (Q.path (P.indexOfSourceTarget Q a))
            (PerfectPathPacking.source_indexOfSourceTarget P Q a).symm (hpath a))
          ((P.path b).appendWithEq (Q.path (P.indexOfSourceTarget Q b))
            (PerfectPathPacking.source_indexOfSourceTarget P Q b).symm (hpath b)))
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hSdisj : Disjoint S A)
    (a : (P.concat Q hpath hnode).Index) :
    ((P.concat Q hpath hnode).path a).vertexSet ∩ A =
      (Q.path (P.indexOfSourceTarget Q a)).vertexSet ∩ A := by
  classical
  ext v
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hv, hvA⟩
    have hvPieces := P.concat_path_vertexSet_subset Q hpath hnode a hv
    rcases Finset.mem_union.mp hvPieces with hvP | hvQ
    · rcases hP a hvP hvA with hsource | htarget
      · exact False.elim
          (Finset.disjoint_left.mp hSdisj (P.source_mem a)
            (by simpa [hsource] using hvA))
      · refine ⟨?_, hvA⟩
        have hglue :
            v = (Q.path (P.indexOfSourceTarget Q a)).source :=
          htarget.trans
            (PerfectPathPacking.source_indexOfSourceTarget P Q a).symm
        simpa [hglue] using
          GraphPath.source_mem_vertexSet
            (Q.path (P.indexOfSourceTarget Q a))
    · exact ⟨hvQ, hvA⟩
  · rintro ⟨hvQ, hvA⟩
    refine ⟨?_, hvA⟩
    exact GraphPath.right_vertexSet_subset_appendWithEq
      (P.path a) (Q.path (P.indexOfSourceTarget Q a))
      (PerfectPathPacking.source_indexOfSourceTarget P Q a).symm
      (hpath a) hvQ

/-- If the second path in a perfect-packing concatenation is internally
disjoint from `A` and its target terminal is outside `A`, intersecting the
concatenated path with `A` discards exactly the second-path suffix. -/
private theorem concat_path_inter_eq_left_inter
    {S T U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ a : P.Index,
        ((P.path a).walk.append
          ((Q.path (P.indexOfSourceTarget Q a)).walk.copy
            (PerfectPathPacking.source_indexOfSourceTarget P Q a) rfl)).IsPath)
    (hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((P.path a).appendWithEq (Q.path (P.indexOfSourceTarget Q a))
            (PerfectPathPacking.source_indexOfSourceTarget P Q a).symm (hpath a))
          ((P.path b).appendWithEq (Q.path (P.indexOfSourceTarget Q b))
            (PerfectPathPacking.source_indexOfSourceTarget P Q b).symm (hpath b)))
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (a : (P.concat Q hpath hnode).Index) :
    ((P.concat Q hpath hnode).path a).vertexSet ∩ A =
      (P.path a).vertexSet ∩ A := by
  classical
  ext v
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hv, hvA⟩
    have hvPieces := P.concat_path_vertexSet_subset Q hpath hnode a hv
    rcases Finset.mem_union.mp hvPieces with hvP | hvQ
    · exact ⟨hvP, hvA⟩
    · rcases hQ (P.indexOfSourceTarget Q a) hvQ hvA with hsource | htarget
      · refine ⟨?_, hvA⟩
        have hglue : v = (P.path a).target :=
          hsource.trans
            (PerfectPathPacking.source_indexOfSourceTarget P Q a)
        simp [hglue]
      · exact False.elim
          (Finset.disjoint_left.mp hUdisj
            (Q.target_mem (P.indexOfSourceTarget Q a))
            (by simpa [htarget] using hvA))
  · rintro ⟨hvP, hvA⟩
    refine ⟨?_, hvA⟩
    exact GraphPath.left_vertexSet_subset_appendWithEq
      (P.path a) (Q.path (P.indexOfSourceTarget Q a))
      (PerfectPathPacking.source_indexOfSourceTarget P Q a).symm
      (hpath a) hvP

/-- Provenance for the two-gap path concatenation in Chekuri--Chuzhoy
Appendix C.  Besides the collapsed packing, this retains the exact perfect
packing chosen inside the intervening odd cluster and identifies every
collapsed path with its middle-cluster constituent. -/
structure TwoGapConcatPackingData
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell)
    {R L : Finset V} (Q : PerfectPathPacking G R L) where
  /-- Left terminals selected in the intervening odd cluster. -/
  Lmid : Finset V
  /-- Right terminals selected in the intervening odd cluster. -/
  Rmid : Finset V
  /-- The actual perfect packing selected by linkedness in the odd cluster. -/
  middle : PerfectPathPacking G Lmid Rmid
  /-- The collapsed packing has the requested cardinality. -/
  card_eq : Q.card = R.card
  /-- The retained middle packing has that same cardinality. -/
  middle_card_eq : middle.card = R.card
  /-- The left middle terminals are left nails of the odd cluster. -/
  Lmid_subset : Lmid ⊆ P.left ⟨i.1 + 1, hi⟩
  /-- The right middle terminals are right nails of the odd cluster. -/
  Rmid_subset : Rmid ⊆ P.right ⟨i.1 + 1, hi⟩
  /-- The retained middle packing stays inside the odd cluster. -/
  middle_staysIn : middle.toPathPacking.StaysIn (P.cluster ⟨i.1 + 1, hi⟩)
  /-- The collapsed packing stays in the two connectors and odd cluster. -/
  staysIn :
    Q.toPathPacking.StaysIn
      ((P.connector i hi).toPathPacking.vertexSet ∪
        (P.cluster ⟨i.1 + 1, hi⟩ ∪
          (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet))
  /-- The collapsed packing is internally disjoint from its left endpoint
  cluster. -/
  internallyDisjoint_left :
    Q.toPathPacking.InternallyDisjointFromSet (P.cluster i)
  /-- The collapsed packing is internally disjoint from its right endpoint
  cluster. -/
  internallyDisjoint_right :
    Q.toPathPacking.InternallyDisjointFromSet
      (P.cluster ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩)
  /-- Bijection matching a collapsed path to its retained middle path. -/
  indexEquiv : Q.Index ≃ middle.Index
  /-- Exact middle-cluster trace, oriented as collapsed path intersect cluster. -/
  trace_eq :
    ∀ a : Q.Index,
      (Q.path a).vertexSet ∩ P.cluster ⟨i.1 + 1, hi⟩ =
        (middle.path (indexEquiv a)).vertexSet

/-- Produce a full two-gap packing together with the exact middle packing used
to construct it.  The linkedness chooser is invoked once, so `middle` is the
same `Q₂` whose paths occur in `Q`, not an independently selected packing. -/
theorem exists_twoGap_concatPackingData_between_subsets
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell)
    {R L : Finset V}
    (hR : R ⊆ P.right i)
    (hL : L ⊆ P.left ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩)
    (hcard : R.card = L.card) :
    ∃ Q : PerfectPathPacking G R L,
      Nonempty (TwoGapConcatPackingData P i hi hnext Q) := by
  classical
  let i₁ : Fin ell := ⟨i.1 + 1, hi⟩
  let i₂ : Fin ell := ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩
  rcases P.exists_twoGap_stitchingPieces_between_subsets_with_separation
      i hi hnext hR hL hcard with
    ⟨Lmid, Rmid, Q₁, Q₂, Q₃, hQ₁card, hQ₂card, _hQ₃card,
      hLmid, hRmid, hQ₁stay, hQ₂stay, hQ₃stay,
      hQ₁middle, hQ₃middle, hQ₁Q₃, hQ₁first, hQ₃last⟩
  have hi_ne_i₁ : i ≠ i₁ := by
    intro h
    have hval := congrArg Fin.val h
    simp [i₁] at hval
  have hRdisj : Disjoint R (P.cluster i₁) := by
    rw [Finset.disjoint_left]
    intro v hvR hvMiddle
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi_ne_i₁)
      (P.right_subset_cluster i (hR hvR)) hvMiddle
  have hi₂_ne_i₁ : i₂ ≠ i₁ := by
    intro h
    have hval := congrArg Fin.val h
    simp [i₁, i₂] at hval
  have hLdisj : Disjoint L (P.cluster i₁) := by
    rw [Finset.disjoint_left]
    intro v hvL hvMiddle
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi₂_ne_i₁)
      (P.left_subset_cluster i₂ (by simpa [i₂] using hL hvL)) hvMiddle
  have hQ₂stay_middle :
      Q₂.toPathPacking.StaysIn (P.cluster i₁) := by
    simpa [i₁] using hQ₂stay
  have hQ₃middle_middle :
      Q₃.toPathPacking.InternallyDisjointFromSet (P.cluster i₁) := by
    simpa [i₁] using hQ₃middle
  have hQ₃stay_connector :
      Q₃.toPathPacking.StaysIn
        (P.connector i₁ hnext).toPathPacking.vertexSet := by
    simpa [i₁] using hQ₃stay
  let hpath₂₃ :=
    Q₂.concat_isPath_of_first_staysIn_second_internallyDisjointFromSet Q₃
      hQ₂stay_middle hQ₃middle_middle hLdisj
  let hnode₂₃ :=
    Q₂.concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet Q₃
      hQ₂stay_middle hQ₃middle_middle hLdisj hpath₂₃
  let Q₂₃ : PerfectPathPacking G Lmid L :=
    Q₂.concat Q₃ hpath₂₃ hnode₂₃
  have hQ₂₃split :
      ∀ k : Q₂₃.Index,
        (Q₂₃.path k).vertexSet ⊆
          (Q₂.path k).vertexSet ∪
            (Q₃.path (Q₂.indexOfSourceTarget Q₃ k)).vertexSet := by
    intro k
    simpa [Q₂₃] using
      Q₂.concat_path_vertexSet_subset Q₃ hpath₂₃ hnode₂₃ k
  have hQ₂₃stay :
      Q₂₃.toPathPacking.StaysIn
        (P.cluster i₁ ∪ (P.connector i₁ hnext).toPathPacking.vertexSet) := by
    simpa [Q₂₃, i₁] using
      Q₂.concat_staysIn_union Q₃ hpath₂₃ hnode₂₃
        hQ₂stay_middle hQ₃stay_connector
  have hQ₂₃trace :
      ∀ k : Q₂₃.Index,
        (Q₂₃.path k).vertexSet ∩ P.cluster i₁ =
          (Q₂.path k).vertexSet := by
    intro k
    calc
      (Q₂₃.path k).vertexSet ∩ P.cluster i₁ =
          (Q₂.path k).vertexSet ∩ P.cluster i₁ := by
        simpa [Q₂₃] using
          concat_path_inter_eq_left_inter Q₂ Q₃ hpath₂₃ hnode₂₃
            hQ₃middle_middle hLdisj k
      _ = (Q₂.path k).vertexSet :=
        Finset.inter_eq_left.mpr (hQ₂stay_middle k)
  have hpath :
      ∀ a : Q₁.Index,
        ((Q₁.path a).walk.append
          ((Q₂₃.path (Q₁.indexOfSourceTarget Q₂₃ a)).walk.copy
            (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a) rfl)).IsPath := by
    intro a
    refine GraphPath.appendWithEq_isPath_of_inter_subset_target
      (Q₁.path a) (Q₂₃.path (Q₁.indexOfSourceTarget Q₂₃ a))
      (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a).symm ?_
    intro v hvQ₁ hvQ₂₃
    let k := Q₁.indexOfSourceTarget Q₂₃ a
    have hvsplit := hQ₂₃split k hvQ₂₃
    rcases Finset.mem_union.mp hvsplit with hvQ₂ | hvQ₃
    · have hvMiddle : v ∈ P.cluster i₁ := by
        exact hQ₂stay k hvQ₂
      rcases hQ₁middle a hvQ₁ hvMiddle with hsource | htarget
      · exact False.elim
          (Finset.disjoint_left.mp hRdisj (Q₁.source_mem a)
            (by simpa [hsource] using hvMiddle))
      · exact htarget
    · exact False.elim
        (Finset.disjoint_left.mp
          (hQ₁Q₃ a (Q₂.indexOfSourceTarget Q₃ k)) hvQ₁ hvQ₃)
  have hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((Q₁.path a).appendWithEq
            (Q₂₃.path (Q₁.indexOfSourceTarget Q₂₃ a))
            (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a).symm
            (hpath a))
          ((Q₁.path b).appendWithEq
            (Q₂₃.path (Q₁.indexOfSourceTarget Q₂₃ b))
            (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ b).symm
            (hpath b)) := by
    intro a b hab
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hva hvb
    let ka := Q₁.indexOfSourceTarget Q₂₃ a
    let kb := Q₁.indexOfSourceTarget Q₂₃ b
    have hvasub :=
      GraphPath.appendWithEq_vertexSet_subset
        (Q₁.path a) (Q₂₃.path ka)
        (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a).symm
        (hpath a) hva
    have hvbsub :=
      GraphPath.appendWithEq_vertexSet_subset
        (Q₁.path b) (Q₂₃.path kb)
        (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ b).symm
        (hpath b) hvb
    rcases Finset.mem_union.mp hvasub with hvaQ₁ | hvaQ₂₃
    · rcases Finset.mem_union.mp hvbsub with hvbQ₁ | hvbQ₂₃
      · exact Finset.disjoint_left.mp (Q₁.toPathPacking.node_disjoint hab)
          hvaQ₁ hvbQ₁
      · have hvsplit := hQ₂₃split kb hvbQ₂₃
        rcases Finset.mem_union.mp hvsplit with hvbQ₂ | hvbQ₃
        · have hvMiddle : v ∈ P.cluster i₁ := hQ₂stay kb hvbQ₂
          rcases hQ₁middle a hvaQ₁ hvMiddle with hsource | htarget
          · exact Finset.disjoint_left.mp hRdisj (Q₁.source_mem a)
              (by simpa [hsource] using hvMiddle)
          · have hvLmid : v ∈ Lmid := by
              simpa [htarget] using Q₁.target_mem a
            have hQ₂source :
                v = (Q₂.path kb).source :=
              Q₂.eq_source_of_mem_left_of_mem_path_vertexSet kb hvLmid hvbQ₂
            have htargets : (Q₁.path a).target = (Q₁.path b).target := by
              calc
                (Q₁.path a).target = v := htarget.symm
                _ = (Q₂.path kb).source := hQ₂source
                _ = (Q₁.path b).target := by
                  change (Q₂₃.path kb).source = (Q₁.path b).target
                  exact PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ b
            exact hab (Q₁.target_bijective.1 (Subtype.ext htargets))
        · exact Finset.disjoint_left.mp
            (hQ₁Q₃ a (Q₂.indexOfSourceTarget Q₃ kb)) hvaQ₁ hvbQ₃
    · rcases Finset.mem_union.mp hvbsub with hvbQ₁ | hvbQ₂₃
      · have hvsplit := hQ₂₃split ka hvaQ₂₃
        rcases Finset.mem_union.mp hvsplit with hvaQ₂ | hvaQ₃
        · have hvMiddle : v ∈ P.cluster i₁ := hQ₂stay ka hvaQ₂
          rcases hQ₁middle b hvbQ₁ hvMiddle with hsource | htarget
          · exact Finset.disjoint_left.mp hRdisj (Q₁.source_mem b)
              (by simpa [hsource] using hvMiddle)
          · have hvLmid : v ∈ Lmid := by
              simpa [htarget] using Q₁.target_mem b
            have hQ₂source :
                v = (Q₂.path ka).source :=
              Q₂.eq_source_of_mem_left_of_mem_path_vertexSet ka hvLmid hvaQ₂
            have htargets : (Q₁.path a).target = (Q₁.path b).target := by
              calc
                (Q₁.path a).target = (Q₂.path ka).source := by
                  change (Q₁.path a).target = (Q₂₃.path ka).source
                  exact (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a).symm
                _ = v := hQ₂source.symm
                _ = (Q₁.path b).target := htarget
            exact hab (Q₁.target_bijective.1 (Subtype.ext htargets))
        · exact Finset.disjoint_left.mp
            (hQ₁Q₃ b (Q₂.indexOfSourceTarget Q₃ ka)) hvbQ₁ hvaQ₃
      · have hkb_ne : ka ≠ kb := by
          intro hkab
          apply hab
          apply Q₁.target_bijective.1
          have htargets : (Q₁.path a).target = (Q₁.path b).target := by
            have hsources :=
              congrArg (fun q => (Q₂₃.path q).source) hkab
            exact (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a).symm.trans
              (hsources.trans
                (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ b))
          exact Subtype.ext htargets
        exact Finset.disjoint_left.mp (Q₂₃.toPathPacking.node_disjoint hkb_ne)
          hvaQ₂₃ hvbQ₂₃
  let Q : PerfectPathPacking G R L := Q₁.concat Q₂₃ hpath hnode
  have hQcard : Q.card = R.card := by
    simpa [Q] using hQ₁card
  have hQstay :
      Q.toPathPacking.StaysIn
        ((P.connector i hi).toPathPacking.vertexSet ∪
          (P.cluster i₁ ∪ (P.connector i₁ hnext).toPathPacking.vertexSet)) := by
    simpa [Q, i₁] using
      Q₁.concat_staysIn_union Q₂₃ hpath hnode hQ₁stay hQ₂₃stay
  have hi_ne_i₂ : i ≠ i₂ := by
    intro h
    have hval := congrArg Fin.val h
    simp [i₂] at hval
    omega
  have hi₁_ne_i : i₁ ≠ i := by
    intro h
    exact hi_ne_i₁ h.symm
  have hi₁_ne_i₂ : i₁ ≠ i₂ := by
    intro h
    exact hi₂_ne_i₁ h.symm
  have hLmid_disj_first : Disjoint Lmid (P.cluster i) := by
    rw [Finset.disjoint_left]
    intro v hvLmid hvCluster
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi₁_ne_i)
      (P.left_subset_cluster i₁ (hLmid hvLmid)) hvCluster
  have hQ₂₃disj_first :
      Disjoint Q₂₃.toPathPacking.vertexSet (P.cluster i) := by
    rw [Finset.disjoint_left]
    intro v hvQ₂₃ hvCluster
    have hvRegion :
        v ∈ P.cluster i₁ ∪ (P.connector i₁ hnext).toPathPacking.vertexSet :=
      PathPacking.vertexSet_subset_of_staysIn hQ₂₃stay hvQ₂₃
    rcases Finset.mem_union.mp hvRegion with hvMiddle | hvConn
    · exact Finset.disjoint_left.mp (P.cluster_disjoint hi₁_ne_i)
        hvMiddle hvCluster
    · exact Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne i₁ hnext i
          (by simpa [i₁] using hi_ne_i₁)
          (by simpa [i₂] using hi_ne_i₂))
        hvConn hvCluster
  have hQ₁disj_last :
      Disjoint Q₁.toPathPacking.vertexSet (P.cluster i₂) := by
    rw [Finset.disjoint_left]
    intro v hvQ₁ hvCluster
    have hvConn :
        v ∈ (P.connector i hi).toPathPacking.vertexSet :=
      PathPacking.vertexSet_subset_of_staysIn hQ₁stay hvQ₁
    exact Finset.disjoint_left.mp
      (P.connector_vertexSet_disjoint_cluster_of_ne i hi i₂
        (by
          intro h
          exact hi_ne_i₂ h.symm)
        (by
          simpa [i₁] using hi₂_ne_i₁))
      hvConn hvCluster
  have hLmid_disj_last : Disjoint Lmid (P.cluster i₂) := by
    rw [Finset.disjoint_left]
    intro v hvLmid hvCluster
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi₁_ne_i₂)
      (P.left_subset_cluster i₁ (hLmid hvLmid)) hvCluster
  have hQ₂disj_last :
      Disjoint Q₂.toPathPacking.vertexSet (P.cluster i₂) := by
    rw [Finset.disjoint_left]
    intro v hvQ₂ hvCluster
    have hvMiddle : v ∈ P.cluster i₁ :=
      PathPacking.vertexSet_subset_of_staysIn hQ₂stay hvQ₂
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi₁_ne_i₂)
      hvMiddle hvCluster
  have hRmid_disj_last : Disjoint Rmid (P.cluster i₂) := by
    rw [Finset.disjoint_left]
    intro v hvRmid hvCluster
    exact Finset.disjoint_left.mp (P.cluster_disjoint hi₁_ne_i₂)
      (P.right_subset_cluster i₁ (hRmid hvRmid)) hvCluster
  have hQ₂₃last :
      Q₂₃.toPathPacking.InternallyDisjointFromSet (P.cluster i₂) := by
    intro k v hvQ₂₃ hvCluster
    have hvsplit := hQ₂₃split k hvQ₂₃
    rcases Finset.mem_union.mp hvsplit with hvQ₂ | hvQ₃
    · have hvQ₂total : v ∈ Q₂.toPathPacking.vertexSet :=
        Q₂.toPathPacking.path_vertexSet_subset_vertexSet k hvQ₂
      exact False.elim
        (Finset.disjoint_left.mp hQ₂disj_last hvQ₂total hvCluster)
    · rcases hQ₃last (Q₂.indexOfSourceTarget Q₃ k) hvQ₃ hvCluster with
        hsource | htarget
      · exact False.elim
          (Finset.disjoint_left.mp hRmid_disj_last
            (Q₃.source_mem (Q₂.indexOfSourceTarget Q₃ k))
            (by simpa [hsource] using hvCluster))
      · exact Or.inr (by
          simpa [Q₂₃, PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint,
            GraphPath.IsEndpoint] using htarget)
  have hQfirst :
      Q.toPathPacking.InternallyDisjointFromSet (P.cluster i) := by
    simpa [Q] using
      Q₁.concat_internallyDisjointFromSet_left Q₂₃ hpath hnode
        hQ₁first hLmid_disj_first hQ₂₃disj_first
  have hQlast :
      Q.toPathPacking.InternallyDisjointFromSet (P.cluster i₂) := by
    simpa [Q] using
      Q₁.concat_internallyDisjointFromSet_right Q₂₃ hpath hnode
        hQ₁disj_last hLmid_disj_last hQ₂₃last
  let middleIndexMap : Q.Index → Q₂.Index :=
    fun a => Q₁.indexOfSourceTarget Q₂₃ a
  have hmiddleIndexMap_bijective : Function.Bijective middleIndexMap := by
    constructor
    · intro a b hab
      apply Q₁.target_bijective.1
      apply Subtype.ext
      have hsources := congrArg (fun k => (Q₂₃.path k).source) hab
      exact
        (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a).symm.trans
          (hsources.trans
            (PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ b))
    · intro k
      rcases Q₁.target_bijective.2
          ⟨(Q₂₃.path k).source, Q₂₃.source_mem k⟩ with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Q₂₃.source_bijective.1
      apply Subtype.ext
      calc
        (Q₂₃.path (middleIndexMap a)).source =
            (Q₁.path a).target :=
          PerfectPathPacking.source_indexOfSourceTarget Q₁ Q₂₃ a
        _ = (Q₂₃.path k).source := congrArg Subtype.val ha
  let middleIndexEquiv : Q.Index ≃ Q₂.Index :=
    Equiv.ofBijective middleIndexMap hmiddleIndexMap_bijective
  have hQtrace :
      ∀ a : Q.Index,
        (Q.path a).vertexSet ∩ P.cluster i₁ =
          (Q₂.path (middleIndexEquiv a)).vertexSet := by
    intro a
    calc
      (Q.path a).vertexSet ∩ P.cluster i₁ =
          (Q₂₃.path (Q₁.indexOfSourceTarget Q₂₃ a)).vertexSet ∩
            P.cluster i₁ := by
        simpa [Q] using
          concat_path_inter_eq_right_inter Q₁ Q₂₃ hpath hnode
            (by simpa [i₁] using hQ₁middle) hRdisj a
      _ = (Q₂.path (middleIndexEquiv a)).vertexSet := by
        simpa [middleIndexEquiv, middleIndexMap] using
          hQ₂₃trace (Q₁.indexOfSourceTarget Q₂₃ a)
  refine ⟨Q, ⟨{
    Lmid := Lmid
    Rmid := Rmid
    middle := Q₂
    card_eq := hQcard
    middle_card_eq := hQ₂card
    Lmid_subset := by simpa [i₁] using hLmid
    Rmid_subset := by simpa [i₁] using hRmid
    middle_staysIn := by simpa [i₁] using hQ₂stay_middle
    staysIn := by simpa [i₁] using hQstay
    internallyDisjoint_left := by simpa using hQfirst
    internallyDisjoint_right := by simpa [i₂] using hQlast
    indexEquiv := middleIndexEquiv
    trace_eq := by simpa [i₁] using hQtrace
  }⟩⟩

/-- Full two-gap stitching: prescribed equal-size subsets of the right nails
of cluster `i` and the left nails of cluster `i+2` are linked by a perfect
packing routed through the first connector, the middle cluster, and the second
connector.

This is the collapsed path-splicing conclusion from Chekuri--Chuzhoy Appendix
C.  The stronger `exists_twoGap_concatPackingData_between_subsets` theorem
also retains the exact middle-cluster packing and path traces. -/
theorem exists_twoGap_concatPacking_between_subsets
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell)
    (hnext : (⟨i.1 + 1, hi⟩ : Fin ell).1 + 1 < ell)
    {R L : Finset V}
    (hR : R ⊆ P.right i)
    (hL : L ⊆ P.left ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩)
    (hcard : R.card = L.card) :
    ∃ Q : PerfectPathPacking G R L,
      Q.card = R.card ∧
        Q.toPathPacking.StaysIn
          ((P.connector i hi).toPathPacking.vertexSet ∪
            (P.cluster ⟨i.1 + 1, hi⟩ ∪
              (P.connector ⟨i.1 + 1, hi⟩ hnext).toPathPacking.vertexSet)) ∧
          Q.toPathPacking.InternallyDisjointFromSet (P.cluster i) ∧
            Q.toPathPacking.InternallyDisjointFromSet
              (P.cluster
                ⟨(⟨i.1 + 1, hi⟩ : Fin ell).1 + 1, hnext⟩) := by
  rcases P.exists_twoGap_concatPackingData_between_subsets
      i hi hnext hR hL hcard with ⟨Q, ⟨D⟩⟩
  exact ⟨Q, D.card_eq, D.staysIn, D.internallyDisjoint_left,
    D.internallyDisjoint_right⟩

/-- The left-nail well-linkedness field supplies a packing between any two
disjoint selected subsets of the left nails, routed inside the cluster. -/
theorem exists_left_linkage_between_subsets
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    {A B : Finset V} (hA : A ⊆ P.left i) (hB : B ⊆ P.left i)
    (hdisj : Disjoint A B) :
    ∃ Q : PathPacking G A B,
      Q.card = min A.card B.card ∧ Q.StaysIn (P.cluster i) :=
  (P.left_nodeWellLinked i).2 hA hB hdisj

/-- The right-nail well-linkedness field supplies a packing between any two
disjoint selected subsets of the right nails, routed inside the cluster. -/
theorem exists_right_linkage_between_subsets
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    {A B : Finset V} (hA : A ⊆ P.right i) (hB : B ⊆ P.right i)
    (hdisj : Disjoint A B) :
    ∃ Q : PathPacking G A B,
      Q.card = min A.card B.card ∧ Q.StaysIn (P.cluster i) :=
  (P.right_nodeWellLinked i).2 hA hB hdisj

/-- Restrict a strong path-of-sets system to its first `ell'` clusters. -/
noncomputable def restrictLength (P : StrongPathOfSetsSystem G ell w)
    {ell' : ℕ} (hpos : 0 < ell') (hle : ell' ≤ ell) :
    StrongPathOfSetsSystem G ell' w where
  toPathOfSetsSystem := P.toPathOfSetsSystem.restrictLength hpos hle
  left_nodeWellLinked := by
    intro i
    simpa [PathOfSetsSystem.restrictLength] using
      P.left_nodeWellLinked (Fin.castLE hle i)
  right_nodeWellLinked := by
    intro i
    simpa [PathOfSetsSystem.restrictLength] using
      P.right_nodeWellLinked (Fin.castLE hle i)
  left_right_nodeLinked := by
    intro i
    simpa [PathOfSetsSystem.restrictLength] using
      P.left_right_nodeLinked (Fin.castLE hle i)

/-- Restrict the width of a strong path-of-sets system. -/
noncomputable def restrictWidth (P : StrongPathOfSetsSystem G ell w)
    {w' : ℕ} (hpos : 0 < w') (hle : w' ≤ w) :
    StrongPathOfSetsSystem G ell w' where
  toPathOfSetsSystem := P.toPathOfSetsSystem.restrictWidth hpos hle
  left_nodeWellLinked := by
    intro i
    exact (P.left_nodeWellLinked i).mono_terminals
      (P.toPathOfSetsSystem.leftTrim_subset_left hle i)
  right_nodeWellLinked := by
    intro i
    exact (P.right_nodeWellLinked i).mono_terminals
      (P.toPathOfSetsSystem.rightTrim_subset_right hle i)
  left_right_nodeLinked := by
    intro i
    exact (P.left_right_nodeLinked i).mono_terminals
      (P.toPathOfSetsSystem.leftTrim_subset_left hle i)
      (P.toPathOfSetsSystem.rightTrim_subset_right hle i)

/-- Simultaneously restrict a strong path-of-sets system in length and width.

This is the exact thinning operation used by the path-of-sets-to-grid step:
from a system with at least `ell'` clusters and width at least `w'`, keep the
first `ell'` clusters and choose `w'` connector paths across every gap. -/
noncomputable def restrict
    (P : StrongPathOfSetsSystem G ell w)
    {ell' w' : ℕ} (hell_pos : 0 < ell') (hw_pos : 0 < w')
    (hell : ell' ≤ ell) (hw : w' ≤ w) :
    StrongPathOfSetsSystem G ell' w' :=
  (P.restrictWidth hw_pos hw).restrictLength hell_pos hell

/-- A strong path-of-sets system that is long and wide enough contains an exact
`g^2` by `g^2` strong subsystem. -/
noncomputable def restrictSquare
    (P : StrongPathOfSetsSystem G ell w) {g : ℕ}
    (hg : 2 ≤ g) (hell : g ^ 2 ≤ ell) (hw : g ^ 2 ≤ w) :
    StrongPathOfSetsSystem G (g ^ 2) (g ^ 2) :=
  P.restrict
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    hell hw

end StrongPathOfSetsSystem

end SimpleGraph

end Lax17Proofs
