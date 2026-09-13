import Mathlib.Data.Fin.Rev
import Lax17Proofs.Source.PathOfSets

namespace Lax17Proofs

universe u v w

/-!
# Reversing and joining strong path-of-sets systems

This module contains the order bookkeeping used in Step 2 of
Chekuri--Chuzhoy Theorem 4.6.  It is deliberately independent of the
many-leaves argument: reversing a path-of-sets system and joining two systems
across one additional connector are useful structural operations in their own
right.
-/

namespace SimpleGraph
namespace StrongPathOfSetsSystem


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w : ℕ}

/-- Transport a strong path-of-sets system across an equality of lengths. -/
noncomputable def castLength {ell' : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (h : ell = ell') :
    StrongPathOfSetsSystem G ell' w where
  length_pos := by
    rw [← h]
    exact P.length_pos
  width_pos := P.width_pos
  cluster := fun i => P.cluster (Fin.cast h.symm i)
  cluster_connected := fun i => P.cluster_connected (Fin.cast h.symm i)
  cluster_disjoint := by
    intro i j hij
    apply P.cluster_disjoint
    intro hc
    exact hij ((Fin.cast_injective h.symm) hc)
  left := fun i => P.left (Fin.cast h.symm i)
  right := fun i => P.right (Fin.cast h.symm i)
  left_subset_cluster := fun i => P.left_subset_cluster (Fin.cast h.symm i)
  right_subset_cluster := fun i => P.right_subset_cluster (Fin.cast h.symm i)
  left_right_disjoint := fun i => P.left_right_disjoint (Fin.cast h.symm i)
  left_card := fun i => P.left_card (Fin.cast h.symm i)
  right_card := fun i => P.right_card (Fin.cast h.symm i)
  connector := by
    intro i hi
    let j : Fin ell := Fin.cast h.symm i
    have hj : j.1 + 1 < ell := by
      change i.1 + 1 < ell
      rw [h]
      exact hi
    exact (P.connector j hj).copyTerminals rfl (by
      apply congrArg P.left
      apply Fin.ext
      rfl)
  connector_card := by
    intro i hi
    have hj : (Fin.cast h.symm i).1 + 1 < ell := by
      change i.1 + 1 < ell
      rw [h]
      exact hi
    change
      ((P.connector (Fin.cast h.symm i) hj).copyTerminals _ _).card = w
    simpa using P.connector_card (Fin.cast h.symm i) hj
  connector_internally_disjoint_clusters := by
    intro i hi j
    have hik : (Fin.cast h.symm i).1 + 1 < ell := by
      change i.1 + 1 < ell
      rw [h]
      exact hi
    change
      ((P.connector (Fin.cast h.symm i) hik).copyTerminals _ _).toPathPacking
        |>.InternallyDisjointFromSet (P.cluster (Fin.cast h.symm j))
    simpa using P.connector_internally_disjoint_clusters
      (Fin.cast h.symm i) hik (Fin.cast h.symm j)
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij
    have hik : (Fin.cast h.symm i).1 + 1 < ell := by
      change i.1 + 1 < ell
      rw [h]
      exact hi
    have hjk : (Fin.cast h.symm j).1 + 1 < ell := by
      change j.1 + 1 < ell
      rw [h]
      exact hj
    have hij' : Fin.cast h.symm i ≠ Fin.cast h.symm j := by
      intro hc
      exact hij ((Fin.cast_injective h.symm) hc)
    change
      ((P.connector (Fin.cast h.symm i) hik).copyTerminals _ _).toPathPacking
        |>.MutuallyNodeDisjoint
        ((P.connector (Fin.cast h.symm j) hjk).copyTerminals _ _).toPathPacking
    simpa using P.connector_mutually_nodeDisjoint hik hjk hij'
  left_nodeWellLinked := fun i => P.left_nodeWellLinked (Fin.cast h.symm i)
  right_nodeWellLinked := fun i => P.right_nodeWellLinked (Fin.cast h.symm i)
  left_right_nodeLinked := fun i =>
    P.left_right_nodeLinked (Fin.cast h.symm i)

@[simp] theorem castLength_cluster {ell' : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (h : ell = ell')
    (i : Fin ell') :
    (P.castLength h).cluster i = P.cluster (Fin.cast h.symm i) := by
  subst ell'
  rfl

@[simp] theorem castLength_left {ell' : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (h : ell = ell')
    (i : Fin ell') :
    (P.castLength h).left i = P.left (Fin.cast h.symm i) := by
  subst ell'
  rfl

@[simp] theorem castLength_right {ell' : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (h : ell = ell')
    (i : Fin ell') :
    (P.castLength h).right i = P.right (Fin.cast h.symm i) := by
  subst ell'
  rfl

@[simp] theorem castLength_firstIndex_cast {ell' : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (h : ell = ell') :
    Fin.cast h.symm (P.castLength h).toPathOfSetsSystem.firstIndex =
      P.toPathOfSetsSystem.firstIndex := by
  apply Fin.ext
  rfl

@[simp] theorem castLength_lastIndex_cast {ell' : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (h : ell = ell') :
    Fin.cast h.symm (P.castLength h).toPathOfSetsSystem.lastIndex =
      P.toPathOfSetsSystem.lastIndex := by
  apply Fin.ext
  exact congrArg (fun n => n - 1) h.symm

/-- Replace the unused left nail set of the first cluster.  No connector has
this set as an endpoint, so the path-of-sets data outside the first cluster is
unchanged. -/
noncomputable def replaceLeftFirst
    (P : StrongPathOfSetsSystem G ell w) (N : Finset V)
    (hNcluster : N ⊆ P.cluster P.toPathOfSetsSystem.firstIndex)
    (hNdisj :
      Disjoint N (P.right P.toPathOfSetsSystem.firstIndex))
    (hNcard : N.card = w)
    (hNwl :
      NodeWellLinkedIn G
        (P.cluster P.toPathOfSetsSystem.firstIndex) N)
    (hNlinked :
      NodeLinkedIn G
        (P.cluster P.toPathOfSetsSystem.firstIndex) N
        (P.right P.toPathOfSetsSystem.firstIndex)) :
    StrongPathOfSetsSystem G ell w where
  toPathOfSetsSystem := {
    P.toPathOfSetsSystem with
    left := fun i => if i = P.toPathOfSetsSystem.firstIndex then N else P.left i
    left_subset_cluster := by
      intro i
      by_cases hi : i = P.toPathOfSetsSystem.firstIndex
      · simpa [hi] using hNcluster
      · simp [hi, P.left_subset_cluster i]
    left_right_disjoint := by
      intro i
      by_cases hi : i = P.toPathOfSetsSystem.firstIndex
      · simpa [hi] using hNdisj
      · simp [hi, P.left_right_disjoint i]
    left_card := by
      intro i
      by_cases hi : i = P.toPathOfSetsSystem.firstIndex
      · simpa [hi] using hNcard
      · simp [hi, P.left_card i]
    connector := fun i hi =>
      (P.connector i hi).copyTerminals rfl (by
        have hnext :
            (⟨i.1 + 1, hi⟩ : Fin ell) ≠
              P.toPathOfSetsSystem.firstIndex := by
          intro h
          have := congrArg Fin.val h
          simp at this
        simp [hnext])
    connector_card := by
      intro i hi
      simpa using P.connector_card i hi
    connector_internally_disjoint_clusters :=
      P.connector_internally_disjoint_clusters
    connector_mutually_nodeDisjoint :=
      P.connector_mutually_nodeDisjoint }
  left_nodeWellLinked := by
    intro i
    by_cases hi : i = P.toPathOfSetsSystem.firstIndex
    · simpa [hi] using hNwl
    · simp [hi, P.left_nodeWellLinked i]
  right_nodeWellLinked := P.right_nodeWellLinked
  left_right_nodeLinked := by
    intro i
    by_cases hi : i = P.toPathOfSetsSystem.firstIndex
    · simpa [hi] using hNlinked
    · simp [hi, P.left_right_nodeLinked i]

@[simp] theorem replaceLeftFirst_cluster
    (P : StrongPathOfSetsSystem G ell w) (N : Finset V)
    (hNcluster hNdisj hNcard hNwl hNlinked)
    (i : Fin ell) :
    (P.replaceLeftFirst N hNcluster hNdisj hNcard hNwl hNlinked).cluster i =
      P.cluster i := rfl

@[simp] theorem replaceLeftFirst_left_first
    (P : StrongPathOfSetsSystem G ell w) (N : Finset V)
    (hNcluster hNdisj hNcard hNwl hNlinked) :
    (P.replaceLeftFirst N hNcluster hNdisj hNcard hNwl hNlinked).left
        P.toPathOfSetsSystem.firstIndex = N := by
  simp [replaceLeftFirst]

/-- Replace the unused right nail set of the last cluster. -/
noncomputable def replaceRightLast
    (P : StrongPathOfSetsSystem G ell w) (N : Finset V)
    (hNcluster : N ⊆ P.cluster P.toPathOfSetsSystem.lastIndex)
    (hNdisj :
      Disjoint (P.left P.toPathOfSetsSystem.lastIndex) N)
    (hNcard : N.card = w)
    (hNwl :
      NodeWellLinkedIn G
        (P.cluster P.toPathOfSetsSystem.lastIndex) N)
    (hNlinked :
      NodeLinkedIn G
        (P.cluster P.toPathOfSetsSystem.lastIndex)
        (P.left P.toPathOfSetsSystem.lastIndex) N) :
    StrongPathOfSetsSystem G ell w where
  toPathOfSetsSystem := {
    P.toPathOfSetsSystem with
    right := fun i => if i = P.toPathOfSetsSystem.lastIndex then N else P.right i
    right_subset_cluster := by
      intro i
      by_cases hi : i = P.toPathOfSetsSystem.lastIndex
      · simpa [hi] using hNcluster
      · simp [hi, P.right_subset_cluster i]
    left_right_disjoint := by
      intro i
      by_cases hi : i = P.toPathOfSetsSystem.lastIndex
      · simpa [hi] using hNdisj
      · simp [hi, P.left_right_disjoint i]
    right_card := by
      intro i
      by_cases hi : i = P.toPathOfSetsSystem.lastIndex
      · simpa [hi] using hNcard
      · simp [hi, P.right_card i]
    connector := fun i hi =>
      (P.connector i hi).copyTerminals (by
        have hiNotLast :
            i ≠ P.toPathOfSetsSystem.lastIndex := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp [hiNotLast]) rfl
    connector_card := by
      intro i hi
      simpa using P.connector_card i hi
    connector_internally_disjoint_clusters :=
      P.connector_internally_disjoint_clusters
    connector_mutually_nodeDisjoint :=
      P.connector_mutually_nodeDisjoint }
  left_nodeWellLinked := P.left_nodeWellLinked
  right_nodeWellLinked := by
    intro i
    by_cases hi : i = P.toPathOfSetsSystem.lastIndex
    · simpa [hi] using hNwl
    · simp [hi, P.right_nodeWellLinked i]
  left_right_nodeLinked := by
    intro i
    by_cases hi : i = P.toPathOfSetsSystem.lastIndex
    · simpa [hi] using hNlinked
    · simp [hi, P.left_right_nodeLinked i]

@[simp] theorem replaceRightLast_cluster
    (P : StrongPathOfSetsSystem G ell w) (N : Finset V)
    (hNcluster hNdisj hNcard hNwl hNlinked)
    (i : Fin ell) :
    (P.replaceRightLast N hNcluster hNdisj hNcard hNwl hNlinked).cluster i =
      P.cluster i := rfl

@[simp] theorem replaceRightLast_right_last
    (P : StrongPathOfSetsSystem G ell w) (N : Finset V)
    (hNcluster hNdisj hNcard hNwl hNlinked) :
    (P.replaceRightLast N hNcluster hNdisj hNcard hNwl hNlinked).right
        P.toPathOfSetsSystem.lastIndex = N := by
  simp [replaceRightLast]

/-- `NodeLinkedIn` is symmetric in its two terminal sets. -/
theorem nodeLinkedIn_symm_public {C A B : Finset V}
    (h : NodeLinkedIn G C A B) :
    NodeLinkedIn G C B A := by
  refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
  intro B' A' hB' hA'
  rcases h.2.2.2 hA' hB' with ⟨Q, hQcard, hQstay⟩
  let R : PathPacking G B' A' := {
    Index := Q.Index
    path := fun i => (Q.path i).reverse
    connects := by
      intro i
      rcases Q.connects i with hi | hi
      · exact Or.inl ⟨by simpa using hi.2, by simpa using hi.1⟩
      · exact Or.inr ⟨by simpa using hi.2, by simpa using hi.1⟩
    node_disjoint := by
      intro i j hij
      simpa [GraphPath.NodeDisjoint] using Q.node_disjoint hij }
  refine ⟨R, ?_, ?_⟩
  · change Q.card = min B'.card A'.card
    simpa [Nat.min_comm] using hQcard
  · intro i
    change (Q.path i).reverse.vertexSet ⊆ C
    simpa using hQstay i

/-- Reverse the order of a strong path-of-sets system.  The old connector
across the corresponding gap is reversed as a perfect path packing. -/
noncomputable def reverse (P : StrongPathOfSetsSystem G ell w) :
    StrongPathOfSetsSystem G ell w where
  length_pos := P.length_pos
  width_pos := P.width_pos
  cluster := fun i => P.cluster i.rev
  cluster_connected := fun i => P.cluster_connected i.rev
  cluster_disjoint := by
    intro i j hij
    apply P.cluster_disjoint
    exact fun h => hij (Fin.rev_injective h)
  left := fun i => P.right i.rev
  right := fun i => P.left i.rev
  left_subset_cluster := fun i => P.right_subset_cluster i.rev
  right_subset_cluster := fun i => P.left_subset_cluster i.rev
  left_right_disjoint := fun i => (P.left_right_disjoint i.rev).symm
  left_card := fun i => P.right_card i.rev
  right_card := fun i => P.left_card i.rev
  connector := fun i hi =>
    let j : Fin ell := ⟨ell - 2 - i.1, by omega⟩
    let hj : j.1 + 1 < ell := by
      dsimp [j]
      omega
    (P.connector j hj).reverse.copyTerminals
      (by
        apply congrArg P.left
        apply Fin.ext
        dsimp [j]
        change ell - 2 - i.1 + 1 = ell - (i.1 + 1)
        omega)
      (by
        apply congrArg P.right
        apply Fin.ext
        dsimp [j]
        change ell - 2 - i.1 = ell - (i.1 + 1 + 1)
        omega)
  connector_card := by
    intro i hi
    dsimp
    change
      (P.connector ⟨ell - 2 - i.1, by omega⟩
        (by simp only [Fin.val_mk]; omega)).card = w
    exact P.connector_card ⟨ell - 2 - i.1, by omega⟩ (by
      simp only [Fin.val_mk]
      omega)
  connector_internally_disjoint_clusters := by
    intro i hi k
    dsimp
    intro a v hv hvC
    have hrev :=
      PerfectPathPacking.reverse_internallyDisjointFromSet
        (P.connector ⟨ell - 2 - i.1, by omega⟩
          (by simp only [Fin.val_mk]; omega))
        (P.connector_internally_disjoint_clusters
          ⟨ell - 2 - i.1, by omega⟩
          (by simp only [Fin.val_mk]; omega) k.rev)
    exact hrev a hv hvC
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij
    dsimp
    intro a b
    change GraphPath.NodeDisjoint
      ((P.connector ⟨ell - 2 - i.1, by omega⟩
        (by simp only [Fin.val_mk]; omega)).path a).reverse
      ((P.connector ⟨ell - 2 - j.1, by omega⟩
        (by simp only [Fin.val_mk]; omega)).path b).reverse
    simpa [GraphPath.NodeDisjoint] using
      P.connector_mutually_nodeDisjoint
        (i := ⟨ell - 2 - i.1, by omega⟩)
        (j := ⟨ell - 2 - j.1, by omega⟩)
        (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)
        (by
          intro h
          apply hij
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [Fin.val_mk] at hv
          omega) a b
  left_nodeWellLinked := fun i => P.right_nodeWellLinked i.rev
  right_nodeWellLinked := fun i => P.left_nodeWellLinked i.rev
  left_right_nodeLinked := fun i =>
    nodeLinkedIn_symm_public (P.left_right_nodeLinked i.rev)

@[simp] theorem reverse_cluster (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell) :
    P.reverse.cluster i = P.cluster i.rev := rfl

@[simp] theorem reverse_left (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell) :
    P.reverse.left i = P.right i.rev := rfl

@[simp] theorem reverse_right (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell) :
    P.reverse.right i = P.left i.rev := rfl

section Join

variable {ell₁ ell₂ : ℕ}

/-- The concatenated cluster sequence. -/
private def joinCluster
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) :
    Fin (ell₁ + ell₂) → Finset V :=
  Fin.addCases P.cluster Q.cluster

/-- The concatenated left-nail sequence. -/
private def joinLeft
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) :
    Fin (ell₁ + ell₂) → Finset V :=
  Fin.addCases P.left Q.left

/-- The concatenated right-nail sequence. -/
private def joinRight
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) :
    Fin (ell₁ + ell₂) → Finset V :=
  Fin.addCases P.right Q.right

@[simp] private theorem joinCluster_castAdd
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) (i : Fin ell₁) :
    joinCluster P Q (Fin.castAdd ell₂ i) = P.cluster i :=
  Fin.addCases_left _

@[simp] private theorem joinCluster_natAdd
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) (i : Fin ell₂) :
    joinCluster P Q (Fin.natAdd ell₁ i) = Q.cluster i :=
  Fin.addCases_right _

@[simp] private theorem joinLeft_castAdd
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) (i : Fin ell₁) :
    joinLeft P Q (Fin.castAdd ell₂ i) = P.left i :=
  Fin.addCases_left _

@[simp] private theorem joinLeft_natAdd
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) (i : Fin ell₂) :
    joinLeft P Q (Fin.natAdd ell₁ i) = Q.left i :=
  Fin.addCases_right _

@[simp] private theorem joinRight_castAdd
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) (i : Fin ell₁) :
    joinRight P Q (Fin.castAdd ell₂ i) = P.right i :=
  Fin.addCases_left _

@[simp] private theorem joinRight_natAdd
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w) (i : Fin ell₂) :
    joinRight P Q (Fin.natAdd ell₁ i) = Q.right i :=
  Fin.addCases_right _

/-- Connector across a gap in the concatenation of `P` and `Q`.  Gaps wholly
inside either child use that child's connector; the unique middle gap uses
`bridge`. -/
noncomputable def joinConnector
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w)
    (bridge : PerfectPathPacking G
      (P.right P.toPathOfSetsSystem.lastIndex)
      (Q.left Q.toPathOfSetsSystem.firstIndex))
    (i : Fin (ell₁ + ell₂)) (hi : i.1 + 1 < ell₁ + ell₂) :
    PerfectPathPacking G (joinRight P Q i)
      (joinLeft P Q ⟨i.1 + 1, hi⟩) := by
  classical
  by_cases hinsideP : i.1 + 1 < ell₁
  · let a : Fin ell₁ := ⟨i.1, by omega⟩
    let ha : a.1 + 1 < ell₁ := by
      dsimp [a]
      omega
    have hiEq : i = Fin.castAdd ell₂ a := by
      apply Fin.ext
      rfl
    let aNext : Fin ell₁ := ⟨a.1 + 1, ha⟩
    have hnextEq :
        (⟨i.1 + 1, hi⟩ : Fin (ell₁ + ell₂)) =
          Fin.castAdd ell₂ aNext := by
      apply Fin.ext
      rfl
    exact (P.connector a ha).copyTerminals
      (by
        rw [hiEq]
        simp [joinRight])
      (by
        rw [hnextEq]
        exact (joinLeft_castAdd P Q aNext).symm)
  · by_cases hinP : i.1 < ell₁
    · have hiLast : i = Fin.castAdd ell₂ P.toPathOfSetsSystem.lastIndex := by
        apply Fin.ext
        simp only [PathOfSetsSystem.lastIndex_val, Fin.coe_castAdd]
        omega
      have hnextFirst :
          (⟨i.1 + 1, hi⟩ : Fin (ell₁ + ell₂)) =
            Fin.natAdd ell₁ Q.toPathOfSetsSystem.firstIndex := by
        apply Fin.ext
        simp only [PathOfSetsSystem.firstIndex_val, Fin.coe_natAdd]
        omega
      exact bridge.copyTerminals
        (by
          rw [hiLast]
          simp [joinRight])
        (by
          rw [hnextFirst]
          simp [joinLeft])
    · let a : Fin ell₂ := ⟨i.1 - ell₁, by omega⟩
      let ha : a.1 + 1 < ell₂ := by
        dsimp [a]
        omega
      have hiEq : i = Fin.natAdd ell₁ a := by
        apply Fin.ext
        dsimp [a]
        change i.1 = ell₁ + (i.1 - ell₁)
        omega
      let aNext : Fin ell₂ := ⟨a.1 + 1, ha⟩
      have hnextEq :
          (⟨i.1 + 1, hi⟩ : Fin (ell₁ + ell₂)) =
            Fin.natAdd ell₁ aNext := by
        apply Fin.ext
        dsimp [a, aNext]
        change i.1 + 1 = ell₁ + (i.1 - ell₁ + 1)
        omega
      exact (Q.connector a ha).copyTerminals
        (by
          rw [hiEq]
          simp [joinRight])
        (by
          rw [hnextEq]
          exact (joinLeft_natAdd P Q aNext).symm)

/-- Join two strong path-of-sets systems across one additional connector.

The four proof arguments are the actual global compatibility obligations in a
DFS merge: distinct clusters remain disjoint, every selected connector has
the correct width, connectors avoid all clusters internally, and different
gaps use mutually node-disjoint connector families. -/
noncomputable def join
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w)
    (bridge : PerfectPathPacking G
      (P.right P.toPathOfSetsSystem.lastIndex)
      (Q.left Q.toPathOfSetsSystem.firstIndex))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin (ell₁ + ell₂)⦄, i ≠ j →
        Disjoint (joinCluster P Q i) (joinCluster P Q j))
    (hconnectorCard :
      ∀ (i : Fin (ell₁ + ell₂)) (hi : i.1 + 1 < ell₁ + ell₂),
        (joinConnector P Q bridge i hi).card = w)
    (hconnectorInternal :
      ∀ (i : Fin (ell₁ + ell₂)) (hi : i.1 + 1 < ell₁ + ell₂)
        (j : Fin (ell₁ + ell₂)),
        (joinConnector P Q bridge i hi).toPathPacking
          |>.InternallyDisjointFromSet (joinCluster P Q j))
    (hconnectorMutual :
      ∀ ⦃i j : Fin (ell₁ + ell₂)⦄
        (hi : i.1 + 1 < ell₁ + ell₂)
        (hj : j.1 + 1 < ell₁ + ell₂), i ≠ j →
        (joinConnector P Q bridge i hi).toPathPacking.MutuallyNodeDisjoint
          (joinConnector P Q bridge j hj).toPathPacking) :
    StrongPathOfSetsSystem G (ell₁ + ell₂) w where
  length_pos := Nat.add_pos_left P.length_pos ell₂
  width_pos := P.width_pos
  cluster := joinCluster P Q
  cluster_connected := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinCluster_castAdd] using P.cluster_connected a
    · simpa only [joinCluster_natAdd] using Q.cluster_connected a
  cluster_disjoint := hclusterDisjoint
  left := joinLeft P Q
  right := joinRight P Q
  left_subset_cluster := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinLeft_castAdd, joinCluster_castAdd] using
        P.left_subset_cluster a
    · simpa only [joinLeft_natAdd, joinCluster_natAdd] using
        Q.left_subset_cluster a
  right_subset_cluster := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinRight_castAdd, joinCluster_castAdd] using
        P.right_subset_cluster a
    · simpa only [joinRight_natAdd, joinCluster_natAdd] using
        Q.right_subset_cluster a
  left_right_disjoint := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinLeft_castAdd, joinRight_castAdd] using
        P.left_right_disjoint a
    · simpa only [joinLeft_natAdd, joinRight_natAdd] using
        Q.left_right_disjoint a
  left_card := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinLeft_castAdd] using P.left_card a
    · simpa only [joinLeft_natAdd] using Q.left_card a
  right_card := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinRight_castAdd] using P.right_card a
    · simpa only [joinRight_natAdd] using Q.right_card a
  connector := joinConnector P Q bridge
  connector_card := hconnectorCard
  connector_internally_disjoint_clusters := hconnectorInternal
  connector_mutually_nodeDisjoint := hconnectorMutual
  left_nodeWellLinked := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinCluster_castAdd, joinLeft_castAdd] using
        P.left_nodeWellLinked a
    · simpa only [joinCluster_natAdd, joinLeft_natAdd] using
        Q.left_nodeWellLinked a
  right_nodeWellLinked := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinCluster_castAdd, joinRight_castAdd] using
        P.right_nodeWellLinked a
    · simpa only [joinCluster_natAdd, joinRight_natAdd] using
        Q.right_nodeWellLinked a
  left_right_nodeLinked := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [joinCluster_castAdd, joinLeft_castAdd,
        joinRight_castAdd] using P.left_right_nodeLinked a
    · simpa only [joinCluster_natAdd, joinLeft_natAdd,
        joinRight_natAdd] using Q.left_right_nodeLinked a

theorem copyTerminals_internallyDisjointFromSet
    {S T S' T' C : Finset V}
    (R : PerfectPathPacking G S T) (hS : S = S') (hT : T = T')
    (h : R.toPathPacking.InternallyDisjointFromSet C) :
    (R.copyTerminals hS hT).toPathPacking.InternallyDisjointFromSet C :=
  h

theorem copyTerminals_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ S₁' T₁' S₂' T₂' : Finset V}
    (R₁ : PerfectPathPacking G S₁ T₁)
    (R₂ : PerfectPathPacking G S₂ T₂)
    (hS₁ : S₁ = S₁') (hT₁ : T₁ = T₁')
    (hS₂ : S₂ = S₂') (hT₂ : T₂ = T₂')
    (h : R₁.toPathPacking.MutuallyNodeDisjoint R₂.toPathPacking) :
    (R₁.copyTerminals hS₁ hT₁).toPathPacking.MutuallyNodeDisjoint
      (R₂.copyTerminals hS₂ hT₂).toPathPacking :=
  h

set_option maxRecDepth 10000 in
/-- A source-facing form of `join`.  It separates the four global
compatibility fields into the six local obligations which arise in a DFS
merge: the two old systems are already valid, so one only has to check
cross-system clusters and connectors and the new middle connector. -/
noncomputable def joinOfCompatible
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w)
    (bridge : PerfectPathPacking G
      (P.right P.toPathOfSetsSystem.lastIndex)
      (Q.left Q.toPathOfSetsSystem.firstIndex))
    (hcrossCluster :
      ∀ (i : Fin ell₁) (j : Fin ell₂),
        Disjoint (P.cluster i) (Q.cluster j))
    (hbridgeCard : bridge.card = w)
    (hbridgeInternalP :
      ∀ i : Fin ell₁,
        bridge.toPathPacking.InternallyDisjointFromSet (P.cluster i))
    (hbridgeInternalQ :
      ∀ j : Fin ell₂,
        bridge.toPathPacking.InternallyDisjointFromSet (Q.cluster j))
    (hPConnectorInternalQ :
      ∀ (i : Fin ell₁) (hi : i.1 + 1 < ell₁) (j : Fin ell₂),
        (P.connector i hi).toPathPacking
          |>.InternallyDisjointFromSet (Q.cluster j))
    (hQConnectorInternalP :
      ∀ (j : Fin ell₂) (hj : j.1 + 1 < ell₂) (i : Fin ell₁),
        (Q.connector j hj).toPathPacking
          |>.InternallyDisjointFromSet (P.cluster i))
    (hcrossConnector :
      ∀ (i : Fin ell₁) (hi : i.1 + 1 < ell₁)
        (j : Fin ell₂) (hj : j.1 + 1 < ell₂),
        (P.connector i hi).toPathPacking.MutuallyNodeDisjoint
          (Q.connector j hj).toPathPacking)
    (hPBridge :
      ∀ (i : Fin ell₁) (hi : i.1 + 1 < ell₁),
        (P.connector i hi).toPathPacking.MutuallyNodeDisjoint
          bridge.toPathPacking)
    (hBridgeQ :
      ∀ (j : Fin ell₂) (hj : j.1 + 1 < ell₂),
        bridge.toPathPacking.MutuallyNodeDisjoint
          (Q.connector j hj).toPathPacking) :
    StrongPathOfSetsSystem G (ell₁ + ell₂) w := by
  classical
  apply join P Q bridge
  · intro i j hij
    revert j
    refine Fin.addCases (motive := fun i =>
      ∀ j, i ≠ j → Disjoint (joinCluster P Q i) (joinCluster P Q j))
      (fun a => ?_) (fun a => ?_) i
    · refine Fin.addCases (fun b hab => ?_) (fun b _ => ?_)
      · simpa only [joinCluster_castAdd] using P.cluster_disjoint (by
          intro h
          apply hab
          simpa [h])
      · simpa only [joinCluster_castAdd, joinCluster_natAdd] using
          hcrossCluster a b
    · refine Fin.addCases (fun b _ => ?_) (fun b hab => ?_)
      · simpa only [joinCluster_natAdd, joinCluster_castAdd] using
          (hcrossCluster b a).symm
      · simpa only [joinCluster_natAdd] using Q.cluster_disjoint (by
          intro h
          apply hab
          simpa [h])
  · intro i hi
    by_cases hinsideP : i.1 + 1 < ell₁
    · simp [joinConnector, hinsideP, P.connector_card]
    · by_cases hinP : i.1 < ell₁
      · simpa [joinConnector, hinsideP, hinP] using hbridgeCard
      · simp [joinConnector, hinsideP, hinP, Q.connector_card]
  · intro i hi j
    by_cases hinsideP : i.1 + 1 < ell₁
    · by_cases hjP : j.1 < ell₁
      · let a : Fin ell₁ := ⟨i.1, by omega⟩
        let ha : a.1 + 1 < ell₁ := by
          dsimp [a]
          omega
        let b : Fin ell₁ := ⟨j.1, hjP⟩
        have hjEq : j = Fin.castAdd ell₂ b := by
          apply Fin.ext
          rfl
        rw [hjEq]
        simpa [joinConnector, hinsideP, a, ha] using
          (copyTerminals_internallyDisjointFromSet
            (P.connector a ha) _ _
            (P.connector_internally_disjoint_clusters a ha b))
      · let a : Fin ell₁ := ⟨i.1, by omega⟩
        let ha : a.1 + 1 < ell₁ := by
          dsimp [a]
          omega
        let b : Fin ell₂ := ⟨j.1 - ell₁, by omega⟩
        have hjEq : j = Fin.natAdd ell₁ b := by
          apply Fin.ext
          dsimp [b]
          omega
        rw [hjEq]
        simpa [joinConnector, hinsideP, a, ha] using
          (copyTerminals_internallyDisjointFromSet
            (P.connector a ha) _ _ (hPConnectorInternalQ a ha b))
    · by_cases hinP : i.1 < ell₁
      · by_cases hjP : j.1 < ell₁
        · let b : Fin ell₁ := ⟨j.1, hjP⟩
          have hjEq : j = Fin.castAdd ell₂ b := by
            apply Fin.ext
            rfl
          rw [hjEq]
          simpa [joinConnector, hinsideP, hinP] using
            (copyTerminals_internallyDisjointFromSet
              bridge _ _ (hbridgeInternalP b))
        · let b : Fin ell₂ := ⟨j.1 - ell₁, by omega⟩
          have hjEq : j = Fin.natAdd ell₁ b := by
            apply Fin.ext
            dsimp [b]
            omega
          rw [hjEq]
          simpa [joinConnector, hinsideP, hinP] using
            (copyTerminals_internallyDisjointFromSet
              bridge _ _ (hbridgeInternalQ b))
      · let a : Fin ell₂ := ⟨i.1 - ell₁, by omega⟩
        let ha : a.1 + 1 < ell₂ := by
          dsimp [a]
          omega
        by_cases hjP : j.1 < ell₁
        · let b : Fin ell₁ := ⟨j.1, hjP⟩
          have hjEq : j = Fin.castAdd ell₂ b := by
            apply Fin.ext
            rfl
          rw [hjEq]
          simpa [joinConnector, hinsideP, hinP, a, ha] using
            (copyTerminals_internallyDisjointFromSet
              (Q.connector a ha) _ _ (hQConnectorInternalP a ha b))
        · let b : Fin ell₂ := ⟨j.1 - ell₁, by omega⟩
          have hjEq : j = Fin.natAdd ell₁ b := by
            apply Fin.ext
            dsimp [b]
            omega
          rw [hjEq]
          simpa [joinConnector, hinsideP, hinP, a, ha] using
            (copyTerminals_internallyDisjointFromSet
              (Q.connector a ha) _ _
              (Q.connector_internally_disjoint_clusters a ha b))
  · intro i j hi hj hij
    by_cases hiInsideP : i.1 + 1 < ell₁
    · let a : Fin ell₁ := ⟨i.1, by omega⟩
      let ha : a.1 + 1 < ell₁ := by
        dsimp [a]
        omega
      by_cases hjInsideP : j.1 + 1 < ell₁
      · let b : Fin ell₁ := ⟨j.1, by omega⟩
        let hb : b.1 + 1 < ell₁ := by
          dsimp [b]
          omega
        simpa [joinConnector, hiInsideP, hjInsideP, a, ha, b, hb] using
          P.connector_mutually_nodeDisjoint ha hb (by
            intro h
            apply hij
            apply Fin.ext
            simpa [a, b] using congrArg Fin.val h)
      · by_cases hjInP : j.1 < ell₁
        · simpa [joinConnector, hiInsideP, hjInsideP, hjInP, a, ha] using
            hPBridge a ha
        · let b : Fin ell₂ := ⟨j.1 - ell₁, by omega⟩
          let hb : b.1 + 1 < ell₂ := by
            dsimp [b]
            omega
          simpa [joinConnector, hiInsideP, hjInsideP, hjInP, a, ha, b, hb] using
            hcrossConnector a ha b hb
    · by_cases hiInP : i.1 < ell₁
      · by_cases hjInsideP : j.1 + 1 < ell₁
        · let b : Fin ell₁ := ⟨j.1, by omega⟩
          let hb : b.1 + 1 < ell₁ := by
            dsimp [b]
            omega
          simpa [joinConnector, hiInsideP, hiInP, hjInsideP, b, hb] using
            PathPacking.mutuallyNodeDisjoint_symm (hPBridge b hb)
        · by_cases hjInP : j.1 < ell₁
          · exfalso
            apply hij
            apply Fin.ext
            omega
          · let b : Fin ell₂ := ⟨j.1 - ell₁, by omega⟩
            let hb : b.1 + 1 < ell₂ := by
              dsimp [b]
              omega
            simpa [joinConnector, hiInsideP, hiInP, hjInsideP, hjInP, b, hb] using
              hBridgeQ b hb
      · let a : Fin ell₂ := ⟨i.1 - ell₁, by omega⟩
        let ha : a.1 + 1 < ell₂ := by
          dsimp [a]
          omega
        by_cases hjInsideP : j.1 + 1 < ell₁
        · let b : Fin ell₁ := ⟨j.1, by omega⟩
          let hb : b.1 + 1 < ell₁ := by
            dsimp [b]
            omega
          simpa [joinConnector, hiInsideP, hiInP, hjInsideP, a, ha, b, hb] using
            PathPacking.mutuallyNodeDisjoint_symm
              (hcrossConnector b hb a ha)
        · by_cases hjInP : j.1 < ell₁
          · simpa [joinConnector, hiInsideP, hiInP, hjInsideP, hjInP, a, ha] using
              PathPacking.mutuallyNodeDisjoint_symm (hBridgeQ a ha)
          · let b : Fin ell₂ := ⟨j.1 - ell₁, by omega⟩
            let hb : b.1 + 1 < ell₂ := by
              dsimp [b]
              omega
            simpa [joinConnector, hiInsideP, hiInP, hjInsideP, hjInP,
                a, ha, b, hb] using
              Q.connector_mutually_nodeDisjoint ha hb (by
                intro h
                apply hij
                apply Fin.ext
                have hiVal :
                    ell₁ + (i.1 - ell₁) = i.1 :=
                  Nat.add_sub_of_le (Nat.le_of_not_gt hiInP)
                have hjVal :
                    ell₁ + (j.1 - ell₁) = j.1 :=
                  Nat.add_sub_of_le (Nat.le_of_not_gt hjInP)
                have hv := congrArg Fin.val h
                dsimp [a, b] at hv
                omega)

/-- A joined connector is supported wherever the two old connector families
and the new middle connector are supported. -/
theorem joinConnector_staysIn
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w)
    (bridge : PerfectPathPacking G
      (P.right P.toPathOfSetsSystem.lastIndex)
      (Q.left Q.toPathOfSetsSystem.firstIndex))
    {C : Finset V}
    (hP :
      ∀ (i : Fin ell₁) (hi : i.1 + 1 < ell₁),
        (P.connector i hi).toPathPacking.StaysIn C)
    (hbridge : bridge.toPathPacking.StaysIn C)
    (hQ :
      ∀ (j : Fin ell₂) (hj : j.1 + 1 < ell₂),
        (Q.connector j hj).toPathPacking.StaysIn C)
    (i : Fin (ell₁ + ell₂)) (hi : i.1 + 1 < ell₁ + ell₂) :
    (joinConnector P Q bridge i hi).toPathPacking.StaysIn C := by
  classical
  by_cases hinsideP : i.1 + 1 < ell₁
  · simpa [joinConnector, hinsideP] using
      hP ⟨i.1, by omega⟩ (by omega)
  · by_cases hinP : i.1 < ell₁
    · simpa [joinConnector, hinsideP, hinP] using hbridge
    · have hge : ell₁ ≤ i.1 := Nat.le_of_not_gt hinP
      let j : Fin ell₂ := ⟨i.1 - ell₁, by omega⟩
      have hj : j.1 + 1 < ell₂ := by
        dsimp [j]
        omega
      simpa [joinConnector, hinsideP, hinP, j, hj] using hQ j hj

/-- A packing disjoint from every old connector and the middle bridge is
disjoint from every connector of the joined system. -/
theorem mutuallyNodeDisjoint_joinConnector
    {X Y : Finset V}
    (R : PathPacking G X Y)
    (P : StrongPathOfSetsSystem G ell₁ w)
    (Q : StrongPathOfSetsSystem G ell₂ w)
    (bridge : PerfectPathPacking G
      (P.right P.toPathOfSetsSystem.lastIndex)
      (Q.left Q.toPathOfSetsSystem.firstIndex))
    (hP :
      ∀ (i : Fin ell₁) (hi : i.1 + 1 < ell₁),
        R.MutuallyNodeDisjoint (P.connector i hi).toPathPacking)
    (hbridge : R.MutuallyNodeDisjoint bridge.toPathPacking)
    (hQ :
      ∀ (j : Fin ell₂) (hj : j.1 + 1 < ell₂),
        R.MutuallyNodeDisjoint (Q.connector j hj).toPathPacking)
    (i : Fin (ell₁ + ell₂)) (hi : i.1 + 1 < ell₁ + ell₂) :
    R.MutuallyNodeDisjoint
      (joinConnector P Q bridge i hi).toPathPacking := by
  classical
  by_cases hinsideP : i.1 + 1 < ell₁
  · simpa [joinConnector, hinsideP] using
      hP ⟨i.1, by omega⟩ (by omega)
  · by_cases hinP : i.1 < ell₁
    · simpa [joinConnector, hinsideP, hinP] using hbridge
    · have hge : ell₁ ≤ i.1 := Nat.le_of_not_gt hinP
      let j : Fin ell₂ := ⟨i.1 - ell₁, by omega⟩
      have hj : j.1 + 1 < ell₂ := by
        dsimp [j]
        omega
      simpa [joinConnector, hinsideP, hinP, j, hj] using hQ j hj

end Join

end StrongPathOfSetsSystem
end SimpleGraph

end Lax17Proofs
