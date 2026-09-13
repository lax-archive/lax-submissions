import Lax17Proofs.Source.Theorem214Nonconstructive
import Lax17Proofs.Source.ReedTreeDecompositionRecursion

namespace Lax17Proofs

universe u v w

/-!
# A node-well-linked separator oracle for Reed's recursion

A maximum-cardinality node-well-linked set in the full graph bounds every
locally node-well-linked set.  Minimum balanced separations therefore provide
the bounded-overlap oracle used by Reed's tree-decomposition recursion.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- All globally node-well-linked vertex sets. -/
noncomputable def globalNodeWellLinkedSets
    (G : _root_.SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun T =>
    NodeWellLinkedIn G Finset.univ T

theorem globalNodeWellLinkedSets_nonempty
    (G : _root_.SimpleGraph V) :
    (globalNodeWellLinkedSets G).Nonempty := by
  classical
  have hempty : NodeWellLinkedIn G Finset.univ (∅ : Finset V) :=
    Section46.nodeWellLinkedIn_of_card_le_one (by simp) (by simp)
  refine ⟨∅, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (by simp), hempty⟩

/-- A globally node-well-linked set of maximum cardinality. -/
noncomputable def maximumNodeWellLinkedSet
    (G : _root_.SimpleGraph V) : Finset V :=
  Classical.choose
    (Finset.exists_max_image (globalNodeWellLinkedSets G) Finset.card
      (globalNodeWellLinkedSets_nonempty G))

theorem maximumNodeWellLinkedSet_mem
    (G : _root_.SimpleGraph V) :
    maximumNodeWellLinkedSet G ∈ globalNodeWellLinkedSets G := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_max_image (globalNodeWellLinkedSets G) Finset.card
      (globalNodeWellLinkedSets_nonempty G))).1

theorem maximumNodeWellLinkedSet_maximal
    (G : _root_.SimpleGraph V) {X : Finset V}
    (hX : X ∈ globalNodeWellLinkedSets G) :
    X.card ≤ (maximumNodeWellLinkedSet G).card := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_max_image (globalNodeWellLinkedSets G) Finset.card
      (globalNodeWellLinkedSets_nonempty G))).2 X hX

/-- The selected maximum set is globally node-well-linked. -/
theorem maximumNodeWellLinkedSet_nodeWellLinked
    (G : _root_.SimpleGraph V) :
    NodeWellLinkedIn G Finset.univ (maximumNodeWellLinkedSet G) := by
  classical
  exact (Finset.mem_filter.mp (maximumNodeWellLinkedSet_mem G)).2

/-- Every locally node-well-linked set has cardinality at most the selected
global maximum. -/
theorem nodeWellLinkedIn_card_le_maximum
    {C X : Finset V} (hX : NodeWellLinkedIn G C X) :
    X.card ≤ (maximumNodeWellLinkedSet G).card := by
  classical
  have hglobal : NodeWellLinkedIn G Finset.univ X :=
    nodeWellLinkedIn_mono_region hX (by simp)
  apply maximumNodeWellLinkedSet_maximal G
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (by simp), hglobal⟩

/-- A nonempty vertex type forces the maximum cardinality to be positive. -/
theorem maximumNodeWellLinkedSet_card_pos
    (G : _root_.SimpleGraph V) [Nonempty V] :
    0 < (maximumNodeWellLinkedSet G).card := by
  classical
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have hsingleton : NodeWellLinkedIn G Finset.univ ({v} : Finset V) :=
    Section46.nodeWellLinkedIn_of_card_le_one (by simp) (by simp)
  have hle := nodeWellLinkedIn_card_le_maximum (G := G) hsingleton
  simpa using hle

/-- Minimum balanced separations form the separator oracle at the cardinality
of a maximum globally node-well-linked set. -/
theorem separatorOracle_of_maximumNodeWellLinkedSet
    (G : _root_.SimpleGraph V) :
    ReedTreeDecomposition.SeparatorOracle G
      (maximumNodeWellLinkedSet G).card := by
  classical
  intro C R hRC _hRlower _hRupper
  rcases exists_minimum_balancedSeparation_overlap_nodeWellLinked
      (G := G) (C := C) (T := R) (κ := R.card) hRC rfl with
    ⟨Y, Z, hYZ, _hmin, _hhalf, hoverlap⟩
  exact ⟨Y, Z, hYZ, nodeWellLinkedIn_card_le_maximum hoverlap⟩

/-- Every finite graph has a globally node-well-linked terminal set whose
cardinality controls treewidth within the factor supplied by Reed's recursion.
-/
theorem exists_nodeWellLinked_treewidth_le_nine_mul_card
    (G : _root_.SimpleGraph V) :
    ∃ T : Finset V,
      NodeWellLinkedIn G Finset.univ T ∧ treewidth G ≤ 9 * T.card := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hEmpty =>
      letI : IsEmpty V := hEmpty
      refine ⟨∅, Section46.nodeWellLinkedIn_of_card_le_one (by simp) (by simp), ?_⟩
      simpa using treewidth_le_card_sub_one G
  | inr hNonempty =>
      letI : Nonempty V := hNonempty
      let T := maximumNodeWellLinkedSet G
      have hk : 0 < T.card := maximumNodeWellLinkedSet_card_pos G
      have htw : HasTreewidthAtMost G (9 * T.card) :=
        ReedTreeDecomposition.hasTreewidthAtMost_of_separatorOracle
          G T.card hk (separatorOracle_of_maximumNodeWellLinkedSet G)
      exact ⟨T, maximumNodeWellLinkedSet_nodeWellLinked G,
        treewidth_le_of_hasTreewidthAtMost htw⟩

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
