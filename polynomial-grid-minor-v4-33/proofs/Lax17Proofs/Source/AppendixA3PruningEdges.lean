import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma75Budget

namespace Lax17Proofs

universe u v w

/-!
# Actual deleted-edge bookkeeping for Observation 7.7

The proof of Observation 7.7 maintains an actual edge set `E'`, not only its
cardinality.  This module lifts the one-step budget from
`AppendixA3Lemma75Budget` to a union of finite edge sets and records the
nested-cut containment used when the current set is replaced by one side of a
violating partition.

All budget inequalities are multiplied through by eight.  In particular, no
natural-number division is used to represent the source's `1/8` budget.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- One pruning step with the actual deleted-edge finset.  Overlap between an
old deleted edge and the new cut only improves the cardinality budget. -/
theorem pruning_budget_step_deletedEdges
    {U A B T : Finset V} {deletedEdges : Finset (Sym2 V)} {budget : ℕ}
    (hcover : A ∪ B = U) (hdisj : Disjoint A B)
    (hsparse :
      9 * (Section44.edgeBoundary G A B).card ≤
        (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card)
    (hbudget :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card +
          8 * deletedEdges.card ≤ budget) :
    (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card +
        8 * (deletedEdges ∪ Section44.edgeBoundary G A B).card ≤ budget := by
  classical
  have hunion :
      (deletedEdges ∪ Section44.edgeBoundary G A B).card ≤
        deletedEdges.card + (Section44.edgeBoundary G A B).card :=
    Finset.card_union_le _ _
  have hstep := pruning_budget_step (G := G) (T := T)
    (deleted := deletedEdges.card) hcover hdisj hsparse hbudget
  exact
    (Nat.add_le_add_left (Nat.mul_le_mul_left 8 hunion)
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card).trans
        hstep

/-- Nested-cut containment from the proof of Observation 7.7.  If the edges
from the current set `U` to the part of the original set `S` outside `U` have
already been deleted, then after retaining `A` every edge from `A` to
`S \ A` is either an old deleted edge or a new `A`--`B` cut edge. -/
theorem nested_cut_boundary_subset_deleted_union
    {S U A B : Finset V} {deletedEdges : Finset (Sym2 V)}
    (hcover : A ∪ B = U) (hdisj : Disjoint A B)
    (hexternal :
      Section44.edgeBoundary G U (S \ U) ⊆ deletedEdges) :
    Section44.edgeBoundary G A (S \ A) ⊆
      deletedEdges ∪ Section44.edgeBoundary G A B := by
  classical
  have hAU : A ⊆ U := by
    intro v hvA
    rw [← hcover]
    exact Finset.mem_union_left _ hvA
  have hBU : B ⊆ U := by
    intro v hvB
    rw [← hcover]
    exact Finset.mem_union_right _ hvB
  have hUdiffA : U \ A = B := by
    apply Finset.Subset.antisymm
    · intro v hv
      rcases Finset.mem_sdiff.mp hv with ⟨hvU, hvA⟩
      rw [← hcover] at hvU
      rcases Finset.mem_union.mp hvU with hvA' | hvB
      · exact (hvA hvA').elim
      · exact hvB
    · intro v hvB
      exact Finset.mem_sdiff.mpr
        ⟨hBU hvB, fun hvA => Finset.disjoint_left.mp hdisj hvA hvB⟩
  intro e he
  rcases ((Section44.mem_edgeBoundary (G := G) A (S \ A) e).1 he) with
    ⟨heG, a, haA, v, hvOutsideA, rfl⟩
  have haU : a ∈ U := hAU haA
  rcases Finset.mem_sdiff.mp hvOutsideA with ⟨hvS, hvA⟩
  by_cases hvU : v ∈ U
  · have hvB : v ∈ B := by
      rw [← hUdiffA]
      exact Finset.mem_sdiff.mpr ⟨hvU, hvA⟩
    exact Finset.mem_union_right _
      ((Section44.mem_edgeBoundary (G := G) A B s(a, v)).2
        ⟨heG, a, haA, v, hvB, rfl⟩)
  · have hold :
        s(a, v) ∈ Section44.edgeBoundary G U (S \ U) :=
      (Section44.mem_edgeBoundary (G := G) U (S \ U) s(a, v)).2
        ⟨heG, a, haU, v, Finset.mem_sdiff.mpr ⟨hvS, hvU⟩, rfl⟩
    exact Finset.mem_union_left _ (hexternal hold)

/-- Old deleted edges and a new `A`--`B` cut contain no edge internal to the
retained side `A`. -/
theorem deleted_union_cut_disjoint_internal_left
    {U A B : Finset V} {deletedEdges : Finset (Sym2 V)}
    (hAU : A ⊆ U) (hdisj : Disjoint A B)
    (hold : Disjoint deletedEdges (Section44.edgeBoundary G U U)) :
    Disjoint (deletedEdges ∪ Section44.edgeBoundary G A B)
      (Section44.edgeBoundary G A A) := by
  classical
  rw [Finset.disjoint_left] at hold ⊢
  intro e heDeleted heInternal
  rcases Finset.mem_union.mp heDeleted with heOld | heCut
  · apply hold heOld
    rcases ((Section44.mem_edgeBoundary (G := G) A A e).1 heInternal) with
      ⟨heG, x, hx, y, hy, rfl⟩
    exact (Section44.mem_edgeBoundary (G := G) U U s(x, y)).2
      ⟨heG, x, hAU hx, y, hAU hy, rfl⟩
  · rcases ((Section44.mem_edgeBoundary (G := G) A B e).1 heCut) with
      ⟨_heG, a, ha, b, hb, rfl⟩
    rcases ((Section44.mem_edgeBoundary (G := G) A A s(a, b)).1
        heInternal) with ⟨_heG', x, hx, y, hy, heq⟩
    rw [Sym2.eq_iff] at heq
    have hbA : b ∈ A := by
      rcases heq with heq | heq
      · simpa [heq.2] using hy
      · simpa [heq.2] using hx
    exact Finset.disjoint_left.mp hdisj hbA hb

/-! ## Lightweight pruning states -/

/-- The actual-edge-set invariant maintained in the decomposition inside the
proof of Observation 7.7.  The right side of the budget is fixed to the
augmented boundary of the original set `S`. -/
structure PruningState
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  /-- The currently retained subset of `S`. -/
  U : Finset V
  /-- The union of all cut-edge finsets deleted so far. -/
  deletedEdges : Finset (Sym2 V)
  /-- Every current vertex still belongs to the original set. -/
  U_subset : U ⊆ S
  /-- Every deleted item is an actual edge of `G`. -/
  deletedEdges_subset_edgeSet :
    ∀ ⦃e : Sym2 V⦄, e ∈ deletedEdges → e ∈ G.edgeSet
  /-- Both endpoints of every deleted edge lie in the original ambient set. -/
  deletedEdges_subset_initialEdges :
    deletedEdges ⊆ Section44.edgeBoundary G S S
  /-- No already deleted edge has both endpoints in the current retained set. -/
  deletedEdges_internal_disjoint :
    Disjoint deletedEdges (Section44.edgeBoundary G U U)
  /-- Every edge from the current set to the discarded part of `S` has been
  deleted. -/
  externalBoundary_deleted :
    Section44.edgeBoundary G U (S \ U) ⊆ deletedEdges
  /-- The source invariant, with the `1/8` vertex budgets cleared. -/
  augmentedBoundary_budget :
    (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card +
        8 * deletedEdges.card ≤
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card

namespace PruningState

variable {S T : Finset V}

/-- The initial state `U = S`, `E' = empty`. -/
noncomputable def initial
    (G : _root_.SimpleGraph V) (S T : Finset V) :
    PruningState G S T where
  U := S
  deletedEdges := ∅
  U_subset := Finset.Subset.rfl
  deletedEdges_subset_edgeSet := by simp
  deletedEdges_subset_initialEdges := by simp
  deletedEdges_internal_disjoint := by simp
  externalBoundary_deleted := by simp
  augmentedBoundary_budget := by simp

/-- Retain the left side of a violating partition and add its crossing edges
to the actual deleted-edge finset. -/
noncomputable def retainLeft
    (state : PruningState G S T) {A B : Finset V}
    (hcover : A ∪ B = state.U) (hdisj : Disjoint A B)
    (_horient :
      (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card)
    (hsparse :
      9 * (Section44.edgeBoundary G A B).card <
        (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card) :
    PruningState G S T where
  U := A
  deletedEdges := state.deletedEdges ∪ Section44.edgeBoundary G A B
  U_subset := by
    intro v hvA
    apply state.U_subset
    rw [← hcover]
    exact Finset.mem_union_left _ hvA
  deletedEdges_subset_edgeSet := by
    intro e he
    rcases Finset.mem_union.mp he with heOld | heCut
    · exact state.deletedEdges_subset_edgeSet heOld
    · exact ((Section44.mem_edgeBoundary (G := G) A B e).1 heCut).1
  deletedEdges_subset_initialEdges := by
    intro e he
    rcases Finset.mem_union.mp he with heOld | heCut
    · exact state.deletedEdges_subset_initialEdges heOld
    · rcases ((Section44.mem_edgeBoundary (G := G) A B e).1 heCut) with
        ⟨heG, a, ha, b, hb, rfl⟩
      have haU : a ∈ state.U := by
        rw [← hcover]
        exact Finset.mem_union_left _ ha
      have hbU : b ∈ state.U := by
        rw [← hcover]
        exact Finset.mem_union_right _ hb
      exact (Section44.mem_edgeBoundary (G := G) S S s(a, b)).2
        ⟨heG, a, state.U_subset haU, b, state.U_subset hbU, rfl⟩
  deletedEdges_internal_disjoint := by
    apply deleted_union_cut_disjoint_internal_left (G := G)
      (hdisj := hdisj) (hold := state.deletedEdges_internal_disjoint)
    intro v hvA
    rw [← hcover]
    exact Finset.mem_union_left _ hvA
  externalBoundary_deleted :=
    nested_cut_boundary_subset_deleted_union (G := G)
      hcover hdisj state.externalBoundary_deleted
  augmentedBoundary_budget :=
    pruning_budget_step_deletedEdges (G := G) (T := T)
      hcover hdisj (Nat.le_of_lt hsparse) state.augmentedBoundary_budget

/-- The external cut of any pruning state has at most as many edges as the
actual deleted-edge finset. -/
theorem externalBoundary_card_le_deletedEdges_card
    (state : PruningState G S T) :
    (Section44.edgeBoundary G state.U (S \ state.U)).card ≤
      state.deletedEdges.card :=
  Finset.card_le_card state.externalBoundary_deleted

/-- Denominator-cleared final-cut estimate supplied directly by a pruning
state.  This is the edge-set conclusion used at the last half-threshold
crossing in Observation 7.7. -/
theorem eight_mul_externalBoundary_card_le_initial
    (state : PruningState G S T) :
    8 * (Section44.edgeBoundary G state.U (S \ state.U)).card ≤
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card := by
  apply eight_mul_cutEdges_le_initialMass_of_budget
    (newMass :=
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T).card)
    (deleted := state.deletedEdges.card)
  · exact state.externalBoundary_card_le_deletedEdges_card
  · exact state.augmentedBoundary_budget

end PruningState
end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
