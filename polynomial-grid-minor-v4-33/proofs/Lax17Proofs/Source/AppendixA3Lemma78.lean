import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3ConnectedCore
import Lax17Proofs.Source.AppendixA3PruningEdges

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Lemma 7.8

This is the second finite pruning process in Section 7.  Budgets are cleared
by 96:

`3 * |Gamma'(U)| + 96 * |E'| < 8 * kappa`.

A `1/33` violating cut spends at most 99 units per new cut edge and releases
three units for every discarded augmented-boundary vertex.  The initial
degree-three estimate uses `kappa = 256 * rho`; this is the corrected constant
needed because `|out(Y)| <= 3 * rho`.
-/

namespace SimpleGraph
namespace AppendixA3Lemma78


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

/-- An oriented witness to failure of `1/33` cut well-linkedness. -/
theorem exists_oriented_violating_one_thirty_three_cut
    {U Gamma : Finset V} (hGammaU : Gamma ⊆ U)
    (hbad : ¬ Section46.ScaledEdgeWellLinkedIn G U Gamma 1 33) :
    ∃ A B : Finset V,
      A ∪ B = U ∧ Disjoint A B ∧
        (B ∩ Gamma).card ≤ (A ∩ Gamma).card ∧
          33 * (Section44.edgeBoundary G A B).card <
            (B ∩ Gamma).card ∧
            A ⊂ U := by
  classical
  have hnotCuts :
      ¬ ∀ X Y : Finset V,
        X ⊆ U → Y ⊆ U → X ∪ Y = U → Disjoint X Y →
          1 * min (X ∩ Gamma).card (Y ∩ Gamma).card ≤
            33 * (Section44.edgeBoundary G X Y).card := by
    intro hcuts
    exact hbad ⟨by norm_num, by norm_num, hGammaU, hcuts⟩
  push Not at hnotCuts
  rcases hnotCuts with
    ⟨X, Y, hXU, hYU, hcover, hdisj, hviolate⟩
  have hstrict :
      33 * (Section44.edgeBoundary G X Y).card <
        min (X ∩ Gamma).card (Y ∩ Gamma).card := by
    omega
  by_cases hYX : (Y ∩ Gamma).card ≤ (X ∩ Gamma).card
  · have hsmall :
        33 * (Section44.edgeBoundary G X Y).card <
          (Y ∩ Gamma).card := by
      simpa [Nat.min_eq_right hYX] using hstrict
    have hYnonempty : (Y ∩ Gamma).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hXproper : X ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hXU, ?_⟩
      intro hXeq
      rcases hYnonempty with ⟨v, hvYGamma⟩
      have hvY := (Finset.mem_inter.mp hvYGamma).1
      have hvX : v ∈ X := by simpa [hXeq] using hYU hvY
      exact Finset.disjoint_left.mp hdisj hvX hvY
    exact ⟨X, Y, hcover, hdisj, hYX, hsmall, hXproper⟩
  · have hXY : (X ∩ Gamma).card ≤ (Y ∩ Gamma).card := by omega
    have hsmall :
        33 * (Section44.edgeBoundary G Y X).card <
          (X ∩ Gamma).card := by
      rw [Section44.edgeBoundary_comm (G := G) Y X]
      simpa [Nat.min_eq_left hXY] using hstrict
    have hXnonempty : (X ∩ Gamma).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hYproper : Y ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hYU, ?_⟩
      intro hYeq
      rcases hXnonempty with ⟨v, hvXGamma⟩
      have hvX := (Finset.mem_inter.mp hvXGamma).1
      have hvY : v ∈ Y := by simpa [hYeq] using hXU hvX
      exact Finset.disjoint_left.mp hdisj hvX hvY
    exact ⟨Y, X, by simpa [Finset.union_comm] using hcover,
      hdisj.symm, hXY, hsmall, hYproper⟩

private theorem inter_partition_card
    {U A B Gamma : Finset V}
    (hcover : A ∪ B = U) (hdisj : Disjoint A B)
    (hGammaU : Gamma ⊆ U) :
    Gamma.card =
      (A ∩ Gamma).card + (B ∩ Gamma).card := by
  have hsplit : Gamma = (A ∩ Gamma) ∪ (B ∩ Gamma) := by
    apply Finset.Subset.antisymm
    · intro v hvGamma
      have hvU := hGammaU hvGamma
      rw [← hcover] at hvU
      rcases Finset.mem_union.mp hvU with hvA | hvB
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hvA, hvGamma⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hvB, hvGamma⟩)
    · intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
  calc
    Gamma.card =
        ((A ∩ Gamma) ∪ (B ∩ Gamma)).card :=
      congrArg Finset.card hsplit
    _ = (A ∩ Gamma).card + (B ∩ Gamma).card :=
      Finset.card_union_of_disjoint
        (hdisj.mono Finset.inter_subset_left Finset.inter_subset_left)

/-- The actual-edge state of the Lemma 7.8 pruning. -/
structure State
    (G : _root_.SimpleGraph V) (Y T : Finset V) (kappa : ℕ) where
  U : Finset V
  deletedEdges : Finset (Sym2 V)
  U_subset_complement : U ⊆ (Finset.univ : Finset V) \ Y
  externalBoundary_deleted :
    Section44.clusterBoundary G U ⊆ deletedEdges
  budget :
    3 *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card +
        96 * deletedEdges.card < 8 * kappa
  terminal_mass :
    3 * kappa ≤ 2 * (U ∩ T).card

namespace State

/-- Every augmented-boundary vertex of the current set belongs to that set. -/
theorem augmentedBoundary_subset
    {Y T : Finset V} {kappa : ℕ}
    (state : State G Y T kappa) :
    AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T ⊆
      state.U := by
  intro v hv
  rcases Finset.mem_union.mp hv with hvBoundary | hvTerminal
  · exact
      ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
        hvBoundary).1
  · exact (Finset.mem_inter.mp hvTerminal).2

/-- The cleared budget bounds the deleted-edge set by `kappa/12`. -/
theorem twelve_mul_deleted_lt
    {Y T : Finset V} {kappa : ℕ}
    (state : State G Y T kappa) :
    12 * state.deletedEdges.card < kappa := by
  have hscaled :
      96 * state.deletedEdges.card < 8 * kappa := by
    exact lt_of_le_of_lt
      (Nat.le_add_left
        (96 * state.deletedEdges.card)
        (3 *
          (AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.U T).card))
      state.budget
  have hscaled' :
      8 * (12 * state.deletedEdges.card) < 8 * kappa := by
    simpa only [show 8 * (12 * state.deletedEdges.card) =
        96 * state.deletedEdges.card by ring] using hscaled
  exact Nat.lt_of_mul_lt_mul_left hscaled'

/-- The current external cut is strictly smaller than `kappa/12`. -/
theorem twelve_mul_externalBoundary_lt
    {Y T : Finset V} {kappa : ℕ}
    (state : State G Y T kappa) :
    12 * (Section44.clusterBoundary G state.U).card < kappa := by
  have hcard :=
    Finset.card_le_card state.externalBoundary_deleted
  have hdeleted := state.twelve_mul_deleted_lt
  omega

private theorem successor_budget
    {Y T : Finset V} {kappa : ℕ}
    (state : State G Y T kappa)
    {A B : Finset V}
    (hcover : A ∪ B = state.U) (hdisj : Disjoint A B)
    (hsparse :
      33 * (Section44.edgeBoundary G A B).card <
        (B ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.U T).card) :
    3 *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card +
        96 *
          (state.deletedEdges ∪ Section44.edgeBoundary G A B).card <
      8 * kappa := by
  let Gamma :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T
  let GammaA :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G A T
  have hGammaU : Gamma ⊆ state.U := by
    simpa [Gamma] using state.augmentedBoundary_subset
  have hsplit :
      Gamma.card =
        (A ∩ Gamma).card + (B ∩ Gamma).card :=
    inter_partition_card hcover hdisj hGammaU
  have hnew :
      GammaA.card ≤
        (A ∩ Gamma).card +
          (Section44.edgeBoundary G A B).card := by
    have hAU : A ⊆ state.U := by
      intro v hv
      rw [← hcover]
      exact Finset.mem_union_left _ hv
    simpa [Gamma, GammaA, show state.U \ A = B by
      apply Finset.Subset.antisymm
      · intro v hv
        rcases Finset.mem_sdiff.mp hv with ⟨hvU, hvA⟩
        rw [← hcover] at hvU
        rcases Finset.mem_union.mp hvU with hvA' | hvB
        · exact (hvA hvA').elim
        · exact hvB
      · intro v hvB
        exact Finset.mem_sdiff.mpr
          ⟨by rw [← hcover]; exact Finset.mem_union_right _ hvB,
            fun hvA => Finset.disjoint_left.mp hdisj hvA hvB⟩] using
      (Lax17Proofs.SimpleGraph.AppendixA3AugmentedBoundary.augmentedBoundaryVertices_card_le_retained_add_cut
        (G := G) (T := T) hAU)
  have hunion :
      (state.deletedEdges ∪ Section44.edgeBoundary G A B).card ≤
        state.deletedEdges.card +
          (Section44.edgeBoundary G A B).card :=
    Finset.card_union_le _ _
  have hbudget := state.budget
  change 3 * Gamma.card + 96 * state.deletedEdges.card < 8 * kappa
    at hbudget
  change
    33 * (Section44.edgeBoundary G A B).card <
      (B ∩ Gamma).card at hsparse
  change
    3 * GammaA.card +
        96 * (state.deletedEdges ∪ Section44.edgeBoundary G A B).card <
      8 * kappa
  omega

private theorem retained_terminal_mass
    {Y T : Finset V} {kappa : ℕ}
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V) T 1 3)
    (state : State G Y T kappa)
    {A B : Finset V}
    (hcover : A ∪ B = state.U) (hdisj : Disjoint A B)
    (horient :
      (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card)
    (hnewExternal :
      Section44.clusterBoundary G A ⊆
        state.deletedEdges ∪ Section44.edgeBoundary G A B)
    (hnewBudget :
      3 *
          (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card +
          96 *
            (state.deletedEdges ∪ Section44.edgeBoundary G A B).card <
        8 * kappa) :
    3 * kappa ≤ 2 * (A ∩ T).card := by
  classical
  by_contra hmass
  let Gamma :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T
  have hGammaU : Gamma ⊆ state.U := by
    simpa [Gamma] using state.augmentedBoundary_subset
  change (B ∩ Gamma).card ≤ (A ∩ Gamma).card at horient
  have hsplit :=
    inter_partition_card hcover hdisj hGammaU
  have hhalf : Gamma.card ≤ 2 * (A ∩ Gamma).card := by
    omega
  have hterminalSubset :
      state.U ∩ T ⊆ Gamma := by
    intro v hv
    exact Finset.mem_union_right _
      (Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).2, (Finset.mem_inter.mp hv).1⟩)
  have hcurrentTerm :
      (state.U ∩ T).card ≤ Gamma.card :=
    Finset.card_le_card hterminalSubset
  have hretainedCover :
      A ∩ Gamma ⊆
        (A ∩ T) ∪
          AppendixA3ClusterSplit.boundaryVertices G state.U := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvA, hvGamma⟩
    rcases Finset.mem_union.mp hvGamma with hvBoundary | hvTerminal
    · exact Finset.mem_union_right _ hvBoundary
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hvA, (Finset.mem_inter.mp hvTerminal).1⟩)
  have hretainedCard :
      (A ∩ Gamma).card ≤
        (A ∩ T).card +
          (AppendixA3ClusterSplit.boundaryVertices G state.U).card :=
    (Finset.card_le_card hretainedCover).trans
      (Finset.card_union_le _ _)
  have hboundaryVertices :
      (AppendixA3ClusterSplit.boundaryVertices G state.U).card ≤
        state.deletedEdges.card := by
    exact
      (Lax17Proofs.SimpleGraph.AppendixA3Lemma72.boundaryVertices_card_le_clusterBoundary_card
          (G := G) state.U).trans
        (Finset.card_le_card state.externalBoundary_deleted)
  have hdeleted := state.twelve_mul_deleted_lt
  have hstateMass := state.terminal_mass
  have hretainedLarge : 2 * kappa < 3 * (A ∩ T).card := by
    omega
  have houtsideCard :
      ((Finset.univ \ A) ∩ T).card =
        T.card - (A ∩ T).card := by
    have heq : (Finset.univ \ A) ∩ T = T \ A := by
      ext v
      simp [and_comm]
    rw [heq, Finset.card_sdiff]
  have houtsideLarge :
      kappa < 2 * ((Finset.univ \ A) ∩ T).card := by
    rw [houtsideCard, hTcard]
    omega
  have hcut := hTwell.2.2.2 A (Finset.univ \ A)
    (by simp) (by simp) (by simp) (by
      rw [Finset.disjoint_left]
      intro v hvA hvDiff
      exact (Finset.mem_sdiff.mp hvDiff).2 hvA)
  have hminLarge :
      kappa <
        2 * min (A ∩ T).card ((Finset.univ \ A) ∩ T).card := by
    omega
  have hcutLarge :
      kappa <
        6 * (Section44.clusterBoundary G A).card := by
    change
      1 * min (A ∩ T).card ((Finset.univ \ A) ∩ T).card ≤
        3 * (Section44.clusterBoundary G A).card at hcut
    omega
  have hnewExternalCard :
      (Section44.clusterBoundary G A).card ≤
        (state.deletedEdges ∪ Section44.edgeBoundary G A B).card :=
    Finset.card_le_card hnewExternal
  have hnewDeleted :
      12 *
          (state.deletedEdges ∪ Section44.edgeBoundary G A B).card <
        kappa := by
    have hscaled :
        96 *
            (state.deletedEdges ∪ Section44.edgeBoundary G A B).card <
          8 * kappa := by
      exact lt_of_le_of_lt
        (Nat.le_add_left
          (96 *
            (state.deletedEdges ∪ Section44.edgeBoundary G A B).card)
          (3 *
            (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card))
        hnewBudget
    have hscaled' :
        8 *
            (12 *
              (state.deletedEdges ∪ Section44.edgeBoundary G A B).card) <
          8 * kappa := by
      simpa only [show
        8 *
            (12 *
              (state.deletedEdges ∪ Section44.edgeBoundary G A B).card) =
          96 *
            (state.deletedEdges ∪ Section44.edgeBoundary G A B).card by
              ring] using hscaled
    exact Nat.lt_of_mul_lt_mul_left hscaled'
  omega

/-- Retain the larger augmented-boundary side of a `1/33` violating cut. -/
noncomputable def retainLeft
    {Y T : Finset V} {kappa : ℕ}
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V) T 1 3)
    (state : State G Y T kappa)
    {A B : Finset V}
    (hcover : A ∪ B = state.U) (hdisj : Disjoint A B)
    (horient :
      (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card)
    (hsparse :
      33 * (Section44.edgeBoundary G A B).card <
        (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card) :
    State G Y T kappa := by
  let newDeleted :=
    state.deletedEdges ∪ Section44.edgeBoundary G A B
  have hnewExternal :
      Section44.clusterBoundary G A ⊆ newDeleted := by
    change Section44.edgeBoundary G A (Finset.univ \ A) ⊆ newDeleted
    simpa [newDeleted, Section44.clusterBoundary] using
      (Lax17Proofs.SimpleGraph.AppendixA3Lemma75.nested_cut_boundary_subset_deleted_union
        (G := G) (S := (Finset.univ : Finset V))
        hcover hdisj (by
          simpa [Section44.clusterBoundary] using
            state.externalBoundary_deleted))
  have hbudget :=
    successor_budget state hcover hdisj hsparse
  exact
    { U := A
      deletedEdges := newDeleted
      U_subset_complement := by
        intro v hvA
        apply state.U_subset_complement
        rw [← hcover]
        exact Finset.mem_union_left _ hvA
      externalBoundary_deleted := hnewExternal
      budget := by simpa [newDeleted] using hbudget
      terminal_mass :=
        retained_terminal_mass hTcard hTwell state hcover hdisj
          horient hnewExternal (by simpa [newDeleted] using hbudget) }

/-- Every failed state admits a strict valid successor. -/
theorem exists_strict_successor
    {Y T : Finset V} {kappa : ℕ}
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V) T 1 3)
    (state : State G Y T kappa)
    (hbad :
      ¬ Section46.ScaledEdgeWellLinkedIn G state.U
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T)
        1 33) :
    ∃ next : State G Y T kappa, next.U ⊂ state.U := by
  have hGammaU := state.augmentedBoundary_subset
  obtain ⟨A, B, hcover, hdisj, horient, hsparse, hproper⟩ :=
    exists_oriented_violating_one_thirty_three_cut hGammaU hbad
  let next := state.retainLeft hTcard hTwell hcover hdisj horient hsparse
  exact ⟨next, by simpa [next, retainLeft] using hproper⟩

end State

/-- Initial Lemma 7.8 state on the complement of `Y`. -/
theorem exists_initial_state
    {Y T : Finset V} {rho kappa : ℕ}
    (hrhoPos : 0 < rho)
    (hkappa : kappa = 256 * rho)
    (hTcard : T.card = 2 * kappa)
    (hdegree : MaxDegreeAtMost G 3)
    (hYBoundary :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ≤ rho) :
    ∃ state : State G Y T kappa,
      state.U = (Finset.univ : Finset V) \ Y := by
  classical
  let U := (Finset.univ : Finset V) \ Y
  let deleted := Section44.clusterBoundary G Y
  have hboundaryY :
      (AppendixA3ClusterSplit.boundaryVertices G Y).card ≤ rho := by
    have hsub :
        AppendixA3ClusterSplit.boundaryVertices G Y ⊆
          AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T :=
      Finset.subset_union_left
    exact (Finset.card_le_card hsub).trans hYBoundary
  have hdeleted :
      deleted.card ≤ 3 * rho := by
    exact
      (Lax17Proofs.SimpleGraph.AppendixA3ClusterSplit.clusterBoundary_card_le_maxDegree_mul_boundaryVertices_card
          (G := G) (S := Y) hdegree).trans
        (Nat.mul_le_mul_left 3 hboundaryY)
  have hboundaryUeq :
      Section44.clusterBoundary G U = deleted := by
    simpa [U, deleted, Section44.clusterBoundary] using
      (Lax17Proofs.SimpleGraph.AppendixA3BalancedCut.edgeBoundary_sdiff
        (G := G) (S := (Finset.univ : Finset V)) (A := Y) (by simp))
  have hGammaU :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card ≤
        deleted.card + T.card := by
    have hboundaryVertices :
        (AppendixA3ClusterSplit.boundaryVertices G U).card ≤
          deleted.card := by
      rw [← hboundaryUeq]
      exact
        Lax17Proofs.SimpleGraph.AppendixA3Lemma72.boundaryVertices_card_le_clusterBoundary_card
          (G := G) U
    calc
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card ≤
          (AppendixA3ClusterSplit.boundaryVertices G U).card +
            (T ∩ U).card := Finset.card_union_le _ _
      _ ≤ deleted.card + T.card := by
        have := Finset.card_le_card (Finset.inter_subset_left : T ∩ U ⊆ T)
        omega
  have hbudget :
      3 *
          (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card +
          96 * deleted.card < 8 * kappa := by
    rw [hTcard] at hGammaU
    rw [hkappa] at hGammaU ⊢
    omega
  have hterminalMass :
      3 * kappa ≤ 2 * (U ∩ T).card := by
    have hTY :
        (T ∩ Y).card ≤ rho := by
      have hsub :
          T ∩ Y ⊆
            AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T := by
        intro v hv
        exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
            (Finset.mem_inter.mp hv).2⟩)
      exact (Finset.card_le_card hsub).trans hYBoundary
    have hpartition :
        (U ∩ T).card + (T ∩ Y).card = T.card := by
      have hUinter : U ∩ T = T \ Y := by
        ext v
        constructor
        · intro hv
          exact Finset.mem_sdiff.mpr
            ⟨(Finset.mem_inter.mp hv).2,
              (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).1).2⟩
        · intro hv
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_sdiff.mpr
              ⟨Finset.mem_univ v, (Finset.mem_sdiff.mp hv).2⟩,
              (Finset.mem_sdiff.mp hv).1⟩
      rw [hUinter, Finset.card_sdiff]
      rw [Finset.inter_comm Y T]
      exact Nat.sub_add_cancel
        (Finset.card_le_card
          (Finset.inter_subset_left : T ∩ Y ⊆ T))
    rw [hTcard] at hpartition
    rw [hkappa] at hpartition ⊢
    omega
  let state : State G Y T kappa :=
    { U := U
      deletedEdges := deleted
      U_subset_complement := by exact Finset.Subset.rfl
      externalBoundary_deleted := by
        rw [hboundaryUeq]
      budget := hbudget
      terminal_mass := hterminalMass }
  exact ⟨state, rfl⟩

/-- Lemma 7.8 before connected-component localization. -/
theorem exists_lemma78_set
    {Y T : Finset V} {rho kappa : ℕ}
    (hrhoPos : 0 < rho)
    (hkappa : kappa = 256 * rho)
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V) T 1 3)
    (hdegree : MaxDegreeAtMost G 3)
    (hYBoundary :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ≤ rho) :
    ∃ X : Finset V,
      X ⊆ (Finset.univ : Finset V) \ Y ∧
      3 * kappa ≤ 2 * (X ∩ T).card ∧
      Section46.ScaledEdgeWellLinkedIn G X
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G X T)
        1 33 := by
  obtain ⟨initial, _hinitial⟩ :=
    exists_initial_state hrhoPos hkappa hTcard hdegree hYBoundary
  obtain ⟨terminal, _hvalid, hwell⟩ :=
    AppendixA3FiniteDescent.exists_terminal_of_measure_descent
      (measure := fun state : State G Y T kappa => state.U.card)
      (Valid := fun _state => True)
      (Good := fun state =>
        Section46.ScaledEdgeWellLinkedIn G state.U
          (AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T)
          1 33)
      initial trivial (by
        intro state _ hbad
        obtain ⟨next, hproper⟩ :=
          state.exists_strict_successor hTcard hTwell hbad
        exact ⟨next, trivial, Finset.card_lt_card hproper⟩)
  exact
    ⟨terminal.U, terminal.U_subset_complement,
      terminal.terminal_mass, hwell⟩

/-- Connected-cluster form of Lemma 7.8. -/
theorem exists_lemma78_cluster
    {Y T : Finset V} {rho kappa : ℕ}
    (hrhoPos : 0 < rho)
    (hkappa : kappa = 256 * rho)
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V) T 1 3)
    (hdegree : MaxDegreeAtMost G 3)
    (hYBoundary :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ≤ rho) :
    ∃ X : Finset V,
      Disjoint X Y ∧
      IsCluster G X ∧
      3 * kappa ≤ 2 * (X ∩ T).card ∧
      Section46.ScaledEdgeWellLinkedIn G X
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G X T)
        1 33 := by
  obtain ⟨U, hUY, hmass, hwell⟩ :=
    exists_lemma78_set hrhoPos hkappa hTcard hTwell hdegree hYBoundary
  have hnonempty :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).Nonempty := by
    have hkappaPos : 0 < kappa := by rw [hkappa]; positivity
    apply Finset.card_pos.mp
    have hterm : 0 < (U ∩ T).card := by omega
    have hsub :
        U ∩ T ⊆
          AppendixA3ClusterSplit.augmentedBoundaryVertices G U T := by
      intro v hv
      exact Finset.mem_union_right _
        (Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hv).2, (Finset.mem_inter.mp hv).1⟩)
    exact lt_of_lt_of_le hterm (Finset.card_le_card hsub)
  obtain ⟨X, hXU, hXcluster, hGammaEq, hXwell⟩ :=
    AppendixA3ConnectedCore.exists_connectedCore_same_augmentedBoundary
      hwell hnonempty
  have hUT :
      U ∩ T ⊆ X := by
    intro v hv
    have hvGamma :
        v ∈ AppendixA3ClusterSplit.augmentedBoundaryVertices G U T :=
      Finset.mem_union_right _
        (Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hv).2, (Finset.mem_inter.mp hv).1⟩)
    rw [← hGammaEq] at hvGamma
    exact hXwell.2.2.1 hvGamma
  have hmassX : 3 * kappa ≤ 2 * (X ∩ T).card := by
    have hsub : U ∩ T ⊆ X ∩ T := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨hUT hv, (Finset.mem_inter.mp hv).2⟩
    exact hmass.trans
      (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub))
  have hdisjoint : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro v hvX hvY
    have hvU := hXU hvX
    exact (Finset.mem_sdiff.mp (hUY hvU)).2 hvY
  exact ⟨X, hdisjoint, hXcluster, hmassX, hXwell⟩

end
end AppendixA3Lemma78
end SimpleGraph

end Lax17Proofs
