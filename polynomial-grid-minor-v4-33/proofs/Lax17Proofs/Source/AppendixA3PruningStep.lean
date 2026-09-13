import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3FiniteDescent
import Lax17Proofs.Source.AppendixA3PruningEdges

namespace Lax17Proofs

universe u v w

/-!
# Violating cuts and finite pruning for Observation 7.7

Failure of `1/9` edge well-linkedness supplies an oriented sparse cut whose
larger terminal side is a strict subset of the current set.  Combining that
cut with the actual-edge `PruningState` gives a terminating finite descent.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- An oriented witness to failure of `1/9` edge well-linkedness.  `A` is the
larger terminal side and is nevertheless a strict subset because the smaller
side contains a terminal. -/
theorem exists_oriented_violating_one_nine_cut
    {U Gamma : Finset V} (hGammaU : Gamma ⊆ U)
    (hbad : ¬ Section46.ScaledEdgeWellLinkedIn G U Gamma 1 9) :
    ∃ A B : Finset V,
      A ∪ B = U ∧ Disjoint A B ∧
        (B ∩ Gamma).card ≤ (A ∩ Gamma).card ∧
          9 * (Section44.edgeBoundary G A B).card < (B ∩ Gamma).card ∧
            A ⊂ U := by
  classical
  have hnotCuts :
      ¬ ∀ X Y : Finset V,
        X ⊆ U → Y ⊆ U → X ∪ Y = U → Disjoint X Y →
          1 * min (X ∩ Gamma).card (Y ∩ Gamma).card ≤
            9 * (Section44.edgeBoundary G X Y).card := by
    intro hcuts
    exact hbad ⟨by norm_num, by norm_num, hGammaU, hcuts⟩
  push Not at hnotCuts
  rcases hnotCuts with
    ⟨X, Y, hXU, hYU, hcover, hdisj, hviolate⟩
  have hstrict :
      9 * (Section44.edgeBoundary G X Y).card <
        min (X ∩ Gamma).card (Y ∩ Gamma).card := by
    omega
  by_cases hYX : (Y ∩ Gamma).card ≤ (X ∩ Gamma).card
  · have hsmall :
        9 * (Section44.edgeBoundary G X Y).card <
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
        9 * (Section44.edgeBoundary G Y X).card <
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

/-- States reachable by the source pruning process.  This excludes arbitrary
structure values that satisfy the numerical fields but were not obtained from
the initial state by guarded retained-side transitions. -/
inductive PruningReachable
    (G : _root_.SimpleGraph V) (S T : Finset V) :
    PruningState G S T → Prop
  | initial : PruningReachable G S T (PruningState.initial G S T)
  | retainLeft {state : PruningState G S T}
      (hstate : PruningReachable G S T state)
      {A B : Finset V}
      (hcover : A ∪ B = state.U) (hdisj : Disjoint A B)
      (horient :
        (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.U T).card ≤
          (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.U T).card)
      (hsparse :
        9 * (Section44.edgeBoundary G A B).card <
          (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.U T).card) :
      PruningReachable G S T
        (state.retainLeft hcover hdisj horient hsparse)

/-- Every non-well-linked pruning state has a valid successor with a strictly
smaller retained vertex set. -/
theorem PruningState.exists_strict_successor_of_not_wellLinked
    {S T : Finset V} (state : PruningState G S T)
    (hbad : ¬ Section46.ScaledEdgeWellLinkedIn G state.U
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T) 1 9) :
    ∃ next : PruningState G S T, next.U ⊂ state.U := by
  have hGammaU :
      AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T ⊆
        state.U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvBoundary | hvTerminal
    · exact
        ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
          hvBoundary).1
    · exact (Finset.mem_inter.mp hvTerminal).2
  rcases exists_oriented_violating_one_nine_cut (G := G)
      hGammaU hbad with
    ⟨A, B, hcover, hdisj, horient, hsparse, hproper⟩
  let next := state.retainLeft hcover hdisj horient hsparse
  exact ⟨next, by simpa [next, PruningState.retainLeft] using hproper⟩

/-- Reachability is preserved by the strict successor selected from a failed
well-linkedness cut. -/
theorem PruningState.exists_strict_reachable_successor_of_not_wellLinked
    {S T : Finset V} (state : PruningState G S T)
    (hreachable : PruningReachable G S T state)
    (hbad : ¬ Section46.ScaledEdgeWellLinkedIn G state.U
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T) 1 9) :
    ∃ next : PruningState G S T,
      PruningReachable G S T next ∧ next.U ⊂ state.U := by
  have hGammaU :
      AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T ⊆
        state.U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvBoundary | hvTerminal
    · exact
        ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
          hvBoundary).1
    · exact (Finset.mem_inter.mp hvTerminal).2
  rcases exists_oriented_violating_one_nine_cut (G := G) hGammaU hbad with
    ⟨A, B, hcover, hdisj, horient, hsparse, hproper⟩
  let next := state.retainLeft hcover hdisj horient hsparse
  refine ⟨next, ?_, ?_⟩
  · simpa [next] using
      (PruningReachable.retainLeft hreachable hcover hdisj horient hsparse)
  · simpa [next, PruningState.retainLeft] using hproper

/-- The well-linked decomposition in Observation 7.7 terminates.  The result
retains the actual deleted-edge set, external-cut containment, and source
budget through its `PruningState` fields.  The separate half-mass argument is
still needed before this state contradicts minimum initiality. -/
theorem exists_wellLinked_pruningState
    (G : _root_.SimpleGraph V) (S T : Finset V) :
    ∃ state : PruningState G S T,
      PruningReachable G S T state ∧
        Section46.ScaledEdgeWellLinkedIn G state.U
          (AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T) 1 9 := by
  have hterminal :=
    AppendixA3FiniteDescent.exists_terminal_of_measure_descent
      (measure := fun state : PruningState G S T => state.U.card)
      (Valid := PruningReachable G S T)
      (Good := fun state =>
        Section46.ScaledEdgeWellLinkedIn G state.U
          (AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T) 1 9)
      (initial := PruningState.initial G S T) PruningReachable.initial (by
        intro state hreachable hbad
        rcases state.exists_strict_reachable_successor_of_not_wellLinked
            hreachable hbad with ⟨next, hnext, hproper⟩
        exact ⟨next, hnext, Finset.card_lt_card hproper⟩)
  rcases hterminal with ⟨state, hreachable, hgood⟩
  exact ⟨state, hreachable, hgood⟩

end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
