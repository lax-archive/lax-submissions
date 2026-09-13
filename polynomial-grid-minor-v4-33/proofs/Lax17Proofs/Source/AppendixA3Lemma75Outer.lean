import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Observation77
import Lax17Proofs.Source.AppendixA3Lemma75Step
import Lax17Proofs.Source.AppendixA3QuarterBalancedCandidate
import Lax17Proofs.Source.AppendixA3Corollary74Overlap
import Lax17Proofs.Source.AppendixA3FiniteDescent

namespace Lax17Proofs

universe u v w

/-!
# The outer iteration of Chuzhoy Lemma 7.5

This module implements the corrected bootstrap and the subsequent
quarter-balanced-cut iteration.  The first cut of the minimum initial set is
handled separately, since Observation 7.7 is valid only after reaching a
proper subset.  Corollary 7.4 then gives a fresh uniform boundary bound.

For the degree-three specialization, 128 contraction steps are more than
enough:

`974 * 256 * 7^128 <= 8^128`.

The fixed final well-linkedness denominator is therefore `27 * 3^128`.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

/-- The fixed denominator produced by the degree-three Lemma 7.5 proof. -/
def finalAlphaDen : ℕ := 27 * 3 ^ 128

private theorem contraction_numeric :
    974 * 256 * 7 ^ 128 ≤ 8 ^ 128 := by
  norm_num

/-- A state after the corrected first-cut bootstrap. -/
structure OuterState
    (G : _root_.SimpleGraph V) (T S0 : Finset V)
    (rho kappa : ℕ) where
  S : Finset V
  level : ℕ
  level_le : level ≤ 128
  subset_initial : S ⊆ S0
  proper_initial : S ⊂ S0
  boundary_wellLinked :
    Section46.ScaledEdgeWellLinkedIn G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T)
      1 (27 * 3 ^ level)
  boundary_large :
    rho ≤ 4 *
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card
  contraction_budget :
    8 ^ level *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
      974 * kappa * 7 ^ level

namespace OuterState

private theorem proper_of_quarterBalanced
    {S Gamma A : Finset V}
    (hGammaPos : 0 < Gamma.card)
    (hA : AppendixA3BalancedCut.QuarterBalanced S Gamma A) :
    A ⊂ S := by
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hA.subset, ?_⟩
  intro heq
  have hempty : (S \ A) ∩ Gamma = ∅ := by
    simp [heq]
  have hquarter := hA.complement_quarter
  rw [hempty] at hquarter
  simp only [Finset.card_empty, Nat.mul_zero] at hquarter
  omega

/-- At level 128 the contraction budget already forces the stopping
condition, using `kappa = 256 * rho`. -/
theorem boundary_le_rho_of_level_eq
    {T S0 : Finset V} {rho kappa : ℕ}
    (state : OuterState G T S0 rho kappa)
    (hkappa : kappa = 256 * rho)
    (hlevel : state.level = 128) :
    (AppendixA3ClusterSplit.augmentedBoundaryVertices
      G state.S T).card ≤ rho := by
  let Gamma :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G state.S T
  have hbudget : 8 ^ 128 * Gamma.card ≤ 974 * kappa * 7 ^ 128 := by
    simpa [Gamma, hlevel] using state.contraction_budget
  have hscaled : 8 ^ 128 * Gamma.card ≤ 8 ^ 128 * rho := by
    calc
      8 ^ 128 * Gamma.card ≤ 974 * kappa * 7 ^ 128 := hbudget
      _ = (974 * 256 * 7 ^ 128) * rho := by rw [hkappa]; ring
      _ ≤ (8 ^ 128) * rho :=
        Nat.mul_le_mul_right rho contraction_numeric
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

/-- One post-bootstrap outer iteration. -/
theorem exists_successor
    {T S0 : Finset V} {rho kappa : ℕ}
    (hS0 : IsMinimumInitialSet G T rho S0)
    (hkappa : kappa = 256 * rho)
    (hrhoPos : 0 < rho)
    (state : OuterState G T S0 rho kappa)
    (hbad :
      ¬ (AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.S T).card ≤ rho) :
    ∃ next : OuterState G T S0 rho kappa,
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G next.S T).card <
        (AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.S T).card := by
  classical
  let Gamma :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G state.S T
  have hrho : rho < Gamma.card := by
    simpa [Gamma] using Nat.lt_of_not_ge hbad
  have hGammaPos : 0 < Gamma.card := lt_of_le_of_lt (Nat.zero_le rho) hrho
  have hlevelLt : state.level < 128 := by
    have hne : state.level ≠ 128 := by
      intro heq
      exact hbad (state.boundary_le_rho_of_level_eq hkappa heq)
    have hle := state.level_le
    omega
  have hGammaCard : 2 ≤ Gamma.card := by
    omega
  obtain ⟨cut, hcut0⟩ :=
    AppendixA3BalancedCut.exists_minimumQuarterBalancedEdgeCut_of_two_le_card
      (G := G) state.boundary_wellLinked.2.2.1 hGammaCard
  obtain ⟨A, hcut, horient⟩ := hcut0.exists_oriented
  have hcutSmall :
      8 * (Section44.edgeBoundary G A (state.S \ A)).card ≤ Gamma.card := by
    simpa [Gamma] using
      minimumQuarterBalancedCut_eight_mul_cut_le
        hS0 state.proper_initial hrho hcut
  have hiteration :=
    minimumQuarterBalancedCut_iteration
      (rho := rho) state.boundary_wellLinked hcut horient
      (by simpa [Gamma] using hcutSmall) (by simpa [Gamma] using hrho)
  let GammaA :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G A T
  have hwellA :
      Section46.ScaledEdgeWellLinkedIn G A GammaA
        1 (27 * 3 ^ (state.level + 1)) := by
    have h := hiteration.1
    change
      Section46.ScaledEdgeWellLinkedIn G A GammaA
        1 (3 * (27 * 3 ^ state.level)) at h
    convert h using 1 <;> simp [pow_succ] <;> ring
  have hcontract : 8 * GammaA.card ≤ 7 * Gamma.card := by
    simpa [Gamma, GammaA] using hiteration.2.1
  have hlarge : rho ≤ 4 * GammaA.card := by
    have := hiteration.2.2.2
    change rho ≤ 2 * GammaA.card at this
    omega
  have hproperState : A ⊂ state.S :=
    proper_of_quarterBalanced hGammaPos hcut.toQuarterBalanced
  have hproperInitial : A ⊂ S0 := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hcut.subset.trans state.subset_initial, ?_⟩
    intro heq
    have hcardAState := Finset.card_lt_card hproperState
    have hcardStateS0 :=
      Finset.card_le_card state.subset_initial
    have := congrArg Finset.card heq
    omega
  have hbudget :
      8 ^ (state.level + 1) * GammaA.card ≤
        974 * kappa * 7 ^ (state.level + 1) := by
    calc
      8 ^ (state.level + 1) * GammaA.card =
          8 ^ state.level * (8 * GammaA.card) := by
            rw [pow_succ]
            ring
      _ ≤ 8 ^ state.level * (7 * Gamma.card) :=
        Nat.mul_le_mul_left _ hcontract
      _ = 7 * (8 ^ state.level * Gamma.card) := by ring
      _ ≤ 7 * (974 * kappa * 7 ^ state.level) :=
        Nat.mul_le_mul_left 7 state.contraction_budget
      _ = 974 * kappa * 7 ^ (state.level + 1) := by
        rw [pow_succ]
        ring
  let next : OuterState G T S0 rho kappa :=
    { S := A
      level := state.level + 1
      level_le := by omega
      subset_initial := hcut.subset.trans state.subset_initial
      proper_initial := hproperInitial
      boundary_wellLinked := hwellA
      boundary_large := by simpa [GammaA] using hlarge
      contraction_budget := by simpa [GammaA] using hbudget }
  refine ⟨next, ?_⟩
  change GammaA.card < Gamma.card
  have : 0 < Gamma.card := hGammaPos
  omega

end OuterState

/-- Completed set-valued form of Lemma 7.5 for maximum degree three.

The equation `kappa = 256 * rho` is the division-free form used by the final
constant choice. -/
theorem exists_lemma75_set
    {T : Finset V} {rho kappa terminalNum terminalDen : ℕ}
    (hkappaPos : 0 < kappa)
    (hkappa : kappa = 256 * rho)
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V)
        T terminalNum terminalDen)
    (hminimal :
      ∀ ⦃a b : V⦄, G.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (G.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) T terminalNum terminalDen)
    (hdegree : MaxDegreeAtMost G 3)
    (hInitial :
      ∃ S0 : Finset V, IsMinimumInitialSet G T rho S0) :
    ∃ Y : Finset V,
      rho ≤ 4 *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ∧
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ≤ rho ∧
      Section46.ScaledEdgeWellLinkedIn G Y
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T)
        1 finalAlphaDen := by
  classical
  obtain ⟨S0, hS0⟩ := hInitial
  let Gamma0 :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G S0 T
  by_cases hsmall : Gamma0.card ≤ rho
  · refine ⟨S0, hS0.augmentedBoundary_large, by simpa [Gamma0] using hsmall,
        ?_⟩
    exact scaledEdgeWellLinkedIn_weaken_denominator
      hS0.augmentedBoundary_wellLinked (by norm_num [finalAlphaDen])
  · have hrho : rho < Gamma0.card := Nat.lt_of_not_ge hsmall
    have hrhoPos : 0 < rho := by
      rw [hkappa] at hkappaPos
      omega
    have hGammaCard : 2 ≤ Gamma0.card := by omega
    obtain ⟨cut, hcut0⟩ :=
      AppendixA3BalancedCut.exists_minimumQuarterBalancedEdgeCut_of_two_le_card
        (G := G) hS0.augmentedBoundary_wellLinked.2.2.1 hGammaCard
    obtain ⟨A, hcut, horient⟩ := hcut0.exists_oriented
    let GammaA :=
      AppendixA3ClusterSplit.augmentedBoundaryVertices G A T
    have hwellA :
        Section46.ScaledEdgeWellLinkedIn G A GammaA 1 27 := by
      simpa [GammaA] using
        (Lax17Proofs.SimpleGraph.AppendixA3Lemma211.minimumQuarterBalancedEdgeCut_augmentedBoundary_wellLinked_three
            hS0.augmentedBoundary_wellLinked hcut horient)
    have hproperA : A ⊂ S0 :=
      OuterState.proper_of_quarterBalanced
        (by simpa [Gamma0] using lt_of_le_of_lt (Nat.zero_le rho) hrho)
        hcut.toQuarterBalanced
    have hlargeA : rho ≤ 4 * GammaA.card := by
      have hretained :
          A ∩ Gamma0 ⊆ GammaA := by
        simpa [Gamma0, GammaA] using
          (Lax17Proofs.SimpleGraph.AppendixA3AugmentedBoundary.retained_augmentedBoundaryVertices_subset
              (G := G) (T := T) hcut.subset)
      have hcard := Finset.card_le_card hretained
      have hquarter : Gamma0.card ≤ 4 * (A ∩ Gamma0).card := by
        simpa [Gamma0] using hcut.retained_quarter
      omega
    have hboundA : GammaA.card ≤ 974 * kappa := by
      have hbound :=
        Lax17Proofs.SimpleGraph.AppendixA3Corollary74.corollary_7_4_boundary_bound_with_terminal_overlap
            (kappa := kappa) (d := 3) (alphaDen := 27)
            hkappaPos (by norm_num) (by norm_num) hTcard
            hTwell hminimal hwellA hdegree
      change GammaA.card ≤ 12 * kappa * 3 * 27 + 2 * kappa at hbound
      calc
        GammaA.card ≤ 12 * kappa * 3 * 27 + 2 * kappa := hbound
        _ = 974 * kappa := by ring
    let initial : OuterState G T S0 rho kappa :=
      { S := A
        level := 0
        level_le := by norm_num
        subset_initial := hcut.subset
        proper_initial := hproperA
        boundary_wellLinked := by simpa [GammaA] using hwellA
        boundary_large := by simpa [GammaA] using hlargeA
        contraction_budget := by simpa [GammaA] using hboundA }
    obtain ⟨terminal, _hvalid, hgood⟩ :=
      AppendixA3FiniteDescent.exists_terminal_of_measure_descent
        (measure := fun state : OuterState G T S0 rho kappa =>
          (AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.S T).card)
        (Valid := fun _state => True)
        (Good := fun state =>
          (AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.S T).card ≤ rho)
        initial trivial (by
          intro state _hstate hbad
          obtain ⟨next, hnext⟩ :=
            state.exists_successor hS0 hkappa hrhoPos hbad
          exact ⟨next, trivial, hnext⟩)
    refine ⟨terminal.S, terminal.boundary_large, hgood, ?_⟩
    apply scaledEdgeWellLinkedIn_weaken_denominator
      terminal.boundary_wellLinked
    have hpow : 3 ^ terminal.level ≤ 3 ^ 128 :=
      Nat.pow_le_pow_right (by norm_num) terminal.level_le
    simpa [finalAlphaDen] using Nat.mul_le_mul_left 27 hpow

end
end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
