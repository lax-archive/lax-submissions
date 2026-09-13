import Lax17Proofs.Source.Exponent8.Observation54Refinement

namespace Lax17Proofs

/-!
# Finite three-round recursive slicing

This module discharges the finite recursion formerly hidden by
`threeRoundRecursiveSlicing`.

At one depth, the slices whose cleaned row family reaches the declared cap
give the large-slice exit.  Otherwise the increasing enumeration of all small
slices is refined by Observation 5.4 and Theorem 4.6, the local cut systems
are composed, and a prefix coarsening gives exactly the next declared slice
count.  The persistent `RecursiveSlicingContext` then builds the cleanup and
rooted localization data for the new layer.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

open Finset

namespace RecursiveSliceLayer

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width Dhat g : ℕ}

/-- Slices whose additive cleanup retains at least `rowCap` rows. -/
noncomputable def largeIndices
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (rowCap : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => rowCap ≤ (L.cleanup i).rows.card

/-- The complementary family of slices eligible for another refinement. -/
noncomputable def smallIndices
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (rowCap : ℕ) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)) \ L.largeIndices rowCap

@[simp] theorem mem_largeIndices
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (rowCap : ℕ) (i : Fin m) :
    i ∈ L.largeIndices rowCap ↔
      rowCap ≤ (L.cleanup i).rows.card := by
  classical
  simp [largeIndices]

@[simp] theorem mem_smallIndices
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (rowCap : ℕ) (i : Fin m) :
    i ∈ L.smallIndices rowCap ↔
      (L.cleanup i).rows.card < rowCap := by
  classical
  simp [smallIndices, Nat.not_le]

theorem smallIndices_card_add_largeIndices_card
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (rowCap : ℕ) :
    (L.smallIndices rowCap).card +
      (L.largeIndices rowCap).card = m := by
  classical
  unfold smallIndices
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  exact Nat.sub_add_cancel
    (by
      simpa using
        Finset.card_le_card
          (Finset.subset_univ (L.largeIndices rowCap)))

/-- The exact local Theorem 4.6 budget for a small slice.  The proof uses the
half-retention certificate and the strengthened Claim 5.3 loss only once. -/
theorem goodQ_budget_of_mem_small
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (i : Fin m) {rowCap fanout widthNext : ℕ}
    (hi : i ∈ L.smallIndices rowCap)
    (hbudget :
      2 * (fanout * widthNext + (fanout + 1) * rowCap +
        4 * g ^ 4) ≤ width)
    (hg : 0 < g)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    fanout * widthNext +
        (fanout + 1) * (L.cleanup i).rows.card ≤
      (L.observation54GoodQ i).card := by
  have hrow :
      (L.cleanup i).rows.card ≤ rowCap :=
    Nat.le_of_lt ((L.mem_smallIndices rowCap i).1 hi)
  have hcostRows :
      fanout * widthNext +
          (fanout + 1) * (L.cleanup i).rows.card ≤
        fanout * widthNext + (fanout + 1) * rowCap :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_left (fanout + 1) hrow)
      (fanout * widthNext)
  have hwidth := L.width_at_least i
  have hhalf := (L.cleanup i).half_paths
  have hclaim :
      (L.cleanup i).paths.card ≤
        (L.observation54GoodQ i).card + 4 * g ^ 4 := by
    simpa [observation54GoodQ, observation54BadRows] using
      L.claim53Strong_cleanup i hg hnoCrossbar
  have hcostCap :
      fanout * widthNext + (fanout + 1) * rowCap ≤
        (L.observation54GoodQ i).card := by
    omega
  exact hcostRows.trans hcostCap

end RecursiveSliceLayer

/-- The two outcomes of one recursive round. -/
inductive RecursiveRoundResult
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (g Dhat : ℕ)
    {m width : ℕ}
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (rowCap mNext widthNext : ℕ) : Type (max u v)
  | large
      (output : LargeSliceLayer L rowCap)
  | refined
      (next : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        mNext widthNext (4 * g ^ 2) Dhat)

/-- One complete small-slice refinement round, or the corresponding
majority-large exit. -/
theorem recursiveSlicingRound
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat m width rowCap fanout mNext widthNext : ℕ}
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar Dhat)
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (hg : 0 < g)
    (hfanout : 0 < fanout)
    (hmNext : 0 < mNext)
    (hwidthNext : 0 < widthNext)
    (hcount : 2 * mNext ≤ m * fanout)
    (hbudget :
      2 * (fanout * widthNext + (fanout + 1) * rowCap +
        4 * g ^ 4) ≤ width)
    (hmassNext :
      2 * Rbar.card * (4 * g ^ 2) ≤ Dhat * widthNext)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    Nonempty
      (RecursiveRoundResult
        G H A B X P Q Rbar Qbar g Dhat
        L rowCap mNext widthNext) := by
  classical
  by_cases hlarge :
      m ≤ 2 * (L.largeIndices rowCap).card
  · exact ⟨RecursiveRoundResult.large
      ⟨L.largeIndices rowCap, hlarge, by
        intro i hi
        exact (L.mem_largeIndices rowCap i).1 hi⟩⟩
  · let small := L.smallIndices rowCap
    have hpartition :
        small.card + (L.largeIndices rowCap).card = m := by
      simpa [small] using
        L.smallIndices_card_add_largeIndices_card rowCap
    have hmSmall : m ≤ 2 * small.card := by
      omega
    have hcountProduct :
        mNext ≤ small.card * fanout := by
      have hmul :
          m * fanout ≤ (2 * small.card) * fanout :=
        Nat.mul_le_mul_right fanout hmSmall
      have :
          2 * mNext ≤ 2 * (small.card * fanout) := by
        calc
          2 * mNext ≤ m * fanout := hcount
          _ ≤ (2 * small.card) * fanout := hmul
          _ = 2 * (small.card * fanout) := by
            simp [Nat.mul_assoc]
      omega
    have hsmallPos : 0 < small.card := by
      by_contra hzero
      have : small.card = 0 := Nat.eq_zero_of_not_pos hzero
      rw [this] at hcountProduct
      simp at hcountProduct
      omega
    let selected : Fin small.card → Fin m :=
      small.orderEmbOfFin rfl
    have hselected : StrictMono selected :=
      (small.orderEmbOfFin rfl).strictMono
    have hselectedSmall :
        ∀ a : Fin small.card, selected a ∈ small := by
      intro a
      exact small.orderEmbOfFin_mem rfl a
    let refine :
        ∀ a : Fin small.card,
          PathSlicing.ExtendedParentRefinement
            L.sigma Qbar (selected a) fanout widthNext :=
      fun a =>
        Classical.choice
          (L.exists_observation54ExtendedParentRefinement
            (selected a) C.Dhat_pos hfanout hwidthNext
            (L.goodQ_budget_of_mem_small
              (selected a) (hselectedSmall a)
              hbudget hg hnoCrossbar))
    rcases
        PathSlicing.composeSelectedSliceRefinements
          L.sigma selected hselected refine hsmallPos hfanout with
      ⟨tau, htau, _hcell⟩
    rcases
        PathSlicing.takePrefixCoarsening
          tau Qbar hmNext hcountProduct htau with
      ⟨tauNext, htauNext⟩
    exact ⟨RecursiveRoundResult.refined
      (C.toLayer tauNext htauNext hmassNext)⟩

/-- The three finite rounds, with no project-specific axiom.  The persistent
context is an actual producer exported by the rooted Observation 4.4 state,
not a semantic assumption. -/
theorem threeRoundRecursiveSlicing
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat : ℕ}
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar Dhat)
    (p : ThreeRoundParameters g Rbar.card Dhat)
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      p.m0 p.w0 (4 * g ^ 2) Dhat)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    Nonempty
      (ThreeRoundRecursiveSlicingResult
        G H A B X P Q Rbar Qbar g Dhat p L0) := by
  have hg : 0 < g := by
    have := p.g_at_least_two
    omega
  have hw32 : p.w3 ≤ p.w2 := by
    have hone : 1 ≤ p.fanout := p.fanout_pos
    have hmul : p.w3 ≤ p.fanout * p.w3 := by
      simpa using Nat.mul_le_mul_right p.w3 hone
    let total :=
      p.fanout * p.w3 + (p.fanout + 1) * p.cap2 + 4 * g ^ 4
    have hsum : p.fanout * p.w3 ≤ total := by
      dsimp [total]
      omega
    have hdouble : total ≤ 2 * total := by omega
    exact hmul.trans (hsum.trans (hdouble.trans p.refineBudget23))
  have hw21 : p.w2 ≤ p.w1 := by
    have hone : 1 ≤ p.fanout := p.fanout_pos
    have hmul : p.w2 ≤ p.fanout * p.w2 := by
      simpa using Nat.mul_le_mul_right p.w2 hone
    let total :=
      p.fanout * p.w2 + (p.fanout + 1) * p.cap1 + 4 * g ^ 4
    have hsum : p.fanout * p.w2 ≤ total := by
      dsimp [total]
      omega
    have hdouble : total ≤ 2 * total := by omega
    exact hmul.trans (hsum.trans (hdouble.trans p.refineBudget12))
  have hmass1 :
      2 * Rbar.card * (4 * g ^ 2) ≤ Dhat * p.w1 :=
    p.finalPruning.trans
      (Nat.mul_le_mul_left Dhat (hw32.trans hw21))
  have hmass2 :
      2 * Rbar.card * (4 * g ^ 2) ≤ Dhat * p.w2 :=
    p.finalPruning.trans
      (Nat.mul_le_mul_left Dhat hw32)
  have hmass3 :
      2 * Rbar.card * (4 * g ^ 2) ≤ Dhat * p.w3 :=
    p.finalPruning
  rcases
      recursiveSlicingRound C L0 hg p.fanout_pos p.counts_pos.2.1
        p.widths_pos.2.1 p.count01 p.refineBudget01 hmass1
        hnoCrossbar with
    ⟨round0⟩
  cases round0 with
  | large output =>
      exact ⟨ThreeRoundRecursiveSlicingResult.large0 output⟩
  | refined L1 =>
      rcases
          recursiveSlicingRound C L1 hg p.fanout_pos p.counts_pos.2.2.1
            p.widths_pos.2.2.1 p.count12 p.refineBudget12 hmass2
            hnoCrossbar with
        ⟨round1⟩
      cases round1 with
      | large output =>
          exact ⟨ThreeRoundRecursiveSlicingResult.large1 L1 output⟩
      | refined L2 =>
          rcases
              recursiveSlicingRound C L2 hg p.fanout_pos
                p.counts_pos.2.2.2 p.widths_pos.2.2.2 p.count23
                p.refineBudget23 hmass3 hnoCrossbar with
            ⟨round2⟩
          cases round2 with
          | large output =>
              exact ⟨ThreeRoundRecursiveSlicingResult.large2 L2 output⟩
          | refined L3 =>
              exact ⟨ThreeRoundRecursiveSlicingResult.final L3⟩

end Exponent8
end SimpleGraph

end Lax17Proofs
