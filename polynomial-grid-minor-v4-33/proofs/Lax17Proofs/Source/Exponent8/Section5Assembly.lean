import Lax17Proofs.Source.Exponent8.Case1Section45Assembly
import Lax17Proofs.Source.Exponent8.RootedSection42
import Lax17Proofs.Source.Exponent8.ThreeRoundRecursion
import Lax17Proofs.Source.Exponent8.ThreeRoundParameters

namespace Lax17Proofs

/-!
# Four-branch Section 5 assembly

This module consumes the three-round recursion result.  Each majority-large
branch uses all happy clusters, corrected dyadic grouping, Theorem 4.15, and
the parent-slice row-gap construction.  The all-small branch already has the
final slicing and additive cleanup, so it invokes the source-faithful
one-happy-core-per-slice Section 4.4--4.5 assembly.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

open Finset

namespace ThreeRoundParameters

/-- The exact refinement budgets make the slice widths nonincreasing. -/
theorem w3_le_w0 {g N Dhat : ℕ}
    (p : ThreeRoundParameters g N Dhat) :
    p.w3 ≤ p.w0 := by
  have hone : 1 ≤ p.fanout := p.fanout_pos
  have hw32 : p.w3 ≤ p.w2 := by
    calc
      p.w3 ≤ p.fanout * p.w3 := by
        simpa using Nat.mul_le_mul_right p.w3 hone
      _ ≤ p.fanout * p.w3 +
          (p.fanout + 1) * p.cap2 + 4 * g ^ 4 := by omega
      _ ≤ 2 * (p.fanout * p.w3 +
          (p.fanout + 1) * p.cap2 + 4 * g ^ 4) := by omega
      _ ≤ p.w2 := p.refineBudget23
  have hw21 : p.w2 ≤ p.w1 := by
    calc
      p.w2 ≤ p.fanout * p.w2 := by
        simpa using Nat.mul_le_mul_right p.w2 hone
      _ ≤ p.fanout * p.w2 +
          (p.fanout + 1) * p.cap1 + 4 * g ^ 4 := by omega
      _ ≤ 2 * (p.fanout * p.w2 +
          (p.fanout + 1) * p.cap1 + 4 * g ^ 4) := by omega
      _ ≤ p.w1 := p.refineBudget12
  have hw10 : p.w1 ≤ p.w0 := by
    calc
      p.w1 ≤ p.fanout * p.w1 := by
        simpa using Nat.mul_le_mul_right p.w1 hone
      _ ≤ p.fanout * p.w1 +
          (p.fanout + 1) * p.cap0 + 4 * g ^ 4 := by omega
      _ ≤ 2 * (p.fanout * p.w1 +
          (p.fanout + 1) * p.cap0 + 4 * g ^ 4) := by omega
      _ ≤ p.w0 := p.refineBudget01
  exact hw32.trans (hw21.trans hw10)

end ThreeRoundParameters

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
    {m width g rowCap : ℕ}

private theorem section5_N_large
    (hg : 2 ≤ g) {N : ℕ}
    (hNlower : 64 * g ^ 4 ≤ N) :
    3 * g ^ 2 ≤ N := by
  calc
    3 * g ^ 2 ≤ 64 * g ^ 2 :=
      Nat.mul_le_mul_right (g ^ 2) (by omega)
    _ ≤ 64 * g ^ 4 :=
      Nat.mul_le_mul_left 64
        (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ N := hNlower

private theorem section5_depth_square
    {N Dclass : ℕ}
    (g : ℕ)
    (hNupper : N ≤ 64 * g ^ 6)
    (hdepth : 16 * g ^ 4 ≤ Dclass) :
    4 * N * g ^ 2 ≤ Dclass ^ 2 := by
  calc
    4 * N * g ^ 2 ≤ 4 * (64 * g ^ 6) * g ^ 2 :=
      Nat.mul_le_mul_right (g ^ 2)
        (Nat.mul_le_mul_left 4 hNupper)
    _ = (16 * g ^ 4) ^ 2 := by ring
    _ ≤ Dclass ^ 2 := Nat.pow_le_pow_left hdepth 2

/-- A majority-large recursive layer yields a weak path-of-sets system of
length and width `g^2`.  The mass hypothesis is multiplication-only and is
exactly the one recorded at each recursion depth. -/
theorem weakPathOfSetsSystem_of_largeSliceLayer
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (Large : LargeSliceLayer L rowCap)
    (hintersects : PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hNlower : 64 * g ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * g ^ 6)
    (hmass :
      2 *
          (32 * Rbar.card * g ^ 2 *
            (Nat.log 2 g + 1)) ≤
        m * rowCap) :
    Nonempty (WeakPathOfSetsSystem H (g ^ 2) (g ^ 2)) := by
  have hinputMass :
      32 * Rbar.card * g ^ 2 * (Nat.log 2 g + 1) ≤
        ∑ i ∈ Large.large, (L.cleanup i).rows.card :=
    L.assemblyMass_le_sum_rows Large hmass
  rcases
      L.exists_parentedHappyClusterTable_of_largeSliceMass
        Large hintersects hg hpow hNupper hinputMass with
    ⟨C, Dclass, ⟨T⟩⟩
  have hN : 3 * g ^ 2 ≤ Rbar.card :=
    section5_N_large hg hNlower
  have hDsq : 4 * Rbar.card * g ^ 2 ≤ Dclass ^ 2 :=
    section5_depth_square g hNupper T.depth_base
  rcases T.section45Input (by omega) hN hDsq with ⟨Input⟩
  exact Section45.section45_weak_pathOfSetsSystem Input

/-- The final recursive layer already contains the additive Lemma 4.8
cleanup in every slice.  Select one connected happy core from each cleanup
without rerunning pruning. -/
noncomputable def slicedHappyCores_of_finalLayer
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (hg : 0 < g)
    (hwidth : 0 < width) :
    L.sigma.SlicedHappyCores Qbar (g ^ 2) (16 * g ^ 4) := by
  classical
  have hw : 0 < g ^ 2 := by positivity
  have hD : 0 < 16 * g ^ 4 := by positivity
  have hscale : 8 * g ^ 2 ≤ 16 * g ^ 4 := by
    calc
      8 * g ^ 2 ≤ 16 * g ^ 2 :=
        Nat.mul_le_mul_right (g ^ 2) (by omega)
      _ ≤ 16 * g ^ 4 :=
        Nat.mul_le_mul_left 16
          (Nat.pow_le_pow_right hg (by omega))
  let cleaned :
      ∀ i : Fin m,
        L.sigma.SliceIntersectingSubfamilies
          Qbar i (4 * (g ^ 2)) (2 * (16 * g ^ 4)) :=
    fun i => (L.happyCleanup i).toOrdinary
  let core :
      ∀ i : Fin m,
        L.sigma.SliceHappyCoreData Qbar i (cleaned i) :=
    fun i =>
      Classical.choice <|
        L.sigma.exists_sliceHappyCoreData
          Qbar i (cleaned i) hw hD hscale
          (by
            apply Finset.card_pos.mp
            have hslice :
                0 < (L.sigma.pathsInSlice Qbar i).card :=
              hwidth.trans_le (L.width_at_least i)
            have hhalf := (cleaned i).half_paths
            omega)
  exact { cleaned := cleaned, core := core }

/-- The all-small terminal branch of the three-round recursion. -/
theorem weakPathOfSetsSystem_of_finalLayer
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (hintersects : PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hg : 2 ≤ g)
    (hNlower : 64 * g ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * g ^ 6)
    (hwidth : 0 < width)
    (hcount : 8 * g ^ 4 * (Nat.log 2 g + 1) ≤ m) :
    Nonempty (WeakPathOfSetsSystem H (g ^ 2) (g ^ 2)) := by
  let D := L.slicedHappyCores_of_finalLayer (by omega) hwidth
  have hN : 3 * g ^ 2 ≤ Rbar.card :=
    section5_N_large hg hNlower
  have hDsq :
      4 * Rbar.card * g ^ 2 ≤ (16 * g ^ 4) ^ 2 :=
    section5_depth_square g hNupper le_rfl
  have hlarge :
      2 * Rbar.card * g ^ 2 ≤ (16 * g ^ 4) * m := by
    calc
      2 * Rbar.card * g ^ 2
          ≤ 2 * (64 * g ^ 6) * g ^ 2 :=
        Nat.mul_le_mul_right (g ^ 2)
          (Nat.mul_le_mul_left 2 hNupper)
      _ = 128 * g ^ 8 := by ring
      _ ≤ 128 * g ^ 8 * (Nat.log 2 g + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      _ = (16 * g ^ 4) *
          (8 * g ^ 4 * (Nat.log 2 g + 1)) := by ring
      _ ≤ (16 * g ^ 4) * m :=
        Nat.mul_le_mul_left (16 * g ^ 4) hcount
  rcases
      D.section45Input_of_slicedHappyCores
        hintersects (by positivity)
        (by
          calc
            8 * g ^ 2 ≤ 16 * g ^ 2 :=
              Nat.mul_le_mul_right (g ^ 2) (by omega)
            _ ≤ 16 * g ^ 4 :=
              Nat.mul_le_mul_left 16
                (Nat.pow_le_pow_right (by omega) (by omega)))
        hN hDsq hlarge with
    ⟨Input⟩
  exact Section45.section45_weak_pathOfSetsSystem Input

end RecursiveSliceLayer

/-- All four constructors of `ThreeRoundRecursiveSlicingResult` have the
same source-level Section 5 output. -/
theorem ThreeRoundRecursiveSlicingResult.weakPathOfSetsSystem
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g : ℕ}
    {p : ThreeRoundParameters g Rbar.card (32 * g ^ 4)}
    {L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      p.m0 p.w0 (4 * g ^ 2) (32 * g ^ 4)}
    (Result : ThreeRoundRecursiveSlicingResult
      G H A B X P Q Rbar Qbar g (32 * g ^ 4) p L0)
    (hintersects : PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hNlower : 64 * g ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * g ^ 6)
    (hassembly :
      p.assemblyMass =
        32 * Rbar.card * g ^ 2 * (Nat.log 2 g + 1)) :
    Nonempty (WeakPathOfSetsSystem H (g ^ 2) (g ^ 2)) := by
  cases Result with
  | large0 output =>
      apply L0.weakPathOfSetsSystem_of_largeSliceLayer
        output hintersects p.g_at_least_two hpow hNlower hNupper
      simpa [hassembly] using p.largeMass0
  | large1 L1 output =>
      apply L1.weakPathOfSetsSystem_of_largeSliceLayer
        output hintersects p.g_at_least_two hpow hNlower hNupper
      simpa [hassembly] using p.largeMass1
  | large2 L2 output =>
      apply L2.weakPathOfSetsSystem_of_largeSliceLayer
        output hintersects p.g_at_least_two hpow hNlower hNupper
      simpa [hassembly] using p.largeMass2
  | final L3 =>
      exact L3.weakPathOfSetsSystem_of_finalLayer
        hintersects p.g_at_least_two hNlower hNupper
        p.widths_pos.2.2.2 p.finalSliceCount

/-- Source-level producer through the complete three-round Section 5
assembly.  The conclusion lives in the actual reduced graph constructed by
Observation 4.4.  No contract or project axiom is used.

The `goodQSet` inequality is the exact local Theorem 4.6 cost.  It is kept in
this source-facing form so the public polynomial-grid-minor endpoint remains
unchanged during the exponent-eight experiment. -/
theorem exists_reduced_weakPathOfSetsSystem_threeRound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {g D : ℕ}
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hNlower : 64 * g ^ 4 ≤ Gamma.rowPacking.card)
    (hNupper : Gamma.rowPacking.card ≤ 64 * g ^ 6)
    (hDscale : 64 * g ^ 4 ≤ D)
    (hgood :
      e8M0 g * e8W0 g +
          (e8M0 g + 1) * Gamma.rowPacking.card ≤
        Gamma.goodQSet.card)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    ∃ Root : RootedObservation44State Gamma,
      ∃ hReduced : Root.state.IsReduced,
        Nonempty
          (WeakPathOfSetsSystem
            (Root.state.reducedGraph hReduced)
            (g ^ 2) (g ^ 2)) := by
  have hDpos : 0 < D := by
    have : 0 < 64 * g ^ 4 := by positivity
    exact this.trans_le hDscale
  have hNpos : 0 < Gamma.rowPacking.card := by
    have : 0 < 64 * g ^ 4 := by positivity
    exact this.trans_le hNlower
  let p0 :=
    ThreeRoundParameters.explicitExponentEightParameters
      g Gamma.rowPacking.card (32 * g ^ 4) hg hNupper rfl
  have hinitialMass :
      2 * Gamma.rowPacking.card * (4 * g ^ 2) ≤
        (32 * g ^ 4) * e8W0 g := by
    have hp :
        2 * Gamma.rowPacking.card * (4 * g ^ 2) ≤
          (32 * g ^ 4) * p0.w0 :=
      p0.finalPruning.trans
        (Nat.mul_le_mul_left (32 * g ^ 4) p0.w3_le_w0)
    simpa [p0, ThreeRoundParameters.explicitExponentEightParameters] using hp
  rcases
      exists_initialRecursiveSliceLayer_of_pseudoGrid
        Gamma hminimal hDpos
        (by simp [e8M0, e8Fanout, e8LogFactor]; positivity)
        (by
          have hgpos : 0 < g := by omega
          unfold e8W0 e8W1 e8W2 e8W3 e8Cap0
            e8Cap1 e8Cap2 e8Fanout
          positivity)
        hgood
        (by positivity : 0 < 32 * g ^ 4)
        (by
          calc
            2 * (32 * g ^ 4) = 64 * g ^ 4 := by ring
            _ ≤ D := hDscale)
        hinitialMass hXdisjoint with
    ⟨Root, hReduced, ⟨L0⟩⟩
  let Rbar := Root.state.reducedRow hReduced
  let Qbar := Root.state.reducedRetained hReduced
  have hRcard : Rbar.card = Gamma.rowPacking.card := by
    simp [Rbar]
  have hRlower : 64 * g ^ 4 ≤ Rbar.card := by
    rw [hRcard]
    exact hNlower
  have hRupper : Rbar.card ≤ 64 * g ^ 6 := by
    rw [hRcard]
    exact hNupper
  let p :=
    ThreeRoundParameters.explicitExponentEightParameters
      g Rbar.card (32 * g ^ 4) hg hRupper rfl
  let Ctxt :=
    Root.recursiveSlicingContext hReduced hNpos
      (by positivity : 0 < 32 * g ^ 4)
      (by
        calc
          2 * (32 * g ^ 4) = 64 * g ^ 4 := by ring
          _ ≤ D := hDscale)
      hXdisjoint
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar := by
    simpa [Rbar, Qbar] using
      Root.state.reducedRetained_intersects_reducedRow hReduced hDpos
  let L0' :
      RecursiveSliceLayer
        G (Root.state.reducedGraph hReduced) A B X P Q
        Rbar Qbar p.m0 p.w0 (4 * g ^ 2) (32 * g ^ 4) := by
    simpa [p, ThreeRoundParameters.explicitExponentEightParameters] using L0
  rcases threeRoundRecursiveSlicing Ctxt p L0' hnoCrossbar with
    ⟨Result⟩
  refine ⟨Root, hReduced, ?_⟩
  exact Result.weakPathOfSetsSystem
    hintersects hpow hRlower hRupper
    (by rfl)

end Exponent8
end SimpleGraph

end Lax17Proofs
