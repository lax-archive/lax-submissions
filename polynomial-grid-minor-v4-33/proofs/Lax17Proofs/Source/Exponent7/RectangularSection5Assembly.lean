import Lax17Proofs.Source.Exponent7.AmortizedController
import Lax17Proofs.Source.Exponent7.RectangularCase1Assembly
import Lax17Proofs.Source.Exponent8.Section5Assembly

namespace Lax17Proofs

/-!
# Rectangular Section 5 exits

This module connects the two outputs of the amortized controller to a weak
path-of-sets system of length `ell` and width `g^2`.
-/

namespace SimpleGraph
namespace Exponent7

universe u v

open Finset
open Exponent8

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
    {m width g ell : ℕ}

private theorem rectangular_N_large
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

private theorem rectangular_depth_square
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

/-- Any collection of productive slices with the explicit rectangular mass
bound yields the short-wide weak path-of-sets system. -/
theorem weakPathOfSetsSystem_of_rectangularLargeSliceMass
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (large : Finset (Fin m))
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hEll : 0 < ell)
    (hNlower : 64 * g ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * g ^ 6)
    (hinputMass :
      32 * Rbar.card * ell * (Nat.log 2 g + 1) ≤
        ∑ i ∈ large, (L.cleanup i).rows.card) :
    Nonempty
      (WeakPathOfSetsSystem H ell (g ^ 2)) := by
  rcases
      exists_rectangularParentedHappyClusterTable_of_largeSliceMass
        L large hintersects hg hpow hNupper hinputMass with
    ⟨C, Dclass, ⟨T⟩⟩
  have hN : 3 * g ^ 2 ≤ Rbar.card :=
    rectangular_N_large hg hNlower
  have hDsq :
      4 * Rbar.card * g ^ 2 ≤ Dclass ^ 2 :=
    rectangular_depth_square g hNupper T.depth_base
  rcases
      T.rectangularSection45Input
        hEll (by omega) hN hDsq with
    ⟨Input⟩
  exact rectangular_section45_weak_pathOfSetsSystem Input

/-- The canonical one-happy-core table carried by a terminal recursive
layer. -/
noncomputable def terminalRectangularTable
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hg : 0 < g)
    (hwidth : 0 < width)
    (hcount :
      2 * Rbar.card * ell ≤ (16 * g ^ 4) * m) :
    RectangularParentedHappyClusterTable
      Rbar Qbar L ell m (16 * g ^ 4) := by
  classical
  let D := L.slicedHappyCores_of_finalLayer hg hwidth
  exact {
    parent := id
    parent_monotone := monotone_id
    cluster := fun i => (D.core i).cluster
    rows := fun i => (D.core i).rows
    cluster_connected := fun i => (D.core i).cluster_connected
    cluster_disjoint := by
      intro i j hij
      exact D.cluster_disjoint hintersects (by positivity) hij
    rows_same_parent_disjoint := by
      intro i j hij hparent
      exact (hij hparent).elim
    cluster_subset_support := by
      intro i
      simpa [D, RecursiveSliceLayer.slicedHappyCores_of_finalLayer]
        using (D.core i).cluster_subset_support
    rows_subset_cleanup := by
      intro i
      simpa [D, RecursiveSliceLayer.slicedHappyCores_of_finalLayer]
        using (D.core i).rows_subset
    row_card := fun i => (D.core i).row_card
    row_path_contained := fun i => (D.core i).row_path_contained
    weak := fun i => (D.core i).weak
    depth_base := le_rfl
    count_mass := hcount
  }

/-- A terminal slicing with enough slices yields the same rectangular
short-wide system. -/
theorem weakPathOfSetsSystem_of_rectangularFinalLayer
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hg : 2 ≤ g)
    (hNlower : 64 * g ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * g ^ 6)
    (hEll : 0 < ell)
    (hwidth : 0 < width)
    (hcount :
      2 * Rbar.card * ell ≤ (16 * g ^ 4) * m) :
    Nonempty
      (WeakPathOfSetsSystem H ell (g ^ 2)) := by
  let T :=
    terminalRectangularTable L hintersects
      (by omega) hwidth hcount
  have hN : 3 * g ^ 2 ≤ Rbar.card :=
    rectangular_N_large hg hNlower
  have hDsq :
      4 * Rbar.card * g ^ 2 ≤
        (16 * g ^ 4) ^ 2 :=
    rectangular_depth_square g hNupper le_rfl
  rcases
      T.rectangularSection45Input
        hEll (by omega) hN hDsq with
    ⟨Input⟩
  exact rectangular_section45_weak_pathOfSetsSystem Input

end RecursiveSliceLayer

namespace AmortizedSlicingDichotomy

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
    {g h Dstar initial ell : ℕ}

/-- Both outputs of the amortized controller imply the same rectangular
Section 5 path-of-sets system once the initial potential pays the productive
and terminal accounting inequalities. -/
theorem weakPathOfSetsSystem
    (Result :
      AmortizedSlicingDichotomy
        G H A B X P Q Rbar Qbar
        g (32 * g ^ 4) h Dstar initial)
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hh : 0 < h)
    (hDstar : 0 < Dstar)
    (hEll : 0 < ell)
    (hNlower : 64 * g ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * g ^ 6)
    (hproductiveBudget :
      (16 * (h + 1) * (2048 * h)) *
          (32 * Rbar.card * ell *
            (Nat.log 2 g + 1)) ≤
        7 * initial)
    (hterminalBudget :
      (16 * amortizedStopThreshold h Dstar) *
          (2 * Rbar.card * ell) ≤
        (7 * initial) * (16 * g ^ 4)) :
    Nonempty
      (WeakPathOfSetsSystem H ell (g ^ 2)) := by
  cases Result with
  | productive L hmass =>
      have hfactor :
          0 < 16 * (h + 1) * (2048 * h) := by
        positivity
      have hinputMass :
          32 * Rbar.card * ell *
              (Nat.log 2 g + 1) ≤
            L.rowMass := by
        apply Nat.le_of_mul_le_mul_left
          (hproductiveBudget.trans hmass) hfactor
      apply
        RecursiveSliceLayer.weakPathOfSetsSystem_of_rectangularLargeSliceMass
          L.layer L.indices hintersects hg hpow hEll
          hNlower hNupper
      simpa [AmortizedProductiveLayer.rowMass] using
        hinputMass
  | @terminal m width L hwidthPos hwidth hcount =>
      have hscale :
          0 <
            16 * amortizedStopThreshold h Dstar := by
        simp [amortizedStopThreshold, hh, hDstar]
      have hscaled :
          (16 * amortizedStopThreshold h Dstar) *
              (2 * Rbar.card * ell) ≤
            (16 * amortizedStopThreshold h Dstar) *
              ((16 * g ^ 4) * m) := by
        calc
          (16 * amortizedStopThreshold h Dstar) *
                (2 * Rbar.card * ell)
              ≤ (7 * initial) * (16 * g ^ 4) :=
            hterminalBudget
          _ ≤
              (16 * m *
                amortizedStopThreshold h Dstar) *
                  (16 * g ^ 4) :=
            Nat.mul_le_mul_right (16 * g ^ 4) hcount
          _ =
              (16 * amortizedStopThreshold h Dstar) *
                ((16 * g ^ 4) * m) := by
            ring
      have hcount' :
          2 * Rbar.card * ell ≤
            (16 * g ^ 4) * m :=
        Nat.le_of_mul_le_mul_left hscaled hscale
      exact
        RecursiveSliceLayer.weakPathOfSetsSystem_of_rectangularFinalLayer
          L hintersects hg hNlower hNupper hEll
          hwidthPos hcount'

end AmortizedSlicingDichotomy

end Exponent7
end SimpleGraph

end Lax17Proofs
