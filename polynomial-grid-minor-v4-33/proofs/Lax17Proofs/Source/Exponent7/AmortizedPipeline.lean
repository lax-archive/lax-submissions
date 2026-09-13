import Lax17Proofs.Source.Exponent7.AmortizedParameters
import Lax17Proofs.Source.Exponent7.ConditionalSection5Grid

namespace Lax17Proofs

/-!
# Explicit amortized Section 5 pipeline

The finite-fuel controller is instantiated with logarithmic depth, initial
width equal to the row count, and terminal scale `16*q^4`.
-/

namespace SimpleGraph
namespace Exponent7

universe u v

open Exponent8

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
    {q ell g reserve : ℕ}

/-- Run the logarithmic-depth controller from the explicit initial layer. -/
theorem exists_explicitAmortizedSlicingDichotomy
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar (32 * q ^ 4))
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenInitialSlices q Rbar.card ell)
      Rbar.card (4 * q ^ 2) (32 * q ^ 4))
    (hq : 2 ≤ q)
    (hell : 0 < ell)
    (hNpos : 0 < Rbar.card)
    (hNupper : Rbar.card ≤ 64 * q ^ 6)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (q ^ 2))) :
    Nonempty
      (AmortizedSlicingDichotomy
        G H A B X P Q Rbar Qbar
        q (32 * q ^ 4)
        (amortizedDepth Rbar.card)
        (exponentSevenDstar q)
        (exponentSevenInitialSlices q Rbar.card ell *
          Rbar.card)) := by
  have hMpos :
      0 < exponentSevenInitialSlices q Rbar.card ell :=
    exponentSeven_initialSlices_pos hell
  exact
    exists_amortizedSlicingDichotomy
      C L0 (by omega) (amortizedDepth_pos Rbar.card)
      (exponentSevenDstar_pos (by omega))
      (amortizedLoss_le_exponentSevenDstar q)
      (exponentSeven_additive_budget hNupper)
      (exponentSeven_pruning_budget hNupper)
      hnoCrossbar
      (Nat.mul_pos hMpos hNpos)
      (exponentSeven_width_depth hNpos (by omega))

/-- The explicit amortized pipeline yields the target grid.  Apart from the
clean matching dichotomy hypothesis, all graph constructions and arithmetic
are proof-producing declarations. -/
theorem gridMinor_of_explicitAmortizedPipeline
    (hD : CleanMatchingDichotomyStatement.{v} reserve)
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar (32 * q ^ 4))
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenInitialSlices q Rbar.card ell)
      Rbar.card (4 * q ^ 2) (32 * q ^ 4))
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hdegree : MaxDegreeAtMost H 4)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hell : 0 < ell)
    (hNlower : 64 * q ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * q ^ 6)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (q ^ 2)))
    (hg : 2 ≤ g)
    (hlen : 2 * g ≤ ell)
    (hreserve : 0 < reserve)
    (hscaledWidth :
      20000 * (reserve * g ^ 2) ≤ q ^ 2) :
    ContainsGridMinor H g := by
  obtain ⟨Result⟩ :=
    exists_explicitAmortizedSlicingDichotomy
      C L0 hq hell
        (by
          have : 0 < 64 * q ^ 4 := by positivity
          exact this.trans_le hNlower)
        hNupper hnoCrossbar
  exact
    Result.gridMinor_of_cleanMatchingDichotomy
      hD hintersects hdegree hq hpow
      (amortizedDepth_pos Rbar.card)
      (exponentSevenDstar_pos (by omega))
      hell hNlower hNupper
      (exponentSeven_productive_budget q Rbar.card ell)
      (exponentSeven_terminal_budget q Rbar.card ell)
      hg hlen hreserve hscaledWidth

/-- Uniform-depth version whose initial slice count depends only on `q` and
the requested length, not on the particular reduced row count. -/
theorem exists_uniformAmortizedSlicingDichotomy
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar (32 * q ^ 4))
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenUniformSlices q ell)
      Rbar.card (4 * q ^ 2) (32 * q ^ 4))
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hell : 0 < ell)
    (hNpos : 0 < Rbar.card)
    (hNupper : Rbar.card ≤ 64 * q ^ 6)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (q ^ 2))) :
    Nonempty
      (AmortizedSlicingDichotomy
        G H A B X P Q Rbar Qbar
        q (32 * q ^ 4)
        (exponentSevenUniformDepth q)
        (exponentSevenDstar q)
        (exponentSevenUniformSlices q ell *
          Rbar.card)) := by
  exact
    exists_amortizedSlicingDichotomy
      C L0 (by omega)
      (exponentSevenUniformDepth_pos q)
      (exponentSevenDstar_pos (by omega))
      (amortizedLoss_le_exponentSevenDstar q)
      (exponentSeven_additive_budget hNupper)
      (exponentSeven_pruning_budget hNupper)
      hnoCrossbar
      (Nat.mul_pos
        (exponentSevenUniformSlices_pos hell) hNpos)
      (exponentSeven_uniform_width_depth
        hpow hNupper (by omega))

/-- Unconditional output of the uniform amortized Section 5 controller.

This is the reusable boundary needed for the exact exponent-eight route.
It contains no short-wide or clean-matching hypothesis: the logarithmic-depth
recursion alone produces a weak Path-of-Sets System of the requested length
`ell` and width `q^2`. -/
theorem weakPathOfSetsSystem_of_uniformAmortizedPipeline
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar (32 * q ^ 4))
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenUniformSlices q ell)
      Rbar.card (4 * q ^ 2) (32 * q ^ 4))
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hell : 0 < ell)
    (hNlower : 64 * q ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * q ^ 6)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (q ^ 2))) :
    Nonempty (WeakPathOfSetsSystem H ell (q ^ 2)) := by
  have hNpos : 0 < Rbar.card := by
    have : 0 < 64 * q ^ 4 := by positivity
    exact this.trans_le hNlower
  obtain ⟨Result⟩ :=
    exists_uniformAmortizedSlicingDichotomy
      C L0 hq hpow hell hNpos hNupper hnoCrossbar
  exact
    Result.weakPathOfSetsSystem
      hintersects hq hpow
      (exponentSevenUniformDepth_pos q)
      (exponentSevenDstar_pos (by omega))
      hell hNlower hNupper
      (exponentSeven_uniform_productive_budget
        q Rbar.card ell)
      (exponentSeven_uniform_terminal_budget
        q Rbar.card ell)

/-- Uniform amortized pipeline. -/
theorem gridMinor_of_uniformAmortizedPipeline
    (hD : CleanMatchingDichotomyStatement.{v} reserve)
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar (32 * q ^ 4))
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenUniformSlices q ell)
      Rbar.card (4 * q ^ 2) (32 * q ^ 4))
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hdegree : MaxDegreeAtMost H 4)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hell : 0 < ell)
    (hNlower : 64 * q ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * q ^ 6)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (q ^ 2)))
    (hg : 2 ≤ g)
    (hlen : 2 * g ≤ ell)
    (hreserve : 0 < reserve)
    (hscaledWidth :
      20000 * (reserve * g ^ 2) ≤ q ^ 2) :
    ContainsGridMinor H g := by
  have hNpos : 0 < Rbar.card := by
    have : 0 < 64 * q ^ 4 := by positivity
    exact this.trans_le hNlower
  obtain ⟨Result⟩ :=
    exists_uniformAmortizedSlicingDichotomy
      C L0 hq hpow hell hNpos hNupper hnoCrossbar
  exact
    Result.gridMinor_of_cleanMatchingDichotomy
      hD hintersects hdegree hq hpow
      (exponentSevenUniformDepth_pos q)
      (exponentSevenDstar_pos (by omega))
      hell hNlower hNupper
      (exponentSeven_uniform_productive_budget
        q Rbar.card ell)
      (exponentSeven_uniform_terminal_budget
        q Rbar.card ell)
      hg hlen hreserve hscaledWidth

end Exponent7
end SimpleGraph

end Lax17Proofs
