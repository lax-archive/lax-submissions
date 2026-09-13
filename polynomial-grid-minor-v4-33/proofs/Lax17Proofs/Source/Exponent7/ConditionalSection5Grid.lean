import Lax17Proofs.Source.Exponent7.RectangularSection5Assembly
import Lax17Proofs.Source.Exponent7.ShortWideGrid

namespace Lax17Proofs

/-!
# Conditional exponent-seven Section 5 grid exit

The amortized rectangular Section 5 construction and the short-wide grid
construction are combined under the hypothesis
`CleanMatchingDichotomyStatement reserve`.
-/

namespace SimpleGraph
namespace Exponent7

universe u v

open Exponent8

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
    {q h Dstar initial ell g reserve : ℕ}

/-- A completed amortized slicing run yields the target grid once its
rectangular weak system is wide enough to pay the explicit strongification
loss and the clean matching dichotomy. -/
theorem gridMinor_of_cleanMatchingDichotomy
    (hD : CleanMatchingDichotomyStatement.{v} reserve)
    (Result :
      AmortizedSlicingDichotomy
        G H A B X P Q Rbar Qbar
        q (32 * q ^ 4) h Dstar initial)
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hdegree : MaxDegreeAtMost H 4)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hh : 0 < h)
    (hDstar : 0 < Dstar)
    (hEll : 0 < ell)
    (hNlower : 64 * q ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * q ^ 6)
    (hproductiveBudget :
      (16 * (h + 1) * (2048 * h)) *
          (32 * Rbar.card * ell *
            (Nat.log 2 q + 1)) ≤
        7 * initial)
    (hterminalBudget :
      (16 * amortizedStopThreshold h Dstar) *
          (2 * Rbar.card * ell) ≤
        (7 * initial) * (16 * q ^ 4))
    (hg : 2 ≤ g)
    (hlen : 2 * g ≤ ell)
    (hreserve : 0 < reserve)
    (hscaledWidth :
      20000 * (reserve * g ^ 2) ≤ q ^ 2) :
    ContainsGridMinor H g := by
  obtain ⟨Pweak⟩ :=
    Result.weakPathOfSetsSystem
      hintersects hq hpow hh hDstar hEll
      hNlower hNupper hproductiveBudget hterminalBudget
  exact
    gridMinor_of_weakPathOfSetsSystem_of_cleanMatchingDichotomy
      hD Pweak hdegree hg hlen hreserve hscaledWidth

end AmortizedSlicingDichotomy

end Exponent7
end SimpleGraph

end Lax17Proofs
