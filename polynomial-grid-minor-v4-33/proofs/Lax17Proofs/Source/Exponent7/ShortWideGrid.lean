import Lax17Proofs.Source.Exponent7.AlternatingMatchingGrid
import Lax17Proofs.Source.Section4Assembly

namespace Lax17Proofs

/-!
# Short-wide weak path-of-sets systems

Section 4.6 strongification is combined with the prescribed-matching grid
construction under the hypothesis
`CleanMatchingDichotomyStatement reserve`. The strongification loses a factor
of `20000` in width.
-/

namespace SimpleGraph
namespace Exponent7

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A sufficiently wide weak path-of-sets system contains a grid, conditional
only on the clean prescribed-matching dichotomy.

The weak system keeps its length during strongification.  Its width loses at
most the explicit factor `20000`. -/
theorem gridMinor_of_weakPathOfSetsSystem_of_cleanMatchingDichotomy
    {ell w g reserve : ℕ}
    (hD : CleanMatchingDichotomyStatement.{u} reserve)
    (P : WeakPathOfSetsSystem G ell w)
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hlen : 2 * g ≤ ell)
    (hreserve : 0 < reserve)
    (hwidth : 20000 * (reserve * g ^ 2) ≤ w) :
    ContainsGridMinor G g := by
  let D :=
    Section4Assembly.strongificationData_of_weakPathOfSetsSystem_maxDegreeFour
      P hdegree
  let Pstrong :
      StrongPathOfSetsSystem G ell
        (Section4Assembly.strongifiedWidth w) :=
    Section46.strong_pathOfSetsSystem_of_strongificationData P D
  have hretained :
      reserve * g ^ 2 ≤
        Section4Assembly.strongifiedWidth w := by
    apply Nat.le_of_mul_le_mul_left
      (hwidth.trans (Section4Assembly.strongification_width_bound P))
      (by norm_num : 0 < 20000)
  have hgw :
      g ≤ Section4Assembly.strongifiedWidth w := by
    have hr : 1 ≤ reserve := by omega
    have hgg : g ≤ g ^ 2 := by nlinarith
    exact hgg.trans <|
      calc
        g ^ 2 = 1 * g ^ 2 := by simp
        _ ≤ reserve * g ^ 2 := Nat.mul_le_mul_right (g ^ 2) hr
        _ ≤ Section4Assembly.strongifiedWidth w := hretained
  exact shortWideGrid_of_cleanMatchingDichotomy
    hD Pstrong hg hlen hgw hretained

end Exponent7
end SimpleGraph

end Lax17Proofs
