import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3BalancedCut

namespace Lax17Proofs

universe u v w

/-!
# A concrete quarter-balanced cut candidate

Minimum quarter-balanced cuts are selected from an explicit candidate.  In the
nontrivial regime used by Lemma 7.5, a half-sized subset of the terminal set is
such a candidate.  Keeping this construction separate leaves the singleton
case visible to callers.
-/

namespace SimpleGraph
namespace AppendixA3BalancedCut


variable {V : Type u} [DecidableEq V]

/-- A terminal set of cardinality at least two admits a quarter-balanced
one-sided cut inside every containing set. -/
theorem exists_quarterBalanced_of_two_le_card
    {S Gamma : Finset V} (hGammaS : Gamma ⊆ S)
    (hcard : 2 ≤ Gamma.card) :
    ∃ A : Finset V, QuarterBalanced S Gamma A := by
  classical
  have hhalf_le : Gamma.card / 2 ≤ Gamma.card :=
    Nat.div_le_self Gamma.card 2
  rcases Finset.exists_subset_card_eq hhalf_le with
    ⟨A, hAGamma, hAcard⟩
  refine ⟨A, ?_⟩
  have hAinter : A ∩ Gamma = A := Finset.inter_eq_left.mpr hAGamma
  have hcomplement : (S \ A) ∩ Gamma = Gamma \ A := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_inter.mp hv with ⟨hvSdiff, hvGamma⟩
      exact Finset.mem_sdiff.mpr
        ⟨hvGamma, (Finset.mem_sdiff.mp hvSdiff).2⟩
    · intro hv
      rcases Finset.mem_sdiff.mp hv with ⟨hvGamma, hvA⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hGammaS hvGamma, hvA⟩, hvGamma⟩
  refine ⟨hAGamma.trans hGammaS, ?_, ?_⟩
  · rw [hAinter, hAcard]
    omega
  · rw [hcomplement, Finset.card_sdiff, hAinter, hAcard]
    omega

/-- Consequently, a minimum quarter-balanced edge cut exists in the same
nontrivial cardinality regime. -/
theorem exists_minimumQuarterBalancedEdgeCut_of_two_le_card
    {G : _root_.SimpleGraph V} [Fintype V]
    {S Gamma : Finset V} (hGammaS : Gamma ⊆ S)
    (hcard : 2 ≤ Gamma.card) :
    ∃ A : Finset V, IsMinimumQuarterBalancedEdgeCut G S Gamma A := by
  rcases exists_quarterBalanced_of_two_le_card hGammaS hcard with ⟨A, hA⟩
  exact exists_minimumQuarterBalancedEdgeCut (G := G) hA

end AppendixA3BalancedCut
end SimpleGraph

end Lax17Proofs
