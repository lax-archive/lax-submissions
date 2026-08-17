import Lax3Proofs.CoverDegree
import Lax3Proofs.RamAugment

/-!
# Rank-only transitive-fraternal chains

The materialized ordering phase stores every intermediate orientation as a
CSR.  Semantically that storage is unnecessary: the initial orientation is
determined by its elimination rank, and every later orientation is determined
by the preceding orientation and the next fraternity-elimination rank through
`RamAugment.augOr`.

This file packages that observation at exactly the `CoverDegree.AugChainData`
surface consumed by the cover theorem.  A future linear-resident ordering
engine therefore only has to produce the rank arrays and their elimination
certificates; the augmented graphs may remain implicit.
-/

namespace Lax3Proofs.Refine.OrderVirtualMath

open Lax3Proofs.Augmentation
open Lax3Proofs.RamElim

variable {n : ℕ}

/-- The augmentation chain represented by its successive elimination ranks.
Rank zero orients the input graph.  Rank `i + 1` orients the new fraternal
edges of round `i`. -/
noncomputable def rankChain (G : SimpleGraph (Fin n))
    (rank : ℕ → Fin n → ℕ) : ℕ → Orientation n
  | 0 => ElimCert.elimOr G (rank 0)
  | i + 1 => Lax3Proofs.RamAugment.augOr (rankChain G rank i) (rank (i + 1))

@[simp] theorem rankChain_zero (G : SimpleGraph (Fin n)) (rank : ℕ → Fin n → ℕ) :
    rankChain G rank 0 = ElimCert.elimOr G (rank 0) := rfl

@[simp] theorem rankChain_succ (G : SimpleGraph (Fin n)) (rank : ℕ → Fin n → ℕ)
    (i : ℕ) :
    rankChain G rank (i + 1) =
      Lax3Proofs.RamAugment.augOr (rankChain G rank i) (rank (i + 1)) := rfl

/-- Elimination certificates for the initial graph and each fraternity graph
turn a rank-only representation into an augmentation chain. -/
theorem rankChain_isAugChain {G : SimpleGraph (Fin n)} {rank : ℕ → Fin n → ℕ}
    {R d₀ : ℕ}
    (hzero : ElimCert G (rank 0) d₀)
    (hround : ∀ i < R, ∃ k,
      ElimCert (fratGraph (rankChain G rank i)) (rank (i + 1)) k) :
    IsAugChain G (rankChain G rank) R := by
  refine ⟨hzero.orients, fun i hi => ?_⟩
  obtain ⟨k, hcert⟩ := hround i hi
  simpa only [rankChain_succ] using
    Lax3Proofs.RamAugment.augStep_augOr (rankChain G rank i) hcert.inj

/-- The same per-round certificates give the greedy clause expected by the
cover-degree argument. -/
theorem rankChain_greedy {G : SimpleGraph (Fin n)} {rank : ℕ → Fin n → ℕ}
    {R : ℕ}
    (hround : ∀ i < R, ∃ k,
      ElimCert (fratGraph (rankChain G rank i)) (rank (i + 1)) k) :
    ∀ i < R, GreedyFratRound (rankChain G rank i) (rankChain G rank (i + 1)) := by
  intro i hi
  obtain ⟨k, hcert⟩ := hround i hi
  simpa only [rankChain_succ] using
    Lax3Proofs.RamAugment.greedyFratRound_augOr hcert

/-- A complete rank-only certificate supplies the existing ordering
postcondition without materializing a single augmented graph.

The final permutation is stated in the exact numeric-rank form used by
`CoverDegree.AugChainData`. -/
theorem augChainData_of_rankCerts {G : SimpleGraph (Fin n)}
    {rank : ℕ → Fin n → ℕ} {π : Equiv.Perm (Fin n)} {R d₀ k : ℕ}
    (hzero : ElimCert G (rank 0) d₀)
    (hround : ∀ i < R, ∃ ki,
      ElimCert (fratGraph (rankChain G rank i)) (rank (i + 1)) ki)
    (hfinal : ElimCert (rankChain G rank R).toGraph
      (fun v => ((π v : Fin n) : ℕ)) k) :
    Lax3Proofs.CoverDegree.AugChainData G (rankChain G rank) π R d₀ k := by
  refine ⟨rankChain_isAugChain hzero hround, rankChain_greedy hround,
    hzero.inDegLE, ?_, hfinal.backDegLE, ?_⟩
  · intro k' hk'
    exact hzero.le_of_lowDegreeVertices hk'
  · intro k' hk'
    exact hfinal.le_of_lowDegreeVertices hk'

end Lax3Proofs.Refine.OrderVirtualMath
