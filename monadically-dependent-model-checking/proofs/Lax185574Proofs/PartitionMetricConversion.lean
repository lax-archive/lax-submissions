import Lax185574.PartitionMetricConversion
import Lax185574Proofs.Lib.PartitionMetricConversion
import Lax185574Proofs.FlipBridge

namespace Lax185574Proofs.PartitionMetricConversion

open Lax185574.Flips Lax185574.GraphBalls Lax185574.GaifmanGraph
open Lax185574Proofs.FlipBridge

universe u

/--
---
conclusion: Lax185574.PartitionMetricConversion.exists_refinement_flip
---
Bonnet et al., Lemma 8, for a
partition given by a labeling `V → Fin p`: a refined labeling with at
most `p · 2^p` labels and one toggle on it whose radius-`r` balls lie in
the radius-`6r` balls of the flip metric. Label the parts of `𝒫` by
`Fin |𝒫|`. The fibers of the refined labeling form the partition `𝒬`,
and flips for a labeling with a symmetric toggle are exactly the flips
for its fibers.
-/
theorem exists_refinement_flip {V : Type u} [Finite V] (G : SimpleGraph V)
    (P : Setoid V) :
    ∃ Q : Setoid V, Q ≤ P ∧
      Nat.card (Quotient Q) ≤ Nat.card (Quotient P) * 2 ^ Nat.card (Quotient P) ∧
      ∃ H : SimpleGraph V, IsFlip G Q H ∧
        ∀ (v : V) (r : ℕ), graphBall H r {v} ⊆ flipBall G P (6 * r) v := by
  have := Fintype.ofFinite V
  obtain ⟨q, refined, toggle, hsymm, hq, hrefine, hball⟩ :=
    Lax185574Proofs.Lib.PartitionMetricConversion.exists_refinement_flip G _ (labeling P)
  refine ⟨Setoid.ker refined, ?_, (card_quotient_ker_le refined).trans hq, _,
    isFlip_flip G refined toggle hsymm, ?_⟩
  · intro x y h
    have := hrefine x y h
    rw [← ker_labeling P]
    exact this
  · rintro v r u ⟨c, hc, hcu⟩
    rw [Set.mem_singleton_iff.mp hc] at hcu
    have := hball r v u hcu
    rw [partitionBall_eq_flipBall, ker_labeling] at this
    exact this

end Lax185574Proofs.PartitionMetricConversion
