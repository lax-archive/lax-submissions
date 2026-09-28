import Lax235315Proofs.Construction.AdaptiveStateProtocol
import Lax235315Proofs.Construction.PositionFailureBits

/-! Graph-dependent adaptive queries. The active sets may depend on every
earlier observed block; each newly selected query still has the same local
bad-block bound. -/

namespace Lax235315Proofs.Construction.GraphAdaptiveProtocol

open Lax235315Proofs.Construction.AdaptiveBitBlocks
open Lax235315Proofs.Construction.AdaptiveTapeCounting
open Lax235315Proofs.Construction.AdaptiveStateProtocol
open Lax235315Proofs.Construction.PositionFailureBits
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

set_option maxHeartbeats 800000

structure GraphQueryState (n : ℕ) where
  activeA : ℕ → ℕ
  activeB : ℕ → ℕ
  nonemptyA : (activeFinset (n := n) activeA).Nonempty

def queryWidth (n L : ℕ) (s : GraphQueryState n) : ℕ :=
  ((activeVertices n s.activeA).card * 8) * L

def badBlock {n : ℕ} (G : SimpleGraph (Fin n)) (c L : ℕ)
    (hL : 0 < L) (s : GraphQueryState n) :
    Finset (Tape (queryWidth n L s)) :=
  let A := activeFinset (n := n) s.activeA
  let B := activeFinset (n := n) s.activeB
  let bad := familyBadSamples (traceFamily G A B) id A c L
  badRoundBits (activeVertices n s.activeA).card L
    (sampleSize A.card c) hL (badPositionSamples s.activeA n bad)

/-- The per-round paper bound remains valid for arbitrary adaptive choices
of subsequent active sets, provided they satisfy the graph-state invariant. -/
lemma locallyBounded_graph_queries {n c L : ℕ}
    {G : SimpleGraph (Fin n)}
    (hc : 1 ≤ c)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hNpow : n ≤ 2 ^ L) (hL : 0 < L)
    (next : ∀ s : GraphQueryState n, Tape (queryWidth n L s) → GraphQueryState n) :
    ∀ R s, LocallyBounded
      (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n)
      (protocol (queryWidth n L) (badBlock G c L hL) next R s) := by
  apply AdaptiveStateProtocol.locallyBounded
    (width := queryWidth n L) (bad := badBlock G c L hL) (next := next)
  intro s
  simpa [queryWidth, badBlock] using
    (badRoundBits_fraction_le s.activeA s.activeB hc s.nonemptyA hG hNpow hL)

end

end Lax235315Proofs.Construction.GraphAdaptiveProtocol
