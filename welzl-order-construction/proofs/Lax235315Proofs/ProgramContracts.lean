import Lax235315Proofs.Construction.HistoryDriverSource
import Lax235315Proofs.ConstructionContracts
import Lax235315Proofs.Construction.SourceProbabilityBridge
import Lax235315Proofs.Construction.LiteralGoodDispatch

namespace Lax235315Proofs.ProgramContracts
open Lax235315Proofs.ConstructionContracts
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.HistoryDriverSource

/--
The fixed construction program halts within the claimed word-RAM budget on
every admissible tape, including rejected attempts.

# Proof strategy

Compose setup, the guarded adaptive loop and both final output branches at
source cost `6000 (|x|+1)(ceil(log₂ n)+1)`. Stored graph histories certify safe
reconstruction on accepted paths. The bounded compiler simulation transfers
the full execution to the fixed word-RAM program; `K ≥ 60001` covers its step
cost and workspace bounds. Empty and singleton inputs have separate complete
execution proofs.

# Attribution

The algorithm and asymptotic target are from Dreier and Kuske, arXiv:2602.14625v1.
The source semantics and word-RAM compiler are supplied by Lax808846.
-/
lemma eventually_hasRunningTimeBound :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → HasRunningTimeBound K := by
  refine ⟨60001, by omega, ?_⟩
  intro K hK
  exact runtime_of_source sourceTotal (by omega) (by omega)

/--
Every successful machine execution returns each vertex exactly once and
satisfies the paper's `12 c² ceil(log₂ n)²` crossing bound.

# Proof strategy

Carry the verifier's concrete partitions and the ordered deletion log through
each accepted source round. Replay the actual stored intervals into the
terminal active-vertex scan and apply the crossing induction. The final source
success test preserves this output guarantee. Source and machine determinism
transfer the result to every successful terminal machine state. The proof
uses no probability assumption.

# Attribution

The graph reduction and crossing argument follow Dreier and Kuske,
arXiv:2602.14625v1. Concrete source execution and compiler simulation are
formalized using the Lax808846 word-RAM framework.
-/
lemma eventually_hasCorrectOutput :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → HasCorrectOutput K := by
  refine ⟨60001, by omega, ?_⟩
  intro K hK
  exact correctness_of_source sourceTotal sourceCorrect (by omega) (by omega)

/--
At least two thirds of the finite random tapes make the explicit construction
program terminate successfully.

# Proof strategy

For each adaptive source round, interpret its exact fresh Boolean block as
the literal random-key input. A block outside the graph-dependent bad set
produces a collision-free good sample, so the literal verifier accepts and
the stored reduction history advances. The finite adaptive protocol counts
the bad blocks with a per-round conditional bound; its bit potential fits
within the machine tape. Good paths are coupled to actual source executions,
including the guarded prefix, every reduction round, and terminal output.
The source compiler transfer yields the claimed word-RAM tape count. Empty,
singleton, and initial no-round inputs are handled separately.

# Attribution

The sampling and contraction argument follows Dreier and Kuske,
arXiv:2602.14625v1. The explicit source and word-RAM semantics use
Lax808846.
-/
lemma eventually_hasSuccessProbability :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → HasSuccessProbability K := by
  apply Lax235315Proofs.Construction.SourceProbabilityBridge.eventually_hasSuccessProbability_of_accepted
  intro c n x G hx hG hc s bits hbits
  exact (Lax235315Proofs.Construction.LiteralGoodDispatch.source_good_block_accepted
    hx hG hc s bits hbits).1

end Lax235315Proofs.ProgramContracts
