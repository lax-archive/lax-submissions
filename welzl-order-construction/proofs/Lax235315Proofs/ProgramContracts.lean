import Lax235315Proofs.Construction.HistoryDriverSource
import Lax235315.ConstructionRuntime
import Lax235315.ConstructionCorrectness

namespace Lax235315Proofs.ProgramContracts
open Lax235315.ConstructionContracts
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.HistoryDriverSource

/--
---
conclusion: Lax235315.ConstructionRuntime.eventually_hasRunningTimeBound
---
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
---
conclusion: Lax235315.ConstructionCorrectness.eventually_hasCorrectOutput
---
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

end Lax235315Proofs.ProgramContracts
