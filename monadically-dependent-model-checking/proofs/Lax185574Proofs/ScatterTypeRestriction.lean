import Lax185574.ScatterTypeRestriction

/-!
Proof that the scatter type of rank `(k+1, q)` is the restriction of the
scatter type of rank `(k, q+1)`, following the proof of obs:stp-restrict.
-/

namespace Lax185574Proofs.ScatterTypeRestriction

open Lax185574.PartialGraphs Lax185574.ScatterTypes

/--
---
conclusion: Lax185574.ScatterTypeRestriction.stp_restrict
---
Level `i` of the domain `D_{k+1,q}` is level `i + 1` of `D_{k,q+1}`, since
the ranks and the radius bounds coincide. The values agree because the
caps `(k+1) + q` and `k + (q+1)` coincide and both use the same greedy
scattered set.
-/
theorem stp_restrict {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) :
    domain G (k + 1) q ⊆ domain G k (q + 1) ∧
      ∀ p ∈ domain G (k + 1) q, value G (k + 1) q p = value G k (q + 1) p := by
  refine ⟨?_, fun p _ => ?_⟩
  · rintro p ⟨i, b, hi1, hiq, hr1, hr, hp⟩
    refine ⟨i + 1, b, by omega, by omega, hr1, ?_, ?_⟩
    · rwa [show k + (i + 1) = k + 1 + i by omega, show q + 1 - (i + 1) = q - i by omega]
    · rwa [show k + (i + 1) = k + 1 + i by omega, show q + 1 - (i + 1) = q - i by omega]
  · simp only [value, show k + 1 + q = k + (q + 1) by omega]

end Lax185574Proofs.ScatterTypeRestriction
