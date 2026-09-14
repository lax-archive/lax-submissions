import Mathlib.Computability.DFA
import Lax194892.PebbleConfigurationEncoding

/-!
---
title: Balanced runs between configurations are regular
type: theorem
---
For every height $\ell \in \{1, \ldots, k\}$, the existence of a *balanced
run* between two configurations $(x, y_1)$ and $(x, y_2)$ of height $\ell$ —
sharing the stack $x$ of the lower $\ell - 1$ pebbles, with $y_i$ the state
and the position of the top pebble — is mso-definable (Claim D.2.3 of
*Transducers*): during a balanced run the pebble at height $\ell$ is never
popped, although it may be moved.

# Formalization notes

As for Lemma D.2.2, the mso formula is replaced by a regular language of
encodings of the pair of configurations, correct on genuine encodings; the two
stacks are `x ++ [p₁]` and `x ++ [p₂]` with `x` of length `ℓ - 1`.
-/

namespace Lax194892.BalancedRunReachability

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

/-- The encodings of pairs of configurations of height `ℓ` connected by a balanced
run form a regular language. -/
axiom exists_regular_balancedLang {A B Q : Type} {k : ℕ} [Finite A] [Finite Q]
    (M : Pebble A B Q k) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    ∃ L : Language (PairLetter A Q k), L.IsRegular ∧
      ∀ (q₁ q₂ : Q) (x : List ℕ) (p₁ p₂ : ℕ) (w : List A),
        (∀ p ∈ x, p ≤ w.length) → p₁ ≤ w.length → p₂ ≤ w.length → x.length = ℓ - 1 →
        (pairEnc q₁ q₂ (x ++ [p₁]) (x ++ [p₂]) w ∈ L ↔
          BalancedRun M w ℓ (PebbleCfg.conf q₁ (x ++ [p₁])) (PebbleCfg.conf q₂ (x ++ [p₂])))

end Lax194892.BalancedRunReachability
