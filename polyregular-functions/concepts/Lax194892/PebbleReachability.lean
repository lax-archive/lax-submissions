import Mathlib.Computability.DFA
import Lax194892.PebbleConfigurationEncoding

/-!
---
title: Reachability between configurations of a pebble transducer is regular
type: theorem
---
Reachability between two configurations of a $k$-pebble transducer is
definable: there is an mso formula $\varphi(s, t)$ over configurations which
holds if some run begins in $s$ and ends in $t$ (Lemma D.2.2 of
*Transducers*). Reachability is reduced, by induction on the height, to
reachability between configurations that share their lower pebbles, which is
checked by a pebble automaton with one pebble more.

# Formalization notes

The book asks for an mso formula whose two free variables range over
configurations. Here the pair of configurations is encoded into the input
string (`pairEnc`, one letter per gap) and the conclusion is that the set of
encodings of reachable pairs is a *regular language* — equivalently, by Büchi's
theorem, an mso-definable one. Since a formula is only ever evaluated on a
genuine structure, the language is only required to be correct on genuine
encodings: stacks of at most `k` gaps of the input. Stated for pebble
transducers rather than pebble automata, which have the same configuration
graph.
-/

namespace Lax194892.PebbleReachability

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

/-- The encodings of pairs of configurations connected by a run form a regular
language. -/
axiom exists_regular_reachLang {A B Q : Type} {k : ℕ} [Finite A] [Finite Q] (M : Pebble A B Q k) :
    ∃ L : Language (PairLetter A Q k), L.IsRegular ∧
      ∀ (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A),
        (∀ p ∈ sts, p ≤ w.length) → (∀ p ∈ stt, p ≤ w.length) →
        sts.length ≤ k → stt.length ≤ k →
        (pairEnc q₁ q₂ sts stt w ∈ L ↔
          ∃ v, M.Reaches w (PebbleCfg.conf q₁ sts) v (PebbleCfg.conf q₂ stt))

end Lax194892.PebbleReachability
