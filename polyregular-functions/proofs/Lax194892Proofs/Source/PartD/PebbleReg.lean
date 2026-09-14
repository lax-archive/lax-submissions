/-
Pebble transducers compute continuous functions (Theorem `thm:pebble-are-continuous`).

The regularity of the languages of pebble automata is proved in
`RequestProject/PartD/PebbleLev1.lean` by induction on the number of pebbles; this file only puts
the pieces together: running a deterministic automaton for the target language on the output of
the transducer turns it into a pebble automaton.
-/
import Lax194892Proofs.Source.PartD.PebbleLev1
import Lax194892Proofs.Source.PartD.PebbleProd
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-- **Theorem `thm:pebble-are-continuous`** (the main step).  Pebble transducers compute
continuous functions. -/
theorem continuous_of_isPebbleTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsPebbleTransducer f) : Continuous f := by
  classical
  obtain ⟨k, Q, hQ, M, hM⟩ := hf
  haveI := hQ
  intro L hL
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  haveI : Finite (Q × σ) := inferInstance
  have hreg := pebbleAut_answers_isRegular k (prodAut M D) (M.init, D.start) true
  convert hreg using 1
  ext w
  constructor
  · intro hw
    have hacc : dfaAcc D (D.evalFrom D.start (f w)) = true := by
      rw [dfaAcc_eq_true]
      simpa [DFA.mem_accepts, DFA.eval] using hw
    have h := prodAut_answers_of_reaches M D (hM w) rfl D.start
    rw [hacc] at h
    exact h
  · rintro ⟨n, hn⟩
    obtain ⟨v, hv, hb⟩ := prodAut_reaches_of_answers M D n M.init [] D.start true hn
    obtain rfl : v = f w := Pebble.computes_unique hv (hM w)
    simpa [DFA.mem_accepts, DFA.eval] using dfaAcc_eq_true.1 hb.symm

end Lax194892Proofs.Transducers
