/-
The product of a pebble transducer with a deterministic automaton for the target language.

This is the first step of the book's proof of Theorem `thm:pebble-are-continuous`: running a
deterministic automaton on the output of a pebble transducer turns the transducer into a pebble
*automaton*, so that the theorem reduces to the fact that pebble automata recognise regular
languages.
-/
import Lax194892Proofs.Source.PartD.PebbleAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace Pebble

variable {A B Q : Type} {k : ℕ}

/-- A run that ends in a configuration with no outgoing step has a unique output. -/
lemma reaches_unique_of_stuck {M : Pebble A B Q k} {w : List A} :
    ∀ {c c'' : PebbleCfg Q} {v : List B}, M.Reaches w c v c'' →
      ∀ {v' : List B}, M.Reaches w c v' c'' → M.stepCfg w c'' = none → v = v' := by
  intro c c'' v h
  induction h with
  | refl c =>
      intro v' h' hstuck
      cases h' with
      | refl _ => rfl
      | step hs _ => rw [hstuck] at hs; exact absurd hs (by simp)
  | step hs _ ih =>
      intro v' h' hstuck
      cases h' with
      | refl _ => rw [hstuck] at hs; exact absurd hs (by simp)
      | step hs' h2 =>
          rw [hs'] at hs
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some_injective _ hs
          rw [ih h2 hstuck]

/-- The output of a halting run is unique, because `stepCfg` is a partial function. -/
lemma reaches_halt_unique {M : Pebble A B Q k} {w : List A} {c : PebbleCfg Q} {v v' : List B}
    (h : M.Reaches w c v PebbleCfg.halt) (h' : M.Reaches w c v' PebbleCfg.halt) : v = v' :=
  reaches_unique_of_stuck h h' rfl

lemma computes_unique {M : Pebble A B Q k} {w : List A} {v v' : List B}
    (h : M.Computes w v) (h' : M.Computes w v') : v = v' :=
  reaches_halt_unique h h'

end Pebble

section Prod

variable {A B Q σ : Type} {k : ℕ}

open Classical in
/-- Acceptance of a state of a deterministic automaton, as a Boolean. -/
noncomputable def dfaAcc (D : DFA B σ) (s : σ) : Bool := decide (s ∈ D.accept)

lemma dfaAcc_eq_true {D : DFA B σ} {s : σ} : dfaAcc D s = true ↔ s ∈ D.accept := by
  classical
  simp [dfaAcc]

open Classical in
/-- The pebble automaton obtained by feeding the output of a pebble transducer to a deterministic
automaton for the target language. -/
noncomputable def prodAut (M : Pebble A B Q k) (D : DFA B σ) : PebbleAut A (Q × σ) Bool k where
  step := fun qs v =>
    match (M.step qs.1 v).2 with
    | PebbleAction.out b => (((M.step qs.1 v).1, D.step qs.2 b), PebAutAction.stay)
    | PebbleAction.move d => (((M.step qs.1 v).1, qs.2), PebAutAction.move d)
    | PebbleAction.push => (((M.step qs.1 v).1, qs.2), PebAutAction.push)
    | PebbleAction.pop => (((M.step qs.1 v).1, qs.2), PebAutAction.pop)
    | PebbleAction.terminate =>
        (((M.step qs.1 v).1, qs.2), PebAutAction.halt (dfaAcc D qs.2))

/-- The configuration of the product automaton associated with a configuration of the transducer
and a state of the automaton for the target language. -/
noncomputable def prodCfg (D : DFA B σ) (s : σ) : PebbleCfg Q → PebAutCfg (Q × σ) Bool
  | PebbleCfg.conf q st => Sum.inl ((q, s), st)
  | PebbleCfg.halt => Sum.inr (some (dfaAcc D s))

variable (M : Pebble A B Q k) (D : DFA B σ)

/-- One step of the product automaton is one step of the transducer, with the automaton for the
target language run on the letters that are output. -/
lemma prodAut_next (w : List A) (q : Q) (st : List ℕ) (s : σ) :
    (prodAut M D).next w (prodCfg D s (PebbleCfg.conf q st))
      = (M.stepCfg w (PebbleCfg.conf q st)).elim (Sum.inr none)
          (fun p => prodCfg D (D.evalFrom s p.1) p.2) := by
  cases hact : (M.step q (viewOf w st)).2 with
  | out b =>
      simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact, DFA.evalFrom]
  | terminate =>
      simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact]
  | push =>
      by_cases hlt : st.length < k <;>
        simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact, hlt]
  | pop =>
      by_cases hnil : st = []
      · subst hnil
        simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact]
      · simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact, hnil]
  | move d =>
      cases hlast : st.getLast? with
      | none => simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact, hlast]
      | some x =>
          cases d with
          | false =>
              by_cases hx : 0 < x <;>
                simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact, hlast, hx]
          | true =>
              by_cases hx : x < w.length <;>
                simp [PebbleAut.next, prodAut, prodCfg, Pebble.stepCfg, hact, hlast, hx]

lemma prodAut_next_of_step {w : List A} {c c' : PebbleCfg Q} {v : List B}
    (s : σ) (h : M.stepCfg w c = some (v, c')) :
    (prodAut M D).next w (prodCfg D s c) = prodCfg D (D.evalFrom s v) c' := by
  cases c with
  | halt => simp [Pebble.stepCfg] at h
  | conf q st => rw [prodAut_next, h]; rfl

lemma prodAut_next_of_stuck {w : List A} {q : Q} {st : List ℕ} (s : σ)
    (h : M.stepCfg w (PebbleCfg.conf q st) = none) :
    (prodAut M D).next w (prodCfg D s (PebbleCfg.conf q st)) = Sum.inr none := by
  rw [prodAut_next, h]
  rfl

/-- A halting run of the transducer gives an answering run of the product automaton. -/
lemma prodAut_answers_of_reaches {w : List A} :
    ∀ {c c'' : PebbleCfg Q} {v : List B}, M.Reaches w c v c'' → c'' = PebbleCfg.halt →
      ∀ s : σ, (prodAut M D).Answers w (prodCfg D s c) (dfaAcc D (D.evalFrom s v)) := by
  intro c c'' v h
  induction h with
  | refl c => rintro rfl s; exact ⟨0, rfl⟩
  | step hs _ ih =>
      intro hh s
      refine PebbleAut.answers_of_next ?_
      rw [prodAut_next_of_step M D s hs, DFA.evalFrom_of_append]
      exact ih hh _

/-- Conversely, an answering run of the product automaton comes from a halting run of the
transducer. -/
lemma prodAut_reaches_of_answers {w : List A} :
    ∀ (n : ℕ) (q : Q) (st : List ℕ) (s : σ) (b : Bool),
      ((prodAut M D).next w)^[n] (prodCfg D s (PebbleCfg.conf q st)) = Sum.inr (some b) →
        ∃ v, M.Reaches w (PebbleCfg.conf q st) v PebbleCfg.halt ∧
          b = dfaAcc D (D.evalFrom s v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro q st s b hn
      cases n with
      | zero => simp [prodCfg] at hn
      | succ n =>
          rw [Function.iterate_succ_apply] at hn
          cases hstep : M.stepCfg w (PebbleCfg.conf q st) with
          | none =>
              rw [prodAut_next_of_stuck M D s hstep, PebbleAut.iterate_next_inr] at hn
              simp at hn
          | some p =>
              obtain ⟨v, c'⟩ := p
              rw [prodAut_next_of_step M D s hstep] at hn
              cases c' with
              | halt =>
                  simp only [prodCfg, PebbleAut.iterate_next_inr, Sum.inr.injEq,
                    Option.some.injEq] at hn
                  exact ⟨v, by simpa using Pebble.Reaches.step hstep (Pebble.Reaches.refl _), hn.symm⟩
              | conf q' st' =>
                  obtain ⟨v', hv', hb⟩ := ih n (by omega) q' st' _ b hn
                  exact ⟨v ++ v', Pebble.Reaches.step hstep hv',
                    by rw [hb, DFA.evalFrom_of_append]⟩

end Prod

end Lax194892Proofs.Transducers
