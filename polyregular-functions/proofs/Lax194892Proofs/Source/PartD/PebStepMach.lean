/-
**One step of a pebble transducer, as a reachability question.**

Lemma `lem:reachability-pebble-automaton` (`Transducers.reachability_pebble_automaton`) says that
reachability between two configurations of a pebble transducer is a regular property of the string
representation of the pair.  The proofs of Section D.2 also need *single steps* to be such a
property.  Rather than repeating the analysis of the transition function, this file observes that a
single step of `M` is reachability in the machine `Transducers.Pebble.stepMach M`, which performs
one step of `M` and then dies: the reachability result then applies verbatim.
-/
import Lax194892Proofs.Source.PartD.PebReach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace Pebble

variable {A B Q : Type} {k : ℕ}

/-- **The machine that performs one step of `M` and then dies.**  The Boolean component of the
state records whether the step has been made; once it has, the machine terminates, and terminating
leaves the configuration graph, so that no further configuration is reachable. -/
def stepMach (M : Pebble A B Q k) : Pebble A B (Q × Bool) k where
  init := (M.init, false)
  step := fun p v =>
    if p.2 then (p, PebbleAction.terminate)
    else (((M.step p.1 v).1, true), (M.step p.1 v).2)

/-- The lifting of a configuration of `M` to a configuration of `stepMach M` after the step. -/
def liftCfg : PebbleCfg Q → PebbleCfg (Q × Bool)
  | PebbleCfg.conf q st => PebbleCfg.conf (q, true) st
  | PebbleCfg.halt => PebbleCfg.halt

variable {M : Pebble A B Q k} {w : List A}

/-- Before the step, `stepMach M` does exactly what `M` does. -/
lemma stepCfg_stepMach_false (q : Q) (st : List ℕ) :
    (stepMach M).stepCfg w (PebbleCfg.conf (q, false) st)
      = (M.stepCfg w (PebbleCfg.conf q st)).map (fun r => (r.1, liftCfg r.2)) := by
  have hstep : (stepMach M).step (q, false) (viewOf w st)
      = (((M.step q (viewOf w st)).1, true), (M.step q (viewOf w st)).2) := rfl
  simp only [stepCfg, hstep]
  cases hact : (M.step q (viewOf w st)).2 with
  | out b => simp [liftCfg]
  | move d =>
      cases hgl : st.getLast? with
      | none => simp [liftCfg]
      | some p =>
          cases d with
          | true => by_cases hp : p < w.length <;> simp [hp, liftCfg]
          | false => by_cases hp : 0 < p <;> simp [hp, liftCfg]
  | push => by_cases hst : st.length < k <;> simp [hst, liftCfg]
  | pop => by_cases hst : st = [] <;> simp [hst, liftCfg]
  | terminate => simp [liftCfg]

/-- After the step, `stepMach M` terminates. -/
lemma stepCfg_stepMach_true (q : Q) (st : List ℕ) :
    (stepMach M).stepCfg w (PebbleCfg.conf (q, true) st) = some ([], PebbleCfg.halt) := by
  have hstep : (stepMach M).step (q, true) (viewOf w st) = ((q, true), PebbleAction.terminate) :=
    rfl
  simp [stepCfg, hstep]

/-- Nothing is reachable from the halting vertex. -/
lemma restrReaches_halt {Q' : Type} {M' : Pebble A B Q' k} {ℓ : ℕ} {c : PebbleCfg Q'}
    (h : M'.RestrReaches w ℓ PebbleCfg.halt c) : False := by
  cases h

/-- **Inversion for `RestrReaches`**: a run is either empty, or it begins with a step. -/
lemma restrReaches_cases {Q' : Type} {M' : Pebble A B Q' k} {ℓ : ℕ} {c d : PebbleCfg Q'}
    (h : M'.RestrReaches w ℓ c d) :
    c = d ∨ ∃ o c', M'.stepCfg w c = some (o, c') ∧ M'.RestrReaches w ℓ c' d := by
  cases h with
  | refl q st hq => exact Or.inl rfl
  | step hp hs hr => exact Or.inr ⟨_, _, hs, hr⟩

/-- After the step, `stepMach M` goes nowhere. -/
lemma restrReaches_true_eq {q₁ : Q} {st₁ : List ℕ} {c : PebbleCfg (Q × Bool)}
    (h : (stepMach M).RestrReaches w 0 (PebbleCfg.conf (q₁, true) st₁) c) :
    c = PebbleCfg.conf (q₁, true) st₁ := by
  rcases restrReaches_cases h with h₀ | ⟨o, c', hs, hr⟩
  · exact h₀.symm
  · rw [stepCfg_stepMach_true] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact (restrReaches_halt hr).elim

/-- **A single step of `M` is reachability in `stepMach M`.** -/
theorem restrReaches_stepMach_iff (q q' : Q) (st st' : List ℕ) :
    (stepMach M).RestrReaches w 0 (PebbleCfg.conf (q, false) st) (PebbleCfg.conf (q', true) st')
      ↔ ∃ o, M.stepCfg w (PebbleCfg.conf q st) = some (o, PebbleCfg.conf q' st') := by
  constructor
  · intro h
    rcases restrReaches_cases h with h₀ | ⟨o, c', hs, hr⟩
    · exact absurd h₀ (by simp)
    · rw [stepCfg_stepMach_false] at hs
      rcases hm : M.stepCfg w (PebbleCfg.conf q st) with _ | ⟨o₀, c₀⟩
      · rw [hm] at hs; simp at hs
      · rw [hm] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨-, rfl⟩ := hs
        cases c₀ with
        | halt =>
            simp only [liftCfg] at hr
            exact (restrReaches_halt hr).elim
        | conf q₁ st₁ =>
            simp only [liftCfg] at hr
            have := restrReaches_true_eq (M := M) (w := w) (q₁ := q₁) (st₁ := st₁) hr
            rw [PebbleCfg.conf.injEq] at this
            obtain ⟨h1, h2⟩ := this
            refine ⟨o₀, ?_⟩
            have hq : q' = q₁ := congrArg Prod.fst h1
            rw [hq, h2]
  · rintro ⟨o, ho⟩
    refine RestrReaches.step (o := o) (Nat.zero_le _) ?_ (RestrReaches.refl _ _ (Nat.zero_le _))
    rw [stepCfg_stepMach_false, ho]
    rfl

end Pebble

end Lax194892Proofs.Transducers
