import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic

/-!
---
title: Pebble transducers
type: definition
---
A *pebble transducer* (Section D.2 of *Transducers*) extends a two-way
transducer by a stack of at most $k$ *pebbles* pointing to gaps of the input
string; the topmost pebble is the *head*, and only it can be moved. The
transducer has a finite set of states with an initial state; it looks at its
state and, for every pebble on the stack, at the two input letters adjacent to
it and the set of pebbles in the same place, and deterministically chooses a
new state and an *action*: output a letter, move the head one position left or
right, push a new pebble at the first gap, pop the head, or terminate. It
computes $v$ on $w$ if the run from the initial state with an empty stack
terminates with output $v$. Pebble transducers compute exactly the functions of
for-transducers (Theorem D.2.4), hence the polyregular functions.

# Formalization notes

The information available to the transducer is its `PebbleView`: for each
pebble, from the bottom of the stack, the two adjacent letters and the Booleans
saying which pebbles share its place. A configuration is a state and the stack
of gaps, or the halting vertex; a step is undefined if the head would leave the
input, the stack bound would be exceeded, or an empty stack popped. `IsPebbleTransducer`
asks for some bound `k`, a finite state space and a transducer computing `f w`
on every `w`.
-/

namespace Lax194892.PebbleTransducers

/-- What a pebble transducer sees: for every pebble on the stack, from the
bottom, the two adjacent letters and the pebbles in the same place. -/
abbrev PebbleView (A : Type) := List ((Option A × Option A) × List Bool)

/-- The view of the input from a stack of gaps. -/
def viewOf {A : Type} (w : List A) (st : List ℕ) : PebbleView A :=
  st.map (fun p => ((if p = 0 then none else w[p - 1]?, w[p]?),
    st.map (fun q => decide (q = p))))

/-- The actions of a pebble transducer. -/
inductive PebbleAction (B : Type) : Type
  /-- Output a letter. -/
  | out : B → PebbleAction B
  /-- Move the head right (`true`) or left (`false`). -/
  | move : Bool → PebbleAction B
  /-- Push a new pebble at the first gap. -/
  | push : PebbleAction B
  /-- Pop the topmost pebble. -/
  | pop : PebbleAction B
  /-- Terminate. -/
  | terminate : PebbleAction B

/-- A `k`-pebble transducer: a deterministic machine with a stack of at most `k`
pebbles pointing to gaps of the input. -/
structure Pebble (A B Q : Type) (k : ℕ) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Q → PebbleView A → Q × PebbleAction B

/-- A configuration: the state and the stack of gaps (from the bottom), or the
halting vertex. -/
inductive PebbleCfg (Q : Type) : Type
  | conf : Q → List ℕ → PebbleCfg Q
  | halt : PebbleCfg Q

namespace Pebble

variable {A B Q : Type} {k : ℕ}

/-- One step: the produced output and the next configuration, undefined if the
head leaves the input, the stack bound is exceeded, or an empty stack is popped. -/
def stepCfg (M : Pebble A B Q k) (w : List A) : PebbleCfg Q → Option (List B × PebbleCfg Q)
  | PebbleCfg.halt => none
  | PebbleCfg.conf q st =>
      let r := M.step q (viewOf w st)
      match r.2 with
      | PebbleAction.out b => some ([b], PebbleCfg.conf r.1 st)
      | PebbleAction.terminate => some ([], PebbleCfg.halt)
      | PebbleAction.push =>
          if st.length < k then some ([], PebbleCfg.conf r.1 (st ++ [0])) else none
      | PebbleAction.pop =>
          if st = [] then none else some ([], PebbleCfg.conf r.1 st.dropLast)
      | PebbleAction.move dir =>
          match st.getLast? with
          | none => none
          | some p =>
              if dir then
                (if p < w.length then some ([], PebbleCfg.conf r.1 (st.dropLast ++ [p + 1]))
                 else none)
              else
                (if 0 < p then some ([], PebbleCfg.conf r.1 (st.dropLast ++ [p - 1]))
                 else none)

/-- Reachability in the configuration graph, recording the output. -/
inductive Reaches (M : Pebble A B Q k) (w : List A) :
    PebbleCfg Q → List B → PebbleCfg Q → Prop
  | refl (c : PebbleCfg Q) : Reaches M w c [] c
  | step {c c' c'' : PebbleCfg Q} {o o' : List B} :
      M.stepCfg w c = some (o, c') → Reaches M w c' o' c'' → Reaches M w c (o ++ o') c''

/-- The transducer produces `v` on `w`. -/
def Computes (M : Pebble A B Q k) (w : List A) (v : List B) : Prop :=
  M.Reaches w (PebbleCfg.conf M.init []) v PebbleCfg.halt

end Pebble

/-- A function computed by a pebble transducer with finitely many states, for some
bound on the number of pebbles. -/
def IsPebbleTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (M : Pebble A B Q k), ∀ w, M.Computes w (f w)

end Lax194892.PebbleTransducers
