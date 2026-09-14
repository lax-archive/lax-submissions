/-
Part D: pebble transducers -- the definitions.

The syntax and the semantics of pebble transducers were originally stated in
`RequestProject/PartD/Statements.lean`; they have been moved here, unchanged, so that the
constructions proving Theorem `thm:pebble-are-continuous` can be developed before the statements.
-/
import Lax916827Proofs.Source.PartC.Statements
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-- The information available to a pebble transducer: for every pebble on the
stack (listed from the bottom), the two adjacent input letters and the set of
pebbles that are in the same place. -/
abbrev PebbleView (A : Type) := List ((Option A × Option A) × List Bool)

/-- The view of the input string from a stack of pebbles, which are gaps of the
input string (listed from the bottom of the stack). -/
def viewOf {A : Type} (w : List A) (st : List ℕ) : PebbleView A :=
  st.map (fun p => ((if p = 0 then none else w[p - 1]?, w[p]?),
    st.map (fun q => decide (q = p))))

/-- The actions of a pebble transducer. -/
inductive PebbleAction (B : Type) : Type
  /-- Output a letter. -/
  | out : B → PebbleAction B
  /-- Move the head one position to the right (`true`) or left (`false`). -/
  | move : Bool → PebbleAction B
  /-- Push the first input position onto the pebble stack. -/
  | push : PebbleAction B
  /-- Pop the topmost pebble. -/
  | pop : PebbleAction B
  /-- Terminate. -/
  | terminate : PebbleAction B

/-- A `k`-pebble transducer: a deterministic machine with a stack of at most `k`
pebbles pointing to gaps of the input string.  (Only the finitely many views
that arise from stacks of height at most `k` are relevant for the transition
function.) -/
structure Pebble (A B Q : Type) (k : ℕ) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Q → PebbleView A → Q × PebbleAction B

/-- A configuration of a pebble transducer: the state and the stack of pebbles
(listed from the bottom), or the halting vertex. -/
inductive PebbleCfg (Q : Type) : Type
  | conf : Q → List ℕ → PebbleCfg Q
  | halt : PebbleCfg Q

namespace Pebble

variable {A B Q : Type} {k : ℕ}

/-- One step of the computation: the produced output and the next
configuration, if any.  The step is undefined if the head moves out of the input
string, if the stack bound is exceeded, or if a pebble is popped from an empty
stack. -/
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

/-- Reachability in the configuration graph, recording the produced output. -/
inductive Reaches (M : Pebble A B Q k) (w : List A) :
    PebbleCfg Q → List B → PebbleCfg Q → Prop
  | refl (c : PebbleCfg Q) : Reaches M w c [] c
  | step {c c' c'' : PebbleCfg Q} {o o' : List B} :
      M.stepCfg w c = some (o, c') → Reaches M w c' o' c'' → Reaches M w c (o ++ o') c''

/-- The transducer produces the output `v` on the input `w`. -/
def Computes (M : Pebble A B Q k) (w : List A) (v : List B) : Prop :=
  M.Reaches w (PebbleCfg.conf M.init []) v PebbleCfg.halt

end Pebble

/-- A (total) function computed by a pebble transducer. -/
def IsPebbleTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (M : Pebble A B Q k), ∀ w, M.Computes w (f w)

end Lax194892Proofs.Transducers
