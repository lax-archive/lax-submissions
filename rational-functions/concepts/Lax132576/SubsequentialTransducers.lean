import Lax765601.StateTransformations
import Lax132576.SequentialTransducers

/-!
---
title: Subsequential transducers
type: definition
---
A *subsequential transducer* (Section B.4.3 of *Transducers*) is a sequential
transducer equipped with a partial *end-of-input* function, which is applied to
the state reached after the whole input has been read: its value, if defined,
is appended to the output, and if it is undefined the transducer has no output.
Subsequential transducers therefore compute *partial* functions; they can, for
instance, append a letter to their input, which a sequential transducer cannot,
and a function that is undefined on some inputs can be computed. Theorem B.4.8
characterises the subsequential functions.

# Formalization notes

A partial function is a function into `Option (List B)`. The end-of-input
function is `Q → Option (List B)`; the semantics is the output of the
sequential part followed by the end-of-input value at the state reached, when
that value is defined. `IsSubsequential f` asks for a finite state space.
-/

namespace Lax132576.SubsequentialTransducers

open Lax765601.StateTransformations Lax132576.SequentialTransducers

/-- A subsequential transducer: a sequential transducer with a partial end-of-input
function applied to the last state of the run. -/
structure Subsequential (A B Q : Type) extends Sequential A B Q where
  /-- The partial end-of-input function. -/
  endOfInput : Q → Option (List B)

namespace Subsequential

variable {A B Q : Type}

/-- The semantics of a subsequential transducer: the output of the sequential
part followed by the end-of-input value, when defined. -/
def eval (T : Subsequential A B Q) (w : List A) : Option (List B) :=
  (T.endOfInput (strTrans T.toSequential.transFun w T.toSequential.init)).map
    (fun u => T.toSequential.eval w ++ u)

end Subsequential

/-- A partial function computed by a subsequential transducer with a finite state
space. -/
def IsSubsequential {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Subsequential A B Q), T.eval = f

end Lax132576.SubsequentialTransducers
