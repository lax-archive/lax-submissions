import Mathlib.Data.Finite.Defs

/-!
---
title: Two-way transducers
type: definition
---
A *two-way transducer* (Definition C.2.1 of *Transducers*) consists of a finite
input alphabet $A$, a finite output alphabet $B$, a finite set of states $Q$
with an initial state, and a transition function
$$(A + 1) \times Q \times (A + 1) \;\to\; B^* + (Q \times B^* \times \{-1, +1\})$$
which, on the letter to the left of the head, the current state and the letter
to the right of the head (each possibly missing, at the ends of the input),
either produces an output string and halts, or produces an output string,
changes state and moves the head left or right. The head sits in a *gap*
between two positions of the input; the run starts in the leftmost gap in the
initial state, and the transducer computes $v$ on $w$ if the run started there
halts with the concatenation of the produced outputs equal to $v$. Since the
transducer is deterministic, it computes at most one output on every input; a
function is computed by a two-way transducer if its graph is.

# Formalization notes

A configuration is the input split at the head, `Cfg.conf u q v` with `u` to
the left and `v` to the right, or the halting vertex. `stepCfg` is one step of
the machine, `none` when the head would leave the input; `Reaches` is
reachability in the configuration graph with the produced output recorded;
`Computes M w v` says that the run from the initial configuration halts with
output `v`. The run indexed by time, `cfgAt M w n` — `none` once it has halted or
got stuck — and the configurations it `Visits` are what the string
representation of the reachable configuration graph is built from.
`IsTwoWay f` asks for a finite state space and a transducer computing `f w` on
every `w`.
-/

namespace Lax916827.TwoWayTransducers

/-- A two-way transducer: on the letters adjacent to the head and the state, it
either produces an output string and halts (`Sum.inl`), or produces an output
string, changes state and moves the head left (`false`) or right (`true`). -/
structure TwoWay (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Option A → Q → Option A → List B ⊕ (Q × List B × Bool)

/-- A configuration: the input to the left of the head, the state, and the input
to the right of the head; or the halting vertex. -/
inductive Cfg (A Q : Type) : Type
  | conf : List A → Q → List A → Cfg A Q
  | halt : Cfg A Q

namespace TwoWay

variable {A B Q : Type}

/-- One step of the computation: the produced output and the next configuration,
if the head does not fall off the input. -/
def stepCfg (M : TwoWay A B Q) : Cfg A Q → Option (List B × Cfg A Q)
  | Cfg.halt => none
  | Cfg.conf u q v =>
      match M.step u.getLast? q v.head? with
      | Sum.inl o => some (o, Cfg.halt)
      | Sum.inr (q', o, true) =>
          match v with
          | [] => none
          | a :: v' => some (o, Cfg.conf (u ++ [a]) q' v')
      | Sum.inr (q', o, false) =>
          match u.getLast? with
          | none => none
          | some a => some (o, Cfg.conf u.dropLast q' (a :: v))

/-- Reachability in the configuration graph, recording the produced output. -/
inductive Reaches (M : TwoWay A B Q) : Cfg A Q → List B → Cfg A Q → Prop
  | refl (c : Cfg A Q) : Reaches M c [] c
  | step {c c' c'' : Cfg A Q} {o o' : List B} :
      M.stepCfg c = some (o, c') → Reaches M c' o' c'' → Reaches M c (o ++ o') c''

/-- The transducer produces the output `v` on the input `w`: the run from the
initial configuration reaches the halting vertex with output `v`. -/
def Computes (M : TwoWay A B Q) (w : List A) (v : List B) : Prop :=
  M.Reaches (Cfg.conf [] M.init w) v Cfg.halt

/-- The configuration of the run on `w` after `n` steps; `none` once the run has
halted or got stuck. -/
def cfgAt (M : TwoWay A B Q) (w : List A) : ℕ → Option (Cfg A Q)
  | 0 => some (Cfg.conf [] M.init w)
  | n + 1 => (cfgAt M w n).bind fun c => (M.stepCfg c).map Prod.snd

/-- A configuration lies on the run of `M` on `w`. -/
def Visits (M : TwoWay A B Q) (w : List A) (c : Cfg A Q) : Prop := ∃ n, cfgAt M w n = some c

end TwoWay

/-- A function computed by a two-way transducer with a finite state space. -/
def IsTwoWay {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : TwoWay A B Q), ∀ w, M.Computes w (f w)

end Lax916827.TwoWayTransducers
