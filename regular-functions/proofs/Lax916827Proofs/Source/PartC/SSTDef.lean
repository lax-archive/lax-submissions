/-
Streaming string transducers (Definition `def:sst` of *Transducers*,
M. Bojańczyk) and their semantics.

These definitions were originally stated in `RequestProject/PartC/Statements.lean`; they have been
moved here, unchanged, so that the constructions used in the proof of Theorem
`theorem:sst-two-way-equivalence` can be developed before the statements of the numbered results.
`RequestProject/PartC/Statements.lean` imports this file, so the names `Transducers.Copyless`,
`Transducers.SST`, `Transducers.SST.subst`, `Transducers.SST.stepConfig`,
`Transducers.SST.runConfig`, `Transducers.SST.eval` and `Transducers.IsSST` are unchanged. -/
import Lax765601Proofs.Source.Common.Basic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- A register update is *copyless* if each register name occurs at most once in
the concatenation of the strings assigned to the registers. -/
def Copyless {X B : Type} [Fintype X] (u : X → List (X ⊕ B)) : Prop :=
  ((Finset.univ.toList.map u).flatten.filterMap
      (fun z => match z with | Sum.inl x => some x | Sum.inr _ => none)).Nodup

/-- **Definition `def:sst` (sst).**  A streaming string transducer. -/
structure SST (A B Q X : Type) [Fintype X] where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a new state and a register update. -/
  step : Q → A → Q × (X → List (X ⊕ B))
  /-- Register updates are copyless. -/
  step_copyless : ∀ q a, Copyless (step q a).2
  /-- The final output function. -/
  final : Q → List (X ⊕ B)

namespace SST

variable {A B Q X : Type} [Fintype X]

/-- Substituting the contents of the registers into a string over `X + B`. -/
def subst (η : X → List B) (s : List (X ⊕ B)) : List B :=
  (s.map (fun z => match z with | Sum.inl x => η x | Sum.inr b => [b])).flatten

/-- Reading one input letter. -/
def stepConfig (T : SST A B Q X) (c : Q × (X → List B)) (a : A) : Q × (X → List B) :=
  ((T.step c.1 a).1, fun x => subst c.2 ((T.step c.1 a).2 x))

/-- The configuration reached after reading an input string. -/
def runConfig (T : SST A B Q X) (w : List A) : Q × (X → List B) :=
  w.foldl T.stepConfig (T.init, fun _ => [])

/-- The semantics of a streaming string transducer. -/
def eval (T : SST A B Q X) (w : List A) : List B :=
  subst (T.runConfig w).2 (T.final (T.runConfig w).1)

end SST

/-- A function computed by a streaming string transducer. -/
def IsSST {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q X : Type) (_ : Finite Q) (instX : Fintype X) (T : @SST A B Q X instX), T.eval = f

end Lax916827Proofs.Transducers
