import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic

/-!
---
title: For-transducers
type: definition
---
A *for-transducer* (Section D.1 of *Transducers*) is an imperative program
with `for` loops ranging over the positions of the input string, in increasing
or decreasing order. It has position variables, bound by the loops and read
only, and Boolean variables, initially false and assignable; its tests compare
positions (`x == y`, `x <= y`), read the letter at a position (`w[x] == a`) and
read Boolean variables, with Boolean connectives; and its statements are
`output(b)`, assignment to a Boolean variable, sequential composition,
conditionals and loops. The output of a run is the concatenation of the output
letters produced. A for-transducer is in *prenex form* (Definition D.1.2) if it
is a block of nested loops whose body is loop-free and produces at most one
output letter per iteration, followed by a loop-free epilogue. For-transducers
compute exactly the polyregular functions (Theorem D.1.1).

# Formalization notes

Variables of both kinds are named by natural numbers; a valuation of the
position variables is `ℕ → ℕ` and of the Boolean variables `ℕ → Bool`. `exec`
runs a program from a valuation and returns the final Boolean valuation and the
output; `eval P w` is the output from the all-zero valuations. `loop true x P`
ranges over the positions in increasing order, `loop false x P` in decreasing
order.
-/

namespace Lax194892.ForTransducers

/-- Tests of a for-transducer. -/
inductive ForTest (A : Type) : Type
  /-- The value of a Boolean variable. -/
  | boolVar : ℕ → ForTest A
  /-- The equality test `x == y` on position variables. -/
  | eqPos : ℕ → ℕ → ForTest A
  /-- The order test `x <= y` on position variables. -/
  | lePos : ℕ → ℕ → ForTest A
  /-- The label test `w[x] == a`. -/
  | label : ℕ → A → ForTest A
  /-- Negation. -/
  | not : ForTest A → ForTest A
  /-- Conjunction. -/
  | and : ForTest A → ForTest A → ForTest A
  /-- Disjunction. -/
  | or : ForTest A → ForTest A → ForTest A

/-- Programs of a for-transducer. -/
inductive ForProg (A B : Type) : Type
  /-- The empty program. -/
  | skip : ForProg A B
  /-- `output(b)`. -/
  | output : B → ForProg A B
  /-- `X = true` / `X = false`. -/
  | assign : ℕ → Bool → ForProg A B
  /-- Sequential composition `I ; J`. -/
  | seq : ForProg A B → ForProg A B → ForProg A B
  /-- A conditional. -/
  | ite : ForTest A → ForProg A B → ForProg A B → ForProg A B
  /-- `for x in positions(w)` (`true`) or `for x in positions_reverse(w)` (`false`). -/
  | loop : Bool → ℕ → ForProg A B → ForProg A B

namespace ForTest

variable {A : Type}

/-- The truth value of a test under valuations of the position and Boolean
variables. -/
def Holds (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) : ForTest A → Prop
  | boolVar i => bv i = true
  | eqPos i j => pos i = pos j
  | lePos i j => pos i ≤ pos j
  | label i a => w[pos i]? = some a
  | not t => ¬ Holds w pos bv t
  | and t s => Holds w pos bv t ∧ Holds w pos bv s
  | or t s => Holds w pos bv t ∨ Holds w pos bv s

end ForTest

/-- Running the body of a loop over a list of positions, threading the Boolean
valuation and concatenating the outputs. -/
def forLoopRun {B : Type} (body : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B) :
    List ℕ → (ℕ → Bool) → (ℕ → Bool) × List B
  | [], bv => (bv, [])
  | p :: ps, bv =>
      let r := body bv p
      let r' := forLoopRun body ps r.1
      (r'.1, r.2 ++ r'.2)

namespace ForProg

variable {A B : Type}

open scoped Classical in
/-- The semantics of a program: the final Boolean valuation and the output. -/
noncomputable def exec (w : List A) :
    ForProg A B → (ℕ → ℕ) → (ℕ → Bool) → (ℕ → Bool) × List B
  | skip, _, bv => (bv, [])
  | output b, _, bv => (bv, [b])
  | assign i v, _, bv => (Function.update bv i v, [])
  | seq P Q, pos, bv =>
      let r := exec w P pos bv
      let r' := exec w Q pos r.1
      (r'.1, r.2 ++ r'.2)
  | ite t P Q, pos, bv =>
      if ForTest.Holds w pos bv t then exec w P pos bv else exec w Q pos bv
  | loop dir x P, pos, bv =>
      forLoopRun (fun bv' p => exec w P (Function.update pos x p) bv')
        (if dir then List.range w.length else (List.range w.length).reverse) bv

/-- The function computed by a for-transducer. -/
noncomputable def eval (P : ForProg A B) (w : List A) : List B :=
  (exec w P (fun _ => 0) (fun _ => false)).2

/-- A program without loops. -/
def LoopFree : ForProg A B → Prop
  | skip => True
  | output _ => True
  | assign _ _ => True
  | seq P Q => LoopFree P ∧ LoopFree Q
  | ite _ P Q => LoopFree P ∧ LoopFree Q
  | loop _ _ _ => False

/-- Nested loops `for x₁ in τ₁: ⋯ for x_k in τ_k: body`. -/
def nestLoops : List (Bool × ℕ) → ForProg A B → ForProg A B
  | [], body => body
  | (d, x) :: rest, body => ForProg.loop d x (nestLoops rest body)

/-- A program produces at most one output letter per execution. -/
def OutputsAtMostOne (P : ForProg A B) : Prop :=
  ∀ (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool), ((exec w P pos bv).2).length ≤ 1

/-- Prenex form: nested loops whose body is loop-free and outputs at most one
letter per iteration, followed by a loop-free epilogue. -/
def PrenexForm (P : ForProg A B) : Prop :=
  ∃ (ls : List (Bool × ℕ)) (body epilogue : ForProg A B),
    LoopFree body ∧ LoopFree epilogue ∧ OutputsAtMostOne body ∧
    P = ForProg.seq (nestLoops ls body) epilogue

end ForProg

/-- A function computed by a for-transducer. -/
def IsForTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ P : ForProg A B, ∀ w, P.eval w = f w

end Lax194892.ForTransducers
