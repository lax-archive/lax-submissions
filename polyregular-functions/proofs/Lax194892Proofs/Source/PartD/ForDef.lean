/-
Part D: for-transducers -- the definitions.

The syntax and the semantics of the for-transducers of *Transducers*
(M. Bojańczyk), together with Definition `def:prenex-normal-form-for-transducers` (prenex form).
Everything in this file is moved unchanged from `RequestProject/PartD/Statements.lean`, so that the
constructions used in the proofs of Lemma `lemma:prenex-normal-form` and of Lemma
`lem:for-closed-under-composition` can be developed before the statements of Part D.
-/
import Mathlib

namespace Lax194892Proofs.Transducers

/-! ## For-transducers -/

/-- Tests of a for-transducer: Boolean variables, equality and order tests on
position variables, and label tests. -/
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

/-- Programs of a for-transducer.  Position variables are read-only and are
bound by the loops; Boolean variables are initialised to `false`. -/
inductive ForProg (A B : Type) : Type
  /-- The empty program. -/
  | skip : ForProg A B
  /-- `output('b')`: append the letter `b` to the output. -/
  | output : B → ForProg A B
  /-- `X = true` / `X = false`. -/
  | assign : ℕ → Bool → ForProg A B
  /-- Sequential composition `I ; J`. -/
  | seq : ForProg A B → ForProg A B → ForProg A B
  /-- A conditional. -/
  | ite : ForTest A → ForProg A B → ForProg A B → ForProg A B
  /-- `for x in positions(w)` (`true`) or `for x in positions_reverse(w)`
  (`false`). -/
  | loop : Bool → ℕ → ForProg A B → ForProg A B

namespace ForTest

variable {A : Type}

/-- The truth value of a test, given the input string and the valuations of the
position and Boolean variables. -/
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
/-- The semantics of a for-transducer program: the resulting Boolean valuation
and the produced output string. -/
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

/-- The string-to-string function computed by a for-transducer. -/
noncomputable def eval (P : ForProg A B) (w : List A) : List B :=
  (exec w P (fun _ => 0) (fun _ => false)).2

/-- A program that contains no loops. -/
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

/-- **Definition `def:prenex-normal-form-for-transducers` (Prenex form).**  A block of nested loops
whose body is loop-free and produces at most one output letter per iteration, followed by a
loop-free epilogue. -/
def PrenexForm (P : ForProg A B) : Prop :=
  ∃ (ls : List (Bool × ℕ)) (body epilogue : ForProg A B),
    LoopFree body ∧ LoopFree epilogue ∧ OutputsAtMostOne body ∧
    P = ForProg.seq (nestLoops ls body) epilogue

end ForProg

/-- A function computed by a for-transducer. -/
def IsForTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ P : ForProg A B, ∀ w, P.eval w = f w

end Lax194892Proofs.Transducers
