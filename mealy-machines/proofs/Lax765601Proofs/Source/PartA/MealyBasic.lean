/- Mealy machines: definitions (Definitions `def:mealy-machine` and
`def:prime-mealy-machines`) and their basic properties, from *Transducers* (M. Bojańczyk,
June 25, 2026).

This file collects the definitions of Part A that are used throughout the book,
together with elementary lemmas about runs, state transformations and the
product (composition) construction.
-/
import Lax765601Proofs.Source.Common.Basic

namespace Lax765601Proofs.Transducers

/-- **Definition `def:mealy-machine` (Mealy machine).**  A Mealy machine consists of an input
alphabet `A`, an output alphabet `B`, a state space `Q`, an initial state and a
transition function `Q × A → Q × B`. -/
structure Mealy (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a source state and an input letter determine a
  target state and an output letter. -/
  step : Q → A → Q × B

namespace Mealy

variable {A B C Q P : Type}

/-- Running the machine from a given state, collecting the output letters. -/
def run (M : Mealy A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (M.step q a).2 :: M.run (M.step q a).1 w

/-- The semantics of a Mealy machine: a letter-to-letter function `A* → B*`. -/
def eval (M : Mealy A B Q) (w : List A) : List B := M.run M.init w

/-- The state transformation of an input letter. -/
def letterTrans (M : Mealy A B Q) (a : A) : Q → Q := fun q => (M.step q a).1

/-- The transition function of the underlying pre-automaton. -/
def transFun (M : Mealy A B Q) : Q → A → Q := fun q a => (M.step q a).1

/-- The state transformation of an input string. -/
def trans (M : Mealy A B Q) (w : List A) : Q → Q := strTrans M.transFun w

/-- **Definition `def:prime-mealy-machines` (Reversible machine).**  All state
transformations of all letters are permutations. -/
def Reversible (M : Mealy A B Q) : Prop := ∀ a : A, Function.Bijective (M.letterTrans a)

/-- **Definition `def:prime-mealy-machines` (Flip-flop machine).**  The state transformation
of each letter is either the identity or a constant. -/
def FlipFlop (M : Mealy A B Q) : Prop :=
  ∀ a : A, M.letterTrans a = id ∨ ∃ q₀ : Q, ∀ q : Q, M.letterTrans a q = q₀

/-- Condition (*) of Lemma `lem:aperiodicity-minimal-machine`: for every state transformation `δ`
arising from an input string, the sequence `δ¹, δ², …` eventually stabilises. -/
def TransStabilises (M : Mealy A B Q) : Prop := TransAperiodic M.transFun

/-! ### Elementary lemmas about runs and state transformations -/

@[simp] lemma run_nil (M : Mealy A B Q) (q : Q) : M.run q [] = [] := rfl

@[simp] lemma run_cons (M : Mealy A B Q) (q : Q) (a : A) (w : List A) :
    M.run q (a :: w) = (M.step q a).2 :: M.run (M.step q a).1 w := rfl

@[simp] lemma trans_nil (M : Mealy A B Q) : M.trans [] = id := rfl

lemma transFun_eq_letterTrans (M : Mealy A B Q) (q : Q) (a : A) :
    M.transFun q a = M.letterTrans a q := rfl

lemma trans_cons (M : Mealy A B Q) (a : A) (w : List A) (q : Q) :
    M.trans (a :: w) q = M.trans w (M.letterTrans a q) := rfl

lemma trans_append (M : Mealy A B Q) (u v : List A) (q : Q) :
    M.trans (u ++ v) q = M.trans v (M.trans u q) := by
  simp [trans, strTrans, List.foldl_append]

@[simp] lemma run_length (M : Mealy A B Q) (q : Q) (w : List A) :
    (M.run q w).length = w.length := by
  induction w generalizing q with
  | nil => simp
  | cons a w ih => simp [ih]

lemma run_append (M : Mealy A B Q) (q : Q) (u v : List A) :
    M.run q (u ++ v) = M.run q u ++ M.run (M.trans u q) v := by
  induction u generalizing q with
  | nil => simp
  | cons a u ih => simp [ih, trans_cons, letterTrans]

lemma eval_append (M : Mealy A B Q) (u v : List A) :
    M.eval (u ++ v) = M.eval u ++ M.run (M.trans u M.init) v := by
  simp [eval, run_append]

@[simp] lemma eval_length (M : Mealy A B Q) (w : List A) :
    (M.eval w).length = w.length := by
  simp [eval]

lemma eval_prefix (M : Mealy A B Q) {u v : List A} (h : u <+: v) : M.eval u <+: M.eval v := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨_, (M.eval_append u t).symm⟩

/-! ### The product (composition) construction -/

/-- The product of two Mealy machines: it runs `M`, and feeds its output letters
to `N`.  This is the construction used in Theorem `thm:composition-mealy`. -/
def compose (M : Mealy A B Q) (N : Mealy B C P) : Mealy A C (Q × P) where
  init := (M.init, N.init)
  step := fun qp a =>
    (((M.step qp.1 a).1, (N.step qp.2 (M.step qp.1 a).2).1),
      (N.step qp.2 (M.step qp.1 a).2).2)

lemma run_compose (M : Mealy A B Q) (N : Mealy B C P) (q : Q) (p : P) (w : List A) :
    (M.compose N).run (q, p) w = N.run p (M.run q w) := by
  induction w generalizing q p with
  | nil => rfl
  | cons a w ih =>
    simp only [run_cons]
    unfold Mealy.compose
    simp
    exact ih _ _

lemma eval_compose (M : Mealy A B Q) (N : Mealy B C P) :
    (M.compose N).eval = N.eval ∘ M.eval := by
  funext w
  exact run_compose M N M.init N.init w

lemma letterTrans_compose (M : Mealy A B Q) (N : Mealy B C P) (a : A) (qp : Q × P) :
    (M.compose N).letterTrans a qp =
      (M.letterTrans a qp.1, N.letterTrans (M.step qp.1 a).2 qp.2) := rfl

/-! ### The associated deterministic automaton -/

/-- The dfa obtained by running a Mealy machine and feeding its outputs to a dfa
over the output alphabet.  It accepts exactly those inputs whose image under the
Mealy machine is accepted by the given dfa. -/
def dfaComp (M : Mealy A B Q) {σ : Type} (D : DFA B σ) : DFA A (Q × σ) where
  step := fun qs a => ((M.step qs.1 a).1, D.step qs.2 (M.step qs.1 a).2)
  start := (M.init, D.start)
  accept := {qs | qs.2 ∈ D.accept}

lemma dfaComp_evalFrom (M : Mealy A B Q) {σ : Type} (D : DFA B σ) (q : Q) (s : σ)
    (w : List A) :
    (M.dfaComp D).evalFrom (q, s) w = (M.trans w q, D.evalFrom s (M.run q w)) := by
  induction w generalizing q s with
  | nil => rfl
  | cons a w ih =>
      show (M.dfaComp D).evalFrom ((M.step q a).1, D.step s (M.step q a).2) w = _
      rw [ih, run_cons, DFA.evalFrom_cons, trans_cons]
      rfl

lemma dfaComp_accepts (M : Mealy A B Q) {σ : Type} (D : DFA B σ) :
    (M.dfaComp D).accepts = {w : List A | M.eval w ∈ D.accepts} := by
  ext w
  show ((M.dfaComp D).evalFrom (M.init, D.start) w) ∈ (M.dfaComp D).accept ↔ M.eval w ∈ D.accepts
  rw [dfaComp_evalFrom]
  exact Iff.rfl

end Mealy

/-- A string-to-string function is *computed by a Mealy machine*. -/
def IsMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f

/-- A string-to-string function is computed by a reversible Mealy machine. -/
def IsReversibleMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ M.Reversible

/-- A string-to-string function is computed by a flip-flop Mealy machine. -/
def IsFlipFlopMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ M.FlipFlop

/-- The family of **prime Mealy machines** (Definition `def:prime-mealy-machines`):
reversible or flip-flop. -/
def PrimeMealyFam : ∀ (A B : Type), (List A → List B) → Prop :=
  fun _ _ f => IsReversibleMealy f ∨ IsFlipFlopMealy f

/-- The family of flip-flop Mealy machines, as a family indexed by alphabets. -/
def FlipFlopFam : ∀ (A B : Type), (List A → List B) → Prop :=
  fun _ _ f => IsFlipFlopMealy f

end Lax765601Proofs.Transducers