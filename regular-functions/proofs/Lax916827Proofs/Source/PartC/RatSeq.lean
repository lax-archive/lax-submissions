/-
Sequential rewritings are rational functions.

A *sequential rewriting* reads the input string from left to right and, at every letter, produces a
block that depends on the letter and on the state of a deterministic automaton on the prefix that
precedes it.  This is a special case of a bimachine (the suffix automaton only has to remember the
letter that follows the current gap), and it is the last of the small builders of rational functions
used in the proof of Lemma `lem:regular-closure-properties` of *Transducers* (M. Bojańczyk). -/
import Lax916827Proofs.Source.PartC.RatBuild
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B Mo : Type}

/-- A sequential rewriting: at every letter the block `ψ m a` is produced, where
`m` is the state reached by the deterministic automaton `(Mo, μ, m₀)` on the
prefix that precedes the letter. -/
def seqEval (μ : Mo → A → Mo) (ψ : Mo → A → List B) : Mo → List A → List B
  | _, [] => []
  | m, a :: w => ψ m a ++ seqEval μ ψ (μ m a) w

@[simp] lemma seqEval_nil (μ : Mo → A → Mo) (ψ : Mo → A → List B) (m : Mo) :
    seqEval μ ψ m [] = [] := rfl

@[simp] lemma seqEval_cons (μ : Mo → A → Mo) (ψ : Mo → A → List B) (m : Mo) (a : A)
    (w : List A) : seqEval μ ψ m (a :: w) = ψ m a ++ seqEval μ ψ (μ m a) w := rfl

/-- The bimachine computing a sequential rewriting. -/
def seqBim (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → A → List B) : Bimachine A B Mo (Option A) where
  prefixInit := m₀
  prefixStep := μ
  suffixInit := none
  suffixStep := fun _ a => some a
  out := fun p s => match s with | none => [] | some a => ψ p a

lemma seqBim_evalFrom (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → A → List B) (p : Mo)
    (w : List A) : (seqBim μ m₀ ψ).evalFrom p w = seqEval μ ψ p w := by
  induction w generalizing p with
  | nil => simp [seqBim]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons', bmSfx_cons, ih]
      rfl

/-- A sequential rewriting is a rational function. -/
theorem isRationalFun_seqEval [Finite A] [Finite B] [Finite Mo] (μ : Mo → A → Mo) (m₀ : Mo)
    (ψ : Mo → A → List B) : IsRationalFun (seqEval μ ψ m₀) :=
  isRationalFun_of_bimachine (seqBim μ m₀ ψ) (fun w => by
    rw [Bimachine.eval_eq_evalFrom]
    exact seqBim_evalFrom μ m₀ ψ m₀ w)

/-! ## Sequential rewritings with a final output -/

/-- A sequential rewriting with a final output: at every letter the block `ψ m a` is produced,
where `m` is the state of the deterministic automaton `(Mo, μ, ·)` on the prefix that precedes
the letter, and at the end the block `fin m` is produced, where `m` is the state on the whole
input. -/
def seqFinEval (μ : Mo → A → Mo) (ψ : Mo → A → List B) (fin : Mo → List B) :
    Mo → List A → List B
  | m, [] => fin m
  | m, a :: w => ψ m a ++ seqFinEval μ ψ fin (μ m a) w

@[simp] lemma seqFinEval_nil (μ : Mo → A → Mo) (ψ : Mo → A → List B) (fin : Mo → List B)
    (m : Mo) : seqFinEval μ ψ fin m [] = fin m := rfl

@[simp] lemma seqFinEval_cons (μ : Mo → A → Mo) (ψ : Mo → A → List B) (fin : Mo → List B)
    (m : Mo) (a : A) (w : List A) :
    seqFinEval μ ψ fin m (a :: w) = ψ m a ++ seqFinEval μ ψ fin (μ m a) w := rfl

/-- The bimachine computing a sequential rewriting with a final output: the suffix automaton
remembers the letter that follows the gap, and the final output is produced at the last gap,
where there is none. -/
def seqFinBim (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → A → List B) (fin : Mo → List B) :
    Bimachine A B Mo (Option A) where
  prefixInit := m₀
  prefixStep := μ
  suffixInit := none
  suffixStep := fun _ a => some a
  out := fun p s => match s with | none => fin p | some a => ψ p a

lemma seqFinBim_evalFrom (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → A → List B) (fin : Mo → List B)
    (p : Mo) (w : List A) :
    (seqFinBim μ m₀ ψ fin).evalFrom p w = seqFinEval μ ψ fin p w := by
  induction w generalizing p with
  | nil => simp [seqFinBim]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons', bmSfx_cons, ih]
      rfl

/-- **A sequential rewriting with a final output is a rational function.** -/
theorem isRationalFun_seqFinEval [Finite A] [Finite B] [Finite Mo] (μ : Mo → A → Mo) (m₀ : Mo)
    (ψ : Mo → A → List B) (fin : Mo → List B) : IsRationalFun (seqFinEval μ ψ fin m₀) :=
  isRationalFun_of_bimachine (seqFinBim μ m₀ ψ fin) (fun w => by
    rw [Bimachine.eval_eq_evalFrom]
    exact seqFinBim_evalFrom μ m₀ ψ fin m₀ w)

end Lax916827Proofs.Transducers
