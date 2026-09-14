/-
Rewritings with regular lookaround are rational functions.

`RequestProject/PartC/RatSeq.lean` provides *sequential* rewritings, in which the block produced at
a letter depends on the letter and on the state of a deterministic automaton on the prefix that
precedes it.  Several of the rational functions needed for the proof of the snake lemma of Theorem
`thm:2dfa-decomposition-into-primes` also have to look at the suffix that follows the letter -- for
instance "delete this letter if no separator occurs after it".  This file provides the corresponding
builder: a *bilateral rewriting* `biEval`, in which the block produced at a letter depends on the
letter, on the state of a deterministic automaton run left-to-right on the prefix, and on the state
of a deterministic automaton run right-to-left on the suffix.  Such a function is computed by a
bimachine (Definition `def:bimachine`), and is therefore rational by Theorem `thm:bimachines`. -/
import Lax916827Proofs.Source.PartC.RatBuild
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B P S : Type}

/-- The state reached by the automaton `ν`, run right-to-left on `w`, starting
in the state `s` at the right end of `w`. -/
def revTrans (ν : S → A → S) : List A → S → S
  | [], s => s
  | a :: w, s => ν (revTrans ν w s) a

@[simp] lemma revTrans_nil (ν : S → A → S) (s : S) : revTrans ν [] s = s := rfl

@[simp] lemma revTrans_cons (ν : S → A → S) (a : A) (w : List A) (s : S) :
    revTrans ν (a :: w) s = ν (revTrans ν w s) a := rfl

lemma revTrans_append (ν : S → A → S) (u v : List A) (s : S) :
    revTrans ν (u ++ v) s = revTrans ν u (revTrans ν v s) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [ih]

/-- A bilateral rewriting, with the state of the right-to-left automaton at the
right end of the string given explicitly: at every letter the block
`ψ p a s` is produced, where `p` is the state of the left-to-right automaton on
the prefix before the letter and `s` is the state of the right-to-left automaton
on the suffix after the letter. -/
def biEvalT (μ : P → A → P) (ν : S → A → S) (ψ : P → A → S → List B) :
    P → List A → S → List B
  | _, [], _ => []
  | p, a :: w, t => ψ p a (revTrans ν w t) ++ biEvalT μ ν ψ (μ p a) w t

@[simp] lemma biEvalT_nil (μ : P → A → P) (ν : S → A → S) (ψ : P → A → S → List B)
    (p : P) (t : S) : biEvalT μ ν ψ p [] t = [] := rfl

@[simp] lemma biEvalT_cons (μ : P → A → P) (ν : S → A → S) (ψ : P → A → S → List B)
    (p : P) (a : A) (w : List A) (t : S) :
    biEvalT μ ν ψ p (a :: w) t = ψ p a (revTrans ν w t) ++ biEvalT μ ν ψ (μ p a) w t := rfl

lemma biEvalT_append (μ : P → A → P) (ν : S → A → S) (ψ : P → A → S → List B)
    (p : P) (u v : List A) (t : S) :
    biEvalT μ ν ψ p (u ++ v) t =
      biEvalT μ ν ψ p u (revTrans ν v t) ++ biEvalT μ ν ψ (strTrans μ u p) v t := by
  induction u generalizing p with
  | nil => simp [strTrans]
  | cons a u ih =>
      simp only [List.cons_append, biEvalT_cons, revTrans_append, ih]
      simp [strTrans, List.append_assoc]

/-- A bilateral rewriting: at every letter the block `ψ p a s` is produced,
where `p` is the state reached by the deterministic automaton `(P, μ, p₀)` on
the prefix that precedes the letter, and `s` is the state reached by the
deterministic automaton `(S, ν, s₀)`, run right-to-left, on the suffix that
follows it. -/
def biEval (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S) (ψ : P → A → S → List B)
    (w : List A) : List B := biEvalT μ ν ψ p₀ w s₀

/-- The bimachine computing a bilateral rewriting.  Its suffix automaton
remembers the first letter of the suffix and the state of `ν` on the rest. -/
def biBim (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S) (ψ : P → A → S → List B) :
    Bimachine A B P (S × Option A) where
  prefixInit := p₀
  prefixStep := μ
  suffixInit := (s₀, none)
  suffixStep := fun st a => ((match st.2 with | none => s₀ | some b => ν st.1 b), some a)
  out := fun p st => match st.2 with | none => [] | some a => ψ p a st.1

lemma biBim_sfx (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S)
    (ψ : P → A → S → List B) (v : List A) :
    bmSfx (biBim μ p₀ ν s₀ ψ) v = (revTrans ν v.tail s₀, v.head?) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
      rw [bmSfx_cons, ih]
      cases v with
      | nil => rfl
      | cons b v => rfl

lemma biBim_evalFrom (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S)
    (ψ : P → A → S → List B) (p : P) (w : List A) :
    (biBim μ p₀ ν s₀ ψ).evalFrom p w = biEvalT μ ν ψ p w s₀ := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons', biBim_sfx, ih]
      rfl

lemma biBim_eval (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S)
    (ψ : P → A → S → List B) (w : List A) :
    (biBim μ p₀ ν s₀ ψ).eval w = biEval μ p₀ ν s₀ ψ w := by
  rw [Bimachine.eval_eq_evalFrom]
  exact biBim_evalFrom μ p₀ ν s₀ ψ p₀ w

/-- **A bilateral rewriting is a rational function.** -/
theorem isRationalFun_biEval [Finite A] [Finite B] [Finite P] [Finite S]
    (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S) (ψ : P → A → S → List B) :
    IsRationalFun (biEval μ p₀ ν s₀ ψ) :=
  isRationalFun_of_bimachine (biBim μ p₀ ν s₀ ψ) (biBim_eval μ p₀ ν s₀ ψ)

/-! ## Two standard instances

The two bilateral rewritings that occur again and again: keeping the letters
selected by regular lookaround (which cuts a factor out of the input, the
factor being delimited by regular conditions), and inserting a separator in
front of the selected letters (which cuts the input into blocks delimited by
regular conditions). -/

/-- The function that keeps exactly the letters selected by regular
lookaround. -/
def biFilter (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S) (sel : P → A → S → Bool) :
    List A → List A :=
  biEval μ p₀ ν s₀ (fun p a s => if sel p a s then [a] else [])

/-- Cutting out the factor selected by regular lookaround is a rational
function. -/
theorem isRationalFun_biFilter [Finite A] [Finite P] [Finite S]
    (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S) (sel : P → A → S → Bool) :
    IsRationalFun (biFilter μ p₀ ν s₀ sel) :=
  isRationalFun_biEval _ _ _ _ _

/-- The function that inserts a separator in front of every letter selected by
regular lookaround. -/
def biMarkSep (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S) (sel : P → A → S → Bool) :
    List A → List (Option A) :=
  biEval μ p₀ ν s₀ (fun p a s => if sel p a s then [none, some a] else [some a])

/-- Cutting the input into the blocks delimited by the positions selected by
regular lookaround is a rational function. -/
theorem isRationalFun_biMarkSep [Finite A] [Finite P] [Finite S]
    (μ : P → A → P) (p₀ : P) (ν : S → A → S) (s₀ : S) (sel : P → A → S → Bool) :
    IsRationalFun (biMarkSep μ p₀ ν s₀ sel) :=
  isRationalFun_biEval _ _ _ _ _

end Lax916827Proofs.Transducers
