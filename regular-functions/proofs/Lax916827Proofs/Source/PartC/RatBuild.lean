/- A convenient builder for rational functions, used in the proofs of Lemma
`lem:regular-closure-properties` and Claim `claim:conditional` of *Transducers* (M. Bojańczyk).

Most of the rational functions that appear in these proofs are "contextual
rewritings": at every gap of the input string an output block is produced, which
depends on the state of a deterministic automaton on the prefix and on the state
of a deterministic automaton run right-to-left on the suffix.  This is exactly
what a bimachine (Definition `def:bimachine`) computes, and functions computed by
bimachines are rational by Theorem `thm:bimachines` (`rationalFun_of_isBimachine`).

This file collects the small API that makes such machines easy to use: the state
`bmSfx M w` of the suffix automaton, its recursion `bmSfx_cons`, the recursion
`Bimachine.evalFrom_cons'` for the output, and the fact that the resulting
function is rational.  As a first application, string homomorphisms (in
particular letter-to-letter maps) are rational.
-/
import Lax132576Proofs.Source.PartB.Bimachine
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B P S : Type}

/-- The state of the suffix automaton of a bimachine on the string `w`: the
automaton is run on the reverse of `w`. -/
def bmSfx (M : Bimachine A B P S) (w : List A) : S :=
  strTrans M.suffixStep w.reverse M.suffixInit

@[simp] lemma bmSfx_nil (M : Bimachine A B P S) : bmSfx M [] = M.suffixInit := rfl

lemma bmSfx_cons (M : Bimachine A B P S) (a : A) (w : List A) :
    bmSfx M (a :: w) = M.suffixStep (bmSfx M w) a := by
  simp [bmSfx, strTrans]

@[simp] lemma Bimachine.evalFrom_nil' (M : Bimachine A B P S) (p : P) :
    M.evalFrom p [] = M.out p M.suffixInit := by
  simp

/-- The recursion for the output of a bimachine: the block produced at the
leftmost gap, followed by the output on the rest of the string. -/
lemma Bimachine.evalFrom_cons' (M : Bimachine A B P S) (p : P) (a : A) (w : List A) :
    M.evalFrom p (a :: w) = M.out p (bmSfx M (a :: w)) ++ M.evalFrom (M.prefixStep p a) w :=
  M.evalFrom_cons p a w

/-- A function computed by a bimachine is rational. -/
theorem isRationalFun_of_bimachine [Finite A] [Finite B] [Finite P] [Finite S]
    (M : Bimachine A B P S) {f : List A → List B} (h : ∀ w, M.eval w = f w) :
    IsRationalFun f :=
  rationalFun_of_isBimachine ⟨P, S, inferInstance, inferInstance, M, funext h⟩

/-! ## Homomorphisms are rational -/

section Hom

variable {A B : Type}

/-- The bimachine computing the homomorphism `φ`: the suffix automaton
remembers the first letter of the suffix, and the output at a gap is the image
of that letter. -/
def homBim (φ : A → List B) : Bimachine A B Unit (Option A) where
  prefixInit := ()
  prefixStep := fun _ _ => ()
  suffixInit := none
  suffixStep := fun _ a => some a
  out := fun _ s => match s with | none => [] | some a => φ a

lemma homBim_evalFrom (φ : A → List B) (p : Unit) (w : List A) :
    (homBim φ).evalFrom p w = homOf φ w := by
  induction w with
  | nil => simp [homBim, homOf]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons', bmSfx_cons, ih]
      simp [homBim, homOf]

/-- A string homomorphism is a rational function. -/
theorem isRationalFun_homOf [Finite A] [Finite B] (φ : A → List B) :
    IsRationalFun (homOf φ) :=
  isRationalFun_of_bimachine (homBim φ) (fun w => homBim_evalFrom φ () w)

/-- A letter-to-letter map is a rational function. -/
theorem isRationalFun_map [Finite A] [Finite B] (h : A → B) :
    IsRationalFun (fun w : List A => w.map h) := by
  have : (fun w : List A => w.map h) = homOf (fun a => [h a]) := by
    funext w
    simp only [homOf]
    induction w with
    | nil => rfl
    | cons a w ih => simp [ih]
  rw [this]
  exact isRationalFun_homOf _

end Hom

end Lax916827Proofs.Transducers
