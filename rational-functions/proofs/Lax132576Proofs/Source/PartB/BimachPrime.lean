/-
From bimachines to compositions of prime rational functions (the hard
implication of Theorem `thm:rational-primes`).

A bimachine is decomposed into four steps:

1. `w ↦ w#` appends a fresh separator, so that the `|w| + 1` gaps of `w` are in
   bijection with the positions of the new string;
2. a *right-to-left* Mealy machine annotates every position with the state of
   the suffix automaton at the corresponding gap;
3. a left-to-right Mealy machine annotates every position with the state of the
   prefix automaton at the corresponding gap;
4. a homomorphism replaces every annotated position by the output of the
   bimachine at the corresponding gap.

The two Mealy machines are compositions of prime Mealy machines by the
Krohn-Rhodes Theorem (Theorem `thm:krohn-rhodes`), and reversal turns a decomposition of a
Mealy machine into a decomposition of its right-to-left variant.
-/
import Lax765601Proofs.Source.PartA.Statements
import Lax132576Proofs.Source.PartB.PrimeRat
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace BimachPrime

/-! ### Reversal conjugation -/

/-- The right-to-left variant of a function: read the input from the right and
write the output from the right. -/
def revConj {A B : Type} (f : List A → List B) : List A → List B :=
  fun w => (f w.reverse).reverse

@[simp] lemma revConj_revConj {A B : Type} (f : List A → List B) : revConj (revConj f) = f := by
  funext w
  simp [revConj]

lemma revConj_id {A : Type} : revConj (id : List A → List A) = id := by
  funext w
  simp [revConj]

lemma revConj_comp {A B C : Type} (f : List A → List B) (g : List B → List C) :
    revConj (g ∘ f) = revConj g ∘ revConj f := by
  funext w
  simp [revConj]

/-- A composition of prime Mealy machines is a composition of prime rational
functions. -/
theorem compClosure_prime_of_mealy :
    ∀ {A B : Type} {h : List A → List B}, CompClosure PrimeMealyFam A B h →
      CompClosure PrimeRationalFam A B h := by
  intro A B h hh
  induction hh with
  | base hf => exact CompClosure.base (Or.inl hf)
  | id A => exact CompClosure.id A
  | comp _ _ ihf ihg => exact CompClosure.comp ihf ihg

/-- The right-to-left variant of a composition of prime Mealy machines is a
composition of prime rational functions. -/
theorem compClosure_prime_of_revMealy :
    ∀ {A B : Type} {h : List A → List B}, CompClosure PrimeMealyFam A B h →
      CompClosure PrimeRationalFam A B (revConj h) := by
  intro A B h hh
  induction hh with
  | @base A B f hf =>
      refine CompClosure.base (Or.inr (Or.inl ?_))
      have : (fun w => ((revConj f) w.reverse).reverse) = f := by
        funext w; simp [revConj]
      rw [this]
      exact hf
  | id A => rw [revConj_id]; exact CompClosure.id A
  | comp _ _ ihf ihg => rw [revConj_comp]; exact CompClosure.comp ihf ihg

/-! ### The decomposition of a bimachine -/

variable {A B P S : Type} (M : Bimachine A B P S)

/-- The right-to-left Mealy machine annotating every position with the state of
the suffix automaton. -/
def sufMealy : Mealy (Option A) (Option A × S) S where
  init := M.suffixInit
  step := fun s x =>
    match x with
    | none => (s, (none, s))
    | some a => (M.suffixStep s a, (some a, M.suffixStep s a))

/-- The left-to-right Mealy machine annotating every position with the state of
the prefix automaton. -/
def preMealy : Mealy (Option A × S) (Option A × S × P) P where
  init := M.prefixInit
  step := fun p y =>
    match y.1 with
    | none => (p, (none, y.2, p))
    | some a => (M.prefixStep p a, (some a, y.2, p))

/-- The state of the suffix automaton at the gap before `z`. -/
def sufState (z : List A) : S := strTrans M.suffixStep z.reverse M.suffixInit

@[simp] lemma sufState_nil : sufState M [] = M.suffixInit := rfl

lemma sufState_cons (a : A) (z : List A) :
    sufState M (a :: z) = M.suffixStep (sufState M z) a := by
  simp [sufState, strTrans, List.reverse_cons]

/-- The annotation of the input with the states of the suffix automaton. -/
def annS : List A → List (Option A × S)
  | [] => [(none, M.suffixInit)]
  | a :: w => (some a, sufState M (a :: w)) :: annS w

/-- The annotation of the input with the states of both automata. -/
def annSP (p : P) : List A → List (Option A × S × P)
  | [] => [(none, M.suffixInit, p)]
  | a :: w => (some a, sufState M (a :: w), p) :: annSP (M.prefixStep p a) w

lemma sufMealy_trans (z : List A) (s : S) :
    (sufMealy M).trans (z.map some) s = strTrans M.suffixStep z s := by
  induction z generalizing s with
  | nil => rfl
  | cons a z ih =>
      rw [List.map_cons, Mealy.trans_cons]
      have : (sufMealy M).letterTrans (some a) s = M.suffixStep s a := rfl
      rw [this, ih]
      simp [strTrans]

/-- Step 2 of the decomposition: the right-to-left Mealy machine computes the
annotation `annS`. -/
lemma revConj_sufMealy (w : List A) :
    revConj (sufMealy M).eval (w.map some ++ [none]) = annS M w := by
  have hrev : (w.map some ++ [none]).reverse = (none : Option A) :: (w.reverse.map some) := by
    simp
  have hkey : ∀ u : List A,
      ((sufMealy M).run M.suffixInit (u.reverse.map some)).reverse ++ [(none, M.suffixInit)] =
        annS M u := by
    intro u
    induction u with
    | nil => simp [annS]
    | cons a u ih =>
        have hlist : (a :: u).reverse.map (some : A → Option A) =
            (u.reverse.map some) ++ [some a] := by simp
        rw [hlist, Mealy.run_append]
        have hstate : (sufMealy M).trans (u.reverse.map some) M.suffixInit = sufState M u :=
          sufMealy_trans M u.reverse M.suffixInit
        rw [hstate]
        have hlast : (sufMealy M).run (sufState M u) [some a] =
            [(some a, M.suffixStep (sufState M u) a)] := rfl
        rw [hlast]
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append]
        rw [annS, sufState_cons]
        simp only [List.cons.injEq, true_and]
        exact ih
  rw [revConj, hrev]
  have hstart : (sufMealy M).eval ((none : Option A) :: (w.reverse.map some)) =
      (none, M.suffixInit) :: (sufMealy M).run M.suffixInit (w.reverse.map some) := rfl
  rw [hstart]
  simp only [List.reverse_cons]
  exact hkey w

/-- Step 3 of the decomposition: the left-to-right Mealy machine adds the states
of the prefix automaton. -/
lemma preMealy_run (p : P) (w : List A) :
    (preMealy M).run p (annS M w) = annSP M p w := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
      rw [annS, Mealy.run_cons]
      have hstep : (preMealy M).step p (some a, sufState M (a :: w)) =
          (M.prefixStep p a, (some a, sufState M (a :: w), p)) := rfl
      rw [hstep, annSP]
      simp only [List.cons.injEq, true_and]
      exact ih _

/-- Step 4 of the decomposition: the homomorphism produces the output. -/
lemma homOf_annSP (p : P) (w : List A) :
    homOf (fun y : Option A × S × P => M.out y.2.2 y.2.1) (annSP M p w) = M.evalFrom p w := by
  induction w generalizing p with
  | nil => simp [annSP, homOf, Bimachine.evalFrom_nil]
  | cons a w ih =>
      rw [annSP, Bimachine.evalFrom_cons]
      simp only [homOf, List.map_cons, List.flatten_cons]
      rw [← homOf]
      rw [ih]
      congr 1

/-- The bimachine is the composition of the four steps. -/
theorem eval_eq_comp :
    M.eval =
      (homOf (fun y : Option A × S × P => M.out y.2.2 y.2.1)) ∘
        ((preMealy M).eval ∘
          (revConj (sufMealy M).eval ∘ (fun w : List A => w.map some ++ [none]))) := by
  funext w
  simp only [Function.comp_apply]
  rw [revConj_sufMealy M w]
  have : (preMealy M).eval (annS M w) = annSP M M.prefixInit w := preMealy_run M M.prefixInit w
  rw [this, homOf_annSP M M.prefixInit w, Bimachine.eval_eq_evalFrom]

end BimachPrime

open BimachPrime in
/-- A function computed by a bimachine is a composition of prime rational
functions. -/
theorem compClosure_of_isBimachine {A B : Type} [Finite A] {f : List A → List B}
    (hf : IsBimachine f) : CompClosure PrimeRationalFam A B f := by
  obtain ⟨P, S, hP, hS, M, rfl⟩ := hf
  have h₁ : CompClosure PrimeRationalFam A (Option A) (fun w : List A => w.map some ++ [none]) := by
    refine CompClosure.base (Or.inr (Or.inr (Or.inr ⟨Equiv.refl (Option A), ?_⟩)))
    funext w
    simp
  have h₂ : CompClosure PrimeRationalFam (Option A) (Option A × S)
      (revConj (sufMealy M).eval) :=
    compClosure_prime_of_revMealy (krohn_rhodes ⟨S, hS, sufMealy M, rfl⟩)
  have h₃ : CompClosure PrimeRationalFam (Option A × S) (Option A × S × P)
      (preMealy M).eval :=
    compClosure_prime_of_mealy (krohn_rhodes ⟨P, hP, preMealy M, rfl⟩)
  have h₄ : CompClosure PrimeRationalFam (Option A × S × P) B
      (homOf (fun y : Option A × S × P => M.out y.2.2 y.2.1)) :=
    CompClosure.base (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
  have hcomp := CompClosure.comp (CompClosure.comp (CompClosure.comp h₁ h₂) h₃) h₄
  rw [eval_eq_comp M]
  exact hcomp

end Lax132576Proofs.Transducers
