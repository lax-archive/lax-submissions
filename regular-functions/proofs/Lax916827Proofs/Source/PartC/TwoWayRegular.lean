/-
The prime regular functions are computed by two-way transducers (the content of
the proof of Corollary `cor:2dfa-computes-all-regular-functions` of *Transducers*, M. Bojańczyk).

The book's proof of Corollary `cor:2dfa-computes-all-regular-functions` reads: "Two-way transducers can
compute all rational functions by Corollary `cor:2dfa-closure-under-composition`, and they can
compute map reverse and map duplicate by Example
`lem:check-if-output-string-of-configuration-graph-belongs-to-L`.  Finally, they are closed under
composition thanks to Theorem `thm:composition-of-two-way-transducers`."  This establishes that
every *regular* function is computed by a two-way transducer, i.e. the inclusion opposite to the one
in the printed statement of the corollary; see `RequestProject/PartC/Statements.lean` for a
discussion.

This file collects the three ingredients: closure under pre-composition with a letter-to-letter map
(a special case of Corollary `cor:2dfa-closure-under-composition`), and the two-way transducers for
map reverse and map duplicate (`TwoWaySweep.lean`). -/
import Lax916827Proofs.Source.PartC.TwoWaySweep
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

open TwoWay

/-! ## Pre-composition with a letter-to-letter map -/

/-- A letter-to-letter map is a homomorphism, hence a rational function. -/
lemma rationalFun_listMap {A B : Type} [Finite A] (e : A → B) :
    IsRationalFun (fun w : List A => w.map e) := by
  have h : (fun w : List A => w.map e) = homOf (fun a => [e a]) := by
    funext w
    induction w with
    | nil => rfl
    | cons a w ih => rw [homOf_cons, ← ih]; rfl
  rw [h]
  exact PrimeRat.rationalFun_homOf _

/-- Two-way transducers are closed under pre-composition with a letter-to-letter
map. -/
theorem isTwoWay_precomp_map {A B C : Type} [Finite A] [Finite B] [Finite C]
    {g : List B → List C} (hg : IsTwoWay g) (e : A → B) :
    IsTwoWay (fun w : List A => g (w.map e)) :=
  isTwoWay_comp_rational (rationalFun_listMap e) hg

/-! ## The two-way transducers for map reverse and map duplicate -/

/-- The map lifting of reversal is computed by a two-way transducer. -/
theorem isTwoWay_mapLift_reverse (A : Type) :
    IsTwoWay (mapLift (List.reverse : List A → List A)) := by
  have h := isTwoWay_mapLift_sweep (fun _ : A => ([] : List A)) (fun a => [a]) (fun _ => [])
  rwa [blockF_reverse] at h

/-- The map lifting of duplication is computed by a two-way transducer. -/
theorem isTwoWay_mapLift_dup (A : Type) :
    IsTwoWay (mapLift (fun x : List A => x ++ x)) := by
  have h := isTwoWay_mapLift_sweep (fun a : A => [a]) (fun _ => ([] : List A)) (fun a => [a])
  rwa [blockF_dup] at h

end Lax916827Proofs.Transducers
