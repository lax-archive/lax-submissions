/-
Regular terms (Definition `def:regular-terms`) of Section *Combinators* of *Transducers*
(M. Bojańczyk).

A regular term is an expression built from the atomic terms -- identity, the two projections, the
two co-projections, distributivity, the list constructor and deconstructor, reverse, concatenation,
split and group prefix multiplication -- by composition, pairing, co-pairing and map.  Terms have a
syntax and a semantics; the book does not distinguish them, and here the syntax is the inductive
type `Transducers.RegTerm` and the semantics is `Transducers.RegTerm.eval`.

Two points of the definition need a decision in Lean.

* Group prefix multiplication is parameterised, the book says, "not just by the underlying set of
  the group, but also its group operation", and the underlying set is required to be a finite type.
  So the constructor `RegTerm.pref` carries a type `G`, a `Group G.Elt` structure and the
  hypothesis that `G.Elt` is finite.  (Finiteness of `G.Elt` is *not* automatic: a type of the form
  `A*` is infinite.  It is needed for the semantics to be regular, since the transducer has to keep
  the running product in its state.)

* The atomic terms are indexed by the types they are stated for -- `RegTerm.fst A B` is the first
  projection of `A × B` -- because the type of a term is part of its data here, where the book
  leaves it implicit.
-/
import Lax709149Proofs.Source.PartC.CombTypes
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers

/-! ## The auxiliary functions of two atomic terms -/

/-- The prefix products of a list: the `i`-th entry of the output is the product of the first `i`
entries of the input.  This is the semantics of group prefix multiplication. -/
def prefixProd {M : Type} [Monoid M] (l : List M) : List M := (l.scanl (· * ·) 1).tail

/-- The split function of Example `ex:split`: the input list is cut at its entries from `B`, and
the output is the block of entries from `A` before the first cut, together with the list of the
cutting entries, each with the block of entries from `A` that follows it. -/
def splitList {A B : Type} : List (A ⊕ B) → List A × List (B × List A)
  | [] => ([], [])
  | Sum.inl a :: l => ((splitList l).1.cons a, (splitList l).2)
  | Sum.inr b :: l => ([], (b, (splitList l).1) :: (splitList l).2)

@[simp] lemma splitList_nil {A B : Type} : splitList ([] : List (A ⊕ B)) = ([], []) := rfl

@[simp] lemma splitList_inl {A B : Type} (a : A) (l : List (A ⊕ B)) :
    splitList (Sum.inl a :: l) = (a :: (splitList l).1, (splitList l).2) := rfl

@[simp] lemma splitList_inr {A B : Type} (b : B) (l : List (A ⊕ B)) :
    splitList (Sum.inr b :: l) = ([], (b, (splitList l).1) :: (splitList l).2) := rfl

/-! ## Regular terms (Definition `def:regular-terms`) -/

/-- **Definition `def:regular-terms` (Regular term).**  The syntax of the regular terms: the atomic
terms of item `item:regular-list-functions-fo-atomic` and the combinators of item
`item:regular-list-functions-combinators`. -/
inductive RegTerm : Ty → Ty → Type
  /-- Identity `A → A`. -/
  | id (A : Ty) : RegTerm A A
  /-- First projection `A × B → A`. -/
  | fst (A B : Ty) : RegTerm (.prod A B) A
  /-- Second projection `A × B → B`. -/
  | snd (A B : Ty) : RegTerm (.prod A B) B
  /-- Left co-projection `A → A + B`. -/
  | inl (A B : Ty) : RegTerm A (.sum A B)
  /-- Right co-projection `B → A + B`. -/
  | inr (A B : Ty) : RegTerm B (.sum A B)
  /-- Distributivity `A × (B + C) → (A × B) + (A × C)`. -/
  | distr (A B C : Ty) : RegTerm (.prod A (.sum B C)) (.sum (.prod A B) (.prod A C))
  /-- The list constructor `1 + A × A* → A*`. -/
  | cons (A : Ty) : RegTerm (.sum .one (.prod A (.list A))) (.list A)
  /-- The list deconstructor `A* → 1 + A × A*`. -/
  | uncons (A : Ty) : RegTerm (.list A) (.sum .one (.prod A (.list A)))
  /-- Reverse `A* → A*`. -/
  | reverse (A : Ty) : RegTerm (.list A) (.list A)
  /-- Concatenation `A** → A*`. -/
  | concat (A : Ty) : RegTerm (.list (.list A)) (.list A)
  /-- Split `(A + B)* → A* × (B × A*)*`. -/
  | split (A B : Ty) : RegTerm (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A))))
  /-- Group prefix multiplication `G* → G*`, for a group whose underlying set is a finite type. -/
  | pref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) : RegTerm (.list G) (.list G)
  /-- Composition. -/
  | comp {A B C : Ty} : RegTerm A B → RegTerm B C → RegTerm A C
  /-- Pairing. -/
  | pair {A B C : Ty} : RegTerm A B → RegTerm A C → RegTerm A (.prod B C)
  /-- Co-pairing. -/
  | copair {A B C : Ty} : RegTerm A C → RegTerm B C → RegTerm (.sum A B) C
  /-- Map. -/
  | map {A B : Ty} : RegTerm A B → RegTerm (.list A) (.list B)

/-- The semantics of a regular term: the type-to-type function that it defines. -/
def RegTerm.eval : {A B : Ty} → RegTerm A B → A.Elt → B.Elt
  | _, _, .id _ => fun x => x
  | _, _, .fst _ _ => fun x => x.1
  | _, _, .snd _ _ => fun x => x.2
  | _, _, .inl _ _ => fun x => Sum.inl x
  | _, _, .inr _ _ => fun x => Sum.inr x
  | _, _, .distr _ _ _ => fun x =>
      Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2
  | _, _, .cons _ => fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x
  | _, _, .uncons _ => fun l => match l with
      | [] => Sum.inl ()
      | a :: l' => Sum.inr (a, l')
  | _, _, .reverse _ => fun l => l.reverse
  | _, _, .concat _ => fun l => l.flatten
  | _, _, .split _ _ => fun l => splitList l
  | _, _, .pref _ grp _ => fun l => @prefixProd _ (@Group.toDivisionMonoid _ grp).toMonoid l
  | _, _, .comp s t => fun x => t.eval (s.eval x)
  | _, _, .pair s t => fun x => (s.eval x, t.eval x)
  | _, _, .copair s t => fun x => Sum.elim s.eval t.eval x
  | _, _, .map t => fun l => l.map t.eval

/-- A type-to-type function is *defined by a regular term* if it is the semantics of one. -/
def IsRegularTermFun {A B : Ty} (f : A.Elt → B.Elt) : Prop := ∃ t : RegTerm A B, t.eval = f

lemma IsRegularTermFun.of_term {A B : Ty} (t : RegTerm A B) : IsRegularTermFun t.eval := ⟨t, rfl⟩

lemma IsRegularTermFun.congr {A B : Ty} {f g : A.Elt → B.Elt} (h : IsRegularTermFun f)
    (hfg : ∀ a, f a = g a) : IsRegularTermFun g := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [ht]; exact funext hfg⟩

lemma IsRegularTermFun.comp {A B C : Ty} {f : A.Elt → B.Elt} {g : B.Elt → C.Elt}
    (hf : IsRegularTermFun f) (hg : IsRegularTermFun g) : IsRegularTermFun (fun a => g (f a)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨s.comp t, by funext a; rw [show (s.comp t).eval a = t.eval (s.eval a) from rfl, hs, ht]⟩

end Lax709149Proofs.Transducers
