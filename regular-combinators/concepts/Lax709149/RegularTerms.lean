import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Defs
import Lax709149.Types

/-!
---
title: Regular terms
type: definition
---
A *regular term* (Definition C.5.3 of *Transducers*) is an expression built by
applying combinators to atomic terms. The atomic terms are the identity
$A \to A$, the projections $A \times B \to A$ and $A \times B \to B$, the
co-projections $A \to A + B$ and $B \to A + B$, distributivity
$A \times (B + C) \to (A \times B) + (A \times C)$, the list constructor
$\mathbb{1} + A \times A^* \to A^*$ and deconstructor
$A^* \to \mathbb{1} + A \times A^*$, reverse $A^* \to A^*$, concatenation
$A^{**} \to A^*$, split $(A + B)^* \to A^* \times (B \times A^*)^*$, and group
prefix multiplication $G^* \to G^*$ for a group $G$ whose underlying set is a
finite type. The combinators are composition, pairing $(f, g) : A \to B \times C$,
co-pairing $\mathsf{either}\ f\ g : A + B \to C$, and map $f^* : A^* \to B^*$.
Every regular term defines a type-to-type function; Theorem C.5.4 relates the
functions so defined to the regular functions under string representation.

# Formalization notes

`RegTerm A B` is the syntax, indexed by the source and target types, and
`RegTerm.eval` the semantics. Split cuts its input at the entries from `B`, and
group prefix multiplication maps a list to its prefix products; its constructor
carries the group structure on the elements of `G` and the finiteness of that
type, which the book requires and which the regularity of its semantics needs.
`IsRegularTermFun f` says that some term evaluates to `f`.
-/

namespace Lax709149.RegularTerms

open Lax709149.Types

/-- The prefix products of a list: the `i`-th entry of the output is the product of
the first `i` entries of the input. -/
def prefixProd {M : Type} [Monoid M] (l : List M) : List M := (l.scanl (· * ·) 1).tail

/-- Split: the input is cut at its entries from `B`; the output is the block of
entries from `A` before the first cut, and the cutting entries each with the block
that follows it. -/
def splitList {A B : Type} : List (A ⊕ B) → List A × List (B × List A)
  | [] => ([], [])
  | Sum.inl a :: l => ((splitList l).1.cons a, (splitList l).2)
  | Sum.inr b :: l => ([], (b, (splitList l).1) :: (splitList l).2)

/-- The syntax of regular terms: atomic terms and combinators. -/
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
  /-- Group prefix multiplication `G* → G*`, for a group on a finite type. -/
  | pref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) : RegTerm (.list G) (.list G)
  /-- Composition. -/
  | comp {A B C : Ty} : RegTerm A B → RegTerm B C → RegTerm A C
  /-- Pairing. -/
  | pair {A B C : Ty} : RegTerm A B → RegTerm A C → RegTerm A (.prod B C)
  /-- Co-pairing. -/
  | copair {A B C : Ty} : RegTerm A C → RegTerm B C → RegTerm (.sum A B) C
  /-- Map. -/
  | map {A B : Ty} : RegTerm A B → RegTerm (.list A) (.list B)

/-- The function defined by a regular term. -/
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

/-- A type-to-type function is defined by a regular term. -/
def IsRegularTermFun {A B : Ty} (f : A.Elt → B.Elt) : Prop := ∃ t : RegTerm A B, t.eval = f

end Lax709149.RegularTerms
