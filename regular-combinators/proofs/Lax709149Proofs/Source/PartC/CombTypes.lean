/-
Types, their string representations, and regularity under string representation, from Section
*Combinators* of *Transducers* (M. Bojańczyk).

This file formalises Definition `def:types` (types built from the unit type by product, co-product
and list), the string representation of the elements of a type over the book's eight-letter
alphabet, and Definition `def:regular-functions-on-types-under-string-representation`.

## The string representation

The book fixes the alphabet with eight letters

    (   )   [   ]   ,   1   L   R

and describes the representation of an element by induction on the type: the unique element of the
unit type is `1`, an element of `A + B` is `L a` or `R b`, a pair is `(a,b)`, and a list is
`[a₁,…,aₙ]`.  That is exactly `Ty.repr` below; `Sym8` is the alphabet, and the co-projection
letters are called `Sym8.left` and `Sym8.right`.

Nothing in the book's description fixes the *Lean* shape of the representation, and that is the one
real design decision of this development, because the induction of the easy direction of Theorem
`thm:regular-terms` has to parse it.  Three choices were made, all of them in the service of that
induction.

* The representation is a function `Ty.repr : (t : Ty) → t.Elt → List Sym8` into strings over a
  *single* eight-letter alphabet, not a family of alphabets depending on the type.  So the
  transducers of the easy direction all have the same input and output alphabet, and can be
  composed with each other and with the machinery of Part C without carrying encodings around.

* Lists are written with separators, `[a₁,…,aₙ]`, and *not* with a terminator after every entry.
  This is what the book writes.  It costs the transducers a delayed comma (the comma before an
  entry is emitted when the entry starts, not when the previous one ends), which is a state, and
  it buys the property that the representation of a list of `n` entries contains exactly `n-1`
  top-level commas, which is what the split and concatenation terms need.

* The parsing of a representation is done, in `CombDepth.lean`, by a *bracket counter* rather than
  by an automaton built by recursion on the type.  The point is Lemma `Transducers.Comb.repr_shape`
  below: in the representation of an element, every letter that sits at bracket depth `0` is one of
  `1`, `L`, `R`, `(`, `[`, and in particular a comma or a closing bracket at depth `0` can only be
  the delimiter that the surrounding term itself has written.  A counter that is capped at the
  height of the type is therefore a complete parser, and it is a *uniform* one: one state space,
  one invariant, and one simulation lemma (`Transducers.Comb.run_transparent`) serve all the atomic
  terms, where a family of automata indexed by the type would need a separate correctness proof for
  each of them.

The counterpart of this choice is that the representation must be *self-delimiting*, so that the
counter can find the end of a sub-representation; this is the content of `repr_shape` and it is
where the brackets of the book's representation earn their keep.
-/
import Lax916827Proofs.Source.PartC.RegClosure
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers

/-! ## Types (Definition `def:types`) -/

/-- **Definition `def:types` (Types).**  A type is an expression built from the unit type `one` by
the product, co-product and list constructors. -/
inductive Ty : Type
  | one : Ty
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq

/-- The set represented by a type: the unit type is `Unit`, and the three constructors are the
product, the sum and the list type of Lean. -/
def Ty.Elt : Ty → Type
  | .one => Unit
  | .prod A B => A.Elt × B.Elt
  | .sum A B => A.Elt ⊕ B.Elt
  | .list A => List A.Elt

instance : ∀ t : Ty, Inhabited t.Elt
  | .one => ⟨()⟩
  | .prod A B => ⟨((instInhabitedElt A).default, (instInhabitedElt B).default)⟩
  | .sum A _ => ⟨Sum.inl (instInhabitedElt A).default⟩
  | .list _ => ⟨[]⟩

/-- The height of a type: the maximal number of brackets that the representation of one of its
elements can have open at any one time. -/
def Ty.height : Ty → ℕ
  | .one => 0
  | .prod A B => 1 + max A.height B.height
  | .sum A B => max A.height B.height
  | .list A => 1 + A.height

/-! ## The alphabet with eight letters -/

/-- The book's alphabet with eight letters: `(`, `)`, `[`, `]`, `,`, `1`, `L`, `R`. -/
inductive Sym8 : Type
  | lpar | rpar | lbrack | rbrack | comma | one | left | right
  deriving DecidableEq, Fintype

/-! ## The string representation -/

/-- The entries of a list representation, separated by commas. -/
def joinSep : List (List Sym8) → List Sym8
  | [] => []
  | [x] => x
  | x :: xs => x ++ Sym8.comma :: joinSep xs

@[simp] lemma joinSep_nil : joinSep [] = [] := rfl

@[simp] lemma joinSep_singleton (x : List Sym8) : joinSep [x] = x := rfl

lemma joinSep_cons_cons (x y : List Sym8) (xs : List (List Sym8)) :
    joinSep (x :: y :: xs) = x ++ Sym8.comma :: joinSep (y :: xs) := rfl

/-- **The string representation of the elements of a type.**  The unique element of the unit type
is `1`, an element of `A + B` is `L a` or `R b`, a pair is `(a,b)`, and a list is `[a₁,…,aₙ]`. -/
def Ty.repr : (t : Ty) → t.Elt → List Sym8
  | .one, _ => [Sym8.one]
  | .prod A B, x => Sym8.lpar :: (A.repr x.1 ++ Sym8.comma :: (B.repr x.2 ++ [Sym8.rpar]))
  | .sum A B, x => Sum.elim (fun a => Sym8.left :: A.repr a) (fun b => Sym8.right :: B.repr b) x
  | .list A, l => Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack])

@[simp] lemma Ty.repr_one (x : Ty.one.Elt) : Ty.one.repr x = [Sym8.one] := rfl

@[simp] lemma Ty.repr_prod (A B : Ty) (a : A.Elt) (b : B.Elt) :
    (Ty.prod A B).repr (a, b)
      = Sym8.lpar :: (A.repr a ++ Sym8.comma :: (B.repr b ++ [Sym8.rpar])) := rfl

@[simp] lemma Ty.repr_inl (A B : Ty) (a : A.Elt) :
    (Ty.sum A B).repr (Sum.inl a) = Sym8.left :: A.repr a := rfl

@[simp] lemma Ty.repr_inr (A B : Ty) (b : B.Elt) :
    (Ty.sum A B).repr (Sum.inr b) = Sym8.right :: B.repr b := rfl

@[simp] lemma Ty.repr_list (A : Ty) (l : List A.Elt) :
    (Ty.list A).repr l = Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack]) := rfl

/-- The part of the representation of a list that follows the representation of its first entry:
empty if there is no second entry, and otherwise a comma and the representations of the remaining
entries. -/
def joinSepTail (A : Ty) (l : List A.Elt) : List Sym8 :=
  match l with
  | [] => []
  | _ :: _ => Sym8.comma :: joinSep (l.map A.repr)

@[simp] lemma joinSepTail_nil (A : Ty) : joinSepTail A [] = [] := rfl

lemma joinSepTail_cons (A : Ty) (a : A.Elt) (l : List A.Elt) :
    joinSepTail A (a :: l) = Sym8.comma :: joinSep ((a :: l).map A.repr) := rfl

lemma joinSep_cons (A : Ty) (a : A.Elt) (l : List A.Elt) :
    joinSep ((a :: l).map A.repr) = A.repr a ++ joinSepTail A l := by
  cases l with
  | nil => simp
  | cons b l => rfl

/-- The representations of the entries of a list, each preceded by a comma.  This is the shape in
which a machine that writes a list one entry at a time produces its output: the comma that
separates two entries is written with the entry that follows it, and the leading comma is removed
at the end. -/
def commaBlocks (A : Ty) (l : List A.Elt) : List Sym8 :=
  (l.map (fun a => Sym8.comma :: A.repr a)).flatten

@[simp] lemma commaBlocks_nil (A : Ty) : commaBlocks A [] = [] := rfl

lemma commaBlocks_cons (A : Ty) (a : A.Elt) (l : List A.Elt) :
    commaBlocks A (a :: l) = Sym8.comma :: (A.repr a ++ commaBlocks A l) := by
  simp [commaBlocks]

lemma commaBlocks_append (A : Ty) (l l' : List A.Elt) :
    commaBlocks A (l ++ l') = commaBlocks A l ++ commaBlocks A l' := by
  simp [commaBlocks]

lemma joinSepTail_eq_commaBlocks (A : Ty) (l : List A.Elt) :
    joinSepTail A l = commaBlocks A l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [joinSepTail_cons, joinSep_cons, ih, commaBlocks_cons]

lemma commaBlocks_tail (A : Ty) (l : List A.Elt) :
    (commaBlocks A l).tail = joinSep (l.map A.repr) := by
  cases l with
  | nil => rfl
  | cons a l => rw [commaBlocks_cons, joinSep_cons, joinSepTail_eq_commaBlocks]; rfl

/-! ## Regular under string representation
(Definition `def:regular-functions-on-types-under-string-representation`) -/

/-- **Definition `def:regular-functions-on-types-under-string-representation`.**  A type-to-type
function is *regular under string representation* if some regular string-to-string function over
the eight-letter alphabet makes the square of the book commute: it maps the representation of `a`
to the representation of `f a`.  Nothing is required of it on the strings that represent no
element. -/
def IsRegularUnderRepr {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ f' : List Sym8 → List Sym8, IsRegularFun f' ∧ ∀ a : A.Elt, f' (A.repr a) = B.repr (f a)

/-- The same notion for rational functions, which the book defines in the same breath. -/
def IsRationalUnderRepr {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ f' : List Sym8 → List Sym8, IsRationalFun f' ∧ ∀ a : A.Elt, f' (A.repr a) = B.repr (f a)

lemma IsRationalUnderRepr.isRegularUnderRepr {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsRationalUnderRepr f) : IsRegularUnderRepr f := by
  obtain ⟨f', hf', hfe⟩ := h
  exact ⟨f', IsRegularFun.of_rational hf', hfe⟩

lemma IsRegularUnderRepr.congr {A B : Ty} {f g : A.Elt → B.Elt} (h : IsRegularUnderRepr f)
    (hfg : ∀ a, f a = g a) : IsRegularUnderRepr g := by
  obtain ⟨f', hf', hfe⟩ := h
  exact ⟨f', hf', fun a => by rw [hfe a, hfg a]⟩

/-- Regularity under string representation is preserved by composition. -/
lemma IsRegularUnderRepr.comp {A B C : Ty} {f : A.Elt → B.Elt} {g : B.Elt → C.Elt}
    (hf : IsRegularUnderRepr f) (hg : IsRegularUnderRepr g) :
    IsRegularUnderRepr (fun a => g (f a)) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => g' (f' w), hf'.comp' hg' (fun _ => rfl), fun a => ?_⟩
  show g' (f' (A.repr a)) = C.repr (g (f a))
  rw [hfe a, hge (f a)]

end Lax709149Proofs.Transducers
