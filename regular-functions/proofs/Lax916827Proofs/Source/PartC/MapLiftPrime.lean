/- The map lifting of map reverse and of map duplicate is regular.  This is the second step of the
proof of the first item of Lemma `lem:regular-closure-properties` of *Transducers* (M. Bojańczyk).

The map lifting of map reverse reverses every maximal factor of a string over
`A₀ + 1 + 1` that uses no separator, of either of the two kinds.  Following the
book, the two kinds of separators are merged into one by a rational recoding:
each separator is replaced by a marker letter surrounded by two copies of the
(only) separator of the alphabet `Bool + A₀ + 1`, so that a marker forms a block
of its own and the blocks of letters are exactly the maximal factors that must
be reversed.  Map reverse (resp. map duplicate) over the bigger alphabet then
does the required work, and a rational function decodes the result: it deletes
all the separators, restores the two kinds of separators from the markers, and
deletes a marker that is immediately preceded by another one (which undoes the
duplication of the one-letter blocks that carry the markers).
-/
import Lax916827Proofs.Source.PartC.RatTools
import Lax916827Proofs.Source.PartC.MapLiftAux
import Lax916827Proofs.Source.PartC.ContAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace MapLiftPrime

variable {A₀ : Type}

/-- A factor without separators, seen inside the alphabet `A₀ + 1 + 1`. -/
def letters (u : List A₀) : List (Option (Option A₀)) := u.map (fun a => some (some a))

/-- The two separators of the alphabet `A₀ + 1 + 1`. -/
def sepOf : Bool → Option (Option A₀)
  | false => none
  | true => some none

/-- A factor without separators, after the encoding. -/
def encLet (u : List A₀) : List (Option (Bool ⊕ A₀)) := u.map (fun a => some (Sum.inr a))

/-- The letter-by-letter encoding: a separator becomes a marker letter
surrounded by two separators. -/
def encψ : Option (Option A₀) → List (Option (Bool ⊕ A₀))
  | none => [none, some (Sum.inl false), none]
  | some none => [none, some (Sum.inl true), none]
  | some (some a) => [some (Sum.inr a)]

lemma homOf_app {A B : Type} (φ : A → List B) (x y : List A) :
    homOf φ (x ++ y) = homOf φ x ++ homOf φ y := by simp [homOf]

lemma homOf_encψ_letters (u : List A₀) : homOf encψ (letters u) = encLet u := by
  induction u with
  | nil => rfl
  | cons a u ih => rw [letters, List.map_cons, ← letters, homOf, List.map_cons,
      List.flatten_cons, ← homOf, ih]; rfl

lemma homOf_encψ_sep (b : Bool) (w : List (Option (Option A₀))) :
    homOf encψ (sepOf b :: w)
      = none :: some (Sum.inl b) :: none :: homOf encψ w := by
  cases b <;> · rw [homOf, List.map_cons, List.flatten_cons, ← homOf]; rfl

lemma homOf_encψ_split (u : List A₀) (b : Bool) (w : List (Option (Option A₀))) :
    homOf encψ (letters u ++ sepOf b :: w)
      = encLet u ++ none :: some (Sum.inl b) :: none :: homOf encψ w := by
  rw [homOf_app, homOf_encψ_letters, homOf_encψ_sep]

/-! ## The decoding -/

/-- The output of the decoding at the letter `next`, whose predecessor is
`prev`. -/
def decψ2 : Unit → Option (Option (Bool ⊕ A₀)) → Option (Option (Bool ⊕ A₀)) →
    List (Option (Option A₀))
  | _, _, none => []
  | _, _, some none => []
  | _, prev, some (some (Sum.inl b)) =>
      match prev with
      | some (some (Sum.inl _)) => []
      | _ => [sepOf b]
  | _, _, some (some (Sum.inr a)) => [some (some a)]

/-- The rational decoding. -/
def dec2 : List (Option (Bool ⊕ A₀)) → List (Option (Option A₀)) :=
  ctxEval (fun (_ : Unit) (_ : Option (Bool ⊕ A₀)) => ()) () decψ2

lemma dec2_eq (w : List (Option (Bool ⊕ A₀))) :
    dec2 w = ctxAux (decψ2 (A₀ := A₀) ()) none w := rfl

lemma dec2_encLet (l : List A₀) (prev : Option (Option (Bool ⊕ A₀))) :
    ctxAux (decψ2 (A₀ := A₀) ()) prev (encLet l) = letters l := by
  induction l generalizing prev with
  | nil => rfl
  | cons a l ih =>
      rw [encLet, List.map_cons, ← encLet, ctxAux_cons,
        show decψ2 (A₀ := A₀) () prev (some (some (Sum.inr a))) = [some (some a)] from rfl,
        ih (some (some (Sum.inr a)))]
      rfl

lemma dec2_encLet_app (l : List A₀) (Rest : List (Option (Bool ⊕ A₀)))
    (prev : Option (Option (Bool ⊕ A₀))) :
    ctxAux (decψ2 (A₀ := A₀) ()) prev (encLet l ++ none :: Rest)
      = letters l ++ ctxAux (decψ2 (A₀ := A₀) ()) (some none) Rest := by
  induction l generalizing prev with
  | nil =>
      rw [encLet, List.map_nil, List.nil_append, ctxAux_cons,
        show decψ2 (A₀ := A₀) () prev (some none) = [] from rfl]
      rfl
  | cons a l ih =>
      rw [encLet, List.map_cons, ← encLet, List.cons_append, ctxAux_cons,
        show decψ2 (A₀ := A₀) () prev (some (some (Sum.inr a))) = [some (some a)] from rfl,
        ih (some (some (Sum.inr a)))]
      rfl

lemma dec2_mark (b : Bool) (Rest : List (Option (Bool ⊕ A₀))) :
    ctxAux (decψ2 (A₀ := A₀) ()) (some none) (some (Sum.inl b) :: none :: Rest)
      = sepOf b :: ctxAux (decψ2 (A₀ := A₀) ()) (some none) Rest := by
  rw [ctxAux_cons,
    show decψ2 (A₀ := A₀) () (some none) (some (some (Sum.inl b))) = [sepOf b] from rfl,
    ctxAux_cons,
    show decψ2 (A₀ := A₀) () (some (some (Sum.inl b))) (some none) = [] from rfl]
  rfl

lemma dec2_mark_mark (b : Bool) (Rest : List (Option (Bool ⊕ A₀))) :
    ctxAux (decψ2 (A₀ := A₀) ()) (some none)
        (some (Sum.inl b) :: some (Sum.inl b) :: none :: Rest)
      = sepOf b :: ctxAux (decψ2 (A₀ := A₀) ()) (some none) Rest := by
  rw [ctxAux_cons,
    show decψ2 (A₀ := A₀) () (some none) (some (some (Sum.inl b))) = [sepOf b] from rfl,
    ctxAux_cons,
    show decψ2 (A₀ := A₀) () (some (some (Sum.inl b))) (some (some (Sum.inl b))) = []
      from rfl,
    ctxAux_cons,
    show decψ2 (A₀ := A₀) () (some (some (Sum.inl b))) (some none) = [] from rfl]
  rfl

/-! ## The decomposition of a string with two kinds of separators -/

lemma sep_decomp2 (w : List (Option (Option A₀))) :
    (∃ u : List A₀, w = letters u) ∨
      (∃ (u : List A₀) (b : Bool) (w' : List (Option (Option A₀))),
        w = letters u ++ sepOf b :: w' ∧ w'.length < w.length) := by
  induction w with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons x w ih =>
      match x with
      | none => exact Or.inr ⟨[], false, w, rfl, by simp⟩
      | some none => exact Or.inr ⟨[], true, w, rfl, by simp⟩
      | some (some a) =>
          rcases ih with ⟨u, rfl⟩ | ⟨u, b, w', hw, hlen⟩
          · exact Or.inl ⟨a :: u, rfl⟩
          · refine Or.inr ⟨a :: u, b, w', ?_, ?_⟩
            · rw [letters, List.map_cons, ← letters, List.cons_append, ← hw]
            · simpa using Nat.lt_succ_of_lt hlen

/-! ## The map lifting on the encoded string -/

/-- The generic splitting lemma: prefixing a block to a string prefixes it to
the first block. -/
lemma mapLift_prefix_block {A B : Type} (g : List A → List B) (v : List A)
    (w : List (Option A)) :
    ∃ (c : List A) (t : List (Option B)),
      mapLift g w = (g c).map some ++ t ∧
      mapLift g (v.map some ++ w) = (g (v ++ c)).map some ++ t := by
  rcases sep_decomp w with ⟨c, rfl⟩ | ⟨c, w', rfl, _⟩
  · refine ⟨c, [], by simp [mapLift_map_some], ?_⟩
    rw [show v.map some ++ c.map some = (v ++ c).map some by simp, mapLift_map_some]
    simp
  · refine ⟨c, none :: mapLift g w', mapLift_map_some_cons_none g c w', ?_⟩
    rw [← List.append_assoc,
      show v.map some ++ c.map some = (v ++ c).map some by simp,
      mapLift_map_some_cons_none]

/-! ## Map reverse -/

lemma mapLift_rev_encLet (u : List A₀) :
    mapLift List.reverse (encLet u) = encLet u.reverse := by
  have h : encLet u = (u.map (Sum.inr : A₀ → Bool ⊕ A₀)).map some := by
    simp [encLet, List.map_map, Function.comp_def]
  rw [h, mapLift_map_some, encLet]
  simp [List.map_map, Function.comp_def]

lemma mapLift_rev_encLet_app (u : List A₀) (X : List (Option (Bool ⊕ A₀))) :
    mapLift List.reverse (encLet u ++ none :: X)
      = encLet u.reverse ++ none :: mapLift List.reverse X := by
  have h : encLet u = (u.map (Sum.inr : A₀ → Bool ⊕ A₀)).map some := by
    simp [encLet, List.map_map, Function.comp_def]
  rw [h, mapLift_map_some_cons_none]
  congr 1
  simp [encLet, List.map_map, Function.comp_def]

lemma mapLift_rev_mark (b : Bool) (X : List (Option (Bool ⊕ A₀))) :
    mapLift List.reverse (some (Sum.inl b) :: none :: X)
      = some (Sum.inl b) :: none :: mapLift List.reverse X := by
  rw [show (some (Sum.inl b) :: none :: X)
    = [(Sum.inl b : Bool ⊕ A₀)].map some ++ none :: X from rfl,
    mapLift_map_some_cons_none]
  rfl

lemma mapLift_mapReverse_letters (u : List A₀) :
    mapLift (mapReverse A₀) (letters u) = letters u.reverse := by
  have h : letters u = ((u.map (some : A₀ → Option A₀)).map some) := by
    simp [letters, List.map_map, Function.comp_def]
  rw [h, mapLift_map_some, mapReverse, mapLift_map_some, letters]
  simp [List.map_map, Function.comp_def]

lemma mapLift_mapReverse_split (u : List A₀) (b : Bool) (w : List (Option (Option A₀))) :
    mapLift (mapReverse A₀) (letters u ++ sepOf b :: w)
      = letters u.reverse ++ sepOf b :: mapLift (mapReverse A₀) w := by
  cases b with
  | false =>
      have h : letters u = (u.map (some : A₀ → Option A₀)).map some := by
        simp [letters, List.map_map, Function.comp_def]
      rw [show sepOf false = (none : Option (Option A₀)) from rfl, h,
        mapLift_map_some_cons_none, mapReverse, mapLift_map_some]
      congr 1
      simp [letters, List.map_map, Function.comp_def]
  | true =>
      obtain ⟨c, t, h1, h2⟩ :=
        mapLift_prefix_block (mapReverse A₀) (u.map (some : A₀ → Option A₀) ++ [none]) w
      have hw : letters u ++ sepOf true :: w
          = ((u.map (some : A₀ → Option A₀) ++ [none]).map some) ++ w := by
        simp [letters, List.map_map, Function.comp_def, sepOf]
      rw [hw, h2, h1]
      have hg : mapReverse A₀ ((u.map some ++ [none]) ++ c)
          = (u.reverse.map some) ++ none :: mapReverse A₀ c := by
        rw [List.append_assoc, List.singleton_append, mapReverse, mapLift_map_some_cons_none]
      rw [hg]
      simp [letters, List.map_map, Function.comp_def, sepOf]

lemma dec2_mapLift_rev (w : List (Option (Option A₀))) :
    ∀ prev : Option (Option (Bool ⊕ A₀)),
      ctxAux (decψ2 (A₀ := A₀) ()) prev (mapLift List.reverse (homOf encψ w))
        = mapLift (mapReverse A₀) w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
      subst hn
      intro prev
      rcases sep_decomp2 w with ⟨u, rfl⟩ | ⟨u, b, w', rfl, hlen⟩
      · rw [homOf_encψ_letters, mapLift_rev_encLet, dec2_encLet,
          mapLift_mapReverse_letters]
      · rw [homOf_encψ_split, mapLift_rev_encLet_app, mapLift_rev_mark,
          dec2_encLet_app, dec2_mark, ih w'.length hlen w' rfl,
          mapLift_mapReverse_split]

/-! ## Map duplicate -/

lemma mapLift_dup_encLet (u : List A₀) :
    mapLift (fun l : List (Bool ⊕ A₀) => l ++ l) (encLet u) = encLet (u ++ u) := by
  have h : encLet u = (u.map (Sum.inr : A₀ → Bool ⊕ A₀)).map some := by
    simp [encLet, List.map_map, Function.comp_def]
  rw [h, mapLift_map_some, encLet]
  simp [List.map_map, Function.comp_def]

lemma mapLift_dup_encLet_app (u : List A₀) (X : List (Option (Bool ⊕ A₀))) :
    mapLift (fun l : List (Bool ⊕ A₀) => l ++ l) (encLet u ++ none :: X)
      = encLet (u ++ u) ++ none :: mapLift (fun l : List (Bool ⊕ A₀) => l ++ l) X := by
  have h : encLet u = (u.map (Sum.inr : A₀ → Bool ⊕ A₀)).map some := by
    simp [encLet, List.map_map, Function.comp_def]
  rw [h, mapLift_map_some_cons_none]
  congr 1
  simp [encLet, List.map_map, Function.comp_def]

lemma mapLift_dup_mark (b : Bool) (X : List (Option (Bool ⊕ A₀))) :
    mapLift (fun l : List (Bool ⊕ A₀) => l ++ l) (some (Sum.inl b) :: none :: X)
      = some (Sum.inl b) :: some (Sum.inl b) :: none ::
        mapLift (fun l : List (Bool ⊕ A₀) => l ++ l) X := by
  rw [show (some (Sum.inl b) :: none :: X)
    = [(Sum.inl b : Bool ⊕ A₀)].map some ++ none :: X from rfl,
    mapLift_map_some_cons_none]
  rfl

lemma mapLift_mapDuplicate_letters (u : List A₀) :
    mapLift (mapDuplicate A₀) (letters u) = letters (u ++ u) := by
  have h : letters u = ((u.map (some : A₀ → Option A₀)).map some) := by
    simp [letters, List.map_map, Function.comp_def]
  rw [h, mapLift_map_some, mapDuplicate, mapLift_map_some, letters]
  simp [List.map_map, Function.comp_def]

lemma mapLift_mapDuplicate_split (u : List A₀) (b : Bool) (w : List (Option (Option A₀))) :
    mapLift (mapDuplicate A₀) (letters u ++ sepOf b :: w)
      = letters (u ++ u) ++ sepOf b :: mapLift (mapDuplicate A₀) w := by
  cases b with
  | false =>
      have h : letters u = (u.map (some : A₀ → Option A₀)).map some := by
        simp [letters, List.map_map, Function.comp_def]
      rw [show sepOf false = (none : Option (Option A₀)) from rfl, h,
        mapLift_map_some_cons_none, mapDuplicate, mapLift_map_some]
      congr 1
      simp [letters, List.map_map, Function.comp_def]
  | true =>
      obtain ⟨c, t, h1, h2⟩ :=
        mapLift_prefix_block (mapDuplicate A₀) (u.map (some : A₀ → Option A₀) ++ [none]) w
      have hw : letters u ++ sepOf true :: w
          = ((u.map (some : A₀ → Option A₀) ++ [none]).map some) ++ w := by
        simp [letters, List.map_map, Function.comp_def, sepOf]
      rw [hw, h2, h1]
      have hg : mapDuplicate A₀ ((u.map some ++ [none]) ++ c)
          = ((u ++ u).map some) ++ none :: mapDuplicate A₀ c := by
        rw [List.append_assoc, List.singleton_append, mapDuplicate,
          mapLift_map_some_cons_none]
      rw [hg]
      simp [letters, List.map_map, Function.comp_def, sepOf]

lemma dec2_mapLift_dup (w : List (Option (Option A₀))) :
    ∀ prev : Option (Option (Bool ⊕ A₀)),
      ctxAux (decψ2 (A₀ := A₀) ()) prev
          (mapLift (fun l : List (Bool ⊕ A₀) => l ++ l) (homOf encψ w))
        = mapLift (mapDuplicate A₀) w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
      subst hn
      intro prev
      rcases sep_decomp2 w with ⟨u, rfl⟩ | ⟨u, b, w', rfl, hlen⟩
      · rw [homOf_encψ_letters, mapLift_dup_encLet, dec2_encLet,
          mapLift_mapDuplicate_letters]
      · rw [homOf_encψ_split, mapLift_dup_encLet_app, mapLift_dup_mark,
          dec2_encLet_app, dec2_mark_mark, ih w'.length hlen w' rfl,
          mapLift_mapDuplicate_split]

/-! ## Regularity -/

lemma isRationalFun_encψ [Finite A₀] :
    IsRationalFun (homOf (encψ : Option (Option A₀) → List (Option (Bool ⊕ A₀)))) :=
  isRationalFun_homOf _

lemma isRationalFun_dec2 [Finite A₀] :
    IsRationalFun (dec2 : List (Option (Bool ⊕ A₀)) → List (Option (Option A₀))) :=
  isRationalFun_ctxEval _ _ _

end MapLiftPrime

/-- The map lifting of map reverse is regular. -/
theorem isRegularFun_mapLift_mapReverse (A₀ : Type) [Finite A₀] :
    IsRegularFun (mapLift (mapReverse A₀)) := by
  refine ((IsRegularFun.of_rational MapLiftPrime.isRationalFun_encψ).comp
    (isRegularFun_mapReverse (Bool ⊕ A₀))).comp'
    (IsRegularFun.of_rational MapLiftPrime.isRationalFun_dec2) (fun w => ?_)
  exact (MapLiftPrime.dec2_mapLift_rev w none).symm

/-- The map lifting of map duplicate is regular. -/
theorem isRegularFun_mapLift_mapDuplicate (A₀ : Type) [Finite A₀] :
    IsRegularFun (mapLift (mapDuplicate A₀)) := by
  refine ((IsRegularFun.of_rational MapLiftPrime.isRationalFun_encψ).comp
    (isRegularFun_mapDuplicate (Bool ⊕ A₀))).comp'
    (IsRegularFun.of_rational MapLiftPrime.isRationalFun_dec2) (fun w => ?_)
  exact (MapLiftPrime.dec2_mapLift_dup w none).symm

end Lax916827Proofs.Transducers
