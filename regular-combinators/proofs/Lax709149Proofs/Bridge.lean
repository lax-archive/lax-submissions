import Lax709149.Types
import Lax709149.RegularUnderRepresentation
import Lax709149.RegularTerms
import Lax916827Proofs.Bridge
import Lax709149Proofs.Source.PartC.CombStatements

/-!
The bridge between the concept package of Part C §5 and the ported source
development. The concept's types, eight-letter alphabet, string representation
and regular terms are separate copies of the source's, so each is related to
its counterpart by an explicit bijection: `toSrcTy` on types, `eltEquiv` on the
elements of a type (by recursion on the type), `symEquiv` on the alphabet, and
`toSrcTerm` on terms, with `repr_toSrc` and `eval_toSrcTerm` showing that the
representation and the semantics commute with them. Regularity under string
representation is then equivalent on the two sides (`isRegularUnderRepr_iff`):
a regular string function is conjugated by the letter-to-letter renaming of the
alphabets, which is rational, and Part C §1–3's bridge moves the regular
functions themselves across.
-/

namespace Lax709149Proofs.Bridge

open Lax765601Proofs Lax132576Proofs Lax916827Proofs
open Lax132576.RationalFunctions Lax916827.RegularFunctions
open Lax709149.Types Lax709149.RegularUnderRepresentation Lax709149.RegularTerms

/-! ## Types and their elements -/

/-- A concept type as a source type. -/
def toSrcTy : Ty → Transducers.Ty
  | .one => .one
  | .prod A B => .prod (toSrcTy A) (toSrcTy B)
  | .sum A B => .sum (toSrcTy A) (toSrcTy B)
  | .list A => .list (toSrcTy A)

/-- A source type as a concept type. -/
def ofSrcTy : Transducers.Ty → Ty
  | .one => .one
  | .prod A B => .prod (ofSrcTy A) (ofSrcTy B)
  | .sum A B => .sum (ofSrcTy A) (ofSrcTy B)
  | .list A => .list (ofSrcTy A)

@[simp] lemma ofSrcTy_toSrcTy : ∀ A : Ty, ofSrcTy (toSrcTy A) = A
  | .one => rfl
  | .prod A B => by simp [toSrcTy, ofSrcTy, ofSrcTy_toSrcTy A, ofSrcTy_toSrcTy B]
  | .sum A B => by simp [toSrcTy, ofSrcTy, ofSrcTy_toSrcTy A, ofSrcTy_toSrcTy B]
  | .list A => by simp [toSrcTy, ofSrcTy, ofSrcTy_toSrcTy A]

@[simp] lemma toSrcTy_ofSrcTy : ∀ A : Transducers.Ty, toSrcTy (ofSrcTy A) = A
  | .one => rfl
  | .prod A B => by simp [toSrcTy, ofSrcTy, toSrcTy_ofSrcTy A, toSrcTy_ofSrcTy B]
  | .sum A B => by simp [toSrcTy, ofSrcTy, toSrcTy_ofSrcTy A, toSrcTy_ofSrcTy B]
  | .list A => by simp [toSrcTy, ofSrcTy, toSrcTy_ofSrcTy A]

/-- The bijection between the concept's and the source's types. -/
def tyEquiv : Ty ≃ Transducers.Ty where
  toFun := toSrcTy
  invFun := ofSrcTy
  left_inv := ofSrcTy_toSrcTy
  right_inv := toSrcTy_ofSrcTy

/-- The bijection between the elements of a concept type and the elements of its
source counterpart: the identity on the unit type, and the product, sum and list of
the bijections of the constituents. -/
def eltEquiv : (A : Ty) → A.Elt ≃ (toSrcTy A).Elt
  | .one => Equiv.refl Unit
  | .prod A B => (eltEquiv A).prodCongr (eltEquiv B)
  | .sum A B => (eltEquiv A).sumCongr (eltEquiv B)
  | .list A => Equiv.listEquivOfEquiv (eltEquiv A)

@[simp] lemma eltEquiv_prod (A B : Ty) (a : A.Elt) (b : B.Elt) :
    eltEquiv (.prod A B) (a, b) = (eltEquiv A a, eltEquiv B b) := rfl

@[simp] lemma eltEquiv_inl (A B : Ty) (a : A.Elt) :
    eltEquiv (.sum A B) (Sum.inl a) = Sum.inl (eltEquiv A a) := rfl

@[simp] lemma eltEquiv_inr (A B : Ty) (b : B.Elt) :
    eltEquiv (.sum A B) (Sum.inr b) = Sum.inr (eltEquiv B b) := rfl

@[simp] lemma eltEquiv_list (A : Ty) (l : List A.Elt) :
    eltEquiv (.list A) l = l.map (eltEquiv A) := rfl

/-! ## The alphabet -/

/-- A concept letter as a source letter. -/
def toSrcSym : Sym8 → Transducers.Sym8
  | .lpar => .lpar
  | .rpar => .rpar
  | .lbrack => .lbrack
  | .rbrack => .rbrack
  | .comma => .comma
  | .one => .one
  | .left => .left
  | .right => .right

/-- A source letter as a concept letter. -/
def ofSrcSym : Transducers.Sym8 → Sym8
  | .lpar => .lpar
  | .rpar => .rpar
  | .lbrack => .lbrack
  | .rbrack => .rbrack
  | .comma => .comma
  | .one => .one
  | .left => .left
  | .right => .right

@[simp] lemma ofSrcSym_toSrcSym (x : Sym8) : ofSrcSym (toSrcSym x) = x := by cases x <;> rfl

@[simp] lemma toSrcSym_ofSrcSym (x : Transducers.Sym8) : toSrcSym (ofSrcSym x) = x := by
  cases x <;> rfl

/-- The bijection between the two copies of the eight-letter alphabet. -/
def symEquiv : Sym8 ≃ Transducers.Sym8 where
  toFun := toSrcSym
  invFun := ofSrcSym
  left_inv := ofSrcSym_toSrcSym
  right_inv := toSrcSym_ofSrcSym

lemma map_ofSrcSym_map_toSrcSym (w : List Sym8) : (w.map toSrcSym).map ofSrcSym = w := by
  rw [List.map_map]
  exact (List.map_congr_left fun x _ => ofSrcSym_toSrcSym x).trans (List.map_id w)

lemma map_toSrcSym_map_ofSrcSym (w : List Transducers.Sym8) :
    (w.map ofSrcSym).map toSrcSym = w := by
  rw [List.map_map]
  exact (List.map_congr_left fun x _ => toSrcSym_ofSrcSym x).trans (List.map_id w)

/-! ## The string representation -/

lemma joinSep_toSrc : ∀ l : List (List Sym8),
    (joinSep l).map toSrcSym = Transducers.joinSep (l.map (List.map toSrcSym))
  | [] => rfl
  | [x] => rfl
  | x :: y :: ys => by
      show (x ++ Sym8.comma :: joinSep (y :: ys)).map toSrcSym = _
      rw [List.map_append, List.map_cons, joinSep_toSrc (y :: ys)]
      rfl

/-- The representation commutes with the bijections of elements and letters. -/
lemma repr_toSrc : ∀ (A : Ty) (a : A.Elt),
    (A.repr a).map toSrcSym = (toSrcTy A).repr (eltEquiv A a)
  | .one, _ => rfl
  | .prod A B, (a, b) => by
      show (Sym8.lpar :: (A.repr a ++ Sym8.comma :: (B.repr b ++ [Sym8.rpar]))).map toSrcSym
        = (Transducers.Ty.prod (toSrcTy A) (toSrcTy B)).repr (eltEquiv A a, eltEquiv B b)
      rw [Transducers.Ty.repr_prod, List.map_cons, List.map_append, List.map_cons, List.map_append,
        repr_toSrc A a, repr_toSrc B b]
      rfl
  | .sum A B, Sum.inl a => by
      show (Sym8.left :: A.repr a).map toSrcSym
        = (Transducers.Ty.sum (toSrcTy A) (toSrcTy B)).repr (Sum.inl (eltEquiv A a))
      rw [Transducers.Ty.repr_inl, List.map_cons, repr_toSrc A a]
      rfl
  | .sum A B, Sum.inr b => by
      show (Sym8.right :: B.repr b).map toSrcSym
        = (Transducers.Ty.sum (toSrcTy A) (toSrcTy B)).repr (Sum.inr (eltEquiv B b))
      rw [Transducers.Ty.repr_inr, List.map_cons, repr_toSrc B b]
      rfl
  | .list A, l => by
      show (Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack])).map toSrcSym
        = (Transducers.Ty.list (toSrcTy A)).repr (l.map (eltEquiv A))
      rw [Transducers.Ty.repr_list, List.map_cons, List.map_append, joinSep_toSrc, List.map_map,
        List.map_map]
      have : (List.map toSrcSym ∘ A.repr) = ((toSrcTy A).repr ∘ eltEquiv A) :=
        funext fun a => repr_toSrc A a
      rw [this]
      rfl

/-! ## Regular terms -/

/-- The auxiliary functions of the atomic terms commute with a renaming of the
entries. -/
lemma splitList_map {A B A' B' : Type} (f : A → A') (g : B → B') : ∀ l : List (A ⊕ B),
    Transducers.splitList (l.map (Sum.map f g))
      = ((splitList l).1.map f, (splitList l).2.map (Prod.map g (List.map f)))
  | [] => rfl
  | Sum.inl a :: l => by
      rw [List.map_cons, Sum.map_inl, Transducers.splitList_inl, splitList_map f g l]
      rfl
  | Sum.inr b :: l => by
      rw [List.map_cons, Sum.map_inr, Transducers.splitList_inr, splitList_map f g l]
      rfl

lemma scanl_mul_map {M N : Type} [Group M] (e : M ≃ N) (l : List M) (c : M) :
    letI : Group N := e.symm.group
    (l.map e).scanl (· * ·) (e c) = (l.scanl (· * ·) c).map e := by
  letI : Group N := e.symm.group
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.scanl_cons, List.scanl_cons, List.map_cons, ← ih (c * a)]
      congr 2
      show e (e.symm (e c) * e.symm (e a)) = e (c * a)
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

lemma prefixProd_map {M N : Type} [Group M] (e : M ≃ N) (l : List M) :
    letI : Group N := e.symm.group
    Transducers.prefixProd (l.map e) = (prefixProd l).map e := by
  letI : Group N := e.symm.group
  show ((l.map e).scanl (· * ·) 1).tail = ((l.scanl (· * ·) 1).tail).map e
  rw [show (1 : N) = e 1 from rfl, scanl_mul_map, List.map_tail]

/-- A concept term as a source term: the same constructor, with the types
transported by `toSrcTy` and the group of a prefix-multiplication term
transported along `eltEquiv`. -/
def toSrcTerm : {A B : Ty} → RegTerm A B → Transducers.RegTerm (toSrcTy A) (toSrcTy B)
  | _, _, .id A => .id (toSrcTy A)
  | _, _, .fst A B => .fst (toSrcTy A) (toSrcTy B)
  | _, _, .snd A B => .snd (toSrcTy A) (toSrcTy B)
  | _, _, .inl A B => .inl (toSrcTy A) (toSrcTy B)
  | _, _, .inr A B => .inr (toSrcTy A) (toSrcTy B)
  | _, _, .distr A B C => .distr (toSrcTy A) (toSrcTy B) (toSrcTy C)
  | _, _, .cons A => .cons (toSrcTy A)
  | _, _, .uncons A => .uncons (toSrcTy A)
  | _, _, .reverse A => .reverse (toSrcTy A)
  | _, _, .concat A => .concat (toSrcTy A)
  | _, _, .split A B => .split (toSrcTy A) (toSrcTy B)
  | _, _, .pref G grp hfin =>
      .pref (toSrcTy G) (@Equiv.group _ _ (eltEquiv G).symm grp)
        (@Finite.of_equiv _ _ hfin (eltEquiv G))
  | _, _, .comp s t => .comp (toSrcTerm s) (toSrcTerm t)
  | _, _, .pair s t => .pair (toSrcTerm s) (toSrcTerm t)
  | _, _, .copair s t => .copair (toSrcTerm s) (toSrcTerm t)
  | _, _, .map t => .map (toSrcTerm t)

/-- The semantics commutes with `toSrcTerm` and `eltEquiv`. -/
lemma eval_toSrcTerm : ∀ {A B : Ty} (t : RegTerm A B) (a : A.Elt),
    (toSrcTerm t).eval (eltEquiv A a) = eltEquiv B (t.eval a)
  | _, _, .id _, _ => rfl
  | _, _, .fst _ _, (_, _) => rfl
  | _, _, .snd _ _, (_, _) => rfl
  | _, _, .inl _ _, _ => rfl
  | _, _, .inr _ _, _ => rfl
  | _, _, .distr _ _ _, (_, Sum.inl _) => rfl
  | _, _, .distr _ _ _, (_, Sum.inr _) => rfl
  | _, _, .cons _, Sum.inl _ => rfl
  | _, _, .cons _, Sum.inr (_, _) => rfl
  | _, _, .uncons _, [] => rfl
  | _, _, .uncons _, _ :: _ => rfl
  | _, _, .reverse A, l => by
      show (l.map (eltEquiv A)).reverse = l.reverse.map (eltEquiv A)
      exact List.map_reverse.symm
  | _, _, .concat A, l => by
      show (l.map (List.map (eltEquiv A))).flatten = l.flatten.map (eltEquiv A)
      exact List.map_flatten.symm
  | _, _, .split A B, l => by
      show Transducers.splitList (l.map (Sum.map (eltEquiv A) (eltEquiv B)))
        = ((splitList l).1.map (eltEquiv A),
            (splitList l).2.map (Prod.map (eltEquiv B) (List.map (eltEquiv A))))
      exact splitList_map _ _ l
  | _, _, .pref G grp _, l => by
      letI := grp
      exact prefixProd_map (eltEquiv G) l
  | _, _, .comp s t, a => by
      show (toSrcTerm t).eval ((toSrcTerm s).eval (eltEquiv _ a)) = eltEquiv _ (t.eval (s.eval a))
      rw [eval_toSrcTerm s a, eval_toSrcTerm t]
  | _, _, .pair s t, a => by
      show ((toSrcTerm s).eval (eltEquiv _ a), (toSrcTerm t).eval (eltEquiv _ a))
        = (eltEquiv _ (s.eval a), eltEquiv _ (t.eval a))
      rw [eval_toSrcTerm s a, eval_toSrcTerm t a]
  | _, _, .copair s _, Sum.inl a => eval_toSrcTerm s a
  | _, _, .copair _ t, Sum.inr b => eval_toSrcTerm t b
  | _, _, .map t, l => by
      show (l.map (eltEquiv _)).map (toSrcTerm t).eval = (l.map t.eval).map (eltEquiv _)
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun a _ => eval_toSrcTerm t a

/-- A function defined by a concept term is, transported along `eltEquiv`,
defined by a source term. -/
lemma isRegularTermFun_toSrc {A B : Ty} {f : A.Elt → B.Elt} (hf : IsRegularTermFun f) :
    Transducers.IsRegularTermFun (fun x => eltEquiv B (f ((eltEquiv A).symm x))) := by
  obtain ⟨t, rfl⟩ := hf
  refine ⟨toSrcTerm t, funext fun x => ?_⟩
  rw [← eval_toSrcTerm t ((eltEquiv A).symm x), Equiv.apply_symm_apply]

/-! ## Regular under string representation -/

/-- A regular function conjugated by letter-to-letter renamings of its alphabets is
regular (source side). -/
lemma isRegularFun_conj {A B A' B' : Type} [Finite A] [Finite B] [Finite A'] [Finite B']
    (e : A' → A) (e' : B → B') {f : List A → List B} (hf : Transducers.IsRegularFun f) :
    Transducers.IsRegularFun (fun w : List A' => (f (w.map e)).map e') :=
  ((Transducers.isRegularFun_map e).comp hf).comp' (Transducers.isRegularFun_map e')
    (fun _ => rfl)

/-- Regularity under string representation is the same on both sides, the function
transported along `eltEquiv`. -/
lemma isRegularUnderRepr_iff {A B : Ty} (f : A.Elt → B.Elt) :
    IsRegularUnderRepr f
      ↔ Transducers.IsRegularUnderRepr (fun x => eltEquiv B (f ((eltEquiv A).symm x))) := by
  constructor
  · rintro ⟨f', hf', hfe⟩
    refine ⟨fun w => (f' (w.map ofSrcSym)).map toSrcSym,
      isRegularFun_conj _ _ ((Lax916827Proofs.Bridge.isRegularFun_iff f').1 hf'), fun x => ?_⟩
    obtain ⟨a, rfl⟩ := (eltEquiv A).surjective x
    show (f' (((toSrcTy A).repr (eltEquiv A a)).map ofSrcSym)).map toSrcSym = _
    rw [← repr_toSrc A a, map_ofSrcSym_map_toSrcSym, hfe a, repr_toSrc B (f a)]
    simp only [Equiv.symm_apply_apply]
  · rintro ⟨f', hf', hfe⟩
    refine ⟨fun w => (f' (w.map toSrcSym)).map ofSrcSym,
      (Lax916827Proofs.Bridge.isRegularFun_iff _).2 (isRegularFun_conj _ _ hf'), fun a => ?_⟩
    show (f' ((A.repr a).map toSrcSym)).map ofSrcSym = _
    rw [repr_toSrc A a, hfe (eltEquiv A a)]
    simp only [Equiv.symm_apply_apply]
    rw [← repr_toSrc B (f a), map_ofSrcSym_map_toSrcSym]

/-- The same for rationality under string representation. -/
lemma isRationalUnderRepr_iff {A B : Ty} (f : A.Elt → B.Elt) :
    IsRationalUnderRepr f
      ↔ Transducers.IsRationalUnderRepr (fun x => eltEquiv B (f ((eltEquiv A).symm x))) := by
  constructor
  · rintro ⟨f', hf', hfe⟩
    refine ⟨fun w => (f' (w.map ofSrcSym)).map toSrcSym,
      Transducers.isRationalFun_comp
        (Transducers.isRationalFun_comp (Transducers.isRationalFun_map ofSrcSym)
          ((Lax132576Proofs.Bridge.isRationalFun_iff f').1 hf'))
        (Transducers.isRationalFun_map toSrcSym), fun x => ?_⟩
    obtain ⟨a, rfl⟩ := (eltEquiv A).surjective x
    show (f' (((toSrcTy A).repr (eltEquiv A a)).map ofSrcSym)).map toSrcSym = _
    rw [← repr_toSrc A a, map_ofSrcSym_map_toSrcSym, hfe a, repr_toSrc B (f a)]
    simp only [Equiv.symm_apply_apply]
  · rintro ⟨f', hf', hfe⟩
    refine ⟨fun w => (f' (w.map toSrcSym)).map ofSrcSym,
      (Lax132576Proofs.Bridge.isRationalFun_iff _).2
        (Transducers.isRationalFun_comp
          (Transducers.isRationalFun_comp (Transducers.isRationalFun_map toSrcSym) hf')
          (Transducers.isRationalFun_map ofSrcSym)), fun a => ?_⟩
    show (f' ((A.repr a).map toSrcSym)).map ofSrcSym = _
    rw [repr_toSrc A a, hfe (eltEquiv A a)]
    simp only [Equiv.symm_apply_apply]
    rw [← repr_toSrc B (f a), map_ofSrcSym_map_toSrcSym]

end Lax709149Proofs.Bridge
