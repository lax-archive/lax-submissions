/-
The two remaining base cases of the marked sum (see
`RequestProject/PartC/SumShape.lean`), used in the proof of Claim `claim:conditional` of
*Transducers* (M. Bojańczyk): the marked sum of map reverse (resp. map
duplicate) with the identity.

The construction is the same in both cases.  The marked input is first encoded,
by a rational function, into a string over the alphabet `Alph + 1`, in such a
way that

* the marker letter forms a block of its own,
* in the left case the blocks after the marker are exactly the blocks of the
  input word,
* in the right case every letter of the second alphabet forms a block of its
  own, so that reversing the blocks does nothing and duplicating them merely
  repeats each letter twice,
* an input that is not a marked string is replaced by a fixed two-block string.

Then map reverse (resp. map duplicate) is applied over the bigger alphabet, and
a second rational function decodes the result: it deletes the separators that
were introduced next to a marker or next to a letter of the second alphabet, and
it deletes a marker (resp. a letter of the second alphabet) that is immediately
preceded by another one, which undoes the duplication of the one-letter blocks.

The file ends with the induction over the composition tree of a regular
function, which gives the marked sum of two arbitrary regular functions.
-/
import Lax916827Proofs.Source.PartC.SumShape
import Lax916827Proofs.Source.PartC.MapLiftAux
import Lax916827Proofs.Source.PartC.ContAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SumPrime

variable {A₀ A₂ : Type}

/-- The marked alphabet of the base case: a marker, a letter of `A₁ = A₀ + 1`,
or a letter of `A₂`. -/
abbrev Alph (A₀ A₂ : Type) := Bool ⊕ Option A₀ ⊕ A₂

/-- The embedding of `A₀` into the marked alphabet. -/
def iota (A₂ : Type) {A₀ : Type} (a : A₀) : Alph A₀ A₂ := Sum.inr (Sum.inl (some a))

/-! ## The encoding -/

/-- The letter-by-letter encoding: the marker and the letters of `A₂` become
blocks of their own, the letters of `A₁` are copied. -/
def encφ : Alph A₀ A₂ → List (Option (Alph A₀ A₂))
  | Sum.inl b => [some (Sum.inl b), none]
  | Sum.inr (Sum.inl none) => [none]
  | Sum.inr (Sum.inl (some a)) => [some (Sum.inr (Sum.inl (some a)))]
  | Sum.inr (Sum.inr c) => [some (Sum.inr (Sum.inr c)), none]

lemma homOf_cons_eq {A B : Type} (φ : A → List B) (a : A) (l : List A) :
    homOf φ (a :: l) = φ a ++ homOf φ l := by simp [homOf]

/-- The encoding of the body of a left marked string. -/
lemma homOf_encφ_left (u : List (Option A₀)) :
    homOf encφ (u.map (fun a : Option A₀ => (Sum.inr (Sum.inl a) : Alph A₀ A₂)))
      = u.map (Option.map (iota A₂)) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      cases x with
      | none => rw [List.map_cons, homOf_cons_eq, ih]; rfl
      | some a => rw [List.map_cons, homOf_cons_eq, ih]; rfl

/-- The encoding of a left marked string. -/
lemma homOf_encφ_mkL (u : List (Option A₀)) :
    homOf encφ (mkL A₂ u)
      = [(Sum.inl false : Alph A₀ A₂)].map some ++ none :: u.map (Option.map (iota A₂)) := by
  rw [mkL, homOf_cons_eq, homOf_encφ_left]
  rfl

/-- The encoding of the body of a right marked string. -/
def encR (A₀ : Type) : List A₂ → List (Option (Alph A₀ A₂))
  | [] => []
  | c :: v => some (Sum.inr (Sum.inr c)) :: none :: encR A₀ v

/-- The body of a right marked string after duplication. -/
def encR2 (A₀ : Type) : List A₂ → List (Option (Alph A₀ A₂))
  | [] => []
  | c :: v =>
      some (Sum.inr (Sum.inr c)) :: some (Sum.inr (Sum.inr c)) :: none :: encR2 A₀ v

lemma homOf_encφ_right (v : List A₂) :
    homOf encφ (v.map (fun c : A₂ => (Sum.inr (Sum.inr c) : Alph A₀ A₂))) = encR A₀ v := by
  induction v with
  | nil => rfl
  | cons c v ih => rw [List.map_cons, homOf_cons_eq, ih]; rfl

lemma homOf_encφ_mkR (v : List A₂) :
    homOf encφ (mkR (Option A₀) v)
      = [(Sum.inl true : Alph A₀ A₂)].map some ++ none :: encR A₀ v := by
  rw [mkR, homOf_cons_eq, homOf_encφ_right]
  rfl

/-! ## The preprocessing -/

/-- The string that a non-marked input is replaced by. -/
def badStr (A₀ A₂ : Type) : List (Option (Alph A₀ A₂)) :=
  [(Sum.inl false : Alph A₀ A₂)].map some ++ none :: [some (Sum.inl true)]

/-- The rational preprocessing. -/
def prep (w : List (Alph A₀ A₂)) : List (Option (Alph A₀ A₂)) :=
  if shp w = Shp.inL ∨ shp w = Shp.inR then homOf encφ w else badStr A₀ A₂

lemma prep_mkL (u : List (Option A₀)) :
    prep (mkL A₂ u)
      = [(Sum.inl false : Alph A₀ A₂)].map some ++ none :: u.map (Option.map (iota A₂)) := by
  rw [prep, if_pos (Or.inl (shp_mkL u)), homOf_encφ_mkL]

lemma prep_mkR (v : List A₂) :
    prep (A₀ := A₀) (mkR (Option A₀) v)
      = [(Sum.inl true : Alph A₀ A₂)].map some ++ none :: encR A₀ v := by
  rw [prep, if_pos (Or.inr (shp_mkR v)), homOf_encφ_mkR]

lemma prep_bad {w : List (Alph A₀ A₂)} (h₁ : ∀ u : List (Option A₀), w ≠ mkL A₂ u)
    (h₂ : ∀ v : List A₂, w ≠ mkR (Option A₀) v) : prep w = badStr A₀ A₂ := by
  have hL : shp w ≠ Shp.inL := fun h => by
    obtain ⟨u, hu⟩ := (shp_eq_inL_iff w).1 h; exact h₁ u hu
  have hR : shp w ≠ Shp.inR := fun h => by
    obtain ⟨u, hu⟩ := (shp_eq_inR_iff w).1 h; exact h₂ u hu
  rw [prep, if_neg (by tauto)]

/-! ## The decoding -/

/-- The output of the decoding at the letter `next`, whose predecessor is
`prev`. -/
def decψ : Unit → Option (Option (Alph A₀ A₂)) → Option (Option (Alph A₀ A₂)) →
    List (Alph A₀ A₂)
  | _, _, none => []
  | _, prev, some (some (Sum.inl b)) =>
      match prev with
      | some (some (Sum.inl _)) => []
      | _ => [Sum.inl b]
  | _, _, some (some (Sum.inr (Sum.inl x))) => [Sum.inr (Sum.inl x)]
  | _, prev, some (some (Sum.inr (Sum.inr c))) =>
      match prev with
      | some (some (Sum.inr (Sum.inr _))) => []
      | _ => [Sum.inr (Sum.inr c)]
  | _, prev, some none =>
      match prev with
      | some (some (Sum.inl _)) => []
      | some (some (Sum.inr (Sum.inr _))) => []
      | _ => [Sum.inr (Sum.inl none)]

/-- The rational decoding. -/
def dec : List (Option (Alph A₀ A₂)) → List (Alph A₀ A₂) :=
  ctxEval (fun (_ : Unit) (_ : Option (Alph A₀ A₂)) => ()) () decψ

lemma dec_eq (w : List (Option (Alph A₀ A₂))) : dec w = ctxAux (decψ (A₀ := A₀) (A₂ := A₂) ()) none w :=
  rfl

/-- A predecessor which is neither a marker nor a letter of `A₂`; after such a
letter the decoding keeps the separators. -/
def GoodPrev : Option (Option (Alph A₀ A₂)) → Prop
  | some (some (Sum.inl _)) => False
  | some (some (Sum.inr (Sum.inr _))) => False
  | _ => True

lemma decψ_sep {prev : Option (Option (Alph A₀ A₂))} (h : GoodPrev prev) :
    decψ () prev (some none) = [Sum.inr (Sum.inl none)] := by
  match prev with
  | none => rfl
  | some none => rfl
  | some (some (Sum.inl _)) => exact h.elim
  | some (some (Sum.inr (Sum.inl _))) => rfl
  | some (some (Sum.inr (Sum.inr _))) => exact h.elim

/-- The decoding of the body of a left marked string. -/
lemma dec_body_left (u : List (Option A₀)) :
    ∀ prev : Option (Option (Alph A₀ A₂)), GoodPrev prev →
      ctxAux (decψ (A₀ := A₀) (A₂ := A₂) ()) prev (u.map (Option.map (iota A₂)))
        = u.map (fun x : Option A₀ => (Sum.inr (Sum.inl x) : Alph A₀ A₂)) := by
  induction u with
  | nil => intro prev _; rfl
  | cons x u ih =>
      intro prev hprev
      cases x with
      | none =>
          rw [List.map_cons, show Option.map (iota A₂) (none : Option A₀) = none from rfl,
            ctxAux_cons, decψ_sep hprev, ih (some none) trivial]
          rfl
      | some a =>
          rw [List.map_cons,
            show Option.map (iota A₂) (some a) = some (iota A₂ a) from rfl, ctxAux_cons,
            show decψ (A₀ := A₀) (A₂ := A₂) () prev (some (some (iota A₂ a)))
              = [Sum.inr (Sum.inl (some a))] from rfl,
            ih (some (some (iota A₂ a))) trivial]
          rfl

/-- The decoding of the body of a right marked string. -/
lemma dec_body_right (v : List A₂) :
    ctxAux (decψ (A₀ := A₀) (A₂ := A₂) ()) (some none) (encR A₀ v)
      = v.map (fun c : A₂ => (Sum.inr (Sum.inr c) : Alph A₀ A₂)) := by
  induction v with
  | nil => rfl
  | cons c v ih =>
      rw [show encR A₀ (c :: v)
        = some (Sum.inr (Sum.inr c)) :: none :: encR A₀ v from rfl, ctxAux_cons,
        show decψ (A₀ := A₀) (A₂ := A₂) () (some none)
            (some (some (Sum.inr (Sum.inr c)))) = [Sum.inr (Sum.inr c)] from rfl,
        ctxAux_cons,
        show decψ (A₀ := A₀) (A₂ := A₂) () (some (some (Sum.inr (Sum.inr c)))) (some none)
            = [] from rfl, ih]
      rfl

/-- The decoding of the body of a right marked string, after duplication. -/
lemma dec_body_right2 (v : List A₂) :
    ctxAux (decψ (A₀ := A₀) (A₂ := A₂) ()) (some none) (encR2 A₀ v)
      = v.map (fun c : A₂ => (Sum.inr (Sum.inr c) : Alph A₀ A₂)) := by
  induction v with
  | nil => rfl
  | cons c v ih =>
      rw [show encR2 A₀ (c :: v)
        = some (Sum.inr (Sum.inr c)) :: some (Sum.inr (Sum.inr c)) :: none :: encR2 A₀ v
        from rfl, ctxAux_cons,
        show decψ (A₀ := A₀) (A₂ := A₂) () (some none)
            (some (some (Sum.inr (Sum.inr c)))) = [Sum.inr (Sum.inr c)] from rfl,
        ctxAux_cons,
        show decψ (A₀ := A₀) (A₂ := A₂) () (some (some (Sum.inr (Sum.inr c))))
            (some (some (Sum.inr (Sum.inr c)))) = [] from rfl,
        ctxAux_cons,
        show decψ (A₀ := A₀) (A₂ := A₂) () (some (some (Sum.inr (Sum.inr c)))) (some none)
            = [] from rfl, ih]
      rfl

/-! ## The two functions -/

/-- The marked sum of map reverse and the identity. -/
def frev (w : List (Alph A₀ A₂)) : List (Alph A₀ A₂) :=
  dec (mapReverse (Alph A₀ A₂) (prep w))

/-- The marked sum of map duplicate and the identity. -/
def fdup (w : List (Alph A₀ A₂)) : List (Alph A₀ A₂) :=
  dec (mapDuplicate (Alph A₀ A₂) (prep w))

/-- The value of both functions on the inputs that are not marked strings. -/
def botv (A₀ A₂ : Type) : List (Alph A₀ A₂) := [Sum.inl false, Sum.inl true]

lemma botv_ne_mkL (v : List (Option A₀)) : botv A₀ A₂ ≠ mkL A₂ v := by
  cases v with
  | nil => simp [botv, mkL]
  | cons a v => simp [botv, mkL]

lemma botv_ne_mkR (v : List A₂) : botv A₀ A₂ ≠ mkR (Option A₀) v := by
  cases v with
  | nil => simp [botv, mkR]
  | cons a v => simp [botv, mkR]

/-- Decoding a marked string: the marker is kept and the separator that follows
it is deleted. -/
lemma dec_mark_sep (b : Bool) (Y : List (Option (Alph A₀ A₂))) :
    dec (some (Sum.inl b) :: none :: Y)
      = Sum.inl b :: ctxAux (decψ (A₀ := A₀) (A₂ := A₂) ()) (some none) Y := by
  rw [dec_eq, ctxAux_cons, ctxAux_cons]
  rfl

/-- Decoding a marked string after duplication: the marker is kept once and the
separator that follows it is deleted. -/
lemma dec_mark_mark_sep (b : Bool) (Y : List (Option (Alph A₀ A₂))) :
    dec (some (Sum.inl b) :: some (Sum.inl b) :: none :: Y)
      = Sum.inl b :: ctxAux (decψ (A₀ := A₀) (A₂ := A₂) ()) (some none) Y := by
  rw [dec_eq, ctxAux_cons, ctxAux_cons, ctxAux_cons]
  rfl

/-! ### Map reverse -/

lemma mapLift_rev_encR (v : List A₂) :
    mapLift List.reverse (encR A₀ v) = (encR A₀ v : List (Option (Alph A₀ A₂))) := by
  induction v with
  | nil => simpa using mapLift_map_some (List.reverse) ([] : List (Alph A₀ A₂))
  | cons c v ih =>
      have h : encR A₀ (c :: v)
          = [(Sum.inr (Sum.inr c) : Alph A₀ A₂)].map some ++ none :: encR A₀ v := rfl
      rw [h, mapLift_map_some_cons_none, ih]
      rfl

lemma frev_mkL (u : List (Option A₀)) :
    frev (A₂ := A₂) (mkL A₂ u) = mkL A₂ (mapReverse A₀ u) := by
  have hcomm : ∀ l : List A₀,
      List.reverse (l.map (iota A₂)) = (List.reverse l).map (iota A₂) := fun l => by simp
  have hmap := mapLift_map_optionMap (f := (List.reverse : List A₀ → List A₀))
    (g := (List.reverse : List (Alph A₀ A₂) → List (Alph A₀ A₂))) (iota A₂) hcomm u
  rw [frev, prep_mkL, mapReverse, mapLift_map_some_cons_none, hmap]
  show dec (some (Sum.inl false) :: none ::
      (mapLift List.reverse u).map (Option.map (iota A₂))) = mkL A₂ (mapLift List.reverse u)
  rw [dec_mark_sep, dec_body_left (mapLift List.reverse u) (some none) trivial]
  rfl

lemma frev_mkR (v : List A₂) :
    frev (A₀ := A₀) (mkR (Option A₀) v) = mkR (Option A₀) v := by
  rw [frev, prep_mkR, mapReverse, mapLift_map_some_cons_none, mapLift_rev_encR]
  show dec (some (Sum.inl true) :: none :: encR A₀ v) = mkR (Option A₀) v
  rw [dec_mark_sep, dec_body_right v]
  rfl

lemma frev_bad {w : List (Alph A₀ A₂)} (h₁ : ∀ u : List (Option A₀), w ≠ mkL A₂ u)
    (h₂ : ∀ v : List A₂, w ≠ mkR (Option A₀) v) : frev w = botv A₀ A₂ := by
  rw [frev, prep_bad h₁ h₂]
  rfl

/-! ### Map duplicate -/

lemma mapLift_dup_encR (v : List A₂) :
    mapLift (fun l : List (Alph A₀ A₂) => l ++ l) (encR A₀ v) = encR2 A₀ v := by
  induction v with
  | nil =>
      simpa [encR, encR2] using
        mapLift_map_some (fun l : List (Alph A₀ A₂) => l ++ l) ([] : List (Alph A₀ A₂))
  | cons c v ih =>
      have h : encR A₀ (c :: v)
          = [(Sum.inr (Sum.inr c) : Alph A₀ A₂)].map some ++ none :: encR A₀ v := rfl
      rw [h, mapLift_map_some_cons_none, ih]
      rfl

lemma fdup_mkL (u : List (Option A₀)) :
    fdup (A₂ := A₂) (mkL A₂ u) = mkL A₂ (mapDuplicate A₀ u) := by
  have hcomm : ∀ l : List A₀,
      (l.map (iota A₂)) ++ (l.map (iota A₂)) = (l ++ l).map (iota A₂) := fun l => by simp
  have hmap := mapLift_map_optionMap (f := (fun l : List A₀ => l ++ l))
    (g := (fun l : List (Alph A₀ A₂) => l ++ l)) (iota A₂) hcomm u
  rw [fdup, prep_mkL, mapDuplicate, mapLift_map_some_cons_none, hmap]
  show dec (some (Sum.inl false) :: some (Sum.inl false) :: none ::
      (mapLift (fun l : List A₀ => l ++ l) u).map (Option.map (iota A₂)))
    = mkL A₂ (mapLift (fun l : List A₀ => l ++ l) u)
  rw [dec_mark_mark_sep,
    dec_body_left (mapLift (fun l : List A₀ => l ++ l) u) (some none) trivial]
  rfl

lemma fdup_mkR (v : List A₂) :
    fdup (A₀ := A₀) (mkR (Option A₀) v) = mkR (Option A₀) v := by
  rw [fdup, prep_mkR, mapDuplicate, mapLift_map_some_cons_none, mapLift_dup_encR]
  show dec (some (Sum.inl true) :: some (Sum.inl true) :: none :: encR2 A₀ v)
    = mkR (Option A₀) v
  rw [dec_mark_mark_sep, dec_body_right2 v]
  rfl

lemma fdup_bad {w : List (Alph A₀ A₂)} (h₁ : ∀ u : List (Option A₀), w ≠ mkL A₂ u)
    (h₂ : ∀ v : List A₂, w ≠ mkR (Option A₀) v) : fdup w = botv A₀ A₂ := by
  rw [fdup, prep_bad h₁ h₂]
  rfl

/-! ## Regularity -/

variable (A₀ A₂)

lemma isRationalFun_prep [Finite A₀] [Finite A₂] :
    IsRationalFun (prep : List (Alph A₀ A₂) → List (Option (Alph A₀ A₂))) :=
  isRationalFun_ite shpStep Shp.start (fun s => s = Shp.inL ∨ s = Shp.inR)
    (isRationalFun_homOf encφ) (isRationalFun_const _)

lemma isRationalFun_dec [Finite A₀] [Finite A₂] :
    IsRationalFun (dec : List (Option (Alph A₀ A₂)) → List (Alph A₀ A₂)) :=
  isRationalFun_ctxEval _ _ _

lemma isRegularFun_frev [Finite A₀] [Finite A₂] :
    IsRegularFun (frev : List (Alph A₀ A₂) → List (Alph A₀ A₂)) :=
  ((IsRegularFun.of_rational (isRationalFun_prep A₀ A₂)).comp
      (isRegularFun_mapReverse (Alph A₀ A₂))).comp'
    (IsRegularFun.of_rational (isRationalFun_dec A₀ A₂)) (fun _ => rfl)

lemma isRegularFun_fdup [Finite A₀] [Finite A₂] :
    IsRegularFun (fdup : List (Alph A₀ A₂) → List (Alph A₀ A₂)) :=
  ((IsRegularFun.of_rational (isRationalFun_prep A₀ A₂)).comp
      (isRegularFun_mapDuplicate (Alph A₀ A₂))).comp'
    (IsRegularFun.of_rational (isRationalFun_dec A₀ A₂)) (fun _ => rfl)

end SumPrime

/-! ## The two prime base cases -/

/-- The marked sum of map reverse with the identity. -/
theorem msum_mapReverse_id (A₀ A₂ : Type) [Finite A₀] [Finite A₂] :
    MSum (mapReverse A₀) (id : List A₂ → List A₂) :=
  ⟨SumPrime.frev, SumPrime.isRegularFun_frev A₀ A₂, SumPrime.frev_mkL,
    SumPrime.frev_mkR, SumPrime.botv A₀ A₂, SumPrime.botv_ne_mkL, SumPrime.botv_ne_mkR,
    fun _ h₁ h₂ => SumPrime.frev_bad h₁ h₂⟩

/-- The marked sum of map duplicate with the identity. -/
theorem msum_mapDuplicate_id (A₀ A₂ : Type) [Finite A₀] [Finite A₂] :
    MSum (mapDuplicate A₀) (id : List A₂ → List A₂) :=
  ⟨SumPrime.fdup, SumPrime.isRegularFun_fdup A₀ A₂, SumPrime.fdup_mkL,
    SumPrime.fdup_mkR, SumPrime.botv A₀ A₂, SumPrime.botv_ne_mkL, SumPrime.botv_ne_mkR,
    fun _ h₁ h₂ => SumPrime.fdup_bad h₁ h₂⟩

end Lax916827Proofs.Transducers
