/-
Bracket depth, and the shape of a string representation, for Section *Combinators* of
*Transducers* (M. Bojańczyk).

The easy direction of Theorem `thm:regular-terms` needs to parse the string representation of the
input, and this file is the parsing.  The parser is a counter: `depth w` is the number of brackets
that `w` opens and does not close, counting `(` and `[` as `+1` and `)` and `]` as `-1`.

The one fact that the whole development rests on is `Transducers.Comb.repr_shape`: in the
representation of an element of a type, every proper prefix has depth at least `0`, and a letter
that sits at depth `0` is one of

    1   L   R   (   [

-- never a comma and never a closing bracket.  So, inside the representation of an element, a
delimiter at the lowest depth can only be one that the surrounding term wrote itself, and a machine
that counts brackets can find where a sub-representation ends.  Together with
`Transducers.Comb.repr_depth_le`, which bounds the depth by the height of the type, this makes a
counter capped at the height of the type a complete parser.
-/
import Lax709149Proofs.Source.PartC.CombTypes
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## Splitting a list -/

lemma cons_eq_append_cases {α : Type} {c : α} {w u v : List α} (h : c :: w = u ++ v) :
    (u = [] ∧ v = c :: w) ∨ (∃ u', u = c :: u' ∧ w = u' ++ v) := by
  cases u with
  | nil => exact Or.inl ⟨rfl, by simpa using h.symm⟩
  | cons a u' =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact Or.inr ⟨u', by rw [h.1], h.2⟩

lemma singleton_eq_append_cases {α : Type} {d : α} {u v : List α} (h : [d] = u ++ v) :
    (u = [] ∧ v = [d]) ∨ (u = [d] ∧ v = []) := by
  rcases cons_eq_append_cases h with ⟨rfl, rfl⟩ | ⟨u', rfl, hu⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hu.symm
    exact Or.inr ⟨rfl, rfl⟩

/-! ## The bracket depth of a string -/

/-- The bracket weight of a letter: `+1` for an opening bracket, `-1` for a closing one. -/
def wt : Sym8 → ℤ
  | .lpar => 1
  | .lbrack => 1
  | .rpar => -1
  | .rbrack => -1
  | _ => 0

@[simp] lemma wt_lpar : wt .lpar = 1 := rfl
@[simp] lemma wt_rpar : wt .rpar = -1 := rfl
@[simp] lemma wt_lbrack : wt .lbrack = 1 := rfl
@[simp] lemma wt_rbrack : wt .rbrack = -1 := rfl
@[simp] lemma wt_comma : wt .comma = 0 := rfl
@[simp] lemma wt_one : wt .one = 0 := rfl
@[simp] lemma wt_left : wt .left = 0 := rfl
@[simp] lemma wt_right : wt .right = 0 := rfl

/-- The bracket depth of a string: the number of brackets it opens and does not close. -/
def depth (w : List Sym8) : ℤ := (w.map wt).sum

@[simp] lemma depth_nil : depth [] = 0 := rfl

@[simp] lemma depth_cons (c : Sym8) (w : List Sym8) : depth (c :: w) = wt c + depth w := by
  simp [depth]

@[simp] lemma depth_append (u v : List Sym8) : depth (u ++ v) = depth u + depth v := by
  simp [depth]

/-- The letters that may occur at the lowest bracket depth of a representation. -/
def transparent : Sym8 → Bool
  | .lpar => true
  | .lbrack => true
  | .one => true
  | .left => true
  | .right => true
  | _ => false

/-! ## Balanced strings and the shape of a representation -/

/-- Every *proper* prefix of `w` has depth at least `0`. -/
def PrefNonneg (w : List Sym8) : Prop := ∀ u c v, w = u ++ c :: v → 0 ≤ depth u

/-- A string is *balanced* if it closes exactly the brackets it opens and never closes one it has
not opened. -/
def Balanced (w : List Sym8) : Prop := depth w = 0 ∧ PrefNonneg w

/-- The shape of a representation: balanced, and moreover every letter at depth `0` is
transparent. -/
def RepShape (w : List Sym8) : Prop :=
  depth w = 0 ∧ ∀ u c v, w = u ++ c :: v → 0 ≤ depth u ∧ (depth u = 0 → transparent c = true)

lemma RepShape.balanced {w : List Sym8} (h : RepShape w) : Balanced w :=
  ⟨h.1, fun u c v huv => (h.2 u c v huv).1⟩

lemma Balanced.prefix_nonneg {w : List Sym8} (h : Balanced w) {u v : List Sym8}
    (huv : w = u ++ v) : 0 ≤ depth u := by
  cases v with
  | nil =>
      rw [List.append_nil] at huv
      rw [← huv]
      exact le_of_eq h.1.symm
  | cons c v' => exact h.2 u c v' huv

lemma prefNonneg_nil : PrefNonneg [] := by
  intro u c v huv
  exact absurd huv.symm (by simp)

lemma balanced_nil : Balanced [] := ⟨rfl, prefNonneg_nil⟩

lemma PrefNonneg.append {x y : List Sym8} (hx0 : depth x = 0) (hx : PrefNonneg x)
    (hy : PrefNonneg y) : PrefNonneg (x ++ y) := by
  intro u c v huv
  rcases List.append_eq_append_iff.1 huv.symm with ⟨z, hz1, hz2⟩ | ⟨z, hz1, hz2⟩
  · -- `x = u ++ z`
    cases z with
    | nil => rw [List.append_nil] at hz1; rw [← hz1]; omega
    | cons e z' => exact hx u e z' hz1
  · -- `u = x ++ z` and `y = z ++ c :: v`
    subst hz1
    have := hy z c v hz2
    rw [depth_append, hx0]
    omega

lemma Balanced.append {x y : List Sym8} (hx : Balanced x) (hy : Balanced y) : Balanced (x ++ y) :=
  ⟨by rw [depth_append, hx.1, hy.1]; ring, PrefNonneg.append hx.1 hx.2 hy.2⟩

lemma balanced_comma : Balanced [Sym8.comma] := by
  refine ⟨rfl, fun u c v huv => ?_⟩
  rcases cons_eq_append_cases huv with ⟨rfl, -⟩ | ⟨u', rfl, hu⟩
  · simp
  · have : u' = [] := by
      have := congrArg List.length hu
      simp at this
    rw [this]
    simp [wt]

/-- Prefixing a transparent letter of weight `0` preserves the shape of a representation. -/
lemma RepShape.consTransparent {c : Sym8} (hc : transparent c = true) (hw : wt c = 0)
    {w : List Sym8} (h : RepShape w) : RepShape (c :: w) := by
  refine ⟨by rw [depth_cons, hw, h.1]; ring, fun u c' v huv => ?_⟩
  rcases cons_eq_append_cases huv with ⟨rfl, hv⟩ | ⟨u', rfl, hu⟩
  · have : c' = c := by
      have := hv.symm
      simp at this
      exact this.1.symm
    subst this
    exact ⟨by simp, fun _ => hc⟩
  · have := h.2 u' c' v hu
    rw [depth_cons, hw]
    simpa using this

/-- Prefixes of `y ++ [d]`, where `d` closes a bracket, still have depth at least `0` if `y` is
balanced. -/
lemma prefNonneg_append_close {y : List Sym8} (hy : Balanced y) {d : Sym8} :
    PrefNonneg (y ++ [d]) := by
  refine PrefNonneg.append hy.1 hy.2 ?_
  intro u c v huv
  rcases cons_eq_append_cases huv with ⟨rfl, -⟩ | ⟨u', rfl, hu⟩
  · simp
  · exact absurd hu.symm (by simp)

/-- Wrapping a balanced string in a pair of brackets produces the shape of a representation. -/
lemma RepShape.wrap {y : List Sym8} (hy : Balanced y) {c d : Sym8} (hc : transparent c = true)
    (hwc : wt c = 1) (hwd : wt d = -1) : RepShape (c :: (y ++ [d])) := by
  refine ⟨by rw [depth_cons, depth_append, hy.1, hwc]; simp [depth, hwd], fun u c' v huv => ?_⟩
  rcases cons_eq_append_cases huv with ⟨rfl, hv⟩ | ⟨u', rfl, hu⟩
  · have hcc : c' = c := by injection hv
    subst hcc
    exact ⟨by simp, fun _ => hc⟩
  · have h0 : 0 ≤ depth u' := prefNonneg_append_close hy u' c' v hu
    refine ⟨by rw [depth_cons, hwc]; omega, fun hzero => ?_⟩
    rw [depth_cons, hwc] at hzero
    omega

/-! ## The shape of the string representation -/

lemma balanced_joinSep {A : Ty} (l : List A.Elt)
    (ih : ∀ a : A.Elt, Balanced (A.repr a)) : Balanced (joinSep (l.map A.repr)) := by
  induction l with
  | nil => exact balanced_nil
  | cons a l ihl =>
      cases l with
      | nil => simpa using ih a
      | cons b l' =>
          have hrw : joinSep ((a :: b :: l').map A.repr)
              = A.repr a ++ (Sym8.comma :: joinSep ((b :: l').map A.repr)) := rfl
          rw [hrw]
          exact (ih a).append (balanced_comma.append ihl)

/-- **The shape of a string representation.**  In the representation of an element of a type,
every proper prefix has depth at least `0`, and every letter at depth `0` is one of `1`, `L`, `R`,
`(`, `[`. -/
theorem repr_shape : ∀ (t : Ty) (x : t.Elt), RepShape (t.repr x)
  | .one, _ => by
      refine ⟨rfl, fun u c v huv => ?_⟩
      rcases cons_eq_append_cases (huv : Sym8.one :: [] = u ++ c :: v) with
        ⟨rfl, hv⟩ | ⟨u', rfl, hu⟩
      · have hcc : c = Sym8.one := by injection hv
        subst hcc
        exact ⟨by simp, fun _ => rfl⟩
      · exact absurd hu.symm (by simp)
  | .prod A B, x => by
      have h : (Ty.prod A B).repr x
          = Sym8.lpar :: ((A.repr x.1 ++ Sym8.comma :: B.repr x.2) ++ [Sym8.rpar]) := by
        simp [Ty.repr]
      rw [h]
      exact RepShape.wrap
        (((repr_shape A x.1).balanced).append
          (balanced_comma.append ((repr_shape B x.2).balanced))) rfl rfl rfl
  | .sum A B, x => by
      rcases x with a | b
      · exact RepShape.consTransparent rfl rfl (repr_shape A a)
      · exact RepShape.consTransparent rfl rfl (repr_shape B b)
  | .list A, l =>
      RepShape.wrap (balanced_joinSep l (fun a => (repr_shape A a).balanced)) rfl rfl rfl

lemma repr_balanced (t : Ty) (x : t.Elt) : Balanced (t.repr x) := (repr_shape t x).balanced

/-- A representation is not empty, and its first letter is transparent. -/
lemma repr_eq_cons (t : Ty) (x : t.Elt) :
    ∃ c w, t.repr x = c :: w ∧ transparent c = true := by
  have hne : t.repr x ≠ [] := by
    cases t with
    | one => simp [Ty.repr]
    | prod A B => simp [Ty.repr]
    | sum A B => rcases x with a | b <;> simp [Ty.repr]
    | list A => simp [Ty.repr]
  obtain ⟨c, w, hcw⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨c, w, hcw, ((repr_shape t x).2 [] c w (by simpa using hcw)).2 (by simp)⟩

@[simp] lemma depth_repr (t : Ty) (x : t.Elt) : depth (t.repr x) = 0 := (repr_shape t x).1

/-! ## The depth of a representation is bounded by the height of the type -/

/-- Every prefix of `w` has depth at most `H`. -/
def PrefDepthLe (w : List Sym8) (H : ℤ) : Prop := ∀ u v, w = u ++ v → depth u ≤ H

lemma prefDepthLe_nil {H : ℤ} (hH : 0 ≤ H) : PrefDepthLe [] H := by
  intro u v huv
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 huv.symm
  simpa using hH

lemma PrefDepthLe.mono {w : List Sym8} {H H' : ℤ} (h : PrefDepthLe w H) (hHH : H ≤ H') :
    PrefDepthLe w H' := fun u v huv => le_trans (h u v huv) hHH

lemma PrefDepthLe.append {x y : List Sym8} {H : ℤ} (hx0 : depth x = 0) (hx : PrefDepthLe x H)
    (hy : PrefDepthLe y H) : PrefDepthLe (x ++ y) H := by
  intro u v huv
  rcases List.append_eq_append_iff.1 huv.symm with ⟨z, hz1, hz2⟩ | ⟨z, hz1, hz2⟩
  · exact hx u z hz1
  · subst hz1
    have := hy z v hz2
    rw [depth_append, hx0]
    omega

lemma PrefDepthLe.consZero {c : Sym8} (hw : wt c = 0) {y : List Sym8} {H : ℤ} (hH : 0 ≤ H)
    (hy : PrefDepthLe y H) : PrefDepthLe (c :: y) H := by
  intro u v huv
  rcases cons_eq_append_cases huv with ⟨rfl, -⟩ | ⟨u', rfl, hu⟩
  · simpa using hH
  · have := hy u' v hu
    rw [depth_cons, hw]
    omega

lemma PrefDepthLe.wrap {y : List Sym8} {H : ℤ} (hy0 : depth y = 0) (hy : PrefDepthLe y H)
    {c d : Sym8} (hwc : wt c = 1) (hwd : wt d = -1) (hH : 0 ≤ H) :
    PrefDepthLe (c :: (y ++ [d])) (H + 1) := by
  intro u v huv
  rcases cons_eq_append_cases huv with ⟨rfl, -⟩ | ⟨u', rfl, hu⟩
  · simp only [depth_nil]; omega
  · have hpd : PrefDepthLe (y ++ [d]) H := by
      refine PrefDepthLe.append hy0 hy ?_
      intro u'' v'' hu''
      rcases singleton_eq_append_cases hu'' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simpa using hH
      · rw [depth_cons, hwd, depth_nil]; omega
    have := hpd u' v hu
    rw [depth_cons, hwc]
    omega

lemma prefDepthLe_joinSep {A : Ty} (l : List A.Elt) {H : ℤ}
    (ih : ∀ a : A.Elt, PrefDepthLe (A.repr a) H) (hH : 0 ≤ H) :
    PrefDepthLe (joinSep (l.map A.repr)) H := by
  induction l with
  | nil => exact prefDepthLe_nil hH
  | cons a l ihl =>
      cases l with
      | nil => simpa using ih a
      | cons b l' =>
          have hrw : joinSep ((a :: b :: l').map A.repr)
              = A.repr a ++ (Sym8.comma :: joinSep ((b :: l').map A.repr)) := rfl
          rw [hrw]
          exact PrefDepthLe.append (by simp) (ih a) (PrefDepthLe.consZero rfl hH ihl)

lemma height_nonneg (t : Ty) : (0 : ℤ) ≤ (t.height : ℤ) := Int.natCast_nonneg _

/-- **The depth of a representation is bounded by the height of the type.** -/
theorem repr_depth_le : ∀ (t : Ty) (x : t.Elt), PrefDepthLe (t.repr x) (t.height : ℤ)
  | .one, _ => by
      intro u v huv
      rcases cons_eq_append_cases (huv : Sym8.one :: [] = u ++ v) with ⟨rfl, -⟩ | ⟨u', rfl, hu⟩
      · simp only [depth_nil]; exact height_nonneg Ty.one
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hu.symm
        simp [wt, Ty.height]
  | .prod A B, x => by
      have h : (Ty.prod A B).repr x
          = Sym8.lpar :: ((A.repr x.1 ++ Sym8.comma :: B.repr x.2) ++ [Sym8.rpar]) := by
        simp [Ty.repr]
      have hHnn : (0 : ℤ) ≤ ((max A.height B.height : ℕ) : ℤ) := Int.natCast_nonneg _
      have hA : PrefDepthLe (A.repr x.1) ((max A.height B.height : ℕ) : ℤ) :=
        (repr_depth_le A x.1).mono (by exact_mod_cast Nat.le_max_left A.height B.height)
      have hB : PrefDepthLe (B.repr x.2) ((max A.height B.height : ℕ) : ℤ) :=
        (repr_depth_le B x.2).mono (by exact_mod_cast Nat.le_max_right A.height B.height)
      have hmid : PrefDepthLe (A.repr x.1 ++ Sym8.comma :: B.repr x.2)
          ((max A.height B.height : ℕ) : ℤ) :=
        PrefDepthLe.append (by simp) hA (PrefDepthLe.consZero rfl hHnn hB)
      have hwrap := PrefDepthLe.wrap (y := A.repr x.1 ++ Sym8.comma :: B.repr x.2)
        (by simp) hmid (c := Sym8.lpar) (d := Sym8.rpar) rfl rfl hHnn
      rw [h]
      refine hwrap.mono ?_
      have hht : ((Ty.prod A B).height : ℤ) = ((max A.height B.height : ℕ) : ℤ) + 1 := by
        rw [Ty.height]; push_cast; omega
      omega
  | .sum A B, x => by
      have hle : ∀ C : Ty, (C.height : ℤ) ≤ ((Ty.sum A B).height : ℤ) → True := fun _ _ => trivial
      rcases x with a | b
      · have h : (Ty.sum A B).repr (Sum.inl a) = Sym8.left :: A.repr a := rfl
        rw [h]
        refine (PrefDepthLe.consZero (c := Sym8.left) rfl (height_nonneg A) (repr_depth_le A a)).mono ?_
        have : (A.height : ℤ) ≤ ((Ty.sum A B).height : ℤ) := by
          rw [Ty.height]; exact_mod_cast Nat.le_max_left A.height B.height
        exact this
      · have h : (Ty.sum A B).repr (Sum.inr b) = Sym8.right :: B.repr b := rfl
        rw [h]
        refine (PrefDepthLe.consZero (c := Sym8.right) rfl (height_nonneg B) (repr_depth_le B b)).mono ?_
        have : (B.height : ℤ) ≤ ((Ty.sum A B).height : ℤ) := by
          rw [Ty.height]; exact_mod_cast Nat.le_max_right A.height B.height
        exact this
  | .list A, l => by
      have h : (Ty.list A).repr l
          = Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack]) := rfl
      have hbody : PrefDepthLe (joinSep (l.map A.repr)) (A.height : ℤ) :=
        prefDepthLe_joinSep l (fun a => repr_depth_le A a) (height_nonneg A)
      have hb0 : depth (joinSep (l.map A.repr)) = 0 :=
        (balanced_joinSep l (fun a => (repr_shape A a).balanced)).1
      have hwrap := PrefDepthLe.wrap (y := joinSep (l.map A.repr)) hb0 hbody
        (c := Sym8.lbrack) (d := Sym8.rbrack) rfl rfl (height_nonneg A)
      rw [h]
      refine hwrap.mono ?_
      have hht : ((Ty.list A).height : ℤ) = (A.height : ℤ) + 1 := by
        rw [Ty.height]; push_cast; omega
      omega

end Comb
end Lax709149Proofs.Transducers
