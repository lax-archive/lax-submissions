/-
The bimachine that precomputes, in every position of the input, the state of a
family of automata on the marked string.

This is the construction that is used both for the inclusion
"mso relabellings ⊆ rational" of Theorem `thm:logic-rational-functions` and for the letter-to-letter
rational function of Lemma `lem:logic-precomputation`.  Fix a finite family of deterministic
automata over the doubly marked alphabet `A × 2 × 2`.  For an input string `w`
and a position `x` of it, the run of such an automaton on `markAt2 w x y` is the
composition of three state transformations: the one of the unmarked prefix
`w[..x-1]`, the one of the marked infix `w[x..y]`, and the one of the unmarked
suffix `w[y+1..]`.  The first one is computed by a deterministic automaton
reading the prefix, the last one by a deterministic automaton reading the
suffix from right to left; so the pair

  `(state of the unmarked prefix, transformation of the unmarked suffix)`

is available to a bimachine in every position of the input.  `markFun` is the
function that outputs, in every position, an arbitrary function `h` of the
letter and of that pair, together with a fixed string on the empty input; the
main result of the file is that `markFun` is computed by a bimachine, and hence
rational by Theorem `thm:bimachines`.
-/
import Lax916827Proofs.Source.PartC.MarkStr
import Lax132576Proofs.Source.PartB.Bimachine
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MarkBimach

open MarkStr

variable {A B : Type} {ι : Type} {σ : ι → Type}

/-! ## Evaluating an automaton on a marked string -/

lemma flatten_map_singleton {α β : Type} (l : List α) (f : α → β) :
    (l.map (fun a => [f a])).flatten = l.map f := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]


variable {S : Type}

lemma strTrans_append (step : S → Mark2 A → S) (u v : List (Mark2 A)) (s : S) :
    strTrans step (u ++ v) s = strTrans step v (strTrans step u s) := by
  simp [strTrans, List.foldl_append]

lemma eval_markAt2 (D : DFA (Mark2 A) S) (w : List A) (x y : ℕ) (hxy : x ≤ y)
    (hy : y < w.length) :
    markAt2 w x y ∈ D.accepts ↔
      strTrans D.step (unmark2 (w.drop (y + 1)))
        (strTrans D.step (midMark ((w.drop x).take (y - x + 1)))
          (strTrans D.step (unmark2 (w.take x)) D.start)) ∈ D.accept := by
  rw [DFA.mem_accepts]
  show strTrans D.step (markAt2 w x y) D.start ∈ D.accept ↔ _
  rw [markAt2_split w x y hxy hy, strTrans_append, strTrans_append]

lemma eval_markAt2_diag (D : DFA (Mark2 A) S) (w : List A) (x : ℕ) (hx : x < w.length) :
    markAt2 w x x ∈ D.accepts ↔
      strTrans D.step (unmark2 (w.drop (x + 1)))
        (D.step (strTrans D.step (unmark2 (w.take x)) D.start) (w[x], true, true)) ∈ D.accept := by
  rw [DFA.mem_accepts]
  show strTrans D.step (markAt2 w x x) D.start ∈ D.accept ↔ _
  rw [markAt2_diag w x hx, strTrans_append]
  rfl

/-! ## The precomputed data -/

variable (D : ∀ i, DFA (Mark2 A) (σ i))

/-- The state of the automaton `D i` after reading the unmarked prefix of `w`
before the position `x`. -/
def markPreSt (w : List A) (x : ℕ) (i : ι) : σ i :=
  strTrans (D i).step (unmark2 (w.take x)) (D i).start

/-- The state transformation of the automaton `D i` on the unmarked suffix of
`w` after the position `x`. -/
def sufTr (w : List A) (x : ℕ) (i : ι) : σ i → σ i :=
  fun s => strTrans (D i).step (unmark2 (w.drop (x + 1))) s

variable (h : A → ((i : ι) → σ i × (σ i → σ i)) → List B) (e : List B)

/-- The output produced in the position `x` of `w`. -/
def posOut (w : List A) (x : ℕ) : List B :=
  (w[x]?).elim [] (fun a => h a (fun i => (markPreSt D w x i, sufTr D w x i)))

/-- The function computed by the bimachine: on the empty input it outputs `e`,
and otherwise it outputs, in every position, the string given by `h`. -/
def markFun (w : List A) : List B :=
  if w = [] then e else ((List.range w.length).map (posOut D h w)).flatten

/-! ## The bimachine -/

/-- The states of the prefix automaton: the states of all the automata of the
family, together with a bit saying whether the prefix is nonempty. -/
abbrev PSt (ι : Type) (σ : ι → Type) : Type := ((i : ι) → σ i) × Bool

/-- The states of the suffix automaton: the first letter of the suffix (if any)
and the state transformations of all the automata of the family on the rest of
the suffix. -/
abbrev SSt (A : Type) (ι : Type) (σ : ι → Type) : Type := Option A × ((i : ι) → σ i → σ i)

/-- The bimachine computing `markFun`. -/
def bimach : Bimachine A B (PSt ι σ) (SSt A ι σ) where
  prefixInit := (fun i => (D i).start, false)
  prefixStep := fun p a => (fun i => (D i).step (p.1 i) (a, false, false), true)
  suffixInit := (none, fun _ s => s)
  suffixStep := fun s a =>
    (some a, match s.1 with
      | none => fun _ t => t
      | some b => fun i t => s.2 i ((D i).step t (b, false, false)))
  out := fun p s =>
    match s.1 with
    | none => if p.2 then [] else e
    | some a => h a (fun i => (p.1 i, s.2 i))

lemma bimach_prefix (u : List A) (q : (i : ι) → σ i) (f : Bool) :
    strTrans (bimach D h e).prefixStep u (q, f) =
      (fun i => strTrans (D i).step (unmark2 u) (q i), f || decide (u ≠ [])) := by
  induction u generalizing q f with
  | nil => simp [strTrans]
  | cons a u ih =>
      have : strTrans (bimach D h e).prefixStep (a :: u) (q, f) =
          strTrans (bimach D h e).prefixStep u
            (fun i => (D i).step (q i) (a, false, false), true) := rfl
      rw [this, ih]
      simp [strTrans, unmark2]

lemma bimach_suffix (u : List A) :
    strTrans (bimach D h e).suffixStep u.reverse (bimach D h e).suffixInit =
      (u.head?, fun i s => strTrans (D i).step (unmark2 u.tail) s) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      rw [List.reverse_cons]
      have : strTrans (bimach D h e).suffixStep (u.reverse ++ [a]) (bimach D h e).suffixInit =
          (bimach D h e).suffixStep
            (strTrans (bimach D h e).suffixStep u.reverse (bimach D h e).suffixInit) a := by
        simp [strTrans, List.foldl_append]
      rw [this, ih]
      cases u with
      | nil => rfl
      | cons b u => simp [bimach, strTrans, unmark2]

lemma bimach_eval (w : List A) : (bimach D h e).eval w = markFun D h e w := by
  classical
  have hgap : ∀ i, i ≤ w.length →
      (bimach D h e).out
        (strTrans (bimach D h e).prefixStep (w.take i) (bimach D h e).prefixInit)
        (strTrans (bimach D h e).suffixStep (w.drop i).reverse (bimach D h e).suffixInit) =
      (if i < w.length then posOut D h w i else if w = [] then e else []) := by
    intro i hi
    rw [show (bimach D h e).prefixInit = ((fun i => (D i).start), false) from rfl,
      bimach_prefix, bimach_suffix]
    have hhead : (w.drop i).head? = w[i]? := by
      rw [List.head?_drop]
    have htail : (w.drop i).tail = w.drop (i + 1) := by
      rw [List.tail_drop]
    by_cases hlt : i < w.length
    · have hsome : w[i]? = some w[i] := List.getElem?_eq_getElem hlt
      simp only [hlt, if_true]
      rw [posOut]
      simp only [bimach, hhead, htail, hsome, Option.elim]
      rfl
    · have hnone : w[i]? = none := List.getElem?_eq_none (by omega)
      simp only [hlt, if_false]
      simp only [bimach, hhead, htail, hnone]
      by_cases hw : w = []
      · subst hw
        simp
      · have : w.take i ≠ [] := by
          intro hcon
          have : i = 0 := by
            by_contra hne
            have h0 : 0 < i := Nat.pos_of_ne_zero hne
            have : (w.take i).length = min i w.length := by simp
            rw [hcon] at this
            simp at this
            omega
          subst this
          simp at hi
          exact hw (List.eq_nil_of_length_eq_zero (by omega))
        simp [this, hw]
  rw [Bimachine.eval]
  have hmap : (List.range (w.length + 1)).map (fun i =>
      (bimach D h e).out
        (strTrans (bimach D h e).prefixStep (w.take i) (bimach D h e).prefixInit)
        (strTrans (bimach D h e).suffixStep (w.drop i).reverse (bimach D h e).suffixInit)) =
      (List.range w.length).map (posOut D h w) ++ [if w = [] then e else []] := by
    rw [List.range_succ, List.map_append]
    congr 1
    · refine List.map_congr_left (fun i hi => ?_)
      rw [List.mem_range] at hi
      rw [hgap i (le_of_lt hi), if_pos hi]
    · rw [List.map_cons, List.map_nil, hgap w.length (le_refl _), if_neg (lt_irrefl _)]
  rw [hmap, markFun]
  by_cases hw : w = []
  · subst hw
    simp
  · simp [hw]

/-! ## The letter-to-letter case -/

/-- If every position produces exactly one letter and the empty input produces
the empty string, then `markFun` is the letter-to-letter function given by
`f₀`. -/
lemma markFun_eq_ofFn (f₀ : A → ((i : ι) → σ i × (σ i → σ i)) → B)
    (hh : ∀ a g, h a g = [f₀ a g]) (he : e = []) (w : List A) :
    markFun D h e w =
      List.ofFn (fun x : Fin w.length => f₀ w[x] (fun i => (markPreSt D w x i, sufTr D w x i))) := by
  by_cases hw : w = []
  · subst hw
    simp [markFun, he]
  · rw [markFun, if_neg hw, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
    have : ((List.finRange w.length).map ((posOut D h w) ∘ (fun x : Fin w.length => (x : ℕ)))) =
        (List.finRange w.length).map
          (fun x : Fin w.length => [f₀ w[x] (fun i => (markPreSt D w x i, sufTr D w x i))]) := by
      refine List.map_congr_left (fun x _ => ?_)
      simp only [Function.comp_apply, posOut, List.getElem?_eq_getElem x.isLt, Option.elim]
      exact hh _ _
    rw [this, flatten_map_singleton]

lemma markFun_lengthPreserving (f₀ : A → ((i : ι) → σ i × (σ i → σ i)) → B)
    (hh : ∀ a g, h a g = [f₀ a g]) (he : e = []) : LengthPreserving (markFun D h e) := by
  intro w
  rw [markFun_eq_ofFn D h e f₀ hh he w, List.length_ofFn]

lemma markFun_getElem? (f₀ : A → ((i : ι) → σ i × (σ i → σ i)) → B)
    (hh : ∀ a g, h a g = [f₀ a g]) (he : e = []) (w : List A) (x : ℕ) (hx : x < w.length) :
    (markFun D h e w)[x]? = some (f₀ w[x] (fun i => (markPreSt D w x i, sufTr D w x i))) := by
  rw [markFun_eq_ofFn D h e f₀ hh he w, List.getElem?_ofFn, dif_pos hx]
  rfl

variable [Finite A] [Finite ι] [∀ i, Finite (σ i)]

theorem isBimachine_markFun : IsBimachine (markFun D h e) :=
  ⟨PSt ι σ, SSt A ι σ, inferInstance, inferInstance, bimach D h e,
    funext (bimach_eval D h e)⟩

theorem isRationalFun_markFun [Finite B] : IsRationalFun (markFun D h e) :=
  rationalFun_of_isBimachine (isBimachine_markFun D h e)

end MarkBimach
end Lax314295Proofs.Transducers
