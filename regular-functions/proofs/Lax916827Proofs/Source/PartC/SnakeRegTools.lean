/-
Two elementary closure properties of regular functions that the assembly of the
induction step of the book's snake lemma uses over and over again:

* a *finite case distinction*: if the input determines, by a regular condition,
  an element of a finite set of "parameters", and the function to be applied is
  regular for every value of the parameter, then the function is regular
  (`Transducers.isRegularFun_ofFiniteCases`);
* a *bounded concatenation*: the concatenation of a fixed finite number of
  regular functions is regular (`Transducers.isRegularFun_flatMapRange`).

Both are immediate consequences of Lemma `lem:regular-closure-properties`
(`RequestProject/PartC/RegClosure.lean`), but stating them once avoids repeating
the same inductions in the construction of the block function of the snake
lemma.
-/
import Lax916827Proofs.Source.PartC.RegPair
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B : Type} [Finite A] [Finite B]

/-- The constant empty function is regular. -/
lemma isRegularFun_nil : IsRegularFun (fun _ : List A => ([] : List B)) :=
  IsRegularFun.of_rational (isRationalFun_const [])

section Cases

variable {D : Type}

open scoped Classical in
/-- Auxiliary form of the finite case distinction: the case distinction over the
values occurring in a list of parameters. -/
private lemma isRegularFun_casesOn_list (d : List A → D) (g : D → List A → List B)
    (hg : ∀ e, IsRegularFun (g e))
    (hd : ∀ e : D, Language.IsRegular {u : List A | d u = e}) :
    ∀ l : List D, IsRegularFun (fun u => if d u ∈ l then g (d u) u else ([] : List B)) := by
  intro l
  induction l with
  | nil => simpa using isRegularFun_nil (A := A) (B := B)
  | cons e l ih =>
      have hcond := isRegularFun_cond (f := g e)
        (g := fun u => if d u ∈ l then g (d u) u else ([] : List B)) (hg e) ih (hd e)
      refine hcond.congr ?_
      intro u
      by_cases he : d u = e
      · refine (if_pos he).trans ?_
        rw [if_pos (show d u ∈ e :: l from by simp [he]), he]
      · refine (if_neg he).trans ?_
        show (if d u ∈ l then g (d u) u else ([] : List B)) = _
        by_cases hl : d u ∈ l
        · rw [if_pos hl, if_pos (List.mem_cons_of_mem _ hl)]
        · rw [if_neg hl, if_neg (show d u ∉ e :: l from by simp [he, hl])]

open scoped Classical in
/-- **Finite case distinction.**  If the value `d u ∈ D` of a "parameter" of the
input is decided by a regular condition for every `e : D`, and `g e` is regular
for every `e`, then `u ↦ g (d u) u` is regular. -/
theorem isRegularFun_ofFiniteCases [Finite D] (d : List A → D) (g : D → List A → List B)
    (hg : ∀ e, IsRegularFun (g e))
    (hd : ∀ e : D, Language.IsRegular {u : List A | d u = e}) :
    IsRegularFun (fun u => g (d u) u) := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  have h := isRegularFun_casesOn_list d g hg hd (Finset.univ : Finset D).toList
  exact h.congr (fun u => by simp)

end Cases

/-- **Bounded concatenation.**  The concatenation of finitely many regular
functions is regular. -/
theorem isRegularFun_flatMapRange {g : ℕ → List A → List B} (hg : ∀ j, IsRegularFun (g j)) :
    ∀ n : ℕ, IsRegularFun (fun u => (List.range n).flatMap (fun j => g j u)) := by
  intro n
  induction n with
  | zero => simpa using isRegularFun_nil (A := A) (B := B)
  | succ n ih =>
      have h := isRegularFun_concat ih (hg n)
      refine h.congr ?_
      intro u
      rw [List.range_succ, List.flatMap_append]
      simp

open RegCl RegPair in
/-- **Reversal is a regular function.**  It is map reverse applied to a string
consisting of a single block. -/
theorem isRegularFun_reverse : IsRegularFun (List.reverse : List A → List A) := by
  have h1 : IsRegularFun (fun w : List A => w.map (some : A → Option A)) :=
    isRegularFun_map some
  have h2 : IsRegularFun (mapReverse A) := isRegularFun_mapReverse A
  have h3 : IsRegularFun (del : List (Option A) → List A) := isRegularFun_del
  refine ((h1.comp h2).comp h3).congr ?_
  intro w
  have hb : (w.map (some : A → Option A)) = blockStr [w] := (blockStr_singleton w).symm
  show del (mapReverse A (w.map some)) = w.reverse
  rw [hb, mapReverse, mapLift_blockStr _ _ (by simp), List.map_cons, List.map_nil,
    del_blockStr]
  simp

end Lax916827Proofs.Transducers
