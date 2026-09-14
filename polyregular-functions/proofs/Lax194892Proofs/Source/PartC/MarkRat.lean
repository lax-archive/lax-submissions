/-
**From a finite family of regular languages of marked strings to a rational function.**

Theorem `thm:logic-rational-functions` (`Transducers.rational_iff_msoRelabelling_aux`) says that the
rational functions are exactly the mso relabellings: the functions that attach, to every position
of the input, the output string of the unique formula of a finite family that holds in that
position.  A formula with one free first-order variable is the same thing as a regular language of
strings with one marked position (`Transducers.MarkLogic.exists_form_of_regular`), so the theorem
can be used with regular languages in place of formulas.  That is what this file records, as it is
the shape in which the constructions of Part D produce their functions.
-/
import Lax314295Proofs.Source.PartC.MarkLogic
import Lax314295Proofs.Source.PartC.MSORatRelab
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers
namespace MarkRat

open MarkStr

variable {A B : Type} [Finite A] [Finite B] {ι : Type} [Finite ι]

/-- **A function selected, position by position, by a finite family of regular languages of marked
strings, is rational.**  The family `K` is required to select, in every position of every input,
exactly one index; the function outputs the string `out i` of the selected index `i`, and the
string `e` on the empty input. -/
theorem isRationalFun_of_marked (K : ι → Language (Mark2 A)) (hK : ∀ i, (K i).IsRegular)
    (out : ι → List B) (e : List B) (sel : List A → ℕ → ι)
    (hsel : ∀ (w : List A) (x : ℕ), x < w.length → ∀ i, (markAt2 w x x ∈ K i ↔ i = sel w x))
    (f : List A → List B)
    (hf : ∀ w, f w = if w = [] then e
      else ((List.range w.length).map fun x => out (sel w x)).flatten) :
    IsRationalFun f := by
  classical
  choose form hform using fun i => MarkLogic.exists_form_of_regular (K i) (hK i)
  refine RatRelab.isRationalFun_of_msoRelabelling
    ⟨{ Idx := ι, finIdx := inferInstance, form := form, out := out, emptyOut := e,
       unique := ?_ }, ?_⟩
  · intro w p hp
    refine ⟨sel w p, ?_, ?_⟩
    · exact (hform _ w p).2 ((hsel w p hp _).2 rfl)
    · intro i hi
      exact (hsel w p hp i).1 ((hform i w p).1 hi)
  · intro w
    by_cases hw : w = []
    · exact Or.inl ⟨hw, by rw [hf, if_pos hw]⟩
    · exact Or.inr ⟨hw, sel w, fun p hp => (hform _ w p).2 ((hsel w p hp _).2 rfl),
        by rw [hf, if_neg hw]⟩

/-- **A function whose output letter is determined, position by position, by the truth values of a
finite family of regular languages of marked strings, is rational.**  This is the shape in which
Part D builds its functions: a finite family of *atoms* -- regular properties of the input string
with one distinguished position -- and an output string that depends on the vector `bits` of their
truth values in that position. -/
theorem isRationalFun_of_atoms {J : Type} [Finite J] (atom : J → Language (Mark2 A))
    (hatom : ∀ j, (atom j).IsRegular) (out : (J → Bool) → List B) (e : List B)
    (bits : List A → ℕ → J → Bool)
    (hbits : ∀ w x j, bits w x j = true ↔ markAt2 w x x ∈ atom j)
    (f : List A → List B)
    (hf : ∀ w, f w = if w = [] then e
      else ((List.range w.length).map fun x => out (bits w x)).flatten) :
    IsRationalFun f := by
  classical
  refine isRationalFun_of_marked
    (K := fun d : J → Bool => {u : List (Mark2 A) | ∀ j, (u ∈ atom j ↔ d j = true)})
    (fun d => ?_) out e (fun w x => bits w x) (fun w x _ d => ?_) f hf
  · letI : Fintype J := Fintype.ofFinite J
    have hall := RegAut.isRegular_forall_list
      (fun j : J => {u : List (Mark2 A) | u ∈ atom j ↔ d j = true})
      (Finset.univ : Finset J).toList
      (fun j _ => by
        by_cases hd : d j = true
        · refine RegAut.isRegular_of_eq (hatom j) (fun u => ?_)
          show (u ∈ atom j ↔ d j = true) ↔ u ∈ atom j
          rw [hd]
          simp
        · simp only [Bool.not_eq_true] at hd
          refine RegAut.isRegular_of_eq (RegAut.isRegular_not (hatom j)) (fun u => ?_)
          show (u ∈ atom j ↔ d j = true) ↔ u ∉ atom j
          rw [hd]
          simp)
    refine RegAut.isRegular_of_eq hall (fun u => ?_)
    exact ⟨fun h j _ => h j, fun h j => h j (by simp)⟩
  · show markAt2 w x x ∈ {u : List (Mark2 A) | ∀ j, (u ∈ atom j ↔ d j = true)} ↔ d = bits w x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      funext j
      exact Bool.eq_iff_iff.2 ((h j).symm.trans (hbits w x j).symm)
    · rintro rfl j
      exact (hbits w x j).symm

end MarkRat
end Lax194892Proofs.Transducers
