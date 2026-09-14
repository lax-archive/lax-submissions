/-
Reverse is regular under string representation.  Part of the easy direction of Theorem
`thm:regular-terms` of *Transducers* (M. Bojańczyk).

Reverse is the one atomic term that is not computed by a machine reading its input from left to
right -- indeed the string reverse is not even a rational function.  It is instead obtained from
the map reverse of Definition `def:regular-functions`, through the marking of `CombMark.lean`:
reversing the marked string

    repr a₁ # ⋯ # repr aₙ

turns it into `reverse (repr aₙ) # ⋯ # reverse (repr a₁)`, so it reverses both the order of the
entries and the representation of each of them, and one application of map reverse repairs the
entries and leaves the new order alone.
-/
import Lax709149Proofs.Source.PartC.CombMark
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## Reversing a marked string -/

lemma optBlocks_snoc_cons (y : List Sym8) (ys : List (List Sym8)) (z : List Sym8) :
    optBlocks (y :: ys ++ [z]) = optBlocks (y :: ys) ++ none :: z.map some := by
  induction ys generalizing y with
  | nil =>
      rw [show (([y] : List (List Sym8)) ++ [z]) = [y, z] from rfl,
        optBlocks_cons (x := y) (xs := [z]), optBlocksTail_cons, optBlocks_singleton,
        optBlocks_singleton]
  | cons w ws ih =>
      rw [show ((y :: w :: ws) ++ [z]) = y :: ((w :: ws) ++ [z]) from rfl,
        optBlocks_cons (x := y),
        show ((w :: ws) ++ [z]) = w :: (ws ++ [z]) from rfl, optBlocksTail_cons,
        show (w :: (ws ++ [z])) = (w :: ws) ++ [z] from rfl, ih w,
        optBlocks_cons (x := y) (xs := w :: ws), optBlocksTail_cons]
      simp

/-- Reversing a marked string reverses the order of the blocks and each of the blocks. -/
lemma optBlocks_reverse (xs : List (List Sym8)) :
    (optBlocks xs).reverse = optBlocks (xs.reverse.map List.reverse) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hxs : xs with
      | nil => simp
      | cons y ys =>
          rw [optBlocks_cons, optBlocksTail_cons, List.reverse_append]
          rw [show ((x :: y :: ys).reverse.map List.reverse)
              = ((y :: ys).reverse.map List.reverse) ++ [x.reverse] by simp]
          rw [show ((y :: ys).reverse.map List.reverse)
              = (ys.reverse.map List.reverse ++ [y.reverse]) by simp]
          rw [show (ys.reverse.map List.reverse ++ [y.reverse])
              = (ys.reverse.map List.reverse) ++ [y.reverse] from rfl]
          have hne : ∃ u us, ys.reverse.map List.reverse ++ [y.reverse] = u :: us := by
            cases h : ys.reverse.map List.reverse with
            | nil => exact ⟨y.reverse, [], by simp⟩
            | cons u us => exact ⟨u, us ++ [y.reverse], by simp⟩
          obtain ⟨u, us, hu⟩ := hne
          rw [hu, optBlocks_snoc_cons]
          rw [← hu, ← (by simp : ((y :: ys).reverse.map List.reverse)
            = ys.reverse.map List.reverse ++ [y.reverse])]
          rw [hxs] at ih
          rw [← ih]
          simp

/-! ## Reverse under string representation -/

section Reverse

variable (A : Ty)

/-- The string function that computes reverse under string representation: mark, reverse the
string, apply the map reverse, unmark. -/
def reverseFun : List Sym8 → List Sym8 := fun w =>
  unmark (mapReverse Sym8 ((listMarkMach.run (listMarkN A) .start w).reverse))

lemma isRegularFun_reverseFun : IsRegularFun (reverseFun A) := by
  have h1 : IsRegularFun (fun w => (listMarkMach.run (listMarkN A) ListMarkMode.start w).reverse) :=
    (isRegularFun_listMarkRun A).comp' (isRegularFun_listReverse (Option Sym8)) (fun _ => rfl)
  have h2 : IsRegularFun (fun w =>
      mapReverse Sym8 ((listMarkMach.run (listMarkN A) ListMarkMode.start w).reverse)) :=
    h1.comp' (isRegularFun_mapReverse Sym8) (fun _ => rfl)
  exact h2.comp' isRegularFun_unmark (fun _ => rfl)

/-- **Reverse is regular under string representation.** -/
theorem isRegularUnderRepr_reverse :
    IsRegularUnderRepr (A := Ty.list A) (B := Ty.list A) (fun l => l.reverse) := by
  refine ⟨reverseFun A, isRegularFun_reverseFun A, fun l => ?_⟩
  rw [reverseFun, listMarkMach_run, optBlocks_reverse, mapReverse,
    mapLift_optBlocks (by simp) _, List.map_map]
  rw [show (List.reverse ∘ List.reverse : List Sym8 → List Sym8) = id from by
    funext u; simp]
  rw [List.map_id, ← List.map_reverse, unmark_optBlocks]

end Reverse

end Comb
end Lax709149Proofs.Transducers
