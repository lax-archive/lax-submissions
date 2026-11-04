import Lax185574Proofs.Lib.BipartiteMetricConversion
import Lax185574Proofs.Lib.GraphMetricConversion

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-! Transport the local one-part and two-part short walks into any flip
of the original partition. -/

namespace Lax185574Proofs.Lib.PartitionMetricTransfer

open Lax185574Proofs.Lib.PartitionMetricConversion PartitionMetricWalks BipartiteMetricConversion

universe u
variable {V : Type u} {p : ℕ} (G : SimpleGraph V) (part : V → Fin p)

abbrev Fiber (i : Fin p) := {v : V // part v = i}

theorem distinct_fibers {i j : Fin p} (hij : i ≠ j) (x : Fiber part i) (y : Fiber part j) :
    x.val ≠ y.val := by
  intro h
  exact hij (x.property.symm.trans ((congrArg part h).trans y.property))

theorem diagonal_transfer (T : Fin p → Fin p → Bool) (hT : ∀ i j, T i j = T j i)
    {i : Fin p} {x y : Fiber part i} {r : ℕ}
    (h₀ : Within (G.comap Subtype.val) r x y)
    (h₁ : Within (G.comap Subtype.val)ᶜ r x y) :
    Within (flip G part T hT) r x.val y.val := by
  cases ht : T i i with
  | false =>
    refine within_map Subtype.val ?_ h₀
    intro a b hab
    have hab' : G.Adj a.val b.val := hab
    change a.val ≠ b.val ∧ Xor (G.Adj a.val b.val) (T (part a.val) (part b.val) = true)
    exact ⟨hab'.ne, by simpa [a.property, b.property, ht, Xor] using hab'⟩
  | true =>
    refine within_map Subtype.val ?_ h₁
    intro a b hab
    change a ≠ b ∧ ¬G.Adj a.val b.val at hab
    change a.val ≠ b.val ∧ Xor (G.Adj a.val b.val) (T (part a.val) (part b.val) = true)
    exact ⟨fun h => hab.1 (Subtype.ext h), by simpa [a.property, b.property, ht, Xor] using hab.2⟩

theorem bipartite_transfer (T : Fin p → Fin p → Bool) (hT : ∀ i j, T i j = T j i)
    {i j : Fin p} (hij : i ≠ j) {x : Fiber part i} {y : Fiber part j} {r : ℕ}
    (h₀ : Within (bipGraph (fun a : Fiber part i => fun b : Fiber part j => G.Adj a.val b.val))
      r (.inl x) (.inr y))
    (h₁ : Within (bipGraph (fun a : Fiber part i => fun b : Fiber part j => ¬G.Adj a.val b.val))
      r (.inl x) (.inr y)) :
    Within (flip G part T hT) r x.val y.val := by
  let f : Fiber part i ⊕ Fiber part j → V := Sum.elim Subtype.val Subtype.val
  cases ht : T i j with
  | false =>
    have hedge (a : Fiber part i) (b : Fiber part j) (hab : G.Adj a.val b.val) :
        (flip G part T hT).Adj a.val b.val := by
      exact ⟨distinct_fibers part hij a b, by simpa [a.property, b.property, ht, Xor] using hab⟩
    refine within_map f ?_ h₀
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact False.elim hab
      | inr b => exact hedge a b hab
    | inr a =>
      cases b with
      | inl b => exact (hedge b a hab).symm
      | inr b => exact False.elim hab
  | true =>
    have hedge (a : Fiber part i) (b : Fiber part j) (hab : ¬G.Adj a.val b.val) :
        (flip G part T hT).Adj a.val b.val := by
      exact ⟨distinct_fibers part hij a b, by simpa [a.property, b.property, ht, Xor] using hab⟩
    refine within_map f ?_ h₁
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact False.elim hab
      | inr b => exact hedge a b hab
    | inr a =>
      cases b with
      | inl b => exact (hedge b a hab).symm
      | inr b => exact False.elim hab

end Lax185574Proofs.Lib.PartitionMetricTransfer
