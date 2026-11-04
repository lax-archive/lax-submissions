import Lax185574Proofs.FlipBasics
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum

/-!
The partition into atomic types over a finite set `S` has at most
`3^|S|` parts: the vertices of `S` are singletons, and the others are
grouped by their neighborhood in `S`.
-/

namespace Lax185574Proofs.AtomicPartitionCount

open Lax185574.Partitions

universe u w

variable {V : Type u}

/-- A partition described exactly by the fibers of a map into a finite
type has at most as many parts as that type has elements. -/
theorem card_quotient_le_of_iff {β : Type w} [Finite β] (P : Setoid V) (g : V → β)
    (hg : ∀ x y, P x y ↔ g x = g y) : Nat.card (Quotient P) ≤ Nat.card β := by
  have hinj : Function.Injective (Quotient.lift g fun x y h => (hg x y).mp h :
      Quotient P → β) := by
    rintro ⟨a⟩ ⟨b⟩ h
    exact Quotient.sound ((hg a b).mpr h)
  exact Nat.card_le_card_of_injective _ hinj

theorem add_two_pow_le_three_pow (m : ℕ) : m + 2 ^ m ≤ 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by omega) m
    have h2 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ, pow_succ]
    omega

/-- The partition into atomic types over a finite set `S` has at most
`3^|S|` parts. -/
theorem card_quotient_atomicTypes_le (G : SimpleGraph V) (S : Finset V) :
    Nat.card (Quotient (atomicTypes G (S : Set V))) ≤ 3 ^ S.card := by
  classical
  let g : V → S ⊕ Finset S := fun v =>
    if h : v ∈ S then .inl ⟨v, h⟩ else .inr (Finset.univ.filter fun s : S => G.Adj v s)
  have hg : ∀ x y, atomicTypes G (S : Set V) x y ↔ g x = g y := by
    intro x y
    rw [Lax185574Proofs.FlipBasics.atomicTypes_rel_iff']
    constructor
    · rintro (rfl | ⟨hx, hy, h⟩)
      · rfl
      · have hx' : x ∉ S := hx
        have hy' : y ∉ S := hy
        simp only [g, hx', hy', dite_false, Sum.inr.injEq]
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h s s.2
    · intro h
      by_cases hx : x ∈ S
      · by_cases hy : y ∈ S
        · simp only [g, hx, hy, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at h
          exact Or.inl h
        · simp [g, hx, hy] at h
      · by_cases hy : y ∈ S
        · simp [g, hx, hy] at h
        · simp only [g, hx, hy, dite_false, Sum.inr.injEq] at h
          refine Or.inr ⟨hx, hy, fun s hs => ?_⟩
          have := congrArg (fun T => (⟨s, hs⟩ : S) ∈ T) h
          simpa using this
  refine (card_quotient_le_of_iff _ g hg).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_finset, Fintype.card_coe]
  exact add_two_pow_le_three_pow _

end Lax185574Proofs.AtomicPartitionCount
