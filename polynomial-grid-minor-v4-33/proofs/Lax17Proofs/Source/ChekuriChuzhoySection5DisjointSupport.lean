import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Counting disjoint finite supports

These elementary lemmas are used for the edge groups created by Mader
splitting.  Direct-edge groups draw nonempty disjoint supports from two
doubled copies.  A split-at-`s` group draws at least two copies per output edge
from the doubled star at `s`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

/-- A family of nonempty pairwise-disjoint supports injects into any finite
set containing their union. -/
theorem card_le_card_of_disjoint_nonempty_support
    {I : Type u} {A : Type v} [DecidableEq I] [DecidableEq A]
    (items : Finset I) (support : I → Finset A) (available : Finset A)
    (hnonempty : ∀ i ∈ items, (support i).Nonempty)
    (hpairwise : (↑items : Set I).PairwiseDisjoint support)
    (hsubset : ∀ i ∈ items, support i ⊆ available) :
    items.card ≤ available.card := by
  classical
  have hunionSubset : items.biUnion support ⊆ available := by
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨i, hi, hai⟩
    exact hsubset i hi hai
  exact (Finset.card_le_card_biUnion hpairwise hnonempty).trans
    (Finset.card_le_card hunionSubset)

/-- If every pairwise-disjoint support has at least `q` elements, then
`q * items.card` is bounded by the containing set. -/
theorem mul_card_le_card_of_disjoint_support
    {I : Type u} {A : Type v} [DecidableEq I] [DecidableEq A]
    (q : Nat) (items : Finset I) (support : I → Finset A)
    (available : Finset A)
    (hsize : ∀ i ∈ items, q ≤ (support i).card)
    (hpairwise : (↑items : Set I).PairwiseDisjoint support)
    (hsubset : ∀ i ∈ items, support i ⊆ available) :
    q * items.card ≤ available.card := by
  classical
  have hunionSubset : items.biUnion support ⊆ available := by
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨i, hi, hai⟩
    exact hsubset i hi hai
  calc
    q * items.card = ∑ _i ∈ items, q := by
      simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ items, (support i).card := by
      exact Finset.sum_le_sum fun i hi => hsize i hi
    _ = (items.biUnion support).card :=
      (Finset.card_biUnion hpairwise).symm
    _ ≤ available.card := Finset.card_le_card hunionSubset

end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
