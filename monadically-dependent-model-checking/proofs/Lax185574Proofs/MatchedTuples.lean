import Lax185574.MatchedTuples
import Lax185574Proofs.Lib.BipartiteRamsey
import Lax185574Proofs.BipartiteBasics

namespace Lax185574Proofs.MatchedTuples

open Lax185574.AtomicMatching Lax185574.AtomicTypes Lax185574.BipartiteGraphs
open Lax185574Proofs.BipartiteBasics

universe u v

/--
---
conclusion: Lax185574.MatchedTuples.exists_atomicallyMatched
---
Ding, Oporowski, Oxley and Vertigan, Cor. 2.4, through an explicit Ramsey bound and a staircase argument
on homogeneous matrices. The number of atomic types of the left side
over the right side is the number of distinct neighborhoods. A
half-graph with `i ≤ j` becomes one with `j ≤ i` by reversing both
tuples.
-/
theorem exists_atomicallyMatched :
    ∃ Q : ℕ → ℕ, Computable Q ∧
      ∀ (ℓ : ℕ) (L : Type u) (R : Type v) [Finite L] [Finite R] (E : L → R → Prop),
        Q ℓ < atomicTypeCount (bipartiteGraph E) (Set.range Sum.inl)
            (Set.range Sum.inr) →
          ∃ (a : Fin ℓ → L) (b : Fin ℓ → R),
            AtomicallyMatched (bipartiteGraph E) (Sum.inl ∘ a) (Sum.inr ∘ b) := by
  obtain ⟨Q, hQc, hQ⟩ := Lax185574Proofs.Lib.BipartiteRamsey.exists_computable_pattern_bound.{u, v}
  refine ⟨Q, hQc, fun ℓ L R _ _ E h => ?_⟩
  classical
  have := Fintype.ofFinite L
  have := Fintype.ofFinite R
  rw [atomicTypeCount_eq_card] at h
  obtain ⟨a, b, -, -, hm⟩ := hQ ℓ L R E h.le
  rcases hm with hm | hm | hm
  · exact ⟨a, b, Or.inl fun i j => by simpa using hm i j⟩
  · exact ⟨a, b, Or.inr (Or.inl fun i j => by simpa using hm i j)⟩
  · refine ⟨a ∘ Fin.rev, b ∘ Fin.rev, Or.inr (Or.inr fun i j => ?_)⟩
    simpa [Fin.rev_le_rev] using hm (Fin.rev i) (Fin.rev j)

end Lax185574Proofs.MatchedTuples
