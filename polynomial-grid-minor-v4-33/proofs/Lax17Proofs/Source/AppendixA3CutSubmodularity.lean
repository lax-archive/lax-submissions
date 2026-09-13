import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Cut submodularity for Chuzhoy Section 7

This file proves the two finite edge-cut inequalities used in Claim 7.3 of
Chuzhoy's parallel cluster-splitting argument.  Both statements count ambient
edges with exactly one endpoint in the indicated vertex set.
-/

namespace SimpleGraph
namespace Section44


variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : _root_.SimpleGraph V)

/-- Whether an unordered pair has exactly one endpoint in `S`. -/
private def crossesSet (S : Finset V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y => (x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S), by
    intro x y
    aesop⟩

/-- The `0`--`1` contribution of an edge to the boundary of `S`. -/
private noncomputable def crossingIndicator
    (G : _root_.SimpleGraph V) (S : Finset V) : Sym2 V → ℕ := by
  classical
  exact Sym2.lift ⟨fun x y =>
    if s(x, y) ∈ G.edgeSet ∧
        ((x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S)) then 1 else 0, by
      intro x y
      simp [or_comm, G.adj_comm]⟩

private theorem mem_clusterBoundary_iff_crossesSet
    (S : Finset V) (e : Sym2 V) :
    e ∈ clusterBoundary G S ↔ e ∈ G.edgeSet ∧ crossesSet S e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [clusterBoundary, mem_edgeBoundary, crossesSet,
        Sym2.lift_mk, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨he, a, ha, b, hb, hab⟩
        rw [Sym2.eq_iff] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨he, Or.inl ⟨ha, hb⟩⟩
        · exact ⟨he, Or.inr ⟨ha, hb⟩⟩
      · rintro ⟨he, hcross⟩
        refine ⟨he, ?_⟩
        rcases hcross with hcross | hcross
        · exact ⟨x, hcross.1, y, hcross.2, rfl⟩
        · exact ⟨y, hcross.1, x, hcross.2, Sym2.eq_swap⟩

private theorem clusterBoundary_card_eq_sum_indicator (S : Finset V) :
    (clusterBoundary G S).card =
      ∑ e ∈ (Finset.univ : Finset (Sym2 V)), crossingIndicator G S e := by
  classical
  calc
    (clusterBoundary G S).card =
        ∑ e ∈ (Finset.univ : Finset (Sym2 V)),
          if e ∈ clusterBoundary G S then 1 else 0 := by simp
    _ = ∑ e ∈ (Finset.univ : Finset (Sym2 V)),
          crossingIndicator G S e := by
      apply Finset.sum_congr rfl
      intro e _
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [mem_clusterBoundary_iff_crossesSet G]
          simp [crossingIndicator, crossesSet]

private theorem crossing_indicator_submodular
    (A M : Finset V) (e : Sym2 V) :
    crossingIndicator G (A ∪ M) e + crossingIndicator G (A ∩ M) e ≤
      crossingIndicator G A e + crossingIndicator G M e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases he : s(x, y) ∈ G.edgeSet
      · by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A <;>
          by_cases hxM : x ∈ M <;> by_cases hyM : y ∈ M <;>
          simp [crossingIndicator, he, hxA, hyA, hxM, hyM]
      · simp [crossingIndicator, he]

private theorem crossing_indicator_posimodular
    (A M : Finset V) (e : Sym2 V) :
    crossingIndicator G (A \ M) e + crossingIndicator G (M \ A) e ≤
      crossingIndicator G A e + crossingIndicator G M e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases he : s(x, y) ∈ G.edgeSet
      · by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A <;>
          by_cases hxM : x ∈ M <;> by_cases hyM : y ∈ M <;>
          simp [crossingIndicator, he, hxA, hyA, hxM, hyM]
      · simp [crossingIndicator, he]

/-- Submodularity of the ambient edge boundary:
`|delta(A union M)| + |delta(A inter M)| <= |delta(A)| + |delta(M)|`. -/
theorem clusterBoundary_union_add_inter_card_le
    (A M : Finset V) :
    (clusterBoundary G (A ∪ M)).card +
        (clusterBoundary G (A ∩ M)).card ≤
      (clusterBoundary G A).card + (clusterBoundary G M).card := by
  classical
  rw [clusterBoundary_card_eq_sum_indicator G (A ∪ M),
    clusterBoundary_card_eq_sum_indicator G (A ∩ M),
    clusterBoundary_card_eq_sum_indicator G A,
    clusterBoundary_card_eq_sum_indicator G M,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ => crossing_indicator_submodular G A M e

/-- Posimodularity of the ambient edge boundary, in the difference form used
for `Z' = M \ A` in Chuzhoy's Claim 7.3. -/
theorem clusterBoundary_sdiff_add_sdiff_card_le
    (A M : Finset V) :
    (clusterBoundary G (A \ M)).card +
        (clusterBoundary G (M \ A)).card ≤
      (clusterBoundary G A).card + (clusterBoundary G M).card := by
  classical
  rw [clusterBoundary_card_eq_sum_indicator G (A \ M),
    clusterBoundary_card_eq_sum_indicator G (M \ A),
    clusterBoundary_card_eq_sum_indicator G A,
    clusterBoundary_card_eq_sum_indicator G M,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ => crossing_indicator_posimodular G A M e

end Section44
end SimpleGraph

end Lax17Proofs
