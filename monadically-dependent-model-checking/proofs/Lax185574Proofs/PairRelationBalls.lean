import Lax185574.PairRelationBalls
import Lax185574Proofs.BipartiteWalks

namespace Lax185574Proofs.PairRelationBalls

open Lax185574.PairRelation Lax185574.Flips Lax185574.GraphBalls Lax185574.BipartiteGraphs
open Lax185574.Partitions Lax185574.GaifmanGraph
open Lax185574Proofs.WithinDistBasics Lax185574Proofs.BipartiteWalks

universe z

variable {V : Type z}

/-- The vertex of `V` that a vertex of `V ⊕ V` is a copy of. -/
def proj : V ⊕ V → V := Sum.elim id id

/-- Projecting a walk in the bipartite graph of `E` to `V`: if every
edge `ab` of `E` has `a = b` or `ab` an edge of `H`, then walks project to
walks of at most the same length. -/
theorem withinDist_proj (H : SimpleGraph V) {E : V → V → Prop}
    (hE : ∀ a b, E a b → a = b ∨ H.Adj a b) {d : ℕ} {u v : V}
    (h : WithinDist (bipartiteGraph E) d (.inl u) (.inr v)) : WithinDist H d u v := by
  refine withinDist_of_project (K := bipartiteGraph E) proj (fun s t hst => ?_) h
  rcases s with a | b <;> rcases t with a' | b'
  · exact absurd hst (not_adj_inl_inl E _ _)
  · exact hE _ _ ((adj_inl_inr E _ _).mp hst)
  · rcases hE _ _ ((adj_inr_inl E _ _).mp hst) with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
  · exact absurd hst (not_adj_inr_inr E _ _)

/-- A pair of `R(G, 𝒫)` is within distance `5` in every `𝒫`-flip. -/
theorem withinDist_of_adj (G : SimpleGraph V) (P : Setoid V) {u v : V}
    (huv : (pairRelation G P).Adj u v) (H : SimpleGraph V) (hH : IsFlip G P H) :
    WithinDist H 5 u v := by
  have key : ∀ x y : V,
      WithinDist (pairGraph G (part P x) (part P y)) 5 (.inl x) (.inr y) ∧
        WithinDist (coPairGraph G (part P x) (part P y)) 5 (.inl x) (.inr y) →
      WithinDist H 5 x y := by
    rintro x y ⟨hpos, hneg⟩
    rcases hH x y with hagree | hdis
    · refine withinDist_proj H (fun a b hab => ?_) hpos
      obtain ⟨ha, hb, h | h⟩ := hab
      · exact Or.inl h
      · exact Or.inr ((hagree a b ha hb (G.ne_of_adj h)).mpr h)
    · refine withinDist_proj H (fun a b hab => ?_) hneg
      obtain ⟨ha, hb, h | h⟩ := hab
      · exact Or.inl h
      · by_cases hne : a = b
        · exact Or.inl hne
        · exact Or.inr ((hdis a b ha hb hne).mpr h)
  rw [pairRelation, SimpleGraph.fromRel_adj] at huv
  rcases huv.2 with h | h
  · exact key u v h
  · exact withinDist_symm' (key v u h)

/--
---
conclusion: Lax185574.PairRelationBalls.graphBall_pairRelation_subset
---
As in the paper, every pair `uv ∈ R` has `dist_𝒫(u, v) ≤ 5`. In a
`𝒫`-flip `H`, the bipartite graph `H[X, Y]` is `G[X, Y]` or `Ḡ[X, Y]`,
and the walk of length at most `5` there projects to a walk in `H` by
contracting diagonal edges. A walk of length at most `r` in `R` then
gives a walk of length at most `5r` in every `𝒫`-flip.
-/
theorem graphBall_pairRelation_subset (G : SimpleGraph V) (P : Setoid V)
    (r : ℕ) (v : V) :
    graphBall (pairRelation G P) r {v} ⊆ flipBall G P (5 * r) v := by
  rintro w ⟨c, hc, hcw⟩
  rw [Set.mem_singleton_iff.mp hc] at hcw
  intro H hH
  exact withinDist_of_steps (K := pairRelation G P) id 5
    (fun s t hst => withinDist_of_adj G P hst H hH) hcw

end Lax185574Proofs.PairRelationBalls
