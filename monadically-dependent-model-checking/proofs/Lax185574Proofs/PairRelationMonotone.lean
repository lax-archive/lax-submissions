import Lax185574.PairRelationMonotone
import Lax185574Proofs.BipartiteWalks

namespace Lax185574Proofs.PairRelationMonotone

open Lax185574.PairRelation Lax185574.BipartiteGraphs Lax185574.Partitions
open Lax185574.GaifmanGraph Lax185574Proofs.WithinDistBasics Lax185574Proofs.BipartiteWalks

universe z

variable {V : Type z}

theorem part_mono {P P' : Setoid V} (h : P ≤ P') (v : V) : part P v ⊆ part P' v :=
  fun _ hw => h hw

theorem pairGraph_mono (G : SimpleGraph V) {X Y X' Y' : Set V} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    pairGraph G X Y ≤ pairGraph G X' Y' :=
  bipartiteGraph_mono fun _ _ h => ⟨hX h.1, hY h.2.1, h.2.2⟩

theorem coPairGraph_mono (G : SimpleGraph V) {X Y X' Y' : Set V} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    coPairGraph G X Y ≤ coPairGraph G X' Y' :=
  bipartiteGraph_mono fun _ _ h => ⟨hX h.1, hY h.2.1, h.2.2⟩

/--
---
conclusion: Lax185574.PairRelationMonotone.pairRelation_mono
---
On two copies of `V`, the graph `G[X, Y]` is a subgraph of `G[X', Y']`
whenever `X ⊆ X'` and `Y ⊆ Y'`, and likewise for `Ḡ[X, Y]`. The parts of
`𝒫` lie in the parts of `𝒫'`, so every short walk witnessing `uv ∈ R(G, 𝒫)`
is a walk in the graphs for `𝒫'`.
-/
theorem pairRelation_mono (G : SimpleGraph V) (P P' : Setoid V)
    (h : P ≤ P') : pairRelation G P ≤ pairRelation G P' := by
  have key : ∀ u v : V,
      (WithinDist (pairGraph G (part P u) (part P v)) 5 (.inl u) (.inr v) ∧
        WithinDist (coPairGraph G (part P u) (part P v)) 5 (.inl u) (.inr v)) →
      (WithinDist (pairGraph G (part P' u) (part P' v)) 5 (.inl u) (.inr v) ∧
        WithinDist (coPairGraph G (part P' u) (part P' v)) 5 (.inl u) (.inr v)) :=
    fun u v huv =>
      ⟨withinDist_le_graph (pairGraph_mono G (part_mono h u) (part_mono h v)) huv.1,
        withinDist_le_graph (coPairGraph_mono G (part_mono h u) (part_mono h v)) huv.2⟩
  intro u v huv
  rw [pairRelation, SimpleGraph.fromRel_adj] at huv ⊢
  exact ⟨huv.1, huv.2.imp (key u v) (key v u)⟩

end Lax185574Proofs.PairRelationMonotone
