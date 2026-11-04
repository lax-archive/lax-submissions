import Lax185574.HomogeneousSplitting
import Lax185574.ComplementDiameter
import Lax185574.BipartiteFlip
import Lax185574Proofs.BipartiteWalks

namespace Lax185574Proofs.HomogeneousSplitting

open Lax185574.Partitions Lax185574.PairRelation Lax185574.TypeSplitting
open Lax185574.MergeSequences Lax185574.BipartiteGraphs Lax185574.GaifmanGraph
open Lax185574Proofs.WithinDistBasics Lax185574Proofs.BipartiteWalks

universe z

variable {V : Type z}

theorem part_eq {P : Setoid V} {x a : V} (h : P x a) : part P x = part P a := by
  ext w
  exact ⟨fun hw => P.trans hw h, fun hw => P.trans hw (P.symm h)⟩

theorem rel_of_split {G : SimpleGraph V} {P : Setoid V} {T : Set V} {x a : V}
    (h : split G P T x a) : P x a :=
  Quotient.exact (Prod.mk.inj h).1

/-- Two vertices in the same part of `𝒫 ∧ T` have the same adjacency to
every vertex of `T` outside their part of `𝒫`. -/
theorem adj_iff_of_split {G : SimpleGraph V} {P : Setoid V} {T : Set V} {x a t : V}
    (h : split G P T x a) (ht : t ∈ T) (hta : ¬ P t a) : (G.Adj x t ↔ G.Adj a t) := by
  have hxa := rel_of_split h
  have htx : ¬ P t x := fun h' => hta (P.trans h' hxa)
  have hset := Set.ext_iff.mp (Prod.mk.inj h).2 t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet] at hset
  exact ⟨fun h' => (hset.mp ⟨⟨ht, htx⟩, h'⟩).2, fun h' => (hset.mpr ⟨⟨ht, hta⟩, h'⟩).2⟩

/-- A walk inside a set `X` lifts to a walk of the same length in the
bipartite graph on two copies of `X` with diagonal edges, from either
copy of its start to some copy of its end. -/
theorem lift_walk_aux {X : Set V} {K : SimpleGraph X} {A : V → V → Prop}
    (hK : ∀ s t, K.Adj s t → A s.1 t.1) {s t : X} (p : K.Walk s t) :
    (WithinDist (bipartiteGraph fun u v => u ∈ X ∧ v ∈ X ∧ (u = v ∨ A u v)) p.length
        (.inl s.1) (.inl t.1) ∨
      WithinDist (bipartiteGraph fun u v => u ∈ X ∧ v ∈ X ∧ (u = v ∨ A u v)) p.length
        (.inl s.1) (.inr t.1)) ∧
    (WithinDist (bipartiteGraph fun u v => u ∈ X ∧ v ∈ X ∧ (u = v ∨ A u v)) p.length
        (.inr s.1) (.inl t.1) ∨
      WithinDist (bipartiteGraph fun u v => u ∈ X ∧ v ∈ X ∧ (u = v ∨ A u v)) p.length
        (.inr s.1) (.inr t.1)) := by
  induction p with
  | nil => exact ⟨Or.inl (withinDist_refl _ _), Or.inr (withinDist_refl _ _)⟩
  | cons hadj p ih =>
    rename_i a b c
    have h1 : (bipartiteGraph fun u v => u ∈ X ∧ v ∈ X ∧ (u = v ∨ A u v)).Adj
        (.inl a.1) (.inr b.1) := (adj_inl_inr _ _ _).mpr ⟨a.2, b.2, Or.inr (hK _ _ hadj)⟩
    have h2 : (bipartiteGraph fun u v => u ∈ X ∧ v ∈ X ∧ (u = v ∨ A u v)).Adj
        (.inr a.1) (.inl b.1) := (adj_inr_inl _ _ _).mpr ⟨b.2, a.2, Or.inr (hK _ _ hadj.symm)⟩
    rw [SimpleGraph.Walk.length_cons, Nat.add_comm]
    exact ⟨ih.2.imp (withinDist_trans (withinDist_adj h1)) (withinDist_trans (withinDist_adj h1)),
      ih.1.imp (withinDist_trans (withinDist_adj h2)) (withinDist_trans (withinDist_adj h2))⟩

/-- A walk inside a set `X` lifts to a walk between opposite copies in the
bipartite graph on two copies of `X` with diagonal edges, at the cost of
at most one extra step. -/
theorem lift_walk {X : Set V} {K : SimpleGraph X} {A : V → V → Prop}
    (hK : ∀ s t, K.Adj s t → A s.1 t.1) {s t : X} (p : K.Walk s t) :
    WithinDist (bipartiteGraph fun u v => u ∈ X ∧ v ∈ X ∧ (u = v ∨ A u v)) (p.length + 1)
        (.inl s.1) (.inr t.1) := by
  rcases (lift_walk_aux hK p).1 with h | h
  · exact withinDist_trans h (withinDist_adj ((adj_inl_inr _ _ _).mpr ⟨t.2, t.2, Or.inl rfl⟩))
  · exact withinDist_mono (Nat.le_succ _) h

/-- Within one part `X` of `𝒫`: if `G[X]` has diameter at most `3`, then
all non-adjacent pairs of `X` lie in `R`, and if `Ḡ[X]` has, then all
adjacent pairs do. -/
theorem same_part (G : SimpleGraph V) (P : Setoid V) (a : V) :
    (∀ x y, P x a → P y a → x ≠ y → ¬ G.Adj x y → (pairRelation G P).Adj x y) ∨
      (∀ x y, P x a → P y a → x ≠ y → G.Adj x y → (pairRelation G P).Adj x y) := by
  let X := part P a
  let K : SimpleGraph X := G.induce X
  have hrel : ∀ x y, P x a → P y a → x ≠ y →
      WithinDist (pairGraph G X X) 5 (.inl x) (.inr y) →
      WithinDist (coPairGraph G X X) 5 (.inl x) (.inr y) → (pairRelation G P).Adj x y := by
    intro x y hx hy hxy h1 h2
    rw [pairRelation, SimpleGraph.fromRel_adj]
    refine ⟨hxy, Or.inl ?_⟩
    rw [part_eq hx, part_eq hy]
    exact ⟨h1, h2⟩
  rcases Lax185574.ComplementDiameter.diameter_le_three_or_compl K with hK | hK
  · left
    intro x y hx hy hxy hn
    refine hrel x y hx hy hxy ?_ ?_
    · obtain ⟨p, hp⟩ := hK ⟨x, hx⟩ ⟨y, hy⟩
      have := (lift_walk (A := G.Adj) (fun s t h => h) p)
      exact withinDist_mono (by omega) this
    · refine withinDist_mono (by omega) (withinDist_adj ?_)
      exact (adj_inl_inr _ _ _).mpr ⟨hx, hy, Or.inr hn⟩
  · right
    intro x y hx hy hxy hn
    refine hrel x y hx hy hxy ?_ ?_
    · refine withinDist_mono (by omega) (withinDist_adj ?_)
      exact (adj_inl_inr _ _ _).mpr ⟨hx, hy, Or.inr hn⟩
    · obtain ⟨p, hp⟩ := hK ⟨x, hx⟩ ⟨y, hy⟩
      have := (lift_walk (A := fun u v => ¬ G.Adj u v)
        (fun s t h => ((SimpleGraph.compl_adj _ s t).mp h).2) p)
      exact withinDist_mono (by omega) this

/-- Between two different parts `X ∋ a` and `Y ∋ b` of `𝒫`: the flip of
the bipartite flip lemma for the representatives in `T` decides, for all
pairs of the parts of `𝒫 ∧ T` of `a` and `b` at once, which pairs lie in
`R`. -/
theorem different_parts (G : SimpleGraph V) (P : Setoid V) (T : Set V)
    (hT : IsTransversal P T) (a b : V) (hab : ¬ P a b) :
    (∀ x y, split G P T x a → split G P T y b → x ≠ y → ¬ (pairRelation G P).Adj x y →
        G.Adj x y) ∨
      (∀ x y, split G P T x a → split G P T y b → x ≠ y → ¬ (pairRelation G P).Adj x y →
        ¬ G.Adj x y) := by
  obtain ⟨tx, ⟨htxT, htx⟩, -⟩ := hT a
  obtain ⟨ty, ⟨htyT, hty⟩, -⟩ := hT b
  let X := part P a
  let Y := part P b
  let E : X → Y → Prop := fun u v => G.Adj u.1 v.1
  obtain ⟨E', hflip, hclose⟩ :=
    Lax185574.BipartiteFlip.exists_flip_close E ⟨tx, htx⟩ ⟨ty, hty⟩
  -- a pair whose flipped adjacency holds lies in `R`
  have hR : ∀ (u : X) (v : Y), E' u v → (pairRelation G P).Adj u.1 v.1 := by
    intro u v huv
    obtain ⟨h1, h2⟩ := hclose u v huv
    have hne : u.1 ≠ v.1 := fun h => hab (P.trans (P.symm u.2) (by rw [h]; exact v.2))
    rw [pairRelation, SimpleGraph.fromRel_adj]
    refine ⟨hne, Or.inl ?_⟩
    rw [part_eq u.2, part_eq v.2]
    refine ⟨withinDist_map' (bipartiteHom Subtype.val Subtype.val ?_) h1,
      withinDist_map' (bipartiteHom Subtype.val Subtype.val ?_) h2⟩
    · exact fun s t h => ⟨s.2, t.2, Or.inr h⟩
    · exact fun s t h => ⟨s.2, t.2, Or.inr h⟩
  have hcell : ∀ x y (hx : split G P T x a) (hy : split G P T y b),
      ((E' ⟨x, rel_of_split hx⟩ ⟨y, rel_of_split hy⟩ ↔ G.Adj x y) ↔
        (E' ⟨a, P.refl a⟩ ⟨b, P.refl b⟩ ↔ G.Adj a b)) := by
    intro x y hx hy
    refine hflip _ _ _ _ ?_ ?_
    · exact adj_iff_of_split hx htyT fun h => hab (P.trans (P.symm h) hty)
    · have := adj_iff_of_split hy htxT fun h => hab (P.trans (P.symm htx) h)
      exact (G.adj_comm _ _).trans (this.trans (G.adj_comm _ _))
  by_cases hβ : E' ⟨a, P.refl a⟩ ⟨b, P.refl b⟩ ↔ G.Adj a b
  · right
    intro x y hx hy _ hnR hadj
    have := (hcell x y hx hy).mpr hβ
    exact hnR (hR _ _ (this.mpr hadj))
  · left
    intro x y hx hy _ hnR
    by_contra hadj
    have h1 : ¬ (E' ⟨x, rel_of_split hx⟩ ⟨y, rel_of_split hy⟩ ↔ G.Adj x y) :=
      fun h => hβ ((hcell x y hx hy).mp h)
    have : E' ⟨x, rel_of_split hx⟩ ⟨y, rel_of_split hy⟩ := by
      by_contra h'
      exact h1 ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hadj⟩
    exact hnR (hR _ _ this)

/--
---
conclusion: Lax185574.HomogeneousSplitting.homogeneousModulo_split
---
As in the paper, for each pair of parts of `𝒬 = 𝒫 ∧ T` we find a flip of
`G` on these parts whose edges lie in `R`. Then the pairs outside `R`
are non-edges of the flip, so they are all edges or all non-edges of
`G`. Two parts of `𝒬` inside one part `X` of `𝒫`: by the diameter lemma,
`G[X]` or `Ḡ[X]` has diameter at most `3`. In the first case every
non-adjacent pair of `X` is joined by a walk of length at most `4`
between opposite copies in `G[X, X]` and by an edge in `Ḡ[X, X]`, so it
lies in `R`, and the second case is symmetric. Parts inside different
parts `X`, `Y` of `𝒫`: apply the bipartite flip lemma to `G[X, Y]` with
the representatives in `T`. The parts of `𝒬` refine the four parts of
that lemma, so the flip is constant on the pair.
-/
theorem homogeneousModulo_split {V : Type z} (G : SimpleGraph V) (P : Setoid V) (T : Set V)
    (hT : IsTransversal P T) :
    HomogeneousModulo G (split G P T) (pairRelation G P) := by
  intro a b
  by_cases hab : P a b
  · rcases same_part G P a with h | h
    · left
      intro x y hx hy hxy hnR
      by_contra hn
      exact hnR (h x y (rel_of_split hx) (P.trans (rel_of_split hy) (P.symm hab)) hxy hn)
    · right
      intro x y hx hy hxy hnR hadj
      exact hnR (h x y (rel_of_split hx) (P.trans (rel_of_split hy) (P.symm hab)) hxy hadj)
  · exact different_parts G P T hT a b hab

end Lax185574Proofs.HomogeneousSplitting
