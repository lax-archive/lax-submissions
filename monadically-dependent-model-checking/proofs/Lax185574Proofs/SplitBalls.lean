import Lax185574.SplitBalls
import Lax185574Proofs.WithinDistBasics

namespace Lax185574Proofs.SplitBalls

open Lax185574.Partitions Lax185574.Flips Lax185574.TypeSplitting Lax185574.VCDimension
open Lax185574.GaifmanGraph Lax199508.NeighborhoodComplexity Lax185574Proofs.WithinDistBasics

universe z

variable {V : Type z}

/-- If `g` separates the points of `s` at least as finely as `f`, then
`f` takes at most as many values on `s` as `g`. -/
theorem ncard_image_le_of_factor {α β γ : Type*} [Finite γ] (f : α → β) (g : α → γ) (s : Set α)
    (h : ∀ a ∈ s, ∀ b ∈ s, g a = g b → f a = f b) : (f '' s).ncard ≤ (g '' s).ncard := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  have : Nonempty α := ⟨a₀⟩
  have heq : f '' s = (f ∘ Function.invFunOn g s) '' (g '' s) := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨g a, ⟨a, ha, rfl⟩, ?_⟩
      have hex : ∃ a' ∈ s, g a' = g a := ⟨a, ha, rfl⟩
      exact h _ (Function.invFunOn_mem hex) a ha (Function.invFunOn_eq hex)
    · rintro ⟨c, ⟨a, ha, rfl⟩, rfl⟩
      have hex : ∃ a' ∈ s, g a' = g a := ⟨a, ha, rfl⟩
      exact ⟨_, Function.invFunOn_mem hex, rfl⟩
  rw [heq]
  exact Set.ncard_image_le (Set.toFinite _)

/-- The neighborhood complexity bounds the number of traces on any set
of at most `k` vertices. -/
theorem traceCount_le [Finite V] (G : SimpleGraph V) {k : ℕ} (S : Set V) (hS : S.ncard ≤ k) :
    traceCount G S ≤ neighborhoodComplexity G k := by
  classical
  have hfin : S.Finite := Set.toFinite S
  refine le_csSup ⟨Nat.card (Set V), ?_⟩ ⟨hfin.toFinset, ?_, ?_⟩
  · rintro m ⟨S', -, rfl⟩
    exact Set.ncard_le_card _
  · rwa [← Set.ncard_eq_toFinset_card S hfin]
  · simp

/-- A vertex `u` in the radius-`r` ball and a vertex `t` outside the
radius-`(r+1)` ball: the adjacency of `t` to `u` is the same for all
vertices `u'` in the same part of `𝒬` that lie in the radius-`r` ball. -/
theorem adj_far (G : SimpleGraph V) (Q : Setoid V) (r : ℕ) (v : V) {u u' t : V}
    (hu : u ∈ flipBall G Q r v) (hu' : u' ∈ flipBall G Q r v) (huu' : Q u' u)
    (ht : t ∉ flipBall G Q (r + 1) v) : (G.Adj u t ↔ G.Adj u' t) := by
  simp only [flipBall, FlipWithinDist, Set.mem_ofPred_eq, not_forall] at ht hu hu'
  obtain ⟨H, hH, hfar⟩ := ht
  have hnadj : ∀ w, WithinDist H r v w → ¬ H.Adj w t :=
    fun w hw hadj => hfar (withinDist_trans hw (withinDist_adj hadj))
  have hne : ∀ w, WithinDist H r v w → w ≠ t :=
    fun w hw he => hfar (withinDist_mono (Nat.le_succ r) (he ▸ hw))
  have h1 := hnadj u (hu H hH)
  have h2 := hnadj u' (hu' H hH)
  rcases hH u t with hag | hdis
  · rw [← hag u t (Q.refl u) (Q.refl t) (hne u (hu H hH)),
      ← hag u' t huu' (Q.refl t) (hne u' (hu' H hH))]
    exact iff_of_false h1 h2
  · have e1 := hdis u t (Q.refl u) (Q.refl t) (hne u (hu H hH))
    have e2 := hdis u' t huu' (Q.refl t) (hne u' (hu' H hH))
    exact iff_of_true (by_contra fun h => h1 (e1.mpr h)) (by_contra fun h => h2 (e2.mpr h))

/--
---
conclusion: Lax185574.SplitBalls.partCount_split_le
---
Let `B` be the radius-`r` ball and `B'` the radius-`(r+1)` ball of the
`𝒬`-flip metric around `v`, and `T' = T ∩ B'`. The transversal has one
vertex in each part of `𝒫`, so `|T'| ≤ |B'/𝒫| ≤ k`. Take `u ∈ B` and
`t ∈ T ∖ B'`. Some `𝒬`-flip `H` has no short walk from `v` to `t`, so
`u` and `t` are distinct and non-adjacent in `H`. Hence the adjacency of
`t` in `G` is the same for all vertices of `B` in the part `𝒬(u)`, which
contains `𝒫(u)`. So the part of `u` in `𝒫 ∧ T` is determined by its part
in `𝒫` and its trace on `T'`. There are at most `k` parts of `𝒫` meeting
`B`, and at most `π_G(k)` traces on `T'`.
-/
theorem partCount_split_le {V : Type z} [Finite V] (G : SimpleGraph V) (P Q : Setoid V)
    (T : Set V) (r k : ℕ) (hPQ : P ≤ Q) (hT : IsTransversal P T)
    (hk : ∀ v : V, partCount P (flipBall G Q (r + 1) v) ≤ k) (v : V) :
    partCount (split G P T) (flipBall G Q r v) ≤ k * neighborhoodComplexity G k := by
  classical
  set B := flipBall G Q r v
  set B' := flipBall G Q (r + 1) v
  have hBB' : B ⊆ B' := fun u hu H hH => withinDist_mono (Nat.le_succ r) (hu H hH)
  set T' := T ∩ B'
  -- the transversal meets the larger ball in at most `k` vertices
  have hT' : T'.ncard ≤ k := by
    refine le_trans ?_ (hk v)
    refine Set.ncard_le_ncard_of_injOn (Quotient.mk P) (fun t ht => ⟨t, ht.2, rfl⟩) ?_
      (Set.toFinite _)
    intro t ht t' ht' htt'
    obtain ⟨w, -, huniq⟩ := hT t
    have e1 := huniq t ⟨ht.1, P.refl t⟩
    have e2 := huniq t' ⟨ht'.1, Quotient.exact htt'.symm⟩
    rw [e1, e2]
  -- the part in `𝒫 ∧ T` is determined by the part in `𝒫` and the trace on `T'`
  let g : V → Quotient P × Set V := fun u => (Quotient.mk P u, G.neighborSet u ∩ T')
  have hfactor : ∀ u ∈ B, ∀ u' ∈ B, g u = g u' →
      Quotient.mk (split G P T) u = Quotient.mk (split G P T) u' := by
    intro u hu u' hu' hg
    obtain ⟨h1, h2⟩ := Prod.mk.inj hg
    have hPuu' : P u u' := Quotient.exact h1
    apply Quotient.sound
    change (Quotient.mk P u, _) = (Quotient.mk P u', _)
    refine Prod.ext h1 ?_
    ext t
    have hiff : P t u ↔ P t u' :=
      ⟨fun h => P.trans h hPuu', fun h => P.trans h (P.symm hPuu')⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet]
    rw [← hiff]
    by_cases htB' : t ∈ B'
    · have := Set.ext_iff.mp h2 t
      simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at this
      constructor
      · rintro ⟨⟨htT, htu⟩, hadj⟩; exact ⟨⟨htT, htu⟩, (this.mp ⟨hadj, htT, htB'⟩).1⟩
      · rintro ⟨⟨htT, htu⟩, hadj⟩; exact ⟨⟨htT, htu⟩, (this.mpr ⟨hadj, htT, htB'⟩).1⟩
    · rw [adj_far G Q r v hu hu' (hPQ (P.symm hPuu')) htB']
  calc partCount (split G P T) B
      ≤ (g '' B).ncard := ncard_image_le_of_factor _ g B hfactor
    _ ≤ ((Quotient.mk P '' B') ×ˢ {S | ∃ w, S = G.neighborSet w ∩ T'}).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨⟨u, hBB' hu, rfl⟩, ⟨u, rfl⟩⟩
    _ = partCount P B' * traceCount G T' := Set.ncard_prod
    _ ≤ k * neighborhoodComplexity G k :=
        Nat.mul_le_mul (hk v) (traceCount_le G T' hT')

end Lax185574Proofs.SplitBalls
