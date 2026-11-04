import Lax185574.ComplementDiameter
import Lax185574Proofs.WithinDistBasics

namespace Lax185574Proofs.ComplementDiameter

open Lax185574.GaifmanGraph Lax185574Proofs.WithinDistBasics

universe z

/--
---
conclusion: Lax185574.ComplementDiameter.diameter_le_three_or_compl
---
If some two vertices `u`, `v` are not joined by a walk of length at
most `2` in `G`, then they are distinct, non-adjacent and have no common
neighbor. In `Ḡ` they are adjacent, and every other vertex is adjacent to
`u` or to `v`. So any two vertices are joined in `Ḡ` by a walk that goes
to `u` or `v`, possibly crosses the edge `uv`, and leaves again, of
length at most `3`.
-/
theorem diameter_le_three_or_compl {V : Type z} (G : SimpleGraph V) :
    (∀ u v : V, WithinDist G 3 u v) ∨ (∀ u v : V, WithinDist Gᶜ 3 u v) := by
  by_cases h : ∀ u v : V, WithinDist G 2 u v
  · exact Or.inl fun u v => withinDist_mono (by omega) (h u v)
  right
  push Not at h
  obtain ⟨u, v, huv⟩ := h
  have hne : u ≠ v := fun e => huv (e ▸ withinDist_refl 2 u)
  have hnadj : ¬ G.Adj u v := fun e => huv (withinDist_mono (by omega) (withinDist_adj e))
  have huvc : Gᶜ.Adj u v := (SimpleGraph.compl_adj G u v).mpr ⟨hne, hnadj⟩
  -- every vertex is equal or `Ḡ`-adjacent to `u` or to `v`
  have hnear : ∀ x : V, WithinDist Gᶜ 1 x u ∨ WithinDist Gᶜ 1 x v := by
    intro x
    by_cases hxu : x = u
    · exact Or.inl (hxu ▸ withinDist_refl 1 x)
    by_cases hxv : x = v
    · exact Or.inr (hxv ▸ withinDist_refl 1 x)
    by_cases hGxu : G.Adj x u
    · by_cases hGxv : G.Adj x v
      · exact absurd (withinDist_trans (withinDist_adj hGxu.symm) (withinDist_adj hGxv)) huv
      · exact Or.inr (withinDist_adj ((SimpleGraph.compl_adj G x v).mpr ⟨hxv, hGxv⟩))
    · exact Or.inl (withinDist_adj ((SimpleGraph.compl_adj G x u).mpr ⟨hxu, hGxu⟩))
  have huv1 : WithinDist Gᶜ 1 u v := withinDist_adj huvc
  have hvu1 : WithinDist Gᶜ 1 v u := withinDist_adj huvc.symm
  intro x y
  rcases hnear x with hx | hx <;> rcases hnear y with hy | hy
  · exact withinDist_mono (by omega) (withinDist_trans hx (withinDist_symm' hy))
  · exact withinDist_trans (withinDist_trans hx huv1) (withinDist_symm' hy)
  · exact withinDist_trans (withinDist_trans hx hvu1) (withinDist_symm' hy)
  · exact withinDist_mono (by omega) (withinDist_trans hx (withinDist_symm' hy))

end Lax185574Proofs.ComplementDiameter
