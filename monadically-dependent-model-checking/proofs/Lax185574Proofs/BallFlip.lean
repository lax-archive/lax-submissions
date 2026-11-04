import Lax185574.BallFlip
import Lax185574.VCDuality
import Lax185574Proofs.Lib.BallFlipMetric
import Lax185574Proofs.DefinableFlipBridge
import Lax185574Proofs.VCBridge

namespace Lax185574Proofs.BallFlip

open Lax185574Proofs.Lib.BallFlips Lax185574Proofs.Lib.DefinableFlips
open Lax185574Proofs.Lib.BoundedVCDuality Lax185574Proofs.Lib.PartitionMetricConversion
open Lax185574Proofs.Lib.BallFlipParameters Lax185574Proofs.Lib.BallFlipConstruction
open Lax185574Proofs.Lib.BallFlipMetric

universe u

/-- The duality in the form used by the construction: no exception for
the vertices of the sample, at the cost of doubling its size. A vertex
of the sample that lies on the dominated side either has a neighbor on
the dominating side, which is added, or is non-adjacent to the whole
dominating side and antidominates it alone. On the antidominating side
a vertex of the sample is its own non-neighbor. -/
theorem strong_duality {V : Type u} [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (hk : ∀ X Y : Set V, ∃ S : Finset V, S.card ≤ k ∧
        (((S : Set V) ⊆ Y ∧ Lax185574.VCDuality.Dominates G S X) ∨
          ((S : Set V) ⊆ X ∧ Lax185574.VCDuality.Antidominates G S Y)))
    (X Y : Finset V) :
    (∃ W : Finset V, W ⊆ X ∧ W.card ≤ 2 * k ∧ Dominates G W Y) ∨
      (∃ W : Finset V, W ⊆ Y ∧ W.card ≤ 2 * k ∧ Antidominates G W X) := by
  classical
  obtain ⟨S, hSk, ⟨hSX, hdom⟩ | ⟨hSY, hanti⟩⟩ := hk (Y : Set V) (X : Set V)
  · -- `S ⊆ X` dominates `Y ∖ S`
    by_cases hbad : ∃ y ∈ S, y ∈ Y ∧ ∀ x ∈ X, ¬ G.Adj x y
    · obtain ⟨y, hyS, hy, hyX⟩ := hbad
      have : 1 ≤ S.card := Finset.card_pos.mpr ⟨y, hyS⟩
      right
      refine ⟨{y}, by simpa using hy, by simp; omega, fun x hx => ⟨y, by simp, hyX x hx⟩⟩
    · push Not at hbad
      choose! f hfX hfadj using fun y hy hyY => hbad y hy hyY
      left
      refine ⟨S ∪ (S.filter (· ∈ Y)).image f, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_coe.mp (hSX hx)
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          have hy := Finset.mem_filter.mp hy
          exact hfX y hy.1 hy.2
      · refine (Finset.card_union_le _ _).trans ?_
        have := (Finset.card_image_le (s := S.filter (· ∈ Y)) (f := f)).trans
          (Finset.card_filter_le S _)
        omega
      · intro y hy
        by_cases hyS : y ∈ S
        · exact ⟨f y, Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨y, Finset.mem_filter.mpr ⟨hyS, hy⟩, rfl⟩), hfadj y hyS hy⟩
        · obtain ⟨s, hs, hys⟩ := hdom y ⟨hy, hyS⟩
          exact ⟨s, Finset.mem_union_left _ hs, hys.symm⟩
  · -- `S ⊆ Y` antidominates `X ∖ S`
    right
    refine ⟨S, fun s hs => Finset.mem_coe.mp (hSY hs), by omega, fun x hx => ?_⟩
    by_cases hxS : x ∈ S
    · exact ⟨x, hxS, G.loopless.irrefl x⟩
    · exact hanti x ⟨hx, hxS⟩

/-- The construction of the source, for a graph satisfying the duality
with samples of size `k`. -/
theorem exists_ball_flip_of_duality (k t : ℕ) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hdual : ∀ X Y : Finset V,
      (∃ W : Finset V, W ⊆ X ∧ W.card ≤ k ∧ Dominates G W Y) ∨
      (∃ W : Finset V, W ⊆ Y ∧ W.card ≤ k ∧ Antidominates G W X))
    (r : ℕ) (C A : Finset V) (hdis : Disjoint (ball G C r) A)
    (ht : (traces G A (ball G C r)).card ≤ t) :
    ∃ H : SimpleGraph V, IsDefinableFlip G H (2 ^ t + t + (2 ^ t + t + 1) * (2 ^ t + t + 1) * k) ∧
      Disjoint (ball H C (r + 1)) A := by
  classical
  let B := ball G C r
  let D := if r = 0 then ∅ else ball G C (r - 1)
  obtain ⟨S, hSc, hrepA, hrepB, hdualAA, hdualDB⟩ :=
    exists_control_parameters G k t hdual A B D ht
  let H := edgeFlip G A B S
  have hnotA (a : V) (ha : a ∈ A) : a ∉ B :=
    fun hb => Finset.disjoint_left.mp hdis hb ha
  refine ⟨H, ⟨S, hSc, edgeFlip_isBased G A B S⟩, ?_⟩
  apply ball_avoids_of_barriers G H C A r hdis
  · exact no_edges_AB hrepA hrepB hdualAA
  · intro i hi x hx y hxy
    have hxB : x ∈ B := ball_mono (by omega) hx
    have hfar₁ : ∀ a ∈ A, ¬ G.Adj x a := by
      intro a ha hxa
      exact hnotA a ha (ball_mono (by omega) (ball_step hx hxa))
    have hfar₂ : ∀ z a, a ∈ A → G.Adj x z → ¬ G.Adj z a := by
      intro z a ha hxz hza
      exact hnotA a ha (ball_mono (by omega) (ball_step (ball_step hx hxz) hza))
    have hn := no_toggle_far hrepA hrepB hxB hfar₁ hfar₂ y
    rcases hxy.2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact (hn h).elim
  · intro i hr x hx y hxy
    have hD : D = ball G C i := by simp [D, hr]
    have hDB : D ⊆ B := by
      rw [hD]
      exact ball_mono (by omega)
    have hclosed : ∀ d ∈ D, ∀ z, G.Adj d z → z ∈ B := by
      intro d hd z hdz
      rw [hD] at hd
      have hz := ball_step hd hdz
      simpa only [B, hr] using hz
    exact no_edges_D_outside hrepA hDB hnotA hclosed hdualDB x (hD.symm ▸ hx) y hxy

/--
---
conclusion: Lax185574.BallFlip.exists_ball_flip
---
The proof in the paper. Group `A` by neighborhoods in the ball `B` and
`B` by neighborhoods in `A`. The parameter set consists of
representatives of all groups and of a bounded-VC duality sample for
every pair of groups of `A` and for every group of `B` against the inner
ball. The `S`-flip toggles exactly the pairs of atomic types joined by
an edge of `G` between `A` and `B`. Then `A` and `B` are non-adjacent in
the flip, the inner ball is unchanged, and it has no edges to the
outside of `B`, so the ball of radius `r + 1` still avoids `A`. The
duality is used in a form without exception for the sample, obtained
from the concept at the cost of doubling the sample.
-/
theorem exists_ball_flip (d t : ℕ) :
    ∃ z : ℕ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      Lax185574.VCDimension.vcDim G ≤ d →
      ∀ (r : ℕ) (A C : Set V), Disjoint (Lax185574.GraphBalls.graphBall G r C) A →
        Lax185574.AtomicTypes.atomicTypeCount G (Lax185574.GraphBalls.graphBall G r C) A ≤ t →
        ∃ H : SimpleGraph V, Lax185574.DefinableFlips.IsDefinableFlip G z H ∧
          Disjoint (Lax185574.GraphBalls.graphBall H (r + 1) C) A := by
  obtain ⟨k, hk⟩ := Lax185574.VCDuality.vc_duality.{u} d
  refine ⟨2 ^ t + t + (2 ^ t + t + 1) * (2 ^ t + t + 1) * (2 * k), ?_⟩
  intro V _ G hvc r A C hdis ht
  classical
  have := Fintype.ofFinite V
  have hC : C = (C.toFinset : Set V) := by simp
  have hA : A = (A.toFinset : Set V) := by simp
  rw [hC, hA, ← Lax185574Proofs.DefinableFlipBridge.coe_ball] at hdis ht
  rw [Finset.disjoint_coe] at hdis
  rw [← Lax185574Proofs.DefinableFlipBridge.card_traces_eq _ _ _ hdis] at ht
  obtain ⟨H, hH, hHdis⟩ := exists_ball_flip_of_duality (2 * k) t G
    (strong_duality G k (hk V G hvc)) r C.toFinset A.toFinset hdis ht
  refine ⟨H, Lax185574Proofs.DefinableFlipBridge.isDefinableFlip_of_lib hH, ?_⟩
  rw [hC, hA, ← Lax185574Proofs.DefinableFlipBridge.coe_ball, Finset.disjoint_coe]
  exact hHdis

end Lax185574Proofs.BallFlip
