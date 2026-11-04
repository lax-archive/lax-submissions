import Lax185574Proofs.Lib.BallFlipConstruction
import Lax185574Proofs.Lib.PartitionMetricWalks

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.BallFlipMetric

open Lax185574Proofs.Lib.BallFlips Lax185574Proofs.Lib.PartitionMetricConversion
open PartitionMetricWalks

universe u

theorem mem_ball {V : Type u} [Fintype V] {G : SimpleGraph V} {C : Finset V}
    {r : ℕ} {v : V} : v ∈ ball G C r ↔ ∃ c ∈ C, Within G r c v := by
  classical
  simp [ball]

theorem ball_mono {V : Type u} [Fintype V] {G : SimpleGraph V} {C : Finset V}
    {r s : ℕ} (hrs : r ≤ s) : ball G C r ⊆ ball G C s := by
  intro v hv
  obtain ⟨c, hc, hcv⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨c, hc, within_mono hcv hrs⟩

theorem ball_zero {V : Type u} [Fintype V] (G : SimpleGraph V) (C : Finset V) :
    ball G C 0 = C := by
  classical
  ext v
  rw [mem_ball]
  constructor
  · rintro ⟨c, hc, w, hw⟩
    have hw0 : w.length = 0 := Nat.eq_zero_of_le_zero hw
    cases w with
    | nil => exact hc
    | cons => simp at hw0
  · intro hv
    exact ⟨v, hv, within_refl G v 0⟩

theorem ball_step {V : Type u} [Fintype V] {G : SimpleGraph V} {C : Finset V}
    {r : ℕ} {v w : V} (hv : v ∈ ball G C r) (hvw : G.Adj v w) :
    w ∈ ball G C (r + 1) := by
  obtain ⟨c, hc, hcv⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨c, hc, within_trans hcv (within_edge hvw)⟩

theorem mem_ball_succ {V : Type u} [Fintype V] {G : SimpleGraph V} {C : Finset V}
    {r : ℕ} {v : V} : v ∈ ball G C (r + 1) ↔
      v ∈ ball G C r ∨ ∃ w ∈ ball G C r, G.Adj w v := by
  constructor
  · intro hv
    obtain ⟨c, hc, hcv⟩ := mem_ball.mp hv
    obtain ⟨w, hw⟩ := within_symm hcv
    cases w with
    | nil => exact Or.inl (mem_ball.mpr ⟨v, hc, within_refl G v r⟩)
    | @cons v z c hvz w =>
      have hlen : w.length ≤ r := by simp only [SimpleGraph.Walk.length_cons] at hw; omega
      exact Or.inr ⟨z, mem_ball.mpr ⟨c, hc, within_symm ⟨w, hlen⟩⟩, hvz.symm⟩
  · rintro (h | ⟨w, hw, hwv⟩)
    · exact ball_mono (Nat.le_succ r) h
    · exact ball_step hw hwv

/-- A graph change that preserves the inner layers and the two boundary
barriers keeps the next larger ball disjoint from A. -/
theorem ball_avoids_of_barriers {V : Type u} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (C A : Finset V) (r : ℕ)
    (hdis : Disjoint (ball G C r) A)
    (hAB : ∀ a ∈ A, ∀ b ∈ ball G C r, ¬ H.Adj a b)
    (hinner : ∀ i, i + 2 ≤ r → ∀ x ∈ ball G C i, ∀ y, H.Adj x y → G.Adj x y)
    (hboundary : ∀ i, r = i + 1 →
      ∀ x ∈ ball G C i, ∀ y, H.Adj x y → y ∈ ball G C r) :
    Disjoint (ball H C (r + 1)) A := by
  have hnotA : ∀ x ∈ ball G C r, x ∉ A := Finset.disjoint_left.mp hdis
  have hstep {j : ℕ} (hj : ball H C j ⊆ ball G C r) :
      Disjoint (ball H C (j + 1)) A := by
    apply Finset.disjoint_left.mpr
    intro a ha hAa
    rcases mem_ball_succ.mp ha with ha | ⟨b, hb, hba⟩
    · exact hnotA a (hj ha) hAa
    · exact hAB a hAa b (hj hb) hba.symm
  cases r with
  | zero =>
    apply hstep
    simp only [ball_zero]
    exact Finset.Subset.refl _
  | succ k =>
    have hlevels : ∀ i, i ≤ k → ball H C i ⊆ ball G C i := by
      intro i
      induction i with
      | zero => intro _; simp only [ball_zero]; exact Finset.Subset.refl _
      | succ i ih =>
        intro hi x hx
        rcases mem_ball_succ.mp hx with hx | ⟨y, hy, hyx⟩
        · exact ball_mono (Nat.le_succ i) (ih (by omega) hx)
        · have hyG := ih (by omega) hy
          exact ball_step hyG (hinner i (by omega) y hyG x hyx)
    apply hstep (j := k + 1)
    intro x hx
    rcases mem_ball_succ.mp hx with hx | ⟨y, hy, hyx⟩
    · exact ball_mono (Nat.le_succ k) (hlevels k le_rfl hx)
    · exact hboundary k rfl y (hlevels k le_rfl hy) x hyx

end Lax185574Proofs.Lib.BallFlipMetric
