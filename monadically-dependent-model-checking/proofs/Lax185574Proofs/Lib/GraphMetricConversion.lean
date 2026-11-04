import Lax185574Proofs.Lib.PartitionMetricWalks

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-! The one-part case of partition-metric conversion. -/

namespace Lax185574Proofs.Lib.GraphMetricConversion

open Lax185574Proofs.Lib.PartitionMetricConversion PartitionMetricWalks

universe u
variable {V : Type u}

theorem complement_near {G : SimpleGraph V} {x y : V} (h : ¬G.Adj x y) :
    Within Gᶜ 1 x y := by
  by_cases hxy : x = y
  · subst y
    exact within_refl _ _ _
  · exact within_edge ⟨hxy, h⟩

/-- Either a graph or its complement has diameter at most three. -/
theorem graph_or_complement (G : SimpleGraph V) :
    (∀ x y, Within G 3 x y) ∨ (∀ x y, Within Gᶜ 3 x y) := by
  classical
  by_cases h : ∀ x y, Within G 3 x y
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨x₀, x₁, hfar⟩ := h
  have hnonedge : ¬G.Adj x₀ x₁ :=
    fun h => hfar (within_mono (within_edge h) (by omega))
  have hbridge := complement_near hnonedge
  have hnear (x : V) : Within Gᶜ 1 x x₀ ∨ Within Gᶜ 1 x x₁ := by
    by_cases hx₀ : G.Adj x x₀
    · right
      apply complement_near
      intro hx₁
      exact hfar (within_mono
        (within_trans (within_edge hx₀.symm) (within_edge hx₁)) (by omega))
    · exact Or.inl (complement_near hx₀)
  intro x y
  rcases hnear x with hx | hx <;> rcases hnear y with hy | hy
  · exact within_mono (within_trans hx (within_symm hy)) (by omega)
  · exact within_trans (within_trans hx hbridge) (within_symm hy)
  · exact within_trans (within_trans hx (within_symm hbridge)) (within_symm hy)
  · exact within_mono (within_trans hx (within_symm hy)) (by omega)

theorem exists_toggle (G : SimpleGraph V) :
    ∃ toggle : Bool, ∀ x y, x ≠ y → Xor (G.Adj x y) (toggle = true) →
      Within G 6 x y ∧ Within Gᶜ 6 x y := by
  rcases graph_or_complement G with h | h
  · refine ⟨true, ?_⟩
    intro x y hxy hadj
    have hn : ¬G.Adj x y := by simpa [Xor] using hadj
    exact ⟨within_mono (h x y) (by omega),
      within_mono (within_edge (show Gᶜ.Adj x y from ⟨hxy, hn⟩)) (by omega)⟩
  · refine ⟨false, ?_⟩
    intro x y _ hadj
    have he : G.Adj x y := by simpa [Xor] using hadj
    exact ⟨within_mono (within_edge he) (by omega), within_mono (h x y) (by omega)⟩

end Lax185574Proofs.Lib.GraphMetricConversion
