import Lax185574Proofs.Lib.PartitionMetricWalks

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
An elementary bipartite conversion argument, following the mechanism of
Lemmas 10–12 of Bonnet et al., arXiv:2505.11144. This formulation uses
explicit short walks and avoids connected-component decompositions.
-/

namespace Lax185574Proofs.Lib.BipartiteMetricConversion

open Lax185574Proofs.Lib.PartitionMetricConversion PartitionMetricWalks

universe u v
variable {U : Type u} {V : Type v}

def bipGraph (R : U → V → Prop) : SimpleGraph (U ⊕ V) where
  Adj
    | .inl x, .inr y => R x y
    | .inr y, .inl x => R x y
    | _, _ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

theorem cross_edge {R : U → V → Prop} {x : U} {y : V} (h : R x y) :
    Within (bipGraph R) 1 (.inl x) (.inr y) := within_edge h

theorem cross_three {R : U → V → Prop} {x z : U} {y w : V}
    (hxy : R x y) (hzy : R z y) (hzw : R z w) :
    Within (bipGraph R) 3 (.inl x) (.inr w) :=
  within_trans (within_trans (cross_edge hxy) (within_symm (cross_edge hzy))) (cross_edge hzw)

theorem left_four {R : U → V → Prop} {x z t : U} {y w : V}
    (hxy : R x y) (hzy : R z y) (hzw : R z w) (htw : R t w) :
    Within (bipGraph R) 4 (.inl x) (.inl t) :=
  within_trans (cross_three hxy hzy hzw) (within_symm (cross_edge htw))

theorem cross_swap {R : V → U → Prop} {x : V} {y : U} {r : ℕ}
    (h : Within (bipGraph R) r (.inl x) (.inr y)) :
    Within (bipGraph (fun u v => R v u)) r (.inl y) (.inr x) := by
  apply within_symm
  exact within_map Sum.swap (by
    intro x y h
    cases x <;> cases y <;> exact h) h

def Splits (R : U → V → Prop) (left : U → Bool) (right : V → Bool)
    (toggle : Bool → Bool → Bool) : Prop :=
  ∀ x y, Xor (R x y) (toggle (left x) (right y) = true) →
    Within (bipGraph R) 6 (.inl x) (.inr y) ∧
      Within (bipGraph (fun u v => ¬R u v)) 6 (.inl x) (.inr y)

/-- An isolated row either gives short complementary paths, or is paired
with a universal row to split the other rows into two simple blocks. -/
theorem split_of_isolated_row [Nonempty V] (R : U → V → Prop)
    (x₀ : U) (hx₀ : ∀ y, ¬R x₀ y) :
    ∃ (left : U → Bool) (right : V → Bool) (toggle : Bool → Bool → Bool),
      Splits R left right toggle := by
  classical
  by_cases hfull : ∃ x₁, ∀ y, R x₁ y
  · obtain ⟨x₁, hx₁⟩ := hfull
    let y₀ : V := Classical.arbitrary V
    refine ⟨fun x => decide (R x y₀), fun _ => false, fun a _ => a, ?_⟩
    intro x y h
    have hc : (R x y ∧ ¬R x y₀) ∨ (¬R x y ∧ R x y₀) := by
      simpa [Xor, and_comm] using h
    rcases hc with ⟨hxy, hxy₀⟩ | ⟨hxy, hxy₀⟩
    · exact ⟨within_mono (cross_edge hxy) (by omega),
        within_mono (cross_three hxy₀ (hx₀ y₀) (hx₀ y)) (by omega)⟩
    · exact ⟨within_mono (cross_three hxy₀ (hx₁ y₀) (hx₁ y)) (by omega),
        within_mono (cross_edge hxy) (by omega)⟩
  · have hmiss : ∀ x, ∃ y, ¬R x y := by simpa using hfull
    refine ⟨fun _ => false, fun _ => false, fun _ _ => false, ?_⟩
    intro x y h
    have hxy : R x y := by simpa [Xor] using h
    obtain ⟨y₀, hxy₀⟩ := hmiss x
    exact ⟨within_mono (cross_edge hxy) (by omega),
      within_mono (cross_three hxy₀ (hx₀ y₀) (hx₀ y)) (by omega)⟩

/-- Split each side into at most two parts so that every edge left by the
chosen block toggles has a short path in both original polarities. -/
theorem exists_split (R : U → V → Prop) :
    ∃ (left : U → Bool) (right : V → Bool) (toggle : Bool → Bool → Bool),
      Splits R left right toggle := by
  classical
  rcases isEmpty_or_nonempty U with hU | hU
  · exact ⟨fun _ => false, fun _ => false, fun _ _ => false, fun x => isEmptyElim x⟩
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨fun _ => false, fun _ => false, fun _ _ => false, fun _ y => isEmptyElim y⟩
  by_cases hisoU : ∃ x, ∀ y, ¬R x y
  · obtain ⟨x, hx⟩ := hisoU
    exact split_of_isolated_row R x hx
  by_cases hisoV : ∃ y, ∀ x, ¬R x y
  · obtain ⟨y, hy⟩ := hisoV
    obtain ⟨right, left, toggle, hsplit⟩ := split_of_isolated_row (fun y x => R x y) y hy
    refine ⟨left, right, fun a b => toggle b a, ?_⟩
    intro x y h
    obtain ⟨h₁, h₂⟩ := hsplit y x h
    exact ⟨cross_swap h₁, cross_swap h₂⟩
  have hrow : ∀ x, ∃ y, R x y := by simpa using hisoU
  have hcol : ∀ y, ∃ x, R x y := by simpa using hisoV
  by_cases hshort : ∀ x x', Within (bipGraph R) 4 (.inl x) (.inl x')
  · refine ⟨fun _ => false, fun _ => false, fun _ _ => true, ?_⟩
    intro x y h
    have hn : ¬R x y := by simpa [Xor] using h
    obtain ⟨x', hx'y⟩ := hcol y
    exact ⟨within_mono (within_trans (hshort x x') (cross_edge hx'y)) (by omega),
      within_mono (cross_edge hn) (by omega)⟩
  push Not at hshort
  obtain ⟨x₀, x₁, hfar⟩ := hshort
  obtain ⟨y₀, hx₀y₀⟩ := hrow x₀
  obtain ⟨y₁, hx₁y₁⟩ := hrow x₁
  have hnotbothU (x : U) : ¬ (R x y₀ ∧ R x y₁) := by
    rintro ⟨h₀, h₁⟩
    exact hfar (left_four hx₀y₀ h₀ h₁ hx₁y₁)
  have hnotbothV (y : V) : ¬ (R x₀ y ∧ R x₁ y) := by
    rintro ⟨h₀, h₁⟩
    exact hfar (within_mono (within_trans (cross_edge h₀)
      (within_symm (cross_edge h₁))) (by omega))
  have hcross₀ : ¬R x₁ y₀ := fun h => hnotbothV y₀ ⟨hx₀y₀, h⟩
  have hcross₁ : ¬R x₀ y₁ := fun h => hnotbothV y₁ ⟨h, hx₁y₁⟩
  by_cases hoverU : ∃ x₂, ¬R x₂ y₀ ∧ ¬R x₂ y₁
  · obtain ⟨x₂, hx₂₀, hx₂₁⟩ := hoverU
    refine ⟨fun _ => false, fun _ => false, fun _ _ => false, ?_⟩
    intro x y h
    have hxy : R x y := by simpa [Xor] using h
    have hleft : Within (bipGraph (fun u v => ¬R u v)) 2 (.inl x) (.inl x₂) := by
      by_cases hx : R x y₀
      · exact within_trans (cross_edge (fun h => hnotbothU x ⟨hx, h⟩))
          (within_symm (cross_edge hx₂₁))
      · exact within_trans (cross_edge hx) (within_symm (cross_edge hx₂₀))
    have hright : Within (bipGraph (fun u v => ¬R u v)) 3 (.inl x₂) (.inr y) := by
      by_cases hy : R x₀ y
      · exact cross_three hx₂₀ hcross₀ (fun h => hnotbothV y ⟨hy, h⟩)
      · exact cross_three hx₂₁ hcross₁ hy
    exact ⟨within_mono (cross_edge hxy) (by omega),
      within_mono (within_trans hleft hright) (by omega)⟩
  by_cases hoverV : ∃ y₂, ¬R x₀ y₂ ∧ ¬R x₁ y₂
  · obtain ⟨y₂, hx₀₂, hx₁₂⟩ := hoverV
    refine ⟨fun _ => false, fun _ => false, fun _ _ => false, ?_⟩
    intro x y h
    have hxy : R x y := by simpa [Xor] using h
    have hleft : Within (bipGraph (fun u v => ¬R u v)) 3 (.inl x) (.inr y₂) := by
      by_cases hx : R x y₀
      · exact cross_three (fun h => hnotbothU x ⟨hx, h⟩) hcross₁ hx₀₂
      · exact cross_three hx hcross₀ hx₁₂
    have hright : Within (bipGraph (fun u v => ¬R u v)) 2 (.inr y₂) (.inr y) := by
      by_cases hy : R x₀ y
      · exact within_trans (within_symm (cross_edge hx₁₂))
          (cross_edge (fun h => hnotbothV y ⟨hy, h⟩))
      · exact within_trans (within_symm (cross_edge hx₀₂)) (cross_edge hy)
    exact ⟨within_mono (cross_edge hxy) (by omega),
      within_mono (within_trans hleft hright) (by omega)⟩
  have hcoverU (x : U) : R x y₀ ∨ R x y₁ := by
    by_contra h
    exact hoverU ⟨x, by tauto⟩
  have hcoverV (y : V) : R x₀ y ∨ R x₁ y := by
    by_contra h
    exact hoverV ⟨y, by tauto⟩
  have hsame (x : U) (y : V) (hxy : R x y) : R x y₀ ↔ R x₀ y := by
    constructor
    · intro hx
      by_contra hy
      have hy' := (hcoverV y).resolve_left hy
      exact hfar (left_four hx₀y₀ hx hxy hy')
    · intro hy
      by_contra hx
      have hx' := (hcoverU x).resolve_left hx
      exact hfar (left_four hy hxy hx' hx₁y₁)
  refine ⟨fun x => decide (R x y₀), fun y => decide (R x₀ y),
    fun a b => decide (a = b), ?_⟩
  intro x y h
  have hbits : decide (R x y₀) = decide (R x₀ y) := by
    by_contra hb
    have hxy : R x y := by simpa [Xor, hb] using h
    exact hb (propext (hsame x y hxy) ▸ rfl)
  have hn : ¬R x y := by simpa [Xor, hbits] using h
  have hshort : Within (bipGraph R) 3 (.inl x) (.inr y) := by
    have heq : R x y₀ ↔ R x₀ y := by simpa only [decide_eq_decide] using hbits
    by_cases hx : R x y₀
    · exact cross_three hx hx₀y₀ (heq.mp hx)
    · exact cross_three ((hcoverU x).resolve_left hx) hx₁y₁
        ((hcoverV y).resolve_left (fun hy => hx (heq.mpr hy)))
  exact ⟨within_mono hshort (by omega), within_mono (cross_edge hn) (by omega)⟩

end Lax185574Proofs.Lib.BipartiteMetricConversion
