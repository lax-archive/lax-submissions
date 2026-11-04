import Lax185574Proofs.Lib.BoundedVCDualityDefs
import Lax185574Proofs.Lib.EpsilonNets
import Lax185574Proofs.Lib.FiniteMinimax
import Lax185574Proofs.Lib.VCOperations
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.BoundedVCDuality

open Lax185574Proofs.Lib.BoundedVCDuality Lax185574Proofs.Lib.Internal.EpsilonNets
open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Extend a distribution on a finite subset by zero outside the subset. -/
def extendWeights (X : Finset V) (p : X → ℝ) (v : V) : ℝ :=
  ∑ x : X, if x.val = v then p x else 0

theorem extendWeights_simplex (X : Finset V) (p : X → ℝ)
    (hp : p ∈ stdSimplex ℝ X) : extendWeights X p ∈ stdSimplex ℝ V := by
  constructor
  · intro v
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact hp.1 x
      · exact le_rfl
  · simp only [extendWeights]
    rw [Finset.sum_comm]
    simpa using hp.2

omit [Fintype V] in
theorem extendWeights_mass (X A : Finset V) (p : X → ℝ) :
    (∑ v ∈ A ∩ X, extendWeights X p v) =
      ∑ x : X, if x.val ∈ A then p x else 0 := by
  simp only [extendWeights]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [x.property]

/-- Apply a half-net to a restricted family and a distribution supported
on `X`, and retain only the net vertices lying in `X`. -/
theorem half_net_on_subset (d N : ℕ)
    (hnet : ∀ (𝓕 : Finset (Finset V)), 𝓕.vcDim ≤ d →
      ∀ p ∈ stdSimplex ℝ V, ∃ S : Finset V,
        S.card ≤ N ∧ IsEpsilonNet 𝓕 p ((1 : ℝ) / 2) S)
    (𝓕 : Finset (Finset V)) (hd : 𝓕.vcDim ≤ d)
    (X : Finset V) (p : X → ℝ) (hp : p ∈ stdSimplex ℝ X) :
    ∃ S : Finset V, S ⊆ X ∧ S.card ≤ N ∧
      ∀ A ∈ 𝓕, (1 : ℝ) / 2 ≤ (∑ x : X, if x.val ∈ A then p x else 0) →
        (S ∩ A).Nonempty := by
  obtain ⟨S, hS, hhit⟩ := hnet (𝓕.image (· ∩ X))
    ((VCOperations.vcDim_inter_le 𝓕 X).trans hd) (extendWeights X p)
    (extendWeights_simplex X p hp)
  refine ⟨S ∩ X, Finset.inter_subset_right,
    (Finset.card_le_card Finset.inter_subset_left).trans hS, ?_⟩
  intro A hA hmass
  have hh := hhit (A ∩ X) (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
    (by simpa only [extendWeights_mass] using hmass)
  obtain ⟨v, hv⟩ := hh
  simp only [Finset.mem_inter] at hv
  exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hv.1, hv.2.2⟩, hv.2.1⟩⟩

/--
Finite minimax gives a distribution making all the required neighborhoods
or nonneighborhoods heavy. A weighted half-net hits them all. Restriction
and complementation preserve the VC bound. Empty sides are handled by
the empty witness set.
-/
theorem bounded_vc_duality (d : ℕ) :
    ∃ k : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), (neighborhoodFamily G).vcDim ≤ d →
      ∀ X Y : Finset V,
        (∃ S : Finset V, S ⊆ X ∧ S.card ≤ k ∧ Dominates G S Y) ∨
        (∃ T : Finset V, T ⊆ Y ∧ T.card ≤ k ∧ Antidominates G T X) := by
  classical
  obtain ⟨N, hN⟩ := Lax185574Proofs.Lib.EpsilonNets.finite_epsilon_net.{u}
    d ((1 : ℝ) / 2) (by norm_num)
  refine ⟨N, ?_⟩
  intro V _ _ G hd X Y
  by_cases hX : X.Nonempty
  · by_cases hY : Y.Nonempty
    · let : Nonempty X := ⟨⟨hX.choose, hX.choose_spec⟩⟩
      let : Nonempty Y := ⟨⟨hY.choose, hY.choose_spec⟩⟩
      obtain hp | hq := FiniteMinimax.relation_half_alternative
        (fun (x : X) (y : Y) => G.Adj x.val y.val)
      · obtain ⟨p, hp, hmass⟩ := hp
        obtain ⟨S, hSX, hS, hhit⟩ := half_net_on_subset d N (hN V)
          (neighborhoodFamily G) hd X p hp
        left
        refine ⟨S, hSX, hS, ?_⟩
        intro y hy
        let A := Finset.univ.filter (G.Adj y)
        have hA : A ∈ neighborhoodFamily G := by
          simp only [neighborhoodFamily, Finset.mem_image]
          exact ⟨y, Finset.mem_univ _, rfl⟩
        obtain ⟨x, hx⟩ := hhit A hA (by
          simpa [A, G.adj_comm] using hmass ⟨y, hy⟩)
        have hx' := Finset.mem_inter.mp hx
        exact ⟨x, hx'.1, (Finset.mem_filter.mp hx'.2).2.symm⟩
      · obtain ⟨q, hq, hmass⟩ := hq
        let 𝓕 := (neighborhoodFamily G).image (fun A => Aᶜ)
        have hF : 𝓕.vcDim ≤ d := by
          simpa only [𝓕, VCOperations.vcDim_compl_eq] using hd
        obtain ⟨T, hTY, hT, hhit⟩ := half_net_on_subset d N (hN V) 𝓕 hF Y q hq
        right
        refine ⟨T, hTY, hT, ?_⟩
        intro x hx
        let A := (Finset.univ.filter (G.Adj x))ᶜ
        have hA : A ∈ 𝓕 := by
          apply Finset.mem_image.mpr
          refine ⟨Finset.univ.filter (G.Adj x), ?_, rfl⟩
          simp only [neighborhoodFamily, Finset.mem_image]
          exact ⟨x, Finset.mem_univ _, rfl⟩
        obtain ⟨y, hy⟩ := hhit A hA (by
          simpa [A] using hmass ⟨x, hx⟩)
        have hy' := Finset.mem_inter.mp hy
        refine ⟨y, hy'.1, ?_⟩
        simpa [A] using hy'.2
    · left
      refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro y hy
      exact (hY ⟨y, hy⟩).elim
  · right
    refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    intro x hx
    exact (hX ⟨x, hx⟩).elim

end Lax185574Proofs.Lib.BoundedVCDuality
