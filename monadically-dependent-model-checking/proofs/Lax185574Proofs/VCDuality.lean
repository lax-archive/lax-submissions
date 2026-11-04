import Lax185574.VCDuality
import Lax185574Proofs.Lib.BoundedVCDuality
import Lax185574Proofs.VCBridge

namespace Lax185574Proofs.VCDuality

open Lax185574.VCDimension Lax185574.VCDuality

universe u

/--
---
conclusion: Lax185574.VCDuality.vc_duality
---
The finite form of Matoušek's (p, q)-theorem, through ε-nets and the
finite minimax theorem. Its
statement has the roles of the sides swapped and needs no exception for
the vertices of the sample, so it implies the form used here.
-/
theorem vc_duality (d : ℕ) :
    ∃ k : ℕ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V), vcDim G ≤ d →
      ∀ X Y : Set V, ∃ S : Finset V, S.card ≤ k ∧
        (((S : Set V) ⊆ Y ∧ Dominates G S X) ∨
          ((S : Set V) ⊆ X ∧ Antidominates G S Y)) := by
  obtain ⟨k, hk⟩ := Lax185574Proofs.Lib.BoundedVCDuality.bounded_vc_duality.{u} d
  refine ⟨k, fun V _ G hG X Y => ?_⟩
  classical
  have := Fintype.ofFinite V
  rcases hk V G (Lax185574Proofs.VCBridge.vcDim_neighborhoodFamily_le G hG)
      Y.toFinset X.toFinset with ⟨S, hSY, hSk, hS⟩ | ⟨T, hTX, hTk, hT⟩
  · refine ⟨S, hSk, Or.inl ⟨fun s hs => Set.mem_toFinset.mp (hSY hs), ?_⟩⟩
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hS x (Set.mem_toFinset.mpr hx.1)
    exact ⟨s, hs, hsx.symm⟩
  · refine ⟨T, hTk, Or.inr ⟨fun t ht => Set.mem_toFinset.mp (hTX ht), ?_⟩⟩
    intro y hy
    obtain ⟨t, ht, hyt⟩ := hT y (Set.mem_toFinset.mpr hy.1)
    exact ⟨t, ht, hyt⟩

end Lax185574Proofs.VCDuality
