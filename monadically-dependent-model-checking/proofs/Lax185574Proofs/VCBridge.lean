import Lax185574.VCDimension
import Lax185574Proofs.Lib.BoundedVCDualityDefs

/-!
The VC-dimension of a graph, as an extended natural number defined by
shattered vertex sets, bounds the mathlib VC-dimension of the family of
neighborhoods.
-/

namespace Lax185574Proofs.VCBridge

open Lax185574.VCDimension

universe u

theorem shatters_of_neighborhoodFamily {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {s : Finset V}
    (h : (Lax185574Proofs.Lib.BoundedVCDuality.neighborhoodFamily G).Shatters s) :
    Shatters G s := by
  intro B hB
  obtain ⟨u, hu, hsu⟩ := h hB
  have hu' : ∃ v, ∀ a, a ∈ u ↔ G.Adj v a := by
    unfold Lax185574Proofs.Lib.BoundedVCDuality.neighborhoodFamily at hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨v, rfl⟩ := hu
    exact ⟨v, fun a => by simp⟩
  obtain ⟨v, hv⟩ := hu'
  refine ⟨v, fun a ha => ?_⟩
  have := congrArg (fun T => a ∈ T) hsu
  simp only [Finset.mem_inter, eq_iff_iff] at this
  rw [← hv, ← this]
  exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

theorem vcDim_neighborhoodFamily_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hG : vcDim G ≤ d) :
    (Lax185574Proofs.Lib.BoundedVCDuality.neighborhoodFamily G).vcDim ≤ d := by
  refine Finset.sup_le fun s hs => ?_
  have hsh := shatters_of_neighborhoodFamily G (Finset.mem_shatterer.mp hs)
  have h1 : (s.card : ℕ∞) ≤ vcDim G :=
    le_iSup₂ (f := fun (A : Finset V) (_ : Shatters G A) => (A.card : ℕ∞)) s hsh
  exact_mod_cast h1.trans hG

end Lax185574Proofs.VCBridge
