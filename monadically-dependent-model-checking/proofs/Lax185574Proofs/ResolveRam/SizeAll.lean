import Lax185574Proofs.ResolveRam.LenBounds
import Lax185574Proofs.ResolveRam.EntCalls

/-!
The size bounds of the time bound of lem:resolve-lift hold with
constants of the rank: the lengths by `lenBounds`, the entries by
`entBounds`, with the sum of the two constants.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.Words

theorem polyB_mono {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ P Q : ℕ) (s : Bool) {C C' : ℕ}
    (A : ℕ) (h : C ≤ C') : polyB G k₀ q₀ P Q s C A ≤ polyB G k₀ q₀ P Q s C' A := by
  unfold polyB; gcongr

/-- **The size bounds.** -/
theorem sizeHyp : SizeHyp := by
  intro k₀ q₀ hk
  obtain ⟨C₁, A, hL⟩ := lenBounds k₀ q₀ hk
  obtain ⟨C₂, hE⟩ := entBounds k₀ q₀ hk
  refine ⟨C₁ + C₂, A, fun n G P Q s => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hL n G P Q s
  obtain ⟨h5, h6⟩ := hE n G P Q s
  have hm := polyB_mono G k₀ q₀ P Q s A (show C₁ ≤ C₁ + C₂ by omega)
  refine ⟨le_trans h1 (by gcongr; omega), le_trans h2 hm, fun c hc => le_trans (h3 c hc) hm,
    le_trans h4 hm, fun c hc => le_trans (h5 c hc) (by gcongr; omega),
    le_trans h6 (by gcongr; omega)⟩

end Lax185574Proofs.ResolveRam
