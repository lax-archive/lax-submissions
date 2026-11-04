import Lax185574.SplittingMonotone

namespace Lax185574Proofs.SplittingMonotone

open Lax185574.TypeSplitting Lax185574.SplittingMonotone

universe z

variable {V : Type z}

/-- Splitting is monotone: if `𝒫 ≼ 𝒫'` and `T' ∖ 𝒫'(v) ⊆ T` for all `v`,
then `𝒫 ∧ T ≼ 𝒫' ∧ T'`. -/
theorem split_le_split (G : SimpleGraph V) {P P' : Setoid V} {T T' : Set V} (hP : P ≤ P')
    (hT : ∀ t ∈ T', t ∈ T) : split G P T ≤ split G P' T' := by
  intro u v huv
  change (Quotient.mk P u, _) = (Quotient.mk P v, _) at huv
  change (Quotient.mk P' u, _) = (Quotient.mk P' v, _)
  obtain ⟨h1, h2⟩ := Prod.mk.inj huv
  have hPuv : P u v := Quotient.exact h1
  have hP'uv : P' u v := hP hPuv
  refine Prod.ext (Quotient.sound hP'uv) ?_
  ext t
  have hiff : P' t u ↔ P' t v :=
    ⟨fun h => P'.trans h hP'uv, fun h => P'.trans h (P'.symm hP'uv)⟩
  have hset := Set.ext_iff.mp h2 t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet] at hset ⊢
  constructor
  · rintro ⟨⟨htT, htu⟩, hadj⟩
    have htu' : ¬ P t u := fun h => htu (hP h)
    exact ⟨⟨htT, hiff.not.mp htu⟩, (hset.mp ⟨⟨hT t htT, htu'⟩, hadj⟩).2⟩
  · rintro ⟨⟨htT, htv⟩, hadj⟩
    have htv' : ¬ P t v := fun h => htv (hP h)
    exact ⟨⟨htT, hiff.not.mpr htv⟩, (hset.mpr ⟨⟨hT t htT, htv'⟩, hadj⟩).2⟩

/-- A vertex minimal in its part of a coarser partition is minimal in
its part of a finer one. -/
theorem minimalVertices_anti [LinearOrder V] {P P' : Setoid V} (hP : P ≤ P') :
    minimalVertices P' ⊆ minimalVertices P :=
  fun _ hv u hu => hv u (hP hu)

/--
---
conclusion: Lax185574.SplittingMonotone.split_minimalVertices_mono
---
As in the paper. If `𝒫ᵢ ≼ 𝒫ⱼ` then a vertex that is minimal in its part
of `𝒫ⱼ` is minimal in its part of `𝒫ᵢ`, so `Tⱼ ⊆ Tᵢ`. Two vertices in
the same part of `𝒬ᵢ` lie in the same part of `𝒫ᵢ`, hence of `𝒫ⱼ`. They
have the same neighbors in `Tᵢ ∖ 𝒫ᵢ(u)`, which contains `Tⱼ ∖ 𝒫ⱼ(u)`, so
they lie in the same part of `𝒬ⱼ`.
-/
theorem split_minimalVertices_mono [LinearOrder V] (G : SimpleGraph V) (Ps : List (Setoid V))
    (h : ∀ (t : ℕ) (ht : t + 1 < Ps.length), Ps[t] ≤ Ps[t + 1]) :
    ∀ (t : ℕ) (ht : t + 1 < Ps.length),
      split G Ps[t] (minimalVertices Ps[t]) ≤ split G Ps[t + 1] (minimalVertices Ps[t + 1]) :=
  fun t ht => split_le_split G (h t ht) fun _ hv => minimalVertices_anti (h t ht) hv

end Lax185574Proofs.SplittingMonotone
