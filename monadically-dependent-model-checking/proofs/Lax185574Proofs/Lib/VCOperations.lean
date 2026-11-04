import Lax185574Proofs.Lib.VCOperationsDefs

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.VCOperations

open Finset

universe u

/--
A set shattered after restriction lies in the restricting set and is
already shattered by the original family.

The argument also appears as `vcDim_image_inter_le` in
`Lax710763Proofs.SetSystems`; it is exposed here as a reusable concept.
-/
theorem vcDim_inter_le {V : Type u} [DecidableEq V]
    (𝓕 : Finset (Finset V)) (X : Finset V) :
    (𝓕.image (· ∩ X)).vcDim ≤ 𝓕.vcDim := by
  apply Finset.sup_le
  intro s hs
  have hsh := mem_shatterer.mp hs
  obtain ⟨_, hu, hsu⟩ := hsh.exists_superset
  obtain ⟨w, _, rfl⟩ := mem_image.mp hu
  have hsX : s ⊆ X := hsu.trans inter_subset_right
  apply Shatters.card_le_vcDim
  intro t ht
  obtain ⟨_, hu', heq⟩ := hsh ht
  obtain ⟨w', hw', rfl⟩ := mem_image.mp hu'
  refine ⟨w', hw', ?_⟩
  rwa [inter_comm w' X, ← inter_assoc, inter_eq_left.mpr hsX] at heq

theorem vcDim_compl_le {V : Type u} [Fintype V] [DecidableEq V]
    (𝓕 : Finset (Finset V)) :
    (𝓕.image (fun A => Aᶜ)).vcDim ≤ 𝓕.vcDim := by
  apply Finset.sup_le
  intro s hs
  have hsh := mem_shatterer.mp hs
  apply Shatters.card_le_vcDim
  intro t ht
  obtain ⟨_, hu, heq⟩ := hsh (sdiff_subset (t := t))
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
  refine ⟨w, hw, ?_⟩
  ext z
  have hz := congrArg (fun A => z ∈ A) heq
  simp only [mem_inter, mem_compl, mem_sdiff] at hz ⊢
  have hts : z ∈ t → z ∈ s := fun h => ht h
  tauto

/--
Shattering is preserved by taking complements: each trace on `s` is
replaced by its complement in `s`. Apply this in both directions.
-/
theorem vcDim_compl_eq {V : Type u} [Fintype V] [DecidableEq V]
    (𝓕 : Finset (Finset V)) :
    (𝓕.image (fun A => Aᶜ)).vcDim = 𝓕.vcDim := by
  apply le_antisymm (vcDim_compl_le 𝓕)
  have h := vcDim_compl_le (𝓕.image (fun A => Aᶜ))
  simpa only [image_image, Function.comp_def, compl_compl, image_id'] using h

end Lax185574Proofs.Lib.VCOperations
