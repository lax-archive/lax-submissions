import Lax457868Proofs.SamplePacking
import Lax457868Proofs.SourceRenaming

/-! Reuse the verified sample-flag packer for a distinct active-side array. -/

namespace Lax457868Proofs.PackedActiveSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.SourceRenaming

/-- Rename the sample packer's private state to the active-side interface. -/
def activePackNames : Names where
  scalar := Equiv.swap "sampleCount" "alen" *
    Equiv.swap "sampleCursor" "activePackCursor"
  array := Equiv.swap "sampleFlags" "activeB"

/-- Fixed source obtained from the existing verified packer by static swaps. -/
def packActiveBSource : Com := renameCom activePackNames packMarkedSamples

private lemma activePackNames_scalar (x : String) :
    activePackNames.scalar x =
      if x = "sampleCount" then "alen" else
      if x = "alen" then "sampleCount" else
      if x = "sampleCursor" then "activePackCursor" else
      if x = "activePackCursor" then "sampleCursor" else x := by
  by_cases h1 : x = "sampleCount"
  · subst x; simp [activePackNames, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  · by_cases h2 : x = "alen"
    · subst x; simp [activePackNames, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    · by_cases h3 : x = "sampleCursor"
      · subst x; simp [activePackNames, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      · by_cases h4 : x = "activePackCursor"
        · subst x; simp [activePackNames, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        · simp [activePackNames, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
            h1, h2, h3, h4]

private lemma activePackNames_array (x : String) :
    activePackNames.array x =
      if x = "sampleFlags" then "activeB" else
      if x = "activeB" then "sampleFlags" else x := by
  simp [activePackNames, Equiv.swap_apply_def]

private lemma activePackNames_fixed_n : activePackNames.scalar "n" = "n" := by
  rw [activePackNames_scalar]
  decide

private lemma activePackNames_fixed_ord : activePackNames.array "ord" = "ord" := by
  rw [activePackNames_array]
  decide

private lemma activePackNames_inverse_scalar_alen :
    activePackNames.scalar.symm "alen" = "sampleCount" := by
  apply activePackNames.scalar.injective
  rw [Equiv.apply_symm_apply, activePackNames_scalar]
  simp

private lemma activePackNames_inverse_scalar_cursor :
    activePackNames.scalar.symm "activePackCursor" = "sampleCursor" := by
  apply activePackNames.scalar.injective
  rw [Equiv.apply_symm_apply, activePackNames_scalar]
  simp

private lemma activePackNames_inverse_array_active :
    activePackNames.array.symm "activeB" = "sampleFlags" := by
  apply activePackNames.array.injective
  rw [Equiv.apply_symm_apply, activePackNames_array]
  simp

private lemma activePackNames_inverse_array_ord :
    activePackNames.array.symm "ord" = "ord" := by
  apply activePackNames.array.injective
  rw [Equiv.apply_symm_apply, activePackNames_fixed_ord]

/-- Packing `activeB` into `ord` reuses the proved linear scan and leaves the
source active flags and all other arrays untouched. `alen` is the resulting
number of active vertices; the packed prefix enumerates them without
duplicates, in the same increasing order as the original scan. -/
lemma packActiveB_run {B n : ℕ} {σ : Env} {flags ord : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hactiveB : σ.arrs "activeB" = arrOf n flags)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hflags01 : ∀ v < n, flags v ≤ 1)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' : Env, ∃ packed : ℕ → ℕ,
      Run B packActiveBSource σ σ' (20 * n + 9) ∧
      σ'.arrs "activeB" = arrOf n flags ∧
      σ'.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ'.vars "alen") packed (flaggedVertices n flags) ∧
      σ'.vars "alen" = (flaggedVertices n flags).card ∧
      σ'.vars "activePackCursor" = n ∧
      (∀ a, a ≠ "ord" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "alen" → v ≠ "activePackCursor" →
        σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let ρ := activePackNames
  let τ := renameEnv ρ.inverse σ
  have hstart : renameEnv ρ τ = σ := by
    simpa [τ] using renameEnv_inverse_left ρ σ
  have hnτ : τ.vars "n" = n := by
    change σ.vars (ρ.scalar "n") = n
    rw [activePackNames_fixed_n]
    exact hn
  have hflagsτ : τ.arrs "sampleFlags" = arrOf n flags := by
    change σ.arrs (ρ.array "sampleFlags") = arrOf n flags
    rw [activePackNames_array]
    exact hactiveB
  have hordτ : τ.arrs "ord" = arrOf n ord := by
    change σ.arrs (ρ.array "ord") = arrOf n ord
    rw [activePackNames_fixed_ord]
    exact hord
  obtain ⟨τ', packed, hrun, hflags', hord', hprefix, hcount, hcursor,
    hframeArr, hframeVar, hinp, hout⟩ :=
      packMarkedSamples_run hnτ hflagsτ hordτ hflags01 hnB honeB
  let σ' := renameEnv ρ τ'
  have hrun' : Run B packActiveBSource σ σ' (20 * n + 9) := by
    simpa [packActiveBSource, ρ, hstart] using run_rename ρ hrun
  have hactiveB' : σ'.arrs "activeB" = arrOf n flags := by
    change τ'.arrs (ρ.array.symm "activeB") = arrOf n flags
    rw [activePackNames_inverse_array_active]
    exact hflags'
  have hord'' : σ'.arrs "ord" = arrOf n packed := by
    change τ'.arrs (ρ.array.symm "ord") = arrOf n packed
    rw [activePackNames_inverse_array_ord]
    exact hord'
  have hcount' : σ'.vars "alen" = (flaggedVertices n flags).card := by
    change τ'.vars (ρ.scalar.symm "alen") = (flaggedVertices n flags).card
    rw [activePackNames_inverse_scalar_alen]
    exact hcount
  have hcursor' : σ'.vars "activePackCursor" = n := by
    change τ'.vars (ρ.scalar.symm "activePackCursor") = n
    rw [activePackNames_inverse_scalar_cursor]
    exact hcursor
  have hprefix' : PrefixEnumerates (σ'.vars "alen") packed
      (flaggedVertices n flags) := by
    rw [show σ'.vars "alen" = τ'.vars "sampleCount" by
      change τ'.vars (ρ.scalar.symm "alen") = _
      rw [activePackNames_inverse_scalar_alen]]
    exact hprefix
  have hframeArr' : ∀ a, a ≠ "ord" → σ'.arrs a = σ.arrs a := by
    intro a ha
    by_cases hactive : a = "activeB"
    · subst a
      rw [hactiveB', hactiveB]
    · have hsource : ρ.array.symm a ≠ "ord" := by
        intro heq
        have : a = ρ.array "ord" := by simpa using congrArg ρ.array heq
        rw [activePackNames_fixed_ord] at this
        exact ha this
      have hf := hframeArr (ρ.array.symm a) hsource
      rw [← hstart]
      change τ'.arrs (ρ.array.symm a) = τ.arrs (ρ.array.symm a)
      exact hf
  have hframeVar' : ∀ v, v ≠ "alen" → v ≠ "activePackCursor" →
      σ'.vars v = σ.vars v := by
    intro v hval hvcursor
    have hsource : ρ.scalar.symm v ≠ "sampleCount" := by
      intro heq
      have : v = ρ.scalar "sampleCount" := by simpa using congrArg ρ.scalar heq
      rw [activePackNames_scalar] at this
      simp at this
      exact hval this
    have hsource' : ρ.scalar.symm v ≠ "sampleCursor" := by
      intro heq
      have : v = ρ.scalar "sampleCursor" := by simpa using congrArg ρ.scalar heq
      rw [activePackNames_scalar] at this
      simp at this
      exact hvcursor this
    have hf := hframeVar (ρ.scalar.symm v) hsource hsource'
    rw [← hstart]
    change τ'.vars (ρ.scalar.symm v) = τ.vars (ρ.scalar.symm v)
    exact hf
  have hinp' : σ'.inp = σ.inp := by
    rw [← hstart]
    simpa [σ', renameEnv] using hinp
  have hout' : σ'.out = σ.out := by
    rw [← hstart]
    simpa [σ', renameEnv] using hout
  exact ⟨σ', packed, hrun', hactiveB', hord'', hprefix', hcount', hcursor',
    hframeArr', hframeVar', hinp', hout'⟩

end Lax457868Proofs.PackedActiveSource
