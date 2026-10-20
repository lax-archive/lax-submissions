import Lax457868Proofs.SamplePacking
import Lax457868Proofs.SourceRenaming

/-! The draw domain is the current active A-side. Reuse the already verified
flag packer by a fixed bijective renaming, without another scan proof. -/

namespace Lax457868Proofs.PackedDomainSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.SamplePacking Lax457868Proofs.SourceRenaming

/-- A static change of names for the existing sample-flag packer. -/
def domainPackNames : Names where
  scalar := Equiv.swap "sampleCount" "drawModulus" *
    Equiv.swap "sampleCursor" "domainPackCursor"
  array := Equiv.swap "sampleFlags" "activeA" * Equiv.swap "ord" "drawDomain"

/-- Pack active A vertices into the sampler's indexed draw domain. -/
def packDomainSource : Com := renameCom domainPackNames packMarkedSamples

/-- The packed prefix enumerates exactly the current active domain. All
other arrays, random input, output, and nonprivate registers are preserved. -/
lemma packDomainSource_run {B n : ℕ} {σ : Env} {flags domain : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hactive : σ.arrs "activeA" = arrOf n flags)
    (hdom : σ.arrs "drawDomain" = arrOf n domain)
    (hflags : ∀ v < n, flags v ≤ 1)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ τ : Env, ∃ packed : ℕ → ℕ,
      Run B packDomainSource σ τ (20 * n + 9) ∧
      τ.arrs "activeA" = arrOf n flags ∧
      τ.arrs "drawDomain" = arrOf n packed ∧
      PrefixEnumerates (τ.vars "drawModulus") packed (flaggedVertices n flags) ∧
      τ.vars "drawModulus" = (flaggedVertices n flags).card ∧
      τ.vars "domainPackCursor" = n ∧
      (∀ a, a ≠ "drawDomain" → τ.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "drawModulus" → v ≠ "domainPackCursor" →
        τ.vars v = σ.vars v) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let ρ := domainPackNames
  let σ₀ := renameEnv ρ.inverse σ
  have hstart : renameEnv ρ σ₀ = σ := renameEnv_inverse_left ρ σ
  have hnρ : ρ.scalar "n" = "n" := by decide
  have hcountρ : ρ.scalar "sampleCount" = "drawModulus" := by decide
  have hcursorρ : ρ.scalar "sampleCursor" = "domainPackCursor" := by decide
  have hactiveρ : ρ.array "sampleFlags" = "activeA" := by decide
  have hdomρ : ρ.array "ord" = "drawDomain" := by decide
  have hn₀ : σ₀.vars "n" = n := by
    change σ.vars (ρ.scalar "n") = n
    rwa [hnρ]
  have hactive₀ : σ₀.arrs "sampleFlags" = arrOf n flags := by
    change σ.arrs (ρ.array "sampleFlags") = arrOf n flags
    rwa [hactiveρ]
  have hdom₀ : σ₀.arrs "ord" = arrOf n domain := by
    change σ.arrs (ρ.array "ord") = arrOf n domain
    rwa [hdomρ]
  obtain ⟨τ₀, packed, hr, ha, hd, hp, hc, hi, hfa, hfv, hin, hout, _hpackedCells⟩ :=
    packMarkedSamples_run hn₀ hactive₀ hdom₀ hflags hnB honeB
  let τ := renameEnv ρ τ₀
  have hr' : Run B packDomainSource σ τ (20 * n + 9) := by
    simpa only [packDomainSource, hstart] using run_rename ρ hr
  have ha' : τ.arrs "activeA" = arrOf n flags := by
    rw [← hactiveρ, renameEnv_arrs]; exact ha
  have hd' : τ.arrs "drawDomain" = arrOf n packed := by
    rw [← hdomρ, renameEnv_arrs]; exact hd
  have hc' : τ.vars "drawModulus" = τ₀.vars "sampleCount" := by
    rw [← hcountρ, renameEnv_vars]
  have hi' : τ.vars "domainPackCursor" = n := by
    rw [← hcursorρ, renameEnv_vars]; exact hi
  refine ⟨τ, packed, hr', ha', hd', hc' ▸ hp, hc'.trans hc, hi', ?_, ?_, hin, hout⟩
  · intro a ha
    have ha₀ : ρ.array.symm a ≠ "ord" := by
      intro h
      have he := congrArg ρ.array h
      simp only [Equiv.apply_symm_apply, hdomρ] at he
      exact ha he
    rw [← hstart]
    exact hfa _ ha₀
  · intro v hv hv'
    have hv₀ : ρ.scalar.symm v ≠ "sampleCount" := by
      intro h
      have he := congrArg ρ.scalar h
      simp only [Equiv.apply_symm_apply, hcountρ] at he
      exact hv he
    have hv₀' : ρ.scalar.symm v ≠ "sampleCursor" := by
      intro h
      have he := congrArg ρ.scalar h
      simp only [Equiv.apply_symm_apply, hcursorρ] at he
      exact hv' he
    rw [← hstart]
    exact hfv _ hv₀ hv₀'

end Lax457868Proofs.PackedDomainSource
