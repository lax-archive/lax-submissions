import Lax457868Proofs.PackedActiveSource
import Lax457868Proofs.PackedDomainSource
import Lax457868Proofs.SamplerRuntimeSetup
import Lax457868Proofs.ExceptionPhaseSource

/-! Prepare the next sampler invocation from the actual current active sets.
Both scans reuse the original flag packer. No mathematical sample is installed
in the machine state. -/

namespace Lax457868Proofs.PrepareRefinedRound

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.SamplePacking Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.PackedActiveSource Lax457868Proofs.PackedDomainSource
open Lax457868Proofs.SamplerRuntimeSetup

/-- Fixed preparation reads the current active sets and the saved parameter. -/
def prepareRefinedRound : Com := seqs [packActiveBSource,
  .assign "activeBCount" (.var "alen"), packDomainSource, samplerParameterSource]

/-- The two packed domains and all sampler parameters are obtained by actual
source execution; untouched scratch storage and the random tape are framed. -/
lemma prepareRefinedRound_run {B c n : ℕ} {σ : Env}
    {A C : Finset ℕ} {ord domain : ℕ → ℕ}
    (hn : σ.vars "n" = n) (hc : σ.vars "c" = c)
    (hL : σ.vars "refinedLogC" = Nat.clog 2 c)
    (hcut : σ.vars "cutoffResult" = 2 * refinedCutoffK c)
    (hA : A ⊆ Finset.range n) (hC : C ⊆ Finset.range n)
    (ha : σ.arrs "activeA" = arrOf n (setFlag A))
    (hb : σ.arrs "activeB" = arrOf n (setFlag C))
    (ho : σ.arrs "ord" = arrOf n ord)
    (hd : σ.arrs "drawDomain" = arrOf n domain)
    (hc2 : 2 ≤ c) (hlarge : 2 * refinedCutoffK c < n) (hnB : n < B) :
    ∃ τ : Env, ∃ packed : ℕ → ℕ,
      Run B prepareRefinedRound σ τ (40 * n + 58) ∧
      τ.arrs "drawDomain" = arrOf n packed ∧
      PrefixEnumerates A.card packed A ∧
      τ.vars "drawModulus" = A.card ∧ τ.vars "activeBCount" = C.card ∧
      τ.vars "batchTarget" = A.card / (4 * c ^ 2) ∧
      τ.vars "repairSampleSize" = 64 * Nat.clog 2 c ∧
      τ.vars "exceptionCap" = A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)) ∧
      τ.vars "nearBound" = refinedCutoffK c / 3 ∧
      τ.vars "repairFarBound" = (2 * refinedCutoffK c) / 3 ∧
      τ.vars "initialRetryCap" = n ∧ τ.vars "repairRetryCap" = n ∧
      τ.vars "drawCap" = n ∧
      (∀ a, a ≠ "ord" → a ≠ "drawDomain" → τ.arrs a = σ.arrs a) ∧
      (∀ v, v ∉ prepareRefinedRound.wvars → τ.vars v = σ.vars v) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  have haCard : A.card ≤ n := by simpa using Finset.card_le_card hA
  have hcCard : C.card ≤ n := by simpa using Finset.card_le_card hC
  have h1B : 1 < B := by have h := (parameter_bounds hc2 hlarge).2.2.2.2.2; omega
  have haFlags : flaggedVertices n (setFlag A) = A := flagged_setFlag hA
  have hcFlags : flaggedVertices n (setFlag C) = C := flagged_setFlag hC
  obtain ⟨σ₁, packedB, rB, hb₁, ho₁, hprefixB, hcountB, hcursorB, hfaB, hfvB, hiB, houtB, _hpackedCellsB⟩ :=
    packActiveB_run hn hb ho (by intro v hv; simp [setFlag]; split_ifs <;> omega) hnB h1B
  rw [hcFlags] at hcountB
  let σ₂ := σ₁.setVar "activeBCount" C.card
  have rCount : Run B (.assign "activeBCount" (.var "alen")) σ₁ σ₂ 2 := by
    apply Run.assign
    rw [evalB_var (by rw [hcountB]; exact hcCard.trans_lt hnB), hcountB]
  have hn₂ : σ₂.vars "n" = n := by
    simp only [σ₂, Env.setVar, String.reduceEq, ite_false]
    exact (hfvB _ (by decide) (by decide)).trans hn
  have ha₂ : σ₂.arrs "activeA" = arrOf n (setFlag A) :=
    (hfaB _ (by decide)).trans ha
  have hd₂ : σ₂.arrs "drawDomain" = arrOf n domain :=
    (hfaB _ (by decide)).trans hd
  obtain ⟨σ₃, packedA, rA, ha₃, hd₃, hpA, hmA, hcursorA, hfaA, hfvA, hiA, houtA⟩ :=
    packDomainSource_run hn₂ ha₂ hd₂
      (by intro v hv; simp [setFlag]; split_ifs <;> omega) hnB h1B
  rw [haFlags] at hpA hmA
  have hn₃ : σ₃.vars "n" = n := (hfvA _ (by decide) (by decide)).trans hn₂
  have hscalar (v : String) (hvb : v ≠ "activeBCount")
      (hvB₁ : v ≠ "alen") (hvB₂ : v ≠ "activePackCursor")
      (hvA₁ : v ≠ "drawModulus") (hvA₂ : v ≠ "domainPackCursor") :
      σ₃.vars v = σ.vars v := by
    rw [hfvA v hvA₁ hvA₂]
    simp only [σ₂, Env.setVar, hvb, ite_false]
    exact hfvB v hvB₁ hvB₂
  obtain ⟨τ, rParams, hr, hs, hcap, hnear, hfar, hiCap, hrCap, hdCap, hfvP, hfaP, hiP, hoP⟩ :=
    samplerParameterSource_run hn₃
      ((hscalar "c" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc)
      ((hscalar "refinedLogC" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL)
      hmA
      ((hscalar "cutoffResult" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcut)
      hc2 haCard hlarge hnB
  have hrun : Run B prepareRefinedRound σ τ (40 * n + 58) := by
    have hh := rB.seq (rCount.seq (rA.seq rParams))
    convert hh using 1 <;> first | rfl | omega
  refine ⟨τ, packedA, hrun, ?_, ?_, ?_, ?_, hr, hs, hcap, hnear, hfar,
    hiCap, hrCap, hdCap, ?_, ?_, ?_, ?_⟩
  · rw [hfaP]; exact hd₃
  · simpa [hmA] using hpA
  · exact (hfvP _ (by decide)).trans hmA
  · rw [hfvP _ (by decide), hfvA _ (by decide) (by decide)]
    simp [σ₂]
  · intro a haOrd haDom
    rw [hfaP, hfaA a haDom]
    exact hfaB a haOrd
  · exact hrun.frame_var
  · exact hiP.trans (hiA.trans hiB)
  · exact hoP.trans (houtA.trans houtB)

end Lax457868Proofs.PrepareRefinedRound
