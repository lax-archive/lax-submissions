import Lax3Proofs.Refine.CoverActiveInit
import Lax3Proofs.Refine.CoverActiveRadixLoop

/-!
# The complete active-cover core

This file composes the member-priced initializer, the block-priced active
cover loop, and the uniform per-block radix sorter.  The result is the
consumer-facing sorted cover while restoring the driver's `elm` scratch
array to zero.  Its cost premise deliberately mentions the actual raw
arena: the later mass argument, rather than a carrier-square fallback,
will discharge that premise.
-/

namespace Lax3Proofs.Refine.CoverActiveCore

open Lax3.ColoredGraphs
open Lax3Proofs.RamCover
open Lax3Proofs.RamCoverActive
open Lax3Proofs.RamDriver (ordName xofName xmmName asgName)
open Lax3Proofs.Refine.CoverActiveInit
open Lax3Proofs.Refine.CoverActiveNamed
open Lax3Proofs.Refine.CoverActiveLoop
open Lax3Proofs.Refine.CoverActiveTurn
open Lax3Proofs.Refine.CoverActiveRadixPass
open Lax3Proofs.Refine.CoverActiveRadixWidth
open Lax3Proofs.Refine.CoverActiveRadixLoop
open Lax3Proofs.Refine.ScatterBlock (renEnv)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Program and output -/

/-- The whole reusable active-cover construction at scratch output names. -/
def activeCoreScratchCom (j r : ℕ) : Com :=
  .seq (activeInitCom j r)
    (.seq (activeLoopAtCom j r) radixCoverUniformCom)

/-- Machine representation and mathematical result of the active core. -/
structure ActiveCoreOut {n : ℕ} (q r j : ℕ) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ)
    (σ : Env) : Prop where
  n_var : σ.vars "n" = n
  q_var : σ.vars "qn" = q
  pointer_var : ∃ xp, σ.vars "xp" = xp
  centre_arr : σ.arrs (ordName j) = arrOf n centre
  zero_mask : σ.arrs "elm" = arrOf n (fun _ => 0)
  cover : ∃ xp Xoff Xmem asg,
    σ.vars "xp" = xp ∧
    σ.arrs "xoff" = arrOf (n + 1) Xoff ∧
    σ.arrs "xmem" = arrOf (n * n) Xmem ∧
    σ.arrs "asg" = arrOf n asg ∧
    CoverOutA G A₀ π centre r q xp Xoff Xmem asg

/-! ## Direct output into the driver-owned arrays -/

/-- Exchange the three reusable cover-output arrays with their depth-owned
driver destinations.  Running the core through this renaming avoids every
otherwise necessary arena copy. -/
def activeOutputSwap (j : ℕ) (a : String) : String :=
  if a = "xoff" then xofName j
  else if a = xofName j then "xoff"
  else if a = "xmem" then xmmName j
  else if a = xmmName j then "xmem"
  else if a = "asg" then asgName j
  else if a = asgName j then "asg"
  else a

@[simp] theorem activeOutputSwap_xoff (j : ℕ) :
    activeOutputSwap j "xoff" = xofName j := by
  simp [activeOutputSwap]

@[simp] theorem activeOutputSwap_xofName (j : ℕ) :
    activeOutputSwap j (xofName j) = "xoff" := by
  simp [activeOutputSwap, xofName, xmmName, asgName, String.ext_iff]

@[simp] theorem activeOutputSwap_xmem (j : ℕ) :
    activeOutputSwap j "xmem" = xmmName j := by
  simp [activeOutputSwap, xofName, xmmName, String.ext_iff]

@[simp] theorem activeOutputSwap_xmmName (j : ℕ) :
    activeOutputSwap j (xmmName j) = "xmem" := by
  simp [activeOutputSwap, xofName, xmmName, asgName, String.ext_iff]

@[simp] theorem activeOutputSwap_asg (j : ℕ) :
    activeOutputSwap j "asg" = asgName j := by
  simp [activeOutputSwap, xofName, xmmName, asgName, String.ext_iff]

@[simp] theorem activeOutputSwap_asgName (j : ℕ) :
    activeOutputSwap j (asgName j) = "asg" := by
  simp [activeOutputSwap, xofName, xmmName, asgName, String.ext_iff]

theorem activeOutputSwap_of_ne (j : ℕ) (a : String)
    (hxo : a ≠ "xoff") (hxoj : a ≠ xofName j)
    (hxm : a ≠ "xmem") (hxmj : a ≠ xmmName j)
    (ha : a ≠ "asg") (haj : a ≠ asgName j) :
    activeOutputSwap j a = a := by
  simp [activeOutputSwap, hxo, hxoj, hxm, hxmj, ha, haj]

theorem activeOutputSwap_invol (j : ℕ) :
    ∀ a, activeOutputSwap j (activeOutputSwap j a) = a := by
  intro a
  by_cases hxo : a = "xoff"
  · subst a
    simp
  by_cases hxoj : a = xofName j
  · subst a
    simp
  by_cases hxm : a = "xmem"
  · subst a
    simp
  by_cases hxmj : a = xmmName j
  · subst a
    simp
  by_cases ha : a = "asg"
  · subst a
    simp
  by_cases haj : a = asgName j
  · subst a
    simp
  rw [activeOutputSwap_of_ne j a hxo hxoj hxm hxmj ha haj]
  exact activeOutputSwap_of_ne j a hxo hxoj hxm hxmj ha haj

/-- The active core writing its three potentially large answers directly
at the arrays owned by recursion depth `j`. -/
def activeCoreAtCom (j r : ℕ) : Com :=
  Lax3Proofs.Refine.ScatterBlock.renCom (activeOutputSwap j)
    (activeCoreScratchCom j r)

/-- Physical driver-facing output of `activeCoreAtCom`. -/
structure ActiveCoreAtOut {n : ℕ} (q r j : ℕ) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ)
    (σ : Env) : Prop where
  n_var : σ.vars "n" = n
  q_var : σ.vars "qn" = q
  centre_arr : σ.arrs (ordName j) = arrOf n centre
  zero_mask : σ.arrs "elm" = arrOf n (fun _ => 0)
  cover : ∃ xp Xoff Xmem asg,
    σ.vars "xp" = xp ∧
    σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧
    σ.arrs (xmmName j) = arrOf (n * n) Xmem ∧
    σ.arrs (asgName j) = arrOf n asg ∧
    CoverOutA G A₀ π centre r q xp Xoff Xmem asg

/-- The initializer precondition, pulled back so its scratch outputs are
the driver-owned output arrays from the start. -/
def ActiveCoreAtPre (B n ns nt q r j : ℕ) (A₀ centre O T : ℕ → ℕ)
    (σ : Env) : Prop :=
  ActiveInitPre B n ns nt q r j A₀ centre O T
    (renEnv (activeOutputSwap j) σ)

/-! ## Sorter frame facts -/

private theorem radixCoverUniform_preserves_n :
    "n" ∉ radixCoverUniformCom.wvars := by
  simp [radixCoverUniformCom, radixWidthCom, radixWidthTurn,
    radixCoverBody, radixCoverTurn, radixBlockCom, radixRoundCom,
    radixPassCom, stableScatterCom, selectDigitCom, selectDigitSlot,
    copyBackCom, copyBackSlot, Com.wvars]

private theorem radixCoverUniform_preserves_qn :
    "qn" ∉ radixCoverUniformCom.wvars := by
  simp [radixCoverUniformCom, radixWidthCom, radixWidthTurn,
    radixCoverBody, radixCoverTurn, radixBlockCom, radixRoundCom,
    radixPassCom, stableScatterCom, selectDigitCom, selectDigitSlot,
    copyBackCom, copyBackSlot, Com.wvars]

private theorem radixCoverUniform_preserves_xp :
    "xp" ∉ radixCoverUniformCom.wvars := by
  simp [radixCoverUniformCom, radixWidthCom, radixWidthTurn,
    radixCoverBody, radixCoverTurn, radixBlockCom, radixRoundCom,
    radixPassCom, stableScatterCom, selectDigitCom, selectDigitSlot,
    copyBackCom, copyBackSlot, Com.wvars]

private theorem radixCoverUniform_preserves_elm :
    "elm" ∉ radixCoverUniformCom.warrs := by
  simp [radixCoverUniformCom, radixWidthCom, radixWidthTurn,
    radixCoverBody, radixCoverTurn, radixBlockCom, radixRoundCom,
    radixPassCom, stableScatterCom, selectDigitCom, selectDigitSlot,
    copyBackCom, copyBackSlot, Com.warrs]

private theorem radixCoverUniform_preserves_ordName (j : ℕ) :
    ordName j ∉ radixCoverUniformCom.warrs := by
  simp [radixCoverUniformCom, radixWidthCom, radixWidthTurn,
    radixCoverBody, radixCoverTurn, radixBlockCom, radixRoundCom,
    radixPassCom, stableScatterCom, selectDigitCom, selectDigitSlot,
    copyBackCom, copyBackSlot, Com.warrs, ordName, String.ext_iff]

/-! ## Composition -/

variable {B n ns nt q r j K : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre O T : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
variable {bw nb : ℕ → ℕ}

/-- The complete active core.  The caller supplies a bound for every raw
arena the search can return; the active-order mass theorem later turns this
into the required almost-linear closed charge. -/
theorem activeCoreScratch_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt) (hnnB : n * n < B)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hbud : ActiveBallBudget q r G A₀ centre O bw nb)
    (hcost : ∀ xp Xoff Xmem asg,
      RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg →
      activeInitCost q +
        (activeLoopK q bw nb + radixCoverUniformCost n q Xoff) ≤ K) :
    Spec B
      (ActiveInitPre B n ns nt q r j A₀ centre O T)
      (activeCoreScratchCom j r)
      (fun _ σ' => ActiveCoreOut q r j G A₀ π centre σ') K := by
  intro σ hpre
  obtain ⟨σ₁, rinit, hinit⟩ :=
    (activeInit_spec hcentres hnB hqB hrB).run (σ := σ) hpre
  obtain ⟨σ₂, rloop, xp, Xoff, Xmem, asg, M, hstate, hraw⟩ :=
    (activeLoopAt_rawOut_spec hcentres hcsr hnB hnsB hnt hnnB hqB hrB hbud).run
      (σ := σ₁) hinit
  obtain ⟨Q₀, hQ₀⟩ := hstate.queue_arr
  have hn₂ : σ₂.vars "n" = n := by simpa using hstate.n_var
  have hqn₂ : σ₂.vars "qn" = q := by simpa using hstate.q_var
  have hxp₂ : σ₂.vars "xp" = xp := by simpa using hstate.pointer_var
  have hord₂ : σ₂.arrs (ordName j) = arrOf n centre := by
    simpa [renEnv] using hstate.centre_arr
  have helm₂ : σ₂.arrs "elm" = arrOf n M := by
    simpa [renEnv] using hstate.mask_arr
  have hxoff₂ : σ₂.arrs "xoff" = arrOf (n + 1) Xoff := by
    simpa [activeCoverSwap, ordName, String.ext_iff] using hstate.xoff_arr
  have hxmem₂ : σ₂.arrs "xmem" = arrOf (n * n) Xmem := by
    simpa [activeCoverSwap, ordName, String.ext_iff] using hstate.xmem_arr
  have hasg₂ : σ₂.arrs "asg" = arrOf n asg := by
    simpa [activeCoverSwap, ordName, String.ext_iff] using hstate.asg_arr
  have hQ₂ : σ₂.arrs "q" = arrOf n Q₀ := by
    simpa [activeCoverSwap, ordName, String.ext_iff] using hQ₀
  have hMzero : ∀ z < n, M z = 0 := by
    intro z hz
    apply (hstate.raw.mask z hz).2
    by_cases hAz : A₀ z = 0
    · exact Or.inl hAz
    · obtain ⟨i, hi, hic⟩ := hcentres.complete z hz hAz
      exact Or.inr ⟨i, hi, hic⟩
  have helmZero₂ : σ₂.arrs "elm" = arrOf n (fun _ => 0) := by
    rw [helm₂]
    exact arrOf_congr hMzero
  obtain ⟨σ₃, rsort, ⟨Xmem', Q, hxoff₃, hxmem₃, hasg₃, _hQ₃, hcover⟩,
      hfv, hfa, -, -⟩ :=
    ((radixCoverUniformCom_spec hraw (by omega) hnB hnnB).frame).run
      (σ := σ₂) ⟨hn₂, hqn₂, hxoff₂, hxmem₂, hasg₂, hQ₂⟩
  refine ⟨σ₃, ?_, ?_⟩
  · exact (rinit.seq (rloop.seq rsort)).mono (hcost xp Xoff Xmem asg hraw)
  · refine
      { n_var := by rw [hfv "n" radixCoverUniform_preserves_n]; exact hn₂
        q_var := by rw [hfv "qn" radixCoverUniform_preserves_qn]; exact hqn₂
        pointer_var := ⟨xp, by
          rw [hfv "xp" radixCoverUniform_preserves_xp]
          exact hxp₂⟩
        centre_arr := by
          rw [hfa (ordName j) (radixCoverUniform_preserves_ordName j)]
          exact hord₂
        zero_mask := by
          rw [hfa "elm" radixCoverUniform_preserves_elm]
          exact helmZero₂
        cover := ⟨xp, Xoff, Xmem', asg, by
          rw [hfv "xp" radixCoverUniform_preserves_xp]
          exact hxp₂, hxoff₃, hxmem₃, hasg₃, hcover⟩ }

/-- Driver-facing form of the core theorem.  In particular, its program
contains no save walk: the large output arenas are the depth arrays. -/
theorem activeCoreAt_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt) (hnnB : n * n < B)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hbud : ActiveBallBudget q r G A₀ centre O bw nb)
    (hcost : ∀ xp Xoff Xmem asg,
      RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg →
      activeInitCost q +
        (activeLoopK q bw nb + radixCoverUniformCost n q Xoff) ≤ K) :
    Spec B
      (ActiveCoreAtPre B n ns nt q r j A₀ centre O T)
      (activeCoreAtCom j r)
      (fun _ σ' => ActiveCoreAtOut q r j G A₀ π centre σ') K := by
  have hcore := activeCoreScratch_spec (j := j) hcentres hcsr hnB hnsB hnt hnnB hqB
    hrB hbud hcost
  have htransport := Lax3Proofs.Refine.ScatterBlock.renCom_spec
    (activeOutputSwap_invol j) hcore
  intro σ hpre
  obtain ⟨σ', hrun, hout⟩ := htransport.run (σ := σ) hpre
  obtain ⟨xp, Xoff, Xmem, asg, hxp, hxoff, hxmem, hasg, hcover⟩ := hout.cover
  refine ⟨σ', by simpa [activeCoreAtCom] using hrun, ?_⟩
  refine
    { n_var := by simpa [renEnv] using hout.n_var
      q_var := by simpa [renEnv] using hout.q_var
      centre_arr := by
        simpa [renEnv, activeOutputSwap, ordName, xofName, xmmName, asgName,
          String.ext_iff] using hout.centre_arr
      zero_mask := by
        simpa [renEnv, activeOutputSwap, xofName, xmmName, asgName,
          String.ext_iff] using hout.zero_mask
      cover := ⟨xp, Xoff, Xmem, asg, by simpa [renEnv] using hxp,
        by simpa [renEnv] using hxoff, by simpa [renEnv] using hxmem,
        by simpa [renEnv] using hasg, hcover⟩ }

/-! ## Axiom audit -/

#print axioms activeOutputSwap_invol
#print axioms activeCoreScratch_spec
#print axioms activeCoreAt_spec

end Lax3Proofs.Refine.CoverActiveCore
