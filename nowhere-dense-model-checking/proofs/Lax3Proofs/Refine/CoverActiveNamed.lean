import Lax3Proofs.RamDriver
import Lax3Proofs.Refine.CoverActiveLoop
import Lax3Proofs.Refine.ScatterBlockProg

/-!
# Active-cover construction at driver-owned array names

The block-priced cover loop was proved at the reusable scratch names
`alv` and `ord`.  A recursive driver cannot populate either array by a
carrier-wide copy.  It already owns the active ordering at `ordName j`,
and `OrderMem` supplies the zeroed `elm` array that can be populated and
consumed over the live prefix.

This file moves the existing loop to those two arrays by an involutive
renaming.  Program text and cost are unchanged.
-/

namespace Lax3Proofs.Refine.CoverActiveNamed

open Lax3.ColoredGraphs
open Lax11.GraphEncoding
open Lax3Proofs.RamBfs (CsrGraph)
open Lax3Proofs.RamDriver (ordName)
open Lax3Proofs.Refine.CoverActiveLoop
open Lax3Proofs.Refine.CoverActiveTurn
open Lax3Proofs.Refine.ScatterBlock
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## The two-pair array renaming -/

/-- Exchange the reusable mask and ordering names with the two arrays
owned by depth `j`.  The four names are pairwise distinct. -/
def activeCoverSwap (j : ℕ) (a : String) : String :=
  if a = "alv" then "elm"
  else if a = "elm" then "alv"
  else if a = "ord" then ordName j
  else if a = ordName j then "ord"
  else a

@[simp] theorem activeCoverSwap_alv (j : ℕ) : activeCoverSwap j "alv" = "elm" := by
  simp [activeCoverSwap]

@[simp] theorem activeCoverSwap_elm (j : ℕ) : activeCoverSwap j "elm" = "alv" := by
  simp [activeCoverSwap]

@[simp] theorem activeCoverSwap_ord (j : ℕ) : activeCoverSwap j "ord" = ordName j := by
  simp [activeCoverSwap, ordName, String.ext_iff]

@[simp] theorem activeCoverSwap_ordName (j : ℕ) :
    activeCoverSwap j (ordName j) = "ord" := by
  simp [activeCoverSwap, ordName, String.ext_iff]

theorem activeCoverSwap_of_ne (j : ℕ) (a : String)
    (ha : a ≠ "alv") (he : a ≠ "elm") (ho : a ≠ "ord")
    (hj : a ≠ ordName j) : activeCoverSwap j a = a := by
  simp [activeCoverSwap, ha, he, ho, hj]

/-- The simultaneous exchange is its own inverse, which is the exact
hypothesis required by `renCom_spec`. -/
theorem activeCoverSwap_invol (j : ℕ) :
    ∀ a, activeCoverSwap j (activeCoverSwap j a) = a := by
  intro a
  by_cases ha : a = "alv"
  · subst a
    simp
  by_cases he : a = "elm"
  · subst a
    simp
  by_cases ho : a = "ord"
  · subst a
    simp
  by_cases hj : a = ordName j
  · subst a
    simp
  rw [activeCoverSwap_of_ne j a ha he ho hj]
  exact activeCoverSwap_of_ne j a ha he ho hj

/-! ## The named active loop -/

/-- The existing active loop, reading the ordering directly from the
depth and using the zeroed elimination mask as its progressive mask. -/
def activeLoopAtCom (j r : ℕ) : Com :=
  renCom (activeCoverSwap j) (activeLoopCom r)

variable {B n ns nt q r j : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre O T : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
variable {bw nb : ℕ → ℕ}

/-- The raw active-cover theorem transported to the driver-owned arrays.
The cost is definitionally identical to the reusable loop's cost. -/
theorem activeLoopAt_rawOut_spec
    (hcentres : Lax3Proofs.RamCoverActive.CentresBy n q A₀ π centre)
    (hcsr : CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt) (hnnB : n * n < B)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hbud : ActiveBallBudget q r G A₀ centre O bw nb) :
    Spec B
      (fun σ => RawLoopState B ns nt q r G A₀ π centre O T
        ((renEnv (activeCoverSwap j) σ).setVar "c" 0))
      (activeLoopAtCom j r)
      (fun _ σ' => ∃ xp Xoff Xmem asg M,
        RawTurnState B ns nt q r q xp G A₀ π centre O T Xoff Xmem asg M
          (renEnv (activeCoverSwap j) σ') ∧
        Lax3Proofs.RamCover.RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
      (activeLoopK q bw nb) :=
  renCom_spec (activeCoverSwap_invol j)
    (activeLoop_rawOut_spec hcentres hcsr hnB hnsB hnt hnnB hqB hrB hbud)

/-- The degree-priced loop transported to the driver-owned mask and order
arrays.  Its sharp exit-pointer bound survives the renaming unchanged. -/
theorem activeLoopAtK_rawOut_spec {Kball : ℕ}
    (hcentres : Lax3Proofs.RamCoverActive.CentresBy n q A₀ π centre)
    (hcsr : CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (harenaB : n * Kball + n < B)
    (hbud : ActiveBallBudget q r G A₀ centre O bw nb)
    (hnbK : ∀ k < q, nb k ≤ Kball) :
    Spec B
      (fun σ => RawLoopStateK B ns nt q r Kball G A₀ π centre O T
        ((renEnv (activeCoverSwap j) σ).setVar "c" 0))
      (activeLoopAtCom j r)
      (fun _ σ' => ∃ xp Xoff Xmem asg M,
        RawTurnState B ns nt q r q xp G A₀ π centre O T Xoff Xmem asg M
          (renEnv (activeCoverSwap j) σ') ∧
        xp ≤ q * Kball ∧
        Lax3Proofs.RamCover.RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
      (activeLoopK q bw nb) :=
  renCom_spec (activeCoverSwap_invol j)
    (activeLoopK_rawOut_spec hcentres hcsr hnB hnsB hnt hqB hrB harenaB
      hbud hnbK)

/-! ## Axiom audit -/

#print axioms activeCoverSwap_invol
#print axioms activeLoopAt_rawOut_spec
#print axioms activeLoopAtK_rawOut_spec

end Lax3Proofs.Refine.CoverActiveNamed
