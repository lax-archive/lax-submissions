import Lax3Proofs.Refine.OrderVirtualPotential

/-!
# Complete virtual greedy elimination

This file initializes the three elimination counters, runs the amortised
guarded loop, and reads the mathematical greedy-elimination certificate from
the final arrays.  It is the provider-independent driver used by both the
base graph and every virtual augmentation round.
-/

namespace Lax3Proofs.Refine.OrderVirtualLoop

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamElim
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.Augmentation (nbrsIn)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualBucket (bucketExtra)
open Lax3Proofs.Refine.OrderVirtualReady
open Lax3Proofs.Refine.OrderVirtualEnsure
open Lax3Proofs.Refine.OrderVirtualPotential

/-- The result retained from a completed provider-backed elimination. -/
def VirtualElimResult {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Env) : Prop :=
  ∃ R ID : ℕ → ℕ, ∃ k : ℕ,
    σ.vars "n" = n ∧ σ.vars "kmax" = k ∧
    σ.arrs "rnk" = arrOf n R ∧ σ.arrs "idg" = arrOf n ID ∧
    (∀ v < n, R v < n) ∧
    ElimCert G (fun v : Fin n => R (v : ℕ)) k ∧
    ∀ w : Fin n, ID (w : ℕ) =
      ((ElimCert.elimOr G (fun v : Fin n => R (v : ℕ))).inN w).card

/-- At a false loop guard, the invariant contains a complete rank and the
greedy certificate for the unmasked graph. -/
theorem virtualElimExit_read {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {σ : Env} (hI : VirtualElimInv n G P σ)
    (hfalse : (Cond.lt (.var "cnt") (.var "n")).evalB B σ = some false) :
    VirtualElimResult G σ := by
  obtain ⟨E, D, R, ID, BH, BV, BN,
    hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩ := hI
  have hcntn : σ.vars "cnt" = n := by
    have h₁ := le_of_condLt_false hfalse
    have h₂ := helim.cnt_le
    have h₃ := heng.n_eq
    omega
  rw [hcntn] at helim
  have hcert₀ := helim.cert
  have hmask : masked G (fun _ => 1) = G :=
    masked_of_all_alive G (by simp)
  have hcert : ElimCert G (fun v : Fin n => R (v : ℕ))
      (σ.vars "kmax") := by
    simpa only [hmask] using hcert₀
  have hID₀ : ∀ w : Fin n, ID (w : ℕ) =
      ((ElimCert.elimOr (masked G (fun _ => 1))
        (fun v : Fin n => R (v : ℕ))).inN w).card := by
    intro w
    have h₁ := helim.taken w (helim.all_elim w)
    have h₂ := helim.survOf_eq_surv w
    have h₃ : (ElimCert.elimOr (masked G (fun _ => 1))
          (fun v : Fin n => R (v : ℕ))).inN w =
        nbrsIn (masked G (fun _ => 1))
          (surv (fun v : Fin n => R (v : ℕ)) (R (w : ℕ))) w :=
      (curNbrs_eq_backNbrs hcert₀.inj w).symm
    rw [h₁, h₂, h₃]
  refine ⟨R, ID, σ.vars "kmax", heng.n_eq, rfl, heng.rank_eq,
    heng.idg_eq, ?_, hcert, ?_⟩
  · intro v hv
    exact helim.rank_lt v hv (helim.all_elim ⟨v, hv⟩)
  · simpa only [hmask] using hID₀

/-- Counter initialization followed by the complete virtual loop. -/
def virtualElimLoop (provide : Com) : Com :=
  .seq (.assign "mind" (.lit 0))
    (.seq (.assign "cnt" (.lit 0))
      (.seq (.assign "kmax" (.lit 0))
        (virtualElimWhile provide)))

/-- Provider-independent complete elimination theorem.  Its cost is the sum
of the provider's one-use-per-vertex credits plus a carrier-linear term. -/
theorem virtualElimLoop_spec {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide κ)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B) :
    Spec B (VirtualReady n G P)
      (virtualElimLoop provide)
      (fun _ σ' => VirtualElimResult G σ')
      (virtualPotCap G κ + 10) := by
  run_vcg [virtualElimWhile_spec hp hclosed hrunClosed hB]
  · exact virtualElimExit_read ‹VirtualElimInv n G P _ ∧ _›.1
      ‹VirtualElimInv n G P _ ∧ _›.2
  · obtain ⟨hP, E, D, R, ID, BH, BV, BN, heng, helim, hbuck,
      hD, hi, hsp, hls⟩ := ‹VirtualReady n G P _›
    refine ⟨E, D, R, ID, BH, BV, BN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply hclosed.setVar (a := "kmax") (by simp [engineVarNames])
      apply hclosed.setVar (a := "cnt") (by simp [engineVarNames])
      apply hclosed.setVar (a := "mind") (by simp [engineVarNames])
      exact hP
    · refine ⟨by simp [heng.n_eq], by simp [heng.elm_eq],
        by simp [heng.deg_eq], by simp [heng.rank_eq], by simp [heng.idg_eq],
        by simp [heng.head_eq], by simp [heng.val_eq], by simp [heng.next_eq]⟩
    · simpa using helim
    · simpa using hbuck
    · exact hD
    · simp [hsp]
      omega
    · simp [hsp, hls]
    · simp
  all_goals simp [virtualElimLoop, Cond.size, Expr.size]
  all_goals omega

/-! ## Axiom audit -/

#print axioms virtualElimExit_read
#print axioms virtualElimLoop_spec

end Lax3Proofs.Refine.OrderVirtualLoop
