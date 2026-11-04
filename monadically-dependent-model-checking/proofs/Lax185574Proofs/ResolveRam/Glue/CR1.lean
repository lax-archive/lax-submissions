import Lax185574Proofs.ResolveRam.Glue.CR1U

/-!
The case of round `1` of the glue program of lem:resolve-lift, the round
that receives the answer of the scatter type (position `stp`).

`bR1 atC` runs `bR1up atC` if `q₀ = 0` and `bR1dn` otherwise
(`bR1_up_ok`, `bR1_dn_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam
open Lax3.DistFO (rhoPlus)

/-- The test of round `1`: the way down has no level. -/
def cR1q : Cond := .eq (.var "gq") (.lit 0)

/-- The case of round `1`. -/
noncomputable def bR1 (atC : Com) : Com := .ite cR1q (bR1up atC) bR1dn

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem cR1q_eval {W R : ℕ} {wx b : List ℕ} {τ : Env}
    (P0 : PreR W R (scW G P Q s k₀ q₀ .stp) (swAt G P Q s k₀ q₀ .stp).ws wx b τ) :
    cR1q.evalB (W + 1) τ = some (q₀ == 0) := by
  have h := preR_var P0 8 (by omega)
  simp only [scR, scW_stp] at h
  exact evalB_condEq h (evalB_lit (by omega))

/-- **Round `1` when the way down has no level.** -/
theorem bR1_up_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {W : ℕ} (hk : 1 ≤ k₀) (hn : 1 ≤ n) (hq : q₀ = 0) :
    BodyCall (bR1 atC) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ .stp)
      (swAt G P Q s k₀ q₀ .stp).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ .stp))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ .stp)) (libR1 G P Q s k₀ q₀ 0 ++ [aqR1 G P Q s k₀ q₀])
      (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length)
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (1 + cR1q.size + kR1up G P Q s k₀ q₀ hAt hAV) :=
  bodyCall_ite_true (fun τ P0 => by rw [cR1q_eval G P Q s k₀ q₀ P0, hq]; rfl)
    (bR1up_ok G P Q s k₀ q₀ hAt hAV hk hn hq)

/-- **Round `1` when the way down has a level.** -/
theorem bR1_dn_ok (atC : Com) {W : ℕ} (hn : 1 ≤ n) (hq : q₀ ≠ 0) :
    BodyCall (bR1 atC) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ .stp)
      (swAt G P Q s k₀ q₀ .stp).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ .stp))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ .stp)) (libR1 G P Q s k₀ q₀ 1)
      (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length)
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (1 + cR1q.size + kR1dn G P Q s k₀ q₀) :=
  bodyCall_ite_false (fun τ P0 => by
      rw [cR1q_eval G P Q s k₀ q₀ P0]
      cases h : q₀ with
      | zero => exact absurd h hq
      | succ m => rfl)
    (bR1dn_ok G P Q s k₀ q₀ hn hq)

end Lax185574Proofs.ResolveRam.Glue
