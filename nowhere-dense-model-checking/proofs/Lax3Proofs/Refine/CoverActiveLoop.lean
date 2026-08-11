import Lax3Proofs.Refine.CoverActiveTurn
import Lax3Proofs.Refine.CoverBlock

/-!
# The block-priced active-cover loop

This file iterates `activeTurnCom` over the live centre prefix.  Each turn
is charged to its own masked ball, so the exported cost is a sum of block
weights rather than the carrier count times a carrier-wide search.
-/

namespace Lax3Proofs.Refine.CoverActiveLoop

open Lax3.ColoredGraphs
open Lax11.GraphEncoding
open Lax3Proofs.RamBfs (CsrGraph WD)
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.BfsBlock
open Lax3Proofs.Refine.CoverActiveBlock
open Lax3Proofs.Refine.CoverActiveTurn
open Lax3Proofs.Refine.CoverBlock
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Program, budgets, and invariant -/

/-- The active pass has the standard counted-loop shape, but stops at the
live count in `qn`. -/
def activeLoopCom (r : ℕ) : Com :=
  centreLoopCom "c" "qn" (activeTurnCom r)

/-- Per-centre row-slot and vertex budgets. -/
def activeLoopK (q : ℕ) (bw nb : ℕ → ℕ) : ℕ :=
  coverLoopK 150 q (fun k => bw k + nb k)

/-- Every progressive mask reached at centre `c` has a finite ball fitting
the two supplied budgets.  The zero-pattern premise is exactly the mask
clause of `RawCoverInvA`; positive mask payloads are deliberately irrelevant.
-/
def ActiveBallBudget {n : ℕ} (q r : ℕ) (G : SimpleGraph (Fin n))
    (A₀ centre O : ℕ → ℕ) (bw nb : ℕ → ℕ) : Prop :=
  ∀ c, c < q → ∀ M : ℕ → ℕ,
    (∀ u < n, M u = 0 ↔ (A₀ u = 0 ∨ ∃ i < c, centre i = u)) →
    ∃ A : Finset ℕ,
      (∀ v, v < n → M v ≠ 0 → WD G M (2 * r) (centre c) v → v ∈ A) ∧
      (∑ v ∈ A, Csr.rowLen O v) ≤ bw c ∧ A.card ≤ nb c

/-- Existential closure of the mutable mathematical arrays.  Machine state
still pins the current counter and pointer, so consecutive turns compose
without weakening either fact. -/
def RawLoopState {n : ℕ} (B ns q r : ℕ) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (centre O T : ℕ → ℕ)
    (σ : Env) : Prop :=
  ∃ c xp Xoff Xmem asg M,
    RawTurnState B ns q r c xp G A₀ π centre O T Xoff Xmem asg M σ

/-! ## Loop theorem -/

variable {B n ns q r : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre O T : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
variable {bw nb : ℕ → ℕ}

/-- The complete active prefix, charged by the sum of its individual ball
budgets. -/
theorem activeLoop_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnnB : n * n < B)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hbud : ActiveBallBudget q r G A₀ centre O bw nb) :
    Spec B
      (fun σ => RawLoopState B ns q r G A₀ π centre O T (σ.setVar "c" 0))
      (activeLoopCom r)
      (fun _ σ' => ∃ xp Xoff Xmem asg M,
        RawTurnState B ns q r q xp G A₀ π centre O T Xoff Xmem asg M σ')
      (activeLoopK q bw nb) := by
  let I : Env → Prop := RawLoopState B ns q r G A₀ π centre O T
  have hxN : ∀ σ, I σ → σ.vars "c" ≤ q := by
    intro σ hσ
    obtain ⟨c, xp, Xoff, Xmem, asg, M, hS⟩ := hσ
    rw [hS.centre_var]
    exact hS.raw.pos_le
  have hqn : ∀ σ, I σ → σ.vars "qn" = q := by
    intro σ hσ
    obtain ⟨c, xp, Xoff, Xmem, asg, M, hS⟩ := hσ
    exact hS.q_var
  have hbody : CentreImplementsB B "c" (activeTurnCom r) I q 150
      (fun k => bw k + nb k) := by
    intro k hk
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨c, xp, Xoff, Xmem, asg, M, hS⟩, hck⟩ := hσ
    have hceq : c = k := by rw [hS.centre_var] at hck; omega
    subst c
    obtain ⟨A, hA, hbw, hnb⟩ := hbud k hk M hS.raw.mask
    obtain ⟨σ', hrun, tail, Q, QD, Xmem', htail, hS'⟩ :=
      (activeTurn_spec (B := B) (G := G) (A₀ := A₀) (π := π)
        (centre := centre) (O := O) (T := T) (Xoff := Xoff) (Xmem := Xmem)
        (asg := asg) (M := M) hcentres hcsr hnB hnsB hnnB hqB hrB
        hA hbw hnb).run (σ := σ) ⟨hS, hk⟩
    refine ⟨σ', activeTurnK (bw k) (nb k), hrun, ?_, ?_⟩
    · exact activeTurnK_le_weight (bw k) (nb k)
    · refine ⟨?_, hS'.centre_var⟩
      exact ⟨k + 1, xp + tail, upd Xoff (k + 1) (xp + tail), Xmem',
        queueCell asg q k r tail Q QD, upd M (centre k) 0, hS'⟩
  have hloop := centreLoop_spec "c" "qn" q 150 (fun k => bw k + nb k)
    hqB hxN hqn hbody
  simpa only [activeLoopCom, activeLoopK] using hloop.post (by
    intro _ σ' _ hpost
    obtain ⟨⟨c, xp, Xoff, Xmem, asg, M, hS⟩, hcq⟩ := hpost
    have hceq : c = q := by rw [hS.centre_var] at hcq; omega
    subst c
    exact ⟨xp, Xoff, Xmem, asg, M, hS⟩)

/-- At loop exit the raw consumer-facing cover semantics are already
available; only the per-block ordering representation is absent. -/
theorem activeLoop_rawOut_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnnB : n * n < B)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hbud : ActiveBallBudget q r G A₀ centre O bw nb) :
    Spec B
      (fun σ => RawLoopState B ns q r G A₀ π centre O T (σ.setVar "c" 0))
      (activeLoopCom r)
      (fun _ σ' => ∃ xp Xoff Xmem asg M,
        RawTurnState B ns q r q xp G A₀ π centre O T Xoff Xmem asg M σ' ∧
        Lax3Proofs.RamCover.RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
      (activeLoopK q bw nb) :=
  (activeLoop_spec hcentres hcsr hnB hnsB hnnB hqB hrB hbud).post
    (fun _ _ _ h => by
      obtain ⟨xp, Xoff, Xmem, asg, M, hS⟩ := h
      exact ⟨xp, Xoff, Xmem, asg, M, hS, hS.raw.out hcentres⟩)

/-! ## Axiom audit -/

#print axioms activeLoop_spec
#print axioms activeLoop_rawOut_spec

end Lax3Proofs.Refine.CoverActiveLoop
