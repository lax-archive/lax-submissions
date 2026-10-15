import Lax457868Proofs.ReusedOriginal.Construction.RecordedHistory

/-! A narrow specialization of the accepted recorded-history output theorem.
The theorem below uses an actual `History` certificate and the concrete source
program/array premises. It does not construct a history; the existing refined
reduction and partition bridge are the route that can supply that premise. -/

namespace Lax457868Proofs.RefinedHistoryOutput

open Lax457868Proofs.ReusedOriginal.Construction.RecordedHistory
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.Correctness
open Lax195003.WelzlOrdersInGraphs

/-- The accepted reconstruction output theorem at the refined `2k log₂ n`
round budget. This is conditional on the concrete recorded history and source
array certificates listed below. -/
lemma History.reconstructAndWrite_clog2_bound
    {B n k R : ℕ} {G : SimpleGraph (Fin n)}
    {σ : Env} {A C : ℕ → Set (Fin n)}
    {boundary starts ends removed repAt active next : ℕ → ℕ}
    (h : History G k R A C boundary removed repAt)
    (hA : A 0 = Set.univ) (hC : C 0 = Set.univ)
    (hterminal : A R = {v : Fin n | active v.val = 1})
    (hsmall : (A R).ncard ≤ 2 * k)
    (hroundsLog : R + 1 ≤ Nat.clog 2 n)
    (hn : σ.vars "n" = n) (hround : σ.vars "round" = R)
    (hRn : R ≤ n) (hnB : n < B) (hout : σ.out = [])
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hstarts : σ.arrs "roundStart" = arrOf n starts)
    (hends : σ.arrs "roundEnd" = arrOf n ends)
    (hremoved : σ.arrs "removed" = arrOf n removed)
    (hreps : σ.arrs "removedRep" = arrOf n repAt)
    (hstartVals : ∀ r < R, starts r = boundary r)
    (hendVals : ∀ r < R, ends r = boundary (r + 1))
    (hmono : ∀ r < R, boundary r ≤ boundary (r + 1))
    (hcap : ∀ r ≤ R, boundary r ≤ n)
    (hremN : ∀ i < n, removed i < n) (hrepN : ∀ i < n, repAt i < n)
    (hactiveB : ∀ i < n, active i < B) (hnextB : ∀ i < n, next i < B)
    (hnonempty : 0 < n → scanList active 0 n ≠ []) :
    ∃ τ, Run B reconstructAndWrite σ τ (100 * (n + 1)) ∧
      EncodesGraphWelzlOrder G 1 (2 * k * Nat.clog 2 n) τ.out ∧ τ.inp = σ.inp := by
  have hcross : (R + 1) * (2 * k) ≤ 2 * k * Nat.clog 2 n := by
    calc
      (R + 1) * (2 * k) = (2 * k) * (R + 1) := Nat.mul_comm _ _
      _ ≤ (2 * k) * Nat.clog 2 n := Nat.mul_le_mul_left _ hroundsLog
  exact h.reconstructAndWrite_correct
    hA hC hterminal hsmall (by omega) hcross hn hround hRn hnB hout
    hactive hnext hstarts hends hremoved hreps hstartVals hendVals hmono hcap
    hremN hrepN hactiveB hnextB hnonempty

end Lax457868Proofs.RefinedHistoryOutput
