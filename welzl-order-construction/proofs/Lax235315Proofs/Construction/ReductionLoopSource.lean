import Lax235315Proofs.Construction.ReductionRoundSource
import Lax235315Proofs.Construction.RoundPotential

/-! Total bounded execution of the actual guarded reduction loop, with a
finite unread-bit reserve and amortized near-linear source cost. -/
namespace Lax235315Proofs.Construction.ReductionLoopSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.ReductionRoundSource
open Lax235315Proofs.Construction.RoundPotential

structure LoopState (B c n bound : ℕ) (x : List ℕ) (σ : Env) : Prop where
  workspace : Workspace B c n x σ
  square : σ.vars "csq" = c ^ 2
  nearBound : σ.vars "nearBound" = bound
  threshold : σ.vars "threshold" = 12 * c ^ 2 * Nat.clog 2 n
  status : (Frontier B c n x σ ∧
      24 * Nat.clog 2 n * σ.vars "acount" ≤ σ.inp.length) ∨
    (σ.vars "good" ≠ 1 ∧ σ.vars "acount" = 0)

def loopPotential (c n : ℕ) (x : List ℕ) (σ : Env) : ℕ :=
  if 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount" then
    potential (x.length + 1) (Nat.clog 2 n) (σ.vars "round") (σ.vars "acount")
  else 0

/-- The reduction loop terminates on every tape with the stated finite
reserve. Both collision and certificate rejection are included in the bound. -/
lemma reductionLoop_run {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : LoopState B c n bound x σ) (hc : 1 ≤ c) (hn : 1 < n)
    (hqB : 2 ^ Nat.clog 2 n < B)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B (.while (.lt (.var "threshold") (.var "acount")) reductionRound)
      σ σ' (loopPotential c n x σ + 4) ∧
      LoopState B c n bound x σ' ∧
      σ'.vars "acount" ≤ 12 * c ^ 2 * Nat.clog 2 n := by
  have hL : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by omega) hn
  let I := LoopState B c n bound x
  let Φ := loopPotential c n x
  let b : Cond := .lt (.var "threshold") (.var "acount")
  have hdef : ∀ τ, I τ → ∃ v, b.evalB B τ = some v := by
    intro τ ht
    exact ⟨_, evalB_condLt (evalB_var (ht.workspace.bounded.vars "threshold"))
      (evalB_var (ht.workspace.bounded.vars "acount"))⟩
  have hstep : ∀ τ, I τ → b.evalB B τ = some true →
      ∃ τ' K, Run B reductionRound τ τ' K ∧ I τ' ∧
        1 + b.size + K + Φ τ' ≤ Φ τ := by
    intro τ ht htrue
    have htest := evalB_condLt (evalB_var (ht.workspace.bounded.vars "threshold"))
      (evalB_var (ht.workspace.bounded.vars "acount"))
    have hlarge : 12 * c ^ 2 * Nat.clog 2 n < τ.vars "acount" := by
      have he := htest.symm.trans htrue
      simpa [ht.threshold] using he
    rcases ht.status with ⟨hfront, hreserve⟩ | ⟨hfail, hzero⟩
    · obtain ⟨τ', hr, hw, hinp, hout⟩ := reductionRound_run hx hG hfront hc hn
        hlarge ht.square ht.nearBound (by nlinarith) hqB hnB htargetB hdenomB hboundB
      have hsq := (hr.frame_var "csq" (by decide)).trans ht.square
      have hnear := (hr.frame_var "nearBound" (by decide)).trans ht.nearBound
      have hthreshold := (hr.frame_var "threshold" (by decide)).trans ht.threshold
      have hround := hfront.shrinking.rounds_succ_le_clog hc hn
      refine ⟨τ', _, hr, ?_, ?_⟩
      · refine ⟨hw, hsq, hnear, hthreshold, ?_⟩
        rcases hout with ⟨hfront', hrnext, hshrink⟩ | hfail
        · refine Or.inl ⟨hfront', ?_⟩
          rw [hinp]
          exact remaining_bits hL hlarge hshrink hreserve
        · exact Or.inr hfail
      · change 4 + _ + loopPotential c n x τ' ≤ loopPotential c n x τ
        rw [show loopPotential c n x τ =
          potential (x.length + 1) (Nat.clog 2 n) (τ.vars "round") (τ.vars "acount")
          from if_pos hlarge]
        rcases hout with ⟨hfront', hrnext, hshrink⟩ | ⟨hfail, hzero⟩
        · by_cases hlarge' : 12 * c ^ 2 * Nat.clog 2 n < τ'.vars "acount"
          · rw [loopPotential, if_pos hlarge', hrnext]
            have hp := potential_step (N := x.length + 1) (by omega) hL hround hlarge hshrink
            omega
          · rw [loopPotential, if_neg hlarge']
            have hp := potential_exit (N := x.length + 1) (a := τ.vars "acount")
              (by omega) hround
            omega
        · simp only [loopPotential, hzero, Nat.not_lt_zero, ↓reduceIte]
          have hp := potential_exit (N := x.length + 1) (a := τ.vars "acount")
            (by omega) hround
          omega
    · omega
  obtain ⟨τ, K, hr, ht, hfalse, hpay⟩ := Run.while_potential I Φ hdef hstep h
  refine ⟨τ, hr.mono ?_, ht, ?_⟩
  · change K + loopPotential c n x τ ≤ loopPotential c n x σ + 4 at hpay
    omega
  · have htest := evalB_condLt (evalB_var (ht.workspace.bounded.vars "threshold"))
      (evalB_var (ht.workspace.bounded.vars "acount"))
    have he := htest.symm.trans hfalse
    have hnlt : ¬ (τ.vars "threshold" < τ.vars "acount") := by simpa using he
    rw [ht.threshold] at hnlt
    omega

/-- Starting with all n vertices pays for every adaptive loop iteration in
O((input length + 1)(log n + 1)) source steps. -/
lemma reductionLoop_run_initial {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : LoopState B c n bound x σ) (hc : 1 ≤ c) (hn : 1 < n)
    (hround : σ.vars "round" = 0) (ha : σ.vars "acount" = n)
    (hqB : 2 ^ Nat.clog 2 n < B)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B (.while (.lt (.var "threshold") (.var "acount")) reductionRound)
      σ σ' (5360 * (x.length + 1) * (Nat.clog 2 n + 1) + 4) ∧
      LoopState B c n bound x σ' ∧
      σ'.vars "acount" ≤ 12 * c ^ 2 * Nat.clog 2 n := by
  obtain ⟨τ, hr, ht, hsmall⟩ := reductionLoop_run hx hG h hc hn hqB hnB
    htargetB hdenomB hboundB
  refine ⟨τ, hr.mono ?_, ht, hsmall⟩
  have hnN : n ≤ x.length + 1 := by have := hx.length_eq; omega
  have hp := potential_initial (L := Nat.clog 2 n) hnN
  unfold loopPotential
  split_ifs
  · simp only [hround, ha]
    omega
  · omega

end Lax235315Proofs.Construction.ReductionLoopSource
