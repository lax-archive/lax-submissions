import Lax235315Proofs.Construction.TracePartitions
import Lax235315Proofs.Construction.WelzlProgram
import Mathlib.Tactic

/-! Verification of the quotient/remainder code computing the sample size
prescribed in each reduction round. -/

namespace Lax235315Proofs.Construction.SampleCountSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.WelzlProgram

/-- Division followed by a remainder test is the ceiling division used in
the paper's definition of `sampleSize`. -/
theorem div_add_remainder_indicator_eq_sampleSize
    {a c : ℕ} (hc : 1 ≤ c) :
    let d := 2 * c ^ 2
    a / d + (if a - (a / d) * d = 0 then 0 else 1) = sampleSize a c := by
  dsimp only
  let d := 2 * c ^ 2
  have hd : 0 < d := by
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hdsub : d - 1 < d := by omega
  have hrem : a - (a / d) * d = a % d := by
    simpa [Nat.mul_comm] using
      (Nat.mod_eq_sub_mul_div (x := a) (k := d)).symm
  unfold sampleSize
  change a / d + (if a - a / d * d = 0 then 0 else 1) =
    (a + d - 1) / d
  rw [show a + d - 1 = a + (d - 1) by omega, Nat.add_div hd,
    Nat.div_eq_of_lt hdsub, Nat.mod_eq_of_lt hdsub, hrem]
  by_cases hr : a % d = 0
  · simp [hr, hd]
  · have hrpos : 0 < a % d := Nat.pos_of_ne_zero hr
    have hcarry : d ≤ a % d + (d - 1) := by omega
    simp [hr, hcarry]

/-- The literal IMP+ prefix in `reductionRound` computes exactly
`sampleSize acount c`, with a constant source-level cost. -/
theorem prepareSampleCount_run
    {B a c : ℕ} {σ : Env}
    (hacount : σ.vars "acount" = a) (hcsq : σ.vars "csq" = c ^ 2)
    (hc : 1 ≤ c) (ha : 0 < a) (haB : a < B)
    (hdenomB : 2 * c ^ 2 < B) :
    ∃ σ', Run B prepareSampleCount σ σ' 22 ∧
      σ'.vars "denom" = 2 * c ^ 2 ∧
      σ'.vars "sampleCount" = sampleSize a c := by
  let d := 2 * c ^ 2
  let q := a / d
  let r := a - q * d
  have hdpos : 0 < d := by
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hdB : d < B := by simpa [d] using hdenomB
  have hqle : q ≤ a := Nat.div_le_self _ _
  have hqB : q < B := hqle.trans_lt haB
  have hqdle : q * d ≤ a := by
    simpa [Nat.mul_comm] using Nat.mul_div_le a d
  have hqdB : q * d < B := hqdle.trans_lt haB
  have hrB : r < B := (Nat.sub_le _ _).trans_lt haB
  let σ₁ := σ.setVar "denom" d
  have r₁ : Run B (.assign "denom" (.mul (.lit 2) (.var "csq"))) σ σ₁ 4 := by
    apply Run.assign
    have htwo : (Expr.lit 2).evalB B σ = some 2 :=
      evalB_lit (by omega)
    have hsqB : c ^ 2 < B := by
      exact (show c ^ 2 ≤ 2 * c ^ 2 by omega).trans_lt hdenomB
    have hsq : (Expr.var "csq").evalB B σ = some (c ^ 2) := by
      simpa [hcsq] using
        (evalB_var (B := B) (x := "csq") (σ := σ)
          (by rw [hcsq]; exact hsqB))
    have hmul := evalB_bin (op := Bop.mul) htwo hsq hdenomB
    simpa [σ₁, d] using hmul
  let σ₂ := σ₁.setVar "sampleCount" q
  have r₂ : Run B
      (.assign "sampleCount" (.div (.var "acount") (.var "denom")))
      σ₁ σ₂ 4 := by
    apply Run.assign
    have haeval : (Expr.var "acount").evalB B σ₁ = some a := by
      simpa [σ₁, hacount] using
        (evalB_var (B := B) (x := "acount") (σ := σ₁)
          (by simpa [σ₁, hacount] using haB))
    have hdeval : (Expr.var "denom").evalB B σ₁ = some d :=
      evalB_var (by simpa [σ₁] using hdB)
    have hdiv := evalB_bin (op := Bop.div) haeval hdeval hqB
    simpa [σ₂, q] using hdiv
  let σ₃ := σ₂.setVar "rem" r
  have r₃ : Run B
      (.assign "rem" (Expr.sub (.var "acount")
        (Expr.mul (.var "sampleCount") (.var "denom")))) σ₂ σ₃ 6 := by
    apply Run.assign
    have hmul : (Expr.mul (.var "sampleCount") (.var "denom")).evalB B σ₂ =
        some (q * d) := by
      have hqeval : (Expr.var "sampleCount").evalB B σ₂ = some q :=
        evalB_var (by simpa [σ₂] using hqB)
      have hdeval : (Expr.var "denom").evalB B σ₂ = some d :=
        evalB_var (by simpa [σ₂, σ₁] using hdB)
      exact evalB_bin (op := Bop.mul) hqeval hdeval hqdB
    have haeval : (Expr.var "acount").evalB B σ₂ = some a := by
      simpa [σ₂, σ₁, hacount] using
        (evalB_var (B := B) (x := "acount") (σ := σ₂)
          (by simpa [σ₂, σ₁, hacount] using haB))
    have hsub := evalB_bin (op := Bop.sub) haeval hmul hrB
    simpa [σ₃, r] using hsub
  by_cases hr : r = 0
  · have rif : Run B
        (.ite (.eq (.var "rem") (.lit 0)) .skip (inc "sampleCount"))
        σ₃ σ₃ 5 := by
      have hb : (Cond.eq (.var "rem") (.lit 0)).evalB B σ₃ = some true := by
        have hreval : (Expr.var "rem").evalB B σ₃ = some r :=
          evalB_var (by simpa [σ₃] using hrB)
        have hzero : (Expr.lit 0).evalB B σ₃ = some 0 := evalB_lit (by omega)
        simpa [hr] using evalB_condEq hreval hzero
      simpa using Run.ite_true hb Run.skip
    refine ⟨σ₃, ?_, by simp [σ₃, σ₂, σ₁, d], ?_⟩
    · simpa [prepareSampleCount, seqs] using
        (r₁.seq (r₂.seq (r₃.seq rif))).mono (by omega)
    · have hs := div_add_remainder_indicator_eq_sampleSize (a := a) hc
      simpa [σ₃, σ₂, σ₁, q, r, d, hr] using hs
  · have hd1 : 1 < d := by
      dsimp [d]
      nlinarith [sq_pos_of_pos (show 0 < c by omega)]
    have hqsucc : q + 1 ≤ a := by
      have hq_lt : q < a := Nat.div_lt_self ha hd1
      omega
    have hqsuccB : q + 1 < B := hqsucc.trans_lt haB
    let σ₄ := σ₃.setVar "sampleCount" (q + 1)
    have rinc : Run B (inc "sampleCount") σ₃ σ₄ 4 := by
      apply Run.assign
      have hqeval : (Expr.var "sampleCount").evalB B σ₃ = some q :=
        evalB_var (by simpa [σ₃, σ₂] using hqB)
      have hone : (Expr.lit 1).evalB B σ₃ = some 1 := evalB_lit (by omega)
      have hadd := evalB_bin (op := Bop.add) hqeval hone hqsuccB
      simpa [inc, σ₄] using hadd
    have rif : Run B
        (.ite (.eq (.var "rem") (.lit 0)) .skip (inc "sampleCount"))
        σ₃ σ₄ 8 := by
      have hb : (Cond.eq (.var "rem") (.lit 0)).evalB B σ₃ = some false := by
        have hreval : (Expr.var "rem").evalB B σ₃ = some r :=
          evalB_var (by simpa [σ₃] using hrB)
        have hzero : (Expr.lit 0).evalB B σ₃ = some 0 := evalB_lit (by omega)
        simpa [hr] using evalB_condEq hreval hzero
      simpa using Run.ite_false hb rinc
    refine ⟨σ₄, ?_, by simp [σ₄, σ₃, σ₂, σ₁, d], ?_⟩
    · simpa [prepareSampleCount, seqs] using r₁.seq (r₂.seq (r₃.seq rif))
    · have hs := div_add_remainder_indicator_eq_sampleSize (a := a) hc
      simpa [σ₄, σ₃, σ₂, σ₁, q, r, d, hr] using hs

end Lax235315Proofs.Construction.SampleCountSource
