import Mathlib.Data.Nat.Log
import Lax13Proofs.Reasoning
import Lax13Proofs.Spec

/-!
# Runtime radix width for the active cover

The final C0 program is chosen before the input size `n`, so the number
of radix rounds cannot be embedded as a program literal.  This file
computes the least sufficient width at run time by doubling `rspow`
until it covers the driver variable `n`.  The exit value is exactly
`Nat.clog 2 n`, hence it can be fed to the already verified radix loop
without changing the quantifier order of the headline theorem.
-/

namespace Lax3Proofs.Refine.CoverActiveRadixWidth

open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Program and invariant -/

/-- One doubling step of the runtime width computation. -/
def radixWidthTurn : Com :=
  .seq (.assign "rspow" (.add (.var "rspow") (.var "rspow")))
    (.assign "rsbits" (.add (.var "rsbits") (.lit 1)))

/-- Compute the least `bits` with `n ≤ 2^bits`, from the runtime `n`. -/
def radixWidthCom : Com :=
  .seq (.assign "rsbits" (.lit 0))
    (.seq (.assign "rspow" (.lit 1))
      (.while (.lt (.var "rspow") (.var "n")) radixWidthTurn))

/-- Exact exported budget: two initial assignments, twelve units per
doubling turn (body plus guard), and the final failed guard. -/
def radixWidthCost (n : ℕ) : ℕ := 12 * Nat.clog 2 n + 8

/-- The machine state while finding the least sufficient power of two. -/
def RadixWidthInv (B n : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧
    σ.vars "rspow" = 2 ^ σ.vars "rsbits" ∧
    σ.vars "rsbits" ≤ Nat.clog 2 n ∧
    σ.vars "rspow" < B

theorem clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  exact Nat.clog_le_of_le_pow n.lt_two_pow_self.le

/-! ## One doubling turn -/

theorem radixWidthTurn_double_spec {B n : ℕ} (hB : 1 < B) (hnB : n < B)
    (hdouble : ∀ p < n, p + p < B) :
    Spec B
      (fun σ => RadixWidthInv B n σ ∧ σ.vars "rspow" < n)
      radixWidthTurn
      (fun σ σ' => RadixWidthInv B n σ' ∧
        σ'.vars "rsbits" = σ.vars "rsbits" + 1)
      8 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hn, hp, hble, hpB⟩, hpn⟩ := hσ
  let b := σ.vars "rsbits"
  let p := σ.vars "rspow"
  have hpone : 1 ≤ p := by
    change 1 ≤ σ.vars "rspow"
    rw [hp]
    exact Nat.one_le_pow _ _ (by omega)
  have hn2 : 2 ≤ n := by omega
  have hp2B : p + p < B := hdouble p hpn
  have ep : (Expr.var "rspow").evalB B σ = some p :=
    evalB_var (by simpa [p] using hpB)
  have epp : (Expr.add (.var "rspow") (.var "rspow")).evalB B σ =
      some (p + p) := by
    simpa only [Bop.apply_add] using evalB_bin (op := .add) ep ep hp2B
  let σ₁ := σ.setVar "rspow" (p + p)
  have r₁ : Run B (.assign "rspow" (.add (.var "rspow") (.var "rspow"))) σ σ₁ 4 :=
    Run.assign epp
  have hblt : b < Nat.clog 2 n := by
    rw [Nat.lt_clog_iff_pow_lt (by omega)]
    simpa [b, p, hp] using hpn
  have hb1B : b + 1 < B := by
    have : b + 1 ≤ n := le_trans (Nat.succ_le_iff.mpr hblt) (clog_two_le_self n)
    exact lt_of_le_of_lt this hnB
  have eb : (Expr.var "rsbits").evalB B σ₁ = some b := by
    apply evalB_var
    simp only [σ₁, vars_setVar]
    rw [if_neg (by decide)]
    have : b < B := lt_of_lt_of_le hblt (le_trans (clog_two_le_self n) hnB.le)
    exact this
  have eone : (Expr.lit 1).evalB B σ₁ = some 1 := evalB_lit hB
  have eb1 : (Expr.add (.var "rsbits") (.lit 1)).evalB B σ₁ = some (b + 1) := by
    simpa only [Bop.apply_add] using evalB_bin (op := .add) eb eone hb1B
  let σ₂ := σ₁.setVar "rsbits" (b + 1)
  have r₂ : Run B (.assign "rsbits" (.add (.var "rsbits") (.lit 1))) σ₁ σ₂ 4 :=
    Run.assign eb1
  refine ⟨σ₂, 8, r₁.seq r₂, le_rfl, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [σ₂, σ₁, hn]
      · simp only [σ₂, vars_setVar, reduceIte]
        rw [if_neg (by decide)]
        simp only [σ₁, vars_setVar, reduceIte]
        have hpb : p = 2 ^ b := by simpa [p, b] using hp
        rw [hpb, Nat.pow_succ]
        omega
      · simp [σ₂]
        exact Nat.succ_le_iff.mpr hblt
      · simp [σ₂, σ₁]
        exact hp2B
    · simp [σ₂, σ₁, b]

/-! ## Complete runtime width computation -/

theorem radixWidthCom_double_spec {B n : ℕ} (hB : 1 < B) (hnB : n < B)
    (hdouble : ∀ p < n, p + p < B) :
    Spec B
      (fun σ => σ.vars "n" = n)
      radixWidthCom
      (fun _ σ' => σ'.vars "n" = n ∧
        σ'.vars "rsbits" = Nat.clog 2 n ∧
        σ'.vars "rspow" = 2 ^ Nat.clog 2 n)
      (radixWidthCost n) := by
  let I := RadixWidthInv B n
  let C := Nat.clog 2 n
  have hloop : Spec B I
      (.while (.lt (.var "rspow") (.var "n")) radixWidthTurn)
      (fun _ σ' => I σ' ∧
        (Cond.lt (.var "rspow") (.var "n")).evalB B σ' = some false)
      (12 * C + 4) := by
    refine Spec.while_potential I (fun σ => 12 * (C - σ.vars "rsbits"))
      (fun σ hI => ?_) (fun σ hI hg => ?_) (fun _ h => h) (fun σ hI => ?_)
    · exact ⟨_, evalB_condLt (evalB_var hI.2.2.2)
        (evalB_var (by rw [hI.1]; exact hnB))⟩
    · have htrue : σ.vars "rspow" < n := by
        have h := lt_of_condLt_true hg
        rw [hI.1] at h
        exact h
      obtain ⟨σ', hr, hI', hb'⟩ :=
        (radixWidthTurn_double_spec hB hnB hdouble).run ⟨hI, htrue⟩
      refine ⟨σ', 8, hr, hI', ?_⟩
      show 1 + (Cond.lt (.var "rspow") (.var "n")).size + 8 +
          12 * (C - σ'.vars "rsbits") ≤ 12 * (C - σ.vars "rsbits")
      simp only [Cond.size, Expr.size]
      rw [hb']
      have := hI.2.2.1
      have hlt : σ.vars "rsbits" < C := by
        rw [Nat.lt_clog_iff_pow_lt (by omega)]
        simpa [C, hI.2.1] using htrue
      omega
    · show 12 * (C - σ.vars "rsbits") + 1 +
          (Cond.lt (.var "rspow") (.var "n")).size ≤ 12 * C + 4
      simp only [Cond.size, Expr.size]
      have : C - σ.vars "rsbits" ≤ C := Nat.sub_le _ _
      omega
  intro σ hn
  let σ₀ := σ.setVar "rsbits" 0
  have r₀ : Run B (.assign "rsbits" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  let σ₁ := σ₀.setVar "rspow" 1
  have r₁ : Run B (.assign "rspow" (.lit 1)) σ₀ σ₁ 2 :=
    Run.assign (evalB_lit hB)
  have hI₁ : I σ₁ := by
    refine ⟨by simp [σ₁, σ₀, hn], by simp [σ₁, σ₀], by simp [σ₁, σ₀], ?_⟩
    simpa [σ₁] using hB
  obtain ⟨σ', hr, hI', hfalse⟩ := hloop.run hI₁
  have hnle : n ≤ σ'.vars "rspow" := by
    have h := le_of_condLt_false hfalse
    rw [hI'.1] at h
    exact h
  have hCle : C ≤ σ'.vars "rsbits" := by
    rw [Nat.clog_le_iff_le_pow (by omega)]
    simpa [C, hI'.2.1] using hnle
  have hbits : σ'.vars "rsbits" = C :=
    Nat.le_antisymm hI'.2.2.1 hCle
  refine ⟨σ', ?_, ?_⟩
  · exact (r₀.seq (r₁.seq hr)).mono (by simp [radixWidthCost, C]; omega)
  · refine ⟨hI'.1, ?_, ?_⟩
    · simpa [C] using hbits
    · rw [hI'.2.1, hbits]

/-! ## Carrier-square compatibility -/

/-- The old square word bound implies every doubling performed below `n`
is a word, including the degenerate carriers. -/
theorem doubleWords_of_square {B n : ℕ} (hB : 1 < B) (hnnB : n * n < B) :
    ∀ p < n, p + p < B := by
  intro p hp
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · omega
  · have hn2 : 2 ≤ n := by omega
    have hle : p + p ≤ n * n := by nlinarith
    exact lt_of_le_of_lt hle hnnB

theorem radixWidthTurn_spec {B n : ℕ} (hB : 1 < B) (hnB : n < B)
    (hnnB : n * n < B) :
    Spec B
      (fun σ => RadixWidthInv B n σ ∧ σ.vars "rspow" < n)
      radixWidthTurn
      (fun σ σ' => RadixWidthInv B n σ' ∧
        σ'.vars "rsbits" = σ.vars "rsbits" + 1)
      8 :=
  radixWidthTurn_double_spec hB hnB (doubleWords_of_square hB hnnB)

theorem radixWidthCom_spec {B n : ℕ} (hB : 1 < B) (hnB : n < B)
    (hnnB : n * n < B) :
    Spec B
      (fun σ => σ.vars "n" = n)
      radixWidthCom
      (fun _ σ' => σ'.vars "n" = n ∧
        σ'.vars "rsbits" = Nat.clog 2 n ∧
        σ'.vars "rspow" = 2 ^ Nat.clog 2 n)
      (radixWidthCost n) :=
  radixWidthCom_double_spec hB hnB (doubleWords_of_square hB hnnB)

/-! ## Axiom audit -/

#print axioms radixWidthTurn_double_spec
#print axioms radixWidthCom_double_spec
#print axioms radixWidthTurn_spec
#print axioms radixWidthCom_spec

end Lax3Proofs.Refine.CoverActiveRadixWidth
