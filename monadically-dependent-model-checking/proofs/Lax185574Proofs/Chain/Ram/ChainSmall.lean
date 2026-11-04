import Lax185574Proofs.Chain.Ram.ChainTail
import Lax185574Proofs.Chain.Ram.QRam

/-!
Two small phases of the program: the output `[V, ∅]` for graphs with at
most one vertex (`smallOut`), and the computation of `q` from `r` and
`ε` (`qPart`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain Lax185574.WordEncoding

variable {n : ℕ}

/-- Write `[V, ∅]`. -/
def smallOut : Com :=
  .seq (.write (.lit 2)) (.seq (.write (.var "n"))
    (.seq (emitRow (.lt (.var "w") (.var "n"))) (.write (.lit 0))))

theorem toWord_small (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) (ε : ℚ)
    (hn : n ≤ 1) : toWord (chainAlg G r ε) = 2 :: n :: (elemFrames (below n fun w => w < n) ++ [0]) := by
  unfold chainAlg
  rw [if_pos (by rw [Fintype.card_fin]; exact hn)]
  change 2 :: (toWord (univ : Finset (Fin n)) ++ (toWord (∅ : Finset (Fin n)) ++ [])) = _
  have hs : sortedVals (univ : Finset (Fin n)) = below n fun w => w < n :=
    sortedVals_eq_below _ _ fun u => by simp [u.2]
  have he : sortedVals (∅ : Finset (Fin n)) = [] := by simp [sortedVals]
  rw [toWord_finset_fin, toWord_finset_fin, hs, he]
  simp [elemFrames]

theorem smallOut_run {B : ℕ} (hB : n + 3 < B) {σ : Env} (hn : σ.vars "n" = n) :
    ∃ σ', Run B smallOut σ σ' (n * 20 + 20) ∧
      σ'.out = σ.out ++ (2 :: n :: (elemFrames (below n fun w => w < n) ++ [0])) := by
  classical
  obtain ⟨σ1, hr1, hn1, ho1⟩ :=
    emitRow_run (B := B) (n := n) (c := .lt (.var "w") (.var "n"))
      (fun τ => τ.vars "n" = n) (fun w => w < n) (by omega) (fun τ h => h)
      (fun τ x h => by simp [h]) (fun τ o h => h)
      (fun τ k h hw hk => by
        rw [evalB_condLt (evalB_var (by rw [hw]; omega)) (evalB_var (by rw [h]; omega)), hw, h])
      (σ := { { σ with out := σ.out ++ [2] } with out := σ.out ++ [2] ++ [n] }) (by simpa using hn)
  refine ⟨{ σ1 with out := σ1.out ++ [0] }, (Run.seq (Run.write (v := 2) (by simp; omega))
    (Run.seq (Run.write (v := n) (by simp [hn]; omega)) (Run.seq hr1
      (Run.write (v := 0) (by simp; omega))))).mono (by simp; omega), ?_⟩
  simp [ho1]

/-- `q` from `r` and `ε`: `qc = 2 r den`, `qP = num + qc + 2`. -/
def qPart : Com :=
  .seq (.seq (.assign "qc" (.mul (.mul (.lit 2) (.var "tr")) (.var "qden")))
    (.assign "qP" (.add (.add (.var "qa") (.var "qc")) (.lit 2)))) qCom

theorem qPart_run {B r : ℕ} {ε : ℚ} (hr1 : 1 ≤ r) {σ : Env} (hn : σ.vars "n" = n) (hr : σ.vars "tr" = r)
    (ha : σ.vars "qa" = ε.num.natAbs) (hd : σ.vars "qden" = ε.den)
    (hx : (σ.arrs "qx").length = ε.num.natAbs + 2 * r * ε.den + 2)
    (hy : (σ.arrs "qy").length = ε.num.natAbs + 2 * r * ε.den + 2)
    (hB : (n + 2) * (n + 2) + 2 * (ε.num.natAbs + 2 * r * ε.den + 2) + 10 < B) :
    ∃ σ', Run B qPart σ σ' (qCost n ε.num.natAbs (2 * r * ε.den)
        (ε.num.natAbs + 2 * r * ε.den + 2) + 20) ∧
      σ'.vars "q" = qOf n r ε ∧
      (∀ x, x ∉ ["qc", "qP"] ++ qWritten → σ'.vars x = σ.vars x) ∧
      (∀ arr, arr ∉ ["qx", "qy"] → σ'.arrs arr = σ.arrs arr) ∧ σ'.out = σ.out := by
  set a := ε.num.natAbs
  set c := 2 * r * ε.den
  have hden : 1 ≤ ε.den := ε.den_pos
  have h2r : 2 * r ≤ c := Nat.le_mul_of_pos_right _ hden
  have hdc : ε.den ≤ c := by
    have : 1 * ε.den ≤ (2 * r) * ε.den := Nat.mul_le_mul_right _ (by omega)
    simp only [c]; omega
  have hcB : c < B := by omega
  have hrB : 2 * r < B := by omega
  set σ1 := (σ.setVar "qc" c).setVar "qP" (a + c + 2) with hσ1
  have hr1 : Run B (.seq (.assign "qc" (.mul (.mul (.lit 2) (.var "tr")) (.var "qden")))
      (.assign "qP" (.add (.add (.var "qa") (.var "qc")) (.lit 2)))) σ σ1 16 := by
    refine (Run.seq (Run.assign (v := c) ?_) (Run.assign (v := a + c + 2) ?_)).mono (by simp)
    · simp only [evalB_bin_iff, evalB_lit_iff, evalB_var_iff, hr, hd]
      refine ⟨2 * r, ε.den, ⟨2, r, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩,
        ⟨rfl, by omega⟩, by simp [c], by omega⟩
    · simp only [evalB_bin_iff, evalB_lit_iff, evalB_var_iff, vars_setVar]
      simp [ha]
      omega
  obtain ⟨σ2, hr2, hq2, hv2, ha2, -, ho2⟩ :=
    qCom_run (B := B) (n := n) (a := a) (c := c) (P := a + c + 2) (σ := σ1)
      (by simp [hσ1, hn]) (by simp [hσ1, ha]) (by simp [hσ1]) (by simp [hσ1]) le_rfl
      (by simp [hσ1, hx]) (by simp [hσ1, hy]) (by omega)
  refine ⟨σ2, (Run.seq hr1 hr2).mono (by omega), by rw [hq2]; rfl, fun x hx => ?_,
    fun arr h => by rw [ha2 arr h]; rfl, by rw [ho2]; rfl⟩
  simp at hx
  rw [hv2 x (by simp [hx])]
  simp [hσ1, hx.1, hx.2.1]

end Lax185574Proofs.Chain.Ram
