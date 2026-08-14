import Lax3Proofs.Refine.OrderVirtualEnsure

/-!
# Stamping one virtual elimination

This is the constant-cost prefix of a successful extraction.  It marks the
chosen vertex, writes its descending rank and extraction degree, advances the
count, and raises the recorded maximum.  Keeping this prefix separate makes
the provider/row-scan proof branch-free.
-/

namespace Lax3Proofs.Refine.OrderVirtualStamp

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Refine.OrderVirtualProvider

def raiseVirtualKmax : Com :=
  .ite (.lt (.var "kmax") (.var "mind"))
    (.assign "kmax" (.var "mind")) .skip

def stampVirtualVertex : Com :=
  .seq (.store "elm" (.var "w") (.lit 1))
    (.seq (.store "rnk" (.var "w")
        (.sub (.sub (.var "n") (.lit 1)) (.var "cnt")))
      (.seq (.store "idg" (.var "w") (.var "mind"))
        (.seq (.assign "cnt" (.add (.var "cnt") (.lit 1)))
          raiseVirtualKmax)))

/-- Everything the row provider needs after the stamp, plus the scalar facts
used to read the resulting abstract elimination state. -/
structure StampPost (n : ℕ) (P : Env → Prop)
    (E D R ID BH BV BN : ℕ → ℕ)
    (w cv mv kv : ℕ) (σ σ' : Env) : Prop where
  persistent : P σ'
  arrays : EngineArrays n (Lax3Proofs.Refine.OrderVirtualBucket.bucketExtra n)
    (upd E w 1) D (upd R w (n - 1 - cv)) (upd ID w mv) BH BV BN σ'
  w_eq : σ'.vars "w" = w
  cnt_eq : σ'.vars "cnt" = cv + 1
  mind_eq : σ'.vars "mind" = mv
  kmax_eq : σ'.vars "kmax" = max kv mv
  sp_eq : σ'.vars "sp" = σ.vars "sp"
  ls_eq : σ'.vars "ls" = σ.vars "ls"
  i_eq : σ'.vars "i" = σ.vars "i"

theorem stampVirtualVertex_spec {B n : ℕ} {P : Env → Prop}
    (hclosed : EngineClosed P) (hB : 3 * n + 3 < B)
    {E D R ID BH BV BN : ℕ → ℕ} {w cv mv kv : ℕ}
    (hw : w < n) (hcv : cv < n) (hmv : mv ≤ n) (hkv : kv ≤ n) :
    Spec B
      (fun σ => P σ ∧
        EngineArrays n (Lax3Proofs.Refine.OrderVirtualBucket.bucketExtra n)
          E D R ID BH BV BN σ ∧
        σ.vars "w" = w ∧ σ.vars "cnt" = cv ∧
        σ.vars "mind" = mv ∧ σ.vars "kmax" = kv)
      stampVirtualVertex
      (StampPost n P E D R ID BH BV BN w cv mv kv)
      23 := by
  intro σ hpre
  obtain ⟨hP, heng, hwv, hcnt, hmind, hkmax⟩ := hpre
  have hwB : σ.vars "w" < B := by omega
  have hwLen : σ.vars "w" < (σ.arrs "elm").length := by
    rw [heng.elm_eq, length_arrOf, hwv]
    exact hw
  have hrLen : σ.vars "w" < (σ.arrs "rnk").length := by
    rw [heng.rank_eq, length_arrOf, hwv]
    exact hw
  have hiLen : σ.vars "w" < (σ.arrs "idg").length := by
    rw [heng.idg_eq, length_arrOf, hwv]
    exact hw
  have hnB : σ.vars "n" < B := by rw [heng.n_eq]; omega
  have hcntB : σ.vars "cnt" < B := by omega
  have hmindB : σ.vars "mind" < B := by omega
  have hkmaxB : σ.vars "kmax" < B := by omega
  have hrankB : n - 1 - cv < B := by omega
  run_vcg
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq] at *
  · rename_i hcase
    refine ⟨?_, ?_, by simp [hwv], by simp [hcnt], by simp [hmind],
      ?_, by simp, by simp, by simp⟩
    · apply hclosed.setVar (a := "kmax") (by simp [engineVarNames])
      apply hclosed.setVar (a := "cnt") (by simp [engineVarNames])
      apply hclosed.setArr (a := "idg") (by simp [engineArrNames])
      apply hclosed.setArr (a := "rnk") (by simp [engineArrNames])
      apply hclosed.setArr (a := "elm") (by simp [engineArrNames])
      exact hP
    · refine ⟨by simp [heng.n_eq], ?_, by simp [heng.deg_eq], ?_, ?_,
        by simp [heng.head_eq], by simp [heng.val_eq], by simp [heng.next_eq]⟩
      · simp [heng.elm_eq, hwv, set_arrOf_eq_upd]
      · simp [heng.rank_eq, hwv, heng.n_eq, hcnt, set_arrOf_eq_upd]
      · simp [heng.idg_eq, hwv, hmind, set_arrOf_eq_upd]
    · have hlt : kv < mv := by
        simpa [hkmax, hmind] using hcase
      simpa [hmind, Nat.max_eq_right (Nat.le_of_lt hlt)]
  · rename_i hcase
    refine ⟨?_, ?_, by simp [hwv], by simp [hcnt], by simp [hmind],
      ?_, by simp, by simp, by simp⟩
    · apply hclosed.setVar (a := "cnt") (by simp [engineVarNames])
      apply hclosed.setArr (a := "idg") (by simp [engineArrNames])
      apply hclosed.setArr (a := "rnk") (by simp [engineArrNames])
      apply hclosed.setArr (a := "elm") (by simp [engineArrNames])
      exact hP
    · refine ⟨by simp [heng.n_eq], ?_, by simp [heng.deg_eq], ?_, ?_,
        by simp [heng.head_eq], by simp [heng.val_eq], by simp [heng.next_eq]⟩
      · simp [heng.elm_eq, hwv, set_arrOf_eq_upd]
      · simp [heng.rank_eq, hwv, heng.n_eq, hcnt, set_arrOf_eq_upd]
      · simp [heng.idg_eq, hwv, hmind, set_arrOf_eq_upd]
    · have hle : mv ≤ kv := by
        rw [hkmax, hmind] at hcase
        omega
      simpa [hkmax, Nat.max_eq_left hle]
  all_goals omega

/-! ## Axiom audit -/

#print axioms stampVirtualVertex_spec

end Lax3Proofs.Refine.OrderVirtualStamp
