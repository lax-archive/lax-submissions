import Lax185574Proofs.StpRam.EmitLoops
import Lax185574Proofs.StpRam.RadiusCmd
import Lax185574Proofs.Words.SelectLen

/-!
The computation of the final round of lem:compute-stp, once the graph
and the shifted trees are in the arrays.

`finalCompute` fills the radius table, sorts the distinct tree words,
counts the triples, and writes `0`, the number of triples and the
triples. So it writes `0` followed by the word of `emitList`, which is
the word of the scatter type by `toWord_stp`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574Proofs.Words Lax185574.WordEncoding

def finalCompute : Com :=
  .seq rtCmd (.seq (.assign "cap" (.add (.var "kk") (.var "qq")))
    (.seq (.assign "R1" (.get "rt" (.lit 1))) (.seq collect (.seq countLoops
      (.seq (.write (.lit 0)) (.seq (.write (.var "tot")) emitLoops))))))

/-- The cost bound of `finalCompute`. -/
def finalCost (n k q L N R1 : ℕ) : ℕ :=
  (q + 1) * (13 * radExp k q 0 + 50) + 8 + 10 +
    ((((2 * (36 * L + 56) + 68) * N + 8) + 15) * (N + 1) + 4) +
    (R1 * (N * 28 + 20) + 10) + 4 +
    (R1 * (N * (innerCost n L (k + q) + 8) + 18) + 6)

set_option maxHeartbeats 1000000 in
/-- **The final computation.** -/
theorem finalCompute_run {B n nsE nsN k q L : ℕ} {oE tE oN tN g : ℕ → ℕ} {A : List (List ℕ)}
    {adj : Fin n → List (Fin n)} (hD : ∀ (s v : Fin n) (r : ℕ), DT g n s v r ↔ v ∈ Lax185574Proofs.TreeAlgo.ballFrom adj s r)
    (hF : AFacts A n k q L) (hb : WordsBound B A) (hq : 1 ≤ q)
    (hnB : n + 2 < B) (hnnB : n * n < B) (hgB : ∀ j < n * n, g j < B) (hRB : radius k q 0 + 1 < B)
    (h9B : 9 < B) (hTB : radius k q 1 * A.length + 1 < B) (htB : total A + 3 < B)
    {σ : Env} (hG : GraphAt n nsE nsN oE tE oN tN σ) (hw : WordsAt A σ) (hk : σ.vars "kk" = k)
    (hqq : σ.vars "qq" = q) (hm : σ.vars "m" = A.length) (hrt : (σ.arrs "rt").length = q + 1)
    (hord : A.length ≤ (σ.arrs "ord").length) (hdd : σ.arrs "dd" = arrOf (n * n) g)
    (hdn : (σ.arrs "dn").length = n) (hbl : (σ.arrs "bl").length = n) :
    ∃ σ', Run B finalCompute σ σ' (finalCost n k q L A.length (radius k q 1)) ∧
      σ'.out = σ.out ++ 0 :: toWord (emitList adj A k q) := by
  have hR10 := radius_le_zero k q 1 hq
  have hkq := kq_le_radius k q
  set R1 := radius k q 1 with hR1
  -- the radius table
  obtain ⟨σ1, r1, hrt1, hl1, hv1, ha1⟩ := rtCmd_run (B := B) hk hqq (by omega) hRB h9B
  have hrtA : σ1.arrs "rt" = arrOf (q + 1) (radius k q) := by
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i ≤ q
    · rw [hrt1 i hi, getElem?_arrOf _ (by omega)]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  have hv1' : ∀ x ∈ ["kk", "qq", "m", "n"], σ1.vars x = σ.vars x := by
    intro x hx; exact hv1 x (by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
  -- the cap and the first radius bound
  set σ2 := (σ1.setVar "cap" (k + q)).setVar "R1" R1 with hσ2
  have r2a : Run B (.assign "cap" (.add (.var "kk") (.var "qq"))) σ1 (σ1.setVar "cap" (k + q)) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff]
    exact ⟨k, q, ⟨by rw [hv1' "kk" (by simp), hk], by rw [hv1' "kk" (by simp), hk]; omega⟩,
      ⟨by rw [hv1' "qq" (by simp), hqq], by rw [hv1' "qq" (by simp), hqq]; omega⟩,
      by simp [Bop.apply], by omega⟩
  have r2b : Run B (.assign "R1" (.get "rt" (.lit 1))) (σ1.setVar "cap" (k + q)) σ2 3 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_lit_iff]
    exact ⟨1, ⟨rfl, by omega⟩, by rw [arrs_setVar, hrtA, getElem?_arrOf _ (show 1 < q + 1 by omega)],
      by omega⟩
  have hG2 : GraphAt n nsE nsN oE tE oN tN σ2 := by
    refine ((GraphAt.of_arrs hG (hv1' "n" (by simp)) (ha1 _ (by decide)) (ha1 _ (by decide))
      (ha1 _ (by decide)) (ha1 _ (by decide))).setVar (by decide) _).setVar (by decide) _
  have hw2 : WordsAt A σ2 := hw.of_arrs (by simp [hσ2, ha1 "a" (by decide)])
    (by simp [hσ2, ha1 "st" (by decide)]) (by simp [hσ2, ha1 "ln" (by decide)])
  -- sorting
  obtain ⟨σ3, r3, hcnt3, hw3, hol3, hord3⟩ := Fast.collect_run hb hw2
    (by simp [hσ2, hv1' "m" (by simp), hm]) (by simp [hσ2, ha1 "ord" (by decide), hord])
  have hf3 : ∀ x, x ∉ collect.wvars → σ3.vars x = σ2.vars x := fun x hx => r3.frame_var x hx
  have ha3 : ∀ x, x ∉ collect.warrs → σ3.arrs x = σ2.arrs x := fun x hx => r3.frame_arr x hx
  have hl3 := run_length_arrs r3
  have hC3 : ECtx A n nsE nsN oE tE oN tN g k q R1 σ3 := by
    refine ⟨GraphAt.of_arrs hG2 (hf3 "n" (by decide)) (ha3 _ (by decide)) (ha3 _ (by decide))
      (ha3 _ (by decide)) (ha3 _ (by decide)), hw3,
      by rw [hf3 "kk" (by decide)]; simp [hσ2, hv1' "kk" (by simp), hk],
      by rw [hf3 "cap" (by decide)]; simp [hσ2],
      by rw [hf3 "R1" (by decide)]; simp [hσ2], hcnt3, hord3,
      by rw [ha3 "rt" (by decide)]; simp [hσ2, hrtA],
      by rw [ha3 "dd" (by decide)]; simp [hσ2, ha1 "dd" (by decide), hdd],
      by rw [hl3]; simp [hσ2, ha1 "dn" (by decide), hdn],
      by rw [hl3]; simp [hσ2, ha1 "bl" (by decide), hbl],
      le_trans (length_sortedDistinct_le A) hol3⟩
  -- counting and writing
  obtain ⟨σ4, r4, hC4, htot4⟩ := countLoops_run (adj := adj) hF hb hR1 (by omega) hTB hC3
  set σ5 : Env := { σ4 with out := σ4.out ++ [0] } with hσ5
  have r5 : Run B (.write (.lit 0)) σ4 σ5 2 := (Run.write (by simp; omega)).mono (by simp)
  have hlenE : (emitPre adj A k q R1).length ≤ R1 * A.length := by
    have := length_emitPre_le adj A k q R1
    exact le_trans this (Nat.mul_le_mul_left _ (length_sortedDistinct_le A))
  set σ6 : Env := { σ5 with out := σ5.out ++ [(emitPre adj A k q R1).length] } with hσ6
  have r6 : Run B (.write (.var "tot")) σ5 σ6 2 :=
    (Run.write (by simp only [evalB_var_iff]; exact ⟨by simp [hσ5, htot4], by
      simp [hσ5, htot4]; omega⟩)).mono (by simp)
  have hC6 : ECtx A n nsE nsN oE tE oN tN g k q R1 σ6 :=
    hC4.of_eq (fun x _ => by simp [hσ6, hσ5]) (fun x _ => by simp [hσ6, hσ5])
      (fun x _ => by simp [hσ6, hσ5])
  obtain ⟨σ7, r7, -, hout7⟩ := emitLoops_run hD hF hb hR1 hnB hnnB hgB (by omega) (by omega) htB hC6
  refine ⟨σ7, (Run.seq r1 (Run.seq r2a (Run.seq r2b (Run.seq r3 (Run.seq r4 (Run.seq r5
    (Run.seq r6 r7))))))).mono ?_, ?_⟩
  · have hml := Fast.maxLen_le hF.maxl
    have hKs : (Fast.Ks A + 15) * (A.length + 1) + 4 ≤
        (((2 * (36 * L + 56) + 68) * A.length + 8) + 15) * (A.length + 1) + 4 := by
      unfold Fast.Ks Fast.Kc
      have : (2 * (36 * Fast.maxLen A + 56) + 68) * A.length ≤ (2 * (36 * L + 56) + 68) * A.length :=
        Nat.mul_le_mul_right _ (by omega)
      have := Nat.mul_le_mul_right (A.length + 1) (show (2 * (36 * Fast.maxLen A + 56) + 68) * A.length
        + 8 + 15 ≤ (2 * (36 * L + 56) + 68) * A.length + 8 + 15 by omega)
      omega
    simp only [finalCost]; omega
  · rw [hout7, ← emitPre_full, toWord_words]
    simp only [hσ6, hσ5]
    rw [r4.out_eq (by decide), r3.out_eq (by decide)]
    simp [hσ2, r1.out_eq (by decide)]
    exact ⟨rfl, rfl⟩

end Lax185574Proofs.StpRam
