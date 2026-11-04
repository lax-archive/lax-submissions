import Lax185574Proofs.EvalRam.Cell

/-!
The rows of the evaluation table.

Round `k` of `dpCmd` fills row `p = fl − 1 − k`: first the end `en[p]`,
then the values of all nodes. After round `k` the rows from `fl − k` on
are right (`RowsOK`), so after the last round all rows are.
-/

namespace Lax185574Proofs.EvalRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-- The end of the subformula at `p`, before capping. -/
def endSel : Com :=
  .ite (.lt (.var "op") (.lit 4)) (.assign "ee" (.add (.var "p") (.lit 3)))
    (.ite (.lt (.var "op") (.lit 6)) (.assign "ee" (.add (.var "p") (.lit 4)))
      (.ite (.eq (.var "op") (.lit 6)) (.assign "ee" (.get "en" (.add (.var "p") (.lit 1))))
        (.ite (.eq (.var "op") (.lit 7)) (.assign "ee" (.get "en" (.get "en" (.add (.var "p") (.lit 1)))))
          (.ite (.eq (.var "op") (.lit 8)) (.assign "ee" (.get "en" (.add (.var "p") (.lit 3))))
            (.assign "ee" (.add (.var "p") (.lit 1)))))))

/-- Store the end of the subformula at `p`, capped at `fl`. -/
def endCmd : Com :=
  .seq (.assign "op" (.get "f" (.var "p")))
    (.seq endSel (.ite (.lt (.var "fl") (.var "ee")) (.store "en" (.var "p") (.var "fl"))
      (.store "en" (.var "p") (.var "ee"))))

theorem endVal_le (F EN : List ℕ) (L p : ℕ) : endVal F EN L p ≤ L := by
  unfold endVal; exact min_le_left _ _

theorem endCmd_spec (B : ℕ) (F EN : List ℕ) (L p : ℕ) (hp : p < L) (hEN : ∀ v ∈ EN, v ≤ L)
    (hENl : L + 4 ≤ EN.length) (hF : ∀ v ∈ F, v < B) (hFL : L + 4 ≤ F.length) (hLB : L + 4 < B)
    (h9 : 9 < B) :
    Spec B (fun ρ => ρ.arrs "f" = F ∧ ρ.arrs "en" = EN ∧ ρ.vars "p" = p ∧ ρ.vars "fl" = L) endCmd
      (fun _ ρ' => ρ'.arrs "en" = EN.set p (endVal F EN L p)) 60 := by
  rintro ρ ⟨hf, hen, hp', hfl⟩
  subst hf hen hp' hfl
  have hop : (ρ.arrs "f").getD (ρ.vars "p") 0 < B := xg_lt hF (by omega)
  have hpf : ρ.vars "p" < (ρ.arrs "f").length := by omega
  have he1 : (ρ.arrs "en").getD (ρ.vars "p" + 1) 0 ≤ ρ.vars "fl" := mem_le_of_xg hEN _
  have he3 : (ρ.arrs "en").getD (ρ.vars "p" + 3) 0 ≤ ρ.vars "fl" := mem_le_of_xg hEN _
  have he11 : (ρ.arrs "en").getD ((ρ.arrs "en").getD (ρ.vars "p" + 1) 0) 0 ≤ ρ.vars "fl" :=
    mem_le_of_xg hEN _
  unfold endCmd endSel
  run_vcg
  all_goals (try (simp; omega))
  all_goals (simp only [arrs_setVar, arrs_setArr, if_true, vars_setVar]; congr 1)
  all_goals (simp_all [endVal, xg] <;> (try split_ifs) <;> omega)

/-- `RowsOK` depends only on the entries of the rows from `p0` on. -/
theorem RowsOK.congr {X F PA DA EN VL EN' VL' : List ℕ} {q N L p0 : ℕ}
    (h : RowsOK X F PA DA EN VL q N L p0) (hE : ∀ i, p0 ≤ i → xg EN' i = xg EN i)
    (hV : ∀ i, p0 * N ≤ i → xg VL' i = xg VL i) : RowsOK X F PA DA EN' VL' q N L p0 := by
  intro p hp hpL ℓ ψ r hF hl
  obtain ⟨h1, h2⟩ := h p hp hpL ℓ ψ r hF hl
  refine ⟨by rw [hE p hp, h1], fun c hc => ?_⟩
  rw [hV _ (le_trans (Nat.mul_le_mul_right N hp) (Nat.le_add_right _ _)), h2 c hc]

theorem xg_set_ne {l : List ℕ} {i j v : ℕ} (h : j ≠ i) : xg (l.set i v) j = xg l j := by
  simp [xg, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem xg_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) : xg (l.set i v) i = v := by
  simp [xg, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem mem_set_le {l : List ℕ} {i v b : ℕ} (h : ∀ u ∈ l, u ≤ b) (hv : v ≤ b) :
    ∀ u ∈ l.set i v, u ≤ b := by
  intro u hu
  rcases List.mem_or_eq_of_mem_set hu with h' | h'
  · exact h u h'
  · rw [h']; exact hv

/-- One round: the row `p = fl − 1 − k`. -/
def rowBody : Com :=
  .seq (.assign "p" (.sub (.sub (.var "fl") (.lit 1)) (.var "k")))
    (.seq endCmd (forUp "c" (.var "nn") cellCmd))

/-- All rows, from the last to the first. -/
def dpCmd : Com := forUp "k" (.var "fl") rowBody

/-- The rows are right from `p` on if they are right after `p` and at `p`,
and the rows after `p` did not change. -/
theorem rowsOK_step {X F PA DA EN VL EN' VL' : List ℕ} {q N L p : ℕ}
    (h : RowsOK X F PA DA EN VL q N L (p + 1)) (hE : ∀ i, i ≠ p → xg EN' i = xg EN i)
    (hV : ∀ i, (p + 1) * N ≤ i → xg VL' i = xg VL i)
    (hp : ∀ (ℓ : ℕ) (ψ : DistFO ℓ) (r : List ℕ), F.drop p = code ψ ++ r → p + (code ψ).length ≤ L →
      xg EN' p = p + (code ψ).length ∧
        ∀ c < N, xg VL' (p * N + c) = bv (evalW X ψ (xg PA c) (q - xg DA c))) :
    RowsOK X F PA DA EN' VL' q N L p := by
  have h' := h.congr (EN' := EN') (VL' := VL') (fun i hi => hE i (by omega)) hV
  intro p' hp' hpL ℓ ψ r hF hl
  rcases Nat.eq_or_lt_of_le hp' with rfl | hlt
  · exact hp ℓ ψ r hF hl
  · exact h' p' hlt hpL ℓ ψ r hF hl

/-- The state between two rounds. -/
def DPAt (B : ℕ) (X F PA DA FA : List ℕ) (q N L k : ℕ) (ρ : Env) : Prop :=
  ρ.arrs "x" = X ∧ ρ.arrs "f" = F ∧ ρ.arrs "pos" = PA ∧ ρ.arrs "dep" = DA ∧ ρ.arrs "fc" = FA ∧
    ρ.vars "hq" = q ∧ ρ.vars "nn" = N ∧ ρ.vars "fl" = L ∧
    ∃ EN VL, ρ.arrs "en" = EN ∧ ρ.arrs "val" = VL ∧ Ctx B X F PA DA FA EN VL q N L ∧
      RowsOK X F PA DA EN VL q N L (L - k)

/-- The state inside a round, after `c` cells of row `p`. -/
def CellsAt (B : ℕ) (X F PA DA FA EN VL0 : List ℕ) (q N L p c : ℕ) (ρ : Env) : Prop :=
  ρ.arrs "x" = X ∧ ρ.arrs "f" = F ∧ ρ.arrs "pos" = PA ∧ ρ.arrs "dep" = DA ∧ ρ.arrs "fc" = FA ∧
    ρ.arrs "en" = EN ∧ ρ.vars "hq" = q ∧ ρ.vars "nn" = N ∧ ρ.vars "fl" = L ∧ ρ.vars "p" = p ∧
    ∃ VL, ρ.arrs "val" = VL ∧ Ctx B X F PA DA FA EN VL q N L ∧
      (∀ i, (i < p * N ∨ (p + 1) * N ≤ i) → xg VL i = xg VL0 i) ∧
      ∀ (ℓ : ℕ) (ψ : DistFO ℓ) (r : List ℕ), F.drop p = code ψ ++ r → p + (code ψ).length ≤ L →
        ∀ c' < c, xg VL (p * N + c') = bv (evalW X ψ (xg PA c') (q - xg DA c'))

theorem Ctx.setEN {B : ℕ} {X F PA DA FA EN VL : List ℕ} {q N L : ℕ} (h : Ctx B X F PA DA FA EN VL q N L)
    (i v : ℕ) (hv : v ≤ L) : Ctx B X F PA DA FA (EN.set i v) VL q N L :=
  ⟨h.hX, h.hF, h.hV, mem_set_le h.hEN hv, h.hXB, h.hFL, h.hFB, (by rw [List.length_set]; exact h.hENl),
    h.hVL, h.hVB, h.hPA, h.hDA, h.hFA, h.hqB, h.hLB, h.h9⟩

theorem Ctx.setVL {B : ℕ} {X F PA DA FA EN VL : List ℕ} {q N L : ℕ} (h : Ctx B X F PA DA FA EN VL q N L)
    (i v : ℕ) (hv : v ≤ 1) : Ctx B X F PA DA FA EN (VL.set i v) q N L :=
  ⟨h.hX, h.hF, mem_set_le h.hV hv, h.hEN, h.hXB, h.hFL, h.hFB, h.hENl,
    (by rw [List.length_set]; exact h.hVL), (by rw [List.length_set]; exact h.hVB), h.hPA, h.hDA, h.hFA,
    h.hqB, h.hLB, h.h9⟩

/-- The cells of one row. -/
theorem cells_spec (B : ℕ) (X F PA DA FA EN VL0 : List ℕ) (q N L p : ℕ) (hp : p < L)
    (hnodes : ∀ c < N, NodeOK X PA DA FA q N c) (hNB : N < B)
    (hrows : RowsOK X F PA DA EN VL0 q N L (p + 1)) :
    Spec B (fun ρ => CellsAt B X F PA DA FA EN VL0 q N L p 0 (ρ.setVar "c" 0))
      (forUp "c" (.var "nn") cellCmd)
      (fun _ ρ' => CellsAt B X F PA DA FA EN VL0 q N L p N ρ')
      (N * (100 * X.length + 208) + 6) := by
  intro σ hσ
  obtain ⟨ρ', hr, hI, -⟩ := forUp_run (B := B) (i := "c") (e := .var "nn") (body := cellCmd) (N := N)
    (K := 100 * X.length + 200) (fun c ρ => CellsAt B X F PA DA FA EN VL0 q N L p c ρ) (σ := σ) hNB
    (fun c _ ρ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.2.2.2.2.2.2.2.1.symm, by rw [hI.2.2.2.2.2.2.2.1]; exact hNB⟩) hσ
    (fun c hc ρ hI hcv => by
      obtain ⟨hx, hf, hpa, hda, hfa, hen, hq, hN, hfl, hp', VL, hvl, hC, hout, hdone⟩ := hI
      obtain ⟨ρ1, hr1, hval1⟩ := cellCmd_spec B X F PA DA FA EN VL q N L p c hC hp hc (hnodes c hc) ρ
        ⟨hx, hf, hpa, hda, hfa, hen, hvl, hq, hN, hp', hcv⟩
      have hfv : ∀ z, z ∉ cellCmd.wvars → ρ1.vars z = ρ.vars z := fun z h => hr1.frame_var z h
      have hfa' : ∀ a, a ∉ cellCmd.warrs → ρ1.arrs a = ρ.arrs a := fun a h => hr1.frame_arr a h
      have hidx : p * N + c < VL.length := by
        have := hC.hVL
        have : p * N + c < (L + 4) * N := by nlinarith
        omega
      refine ⟨ρ1, hr1, by rw [hfv "c" (by decide), hcv], ?_⟩
      refine ⟨by simp [hfa' "x" (by decide), hx], by simp [hfa' "f" (by decide), hf],
        by simp [hfa' "pos" (by decide), hpa], by simp [hfa' "dep" (by decide), hda],
        by simp [hfa' "fc" (by decide), hfa], by simp [hfa' "en" (by decide), hen],
        by simp [hfv "hq" (by decide), hq], by simp [hfv "nn" (by decide), hN],
        by simp [hfv "fl" (by decide), hfl], by simp [hfv "p" (by decide), hp'],
        VL.set (p * N + c) (cellVal X F PA DA FA EN VL q N p c), by simp [hval1],
        hC.setVL _ _ (cellVal_le _ _ _ _ _ _ _ _ _ _ _), fun i hi => ?_, ?_⟩
      · rw [xg_set_ne (by rcases hi with hi | hi <;> nlinarith)]; exact hout i hi
      · intro ℓ ψ r hF hl c' hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
        · rw [xg_set_ne (by omega)]; exact hdone ℓ ψ r hF hl c' hlt
        · rw [xg_set_self hidx]
          refine cellVal_eq (L := L) ?_ (hnodes _ hc) hc ψ hF hl
          exact hrows.congr (fun i _ => rfl) (fun i hi => hout i (Or.inr hi)))
  exact ⟨ρ', hr.mono (by simp), hI⟩

theorem DPAt.setVar {B : ℕ} {X F PA DA FA : List ℕ} {q N L k : ℕ} {ρ : Env}
    (h : DPAt B X F PA DA FA q N L k ρ) {x : String} (h1 : x ≠ "hq") (h2 : x ≠ "nn") (h3 : x ≠ "fl")
    (v : ℕ) : DPAt B X F PA DA FA q N L k (ρ.setVar x v) := by
  obtain ⟨hx, hf, hpa, hda, hfa, hq, hN, hfl, EN, VL, hen, hvl, hC, hR⟩ := h
  exact ⟨by simpa using hx, by simpa using hf, by simpa using hpa, by simpa using hda,
    by simpa using hfa, by simp [h1.symm, hq], by simp [h2.symm, hN], by simp [h3.symm, hfl],
    EN, VL, by simpa using hen, by simpa using hvl, hC, hR⟩

/-- **One round.** -/
theorem rowBody_spec (B : ℕ) (X F PA DA FA : List ℕ) (q N L k : ℕ) (hk : k < L)
    (hnodes : ∀ c < N, NodeOK X PA DA FA q N c) (hNB : N < B) :
    Spec B (fun ρ => DPAt B X F PA DA FA q N L k ρ ∧ ρ.vars "k" = k) rowBody
      (fun _ ρ' => DPAt B X F PA DA FA q N L (k + 1) ρ' ∧ ρ'.vars "k" = k)
      (N * (100 * X.length + 208) + 80) := by
  rintro ρ ⟨⟨hx, hf, hpa, hda, hfa, hq, hN, hfl, EN, VL, hen, hvl, hC, hR⟩, hkv⟩
  set p := L - 1 - k with hpdef
  have hpL : p < L := by omega
  have hLk : L - k = p + 1 := by omega
  rw [hLk] at hR
  have hLB := hC.hLB
  set ρ1 := ρ.setVar "p" p with hρ1
  have r1 : Run B (.assign "p" (.sub (.sub (.var "fl") (.lit 1)) (.var "k"))) ρ ρ1 6 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨L - 1, k, ⟨L, 1, ⟨hfl.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩,
      ⟨hkv.symm, by omega⟩, rfl, by omega⟩
  obtain ⟨ρ2, r2, hen2⟩ := endCmd_spec B F EN L p hpL hC.hEN hC.hENl hC.hF hC.hFL hLB hC.h9 ρ1
    ⟨by simp [hρ1, hf], by simp [hρ1, hen], by simp [hρ1], by simp [hρ1, hfl]⟩
  have hv2 : ∀ z, z ∉ endCmd.wvars → ρ2.vars z = ρ1.vars z := fun z h => r2.frame_var z h
  have ha2 : ∀ a, a ∉ endCmd.warrs → ρ2.arrs a = ρ1.arrs a := fun a h => r2.frame_arr a h
  set EN' := EN.set p (endVal F EN L p) with hEN'
  have hpEN : p < EN.length := by have := hC.hENl; omega
  have hEo : ∀ i, i ≠ p → xg EN' i = xg EN i := fun i hi => xg_set_ne hi
  have hR' : RowsOK X F PA DA EN' VL q N L (p + 1) :=
    hR.congr (fun i hi => hEo i (by omega)) (fun i _ => rfl)
  obtain ⟨ρ3, r3, hI3⟩ := cells_spec B X F PA DA FA EN' VL q N L p hpL hnodes hNB hR' ρ2
    ⟨by simp [ha2 "x" (by decide), hρ1, hx], by simp [ha2 "f" (by decide), hρ1, hf],
      by simp [ha2 "pos" (by decide), hρ1, hpa], by simp [ha2 "dep" (by decide), hρ1, hda],
      by simp [ha2 "fc" (by decide), hρ1, hfa], by simp [hen2],
      by simp [hv2 "hq" (by decide), hρ1, hq], by simp [hv2 "nn" (by decide), hρ1, hN],
      by simp [hv2 "fl" (by decide), hρ1, hfl], by simp [hv2 "p" (by decide), hρ1],
      VL, by simp [ha2 "val" (by decide), hρ1, hvl], hC.setEN _ _ (endVal_le _ _ _ _),
      fun i _ => rfl, fun _ _ _ _ _ _ hc => absurd hc (Nat.not_lt_zero _)⟩
  obtain ⟨hx3, hf3, hpa3, hda3, hfa3, hen3, hq3, hN3, hfl3, -, VLf, hvl3, hC3, hout3, hdone3⟩ := hI3
  have hk3 : ρ3.vars "k" = k := by
    rw [r3.frame_var "k" (by decide), hv2 "k" (by decide)]; simp [hρ1, hkv]
  refine ⟨ρ3, ?_, ⟨hx3, hf3, hpa3, hda3, hfa3, hq3, hN3, hfl3, EN', VLf, hen3, hvl3, hC3, ?_⟩, hk3⟩
  · unfold rowBody
    exact (Run.seq r1 (Run.seq r2 r3)).mono (by omega)
  · rw [show L - (k + 1) = p by omega]
    refine rowsOK_step hR hEo (fun i hi => hout3 i (Or.inr hi)) fun ℓ ψ r hF hl => ⟨?_, ?_⟩
    · rw [hEN', xg_set_self hpEN]; exact endVal_eq hR ψ hF hl
    · exact hdone3 ℓ ψ r hF hl

/-- **All rows.** -/
theorem dpCmd_spec (B : ℕ) (X F PA DA FA : List ℕ) (q N L : ℕ) (hLB : L < B)
    (hnodes : ∀ c < N, NodeOK X PA DA FA q N c) (hNB : N < B) :
    Spec B (fun ρ => DPAt B X F PA DA FA q N L 0 (ρ.setVar "k" 0)) dpCmd
      (fun _ ρ' => DPAt B X F PA DA FA q N L L ρ')
      (L * (N * (100 * X.length + 208) + 88) + 6) := by
  intro σ hσ
  obtain ⟨ρ', hr, hI, -⟩ := forUp_run (B := B) (i := "k") (e := .var "fl") (body := rowBody) (N := L)
    (K := N * (100 * X.length + 208) + 80) (fun k ρ => DPAt B X F PA DA FA q N L k ρ) (σ := σ) hLB
    (fun k _ ρ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.2.2.2.2.2.2.2.1.symm, by rw [hI.2.2.2.2.2.2.2.1]; exact hLB⟩)
    hσ
    (fun k hk ρ hI hkv => by
      obtain ⟨ρ1, hr1, hI1, hk1⟩ := rowBody_spec B X F PA DA FA q N L k hk hnodes hNB ρ ⟨hI, hkv⟩
      exact ⟨ρ1, hr1, hk1, hI1.setVar (by decide) (by decide) (by decide) _⟩)
  exact ⟨ρ', hr.mono (by simp), hI⟩

end Lax185574Proofs.EvalRam
