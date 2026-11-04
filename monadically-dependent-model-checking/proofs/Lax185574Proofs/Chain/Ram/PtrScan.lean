import Lax185574Proofs.Chain.Ram.Loops

/-!
The pointer scans of rules (R2) and (R3).

The rule asks for the first vertex `w` that is far from every chosen
vertex, the chosen vertices being `Sl[0], …, Sl[sc - 1]`. Being far only
becomes more likely as the procedure goes on, so every vertex keeps a
pointer `pa[w]` such that `w` is known to be far from `Sl[j]` for all
`j < pa[w]` (`PtrOK`). The test of `w` (`ptrTst`) advances the pointer
while the next chosen vertex is far, using a pair test `pt` that leaves
its verdict in `ok2`. Then `w` passes if and only if its pointer reaches
`sc`. Every advance is paid by the potential `Σ_w (n - pa[w])`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram

/-- The test of the vertex `w` by the pointer array `pa`. -/
def ptrTst (pa : String) (pt : Com) : Com :=
  .seq (.assign "go" (.lit 1))
    (.seq (.while (.eq (.var "go") (.lit 1))
      (.ite (.lt (.get pa (.var "w")) (.var "sc"))
        (.seq (.assign "s" (.get "Sl" (.get pa (.var "w"))))
          (.seq pt (.ite (.eq (.var "ok2") (.lit 1))
            (.store pa (.var "w") (.add (.get pa (.var "w")) (.lit 1)))
            (.assign "go" (.lit 0)))))
        (.assign "go" (.lit 0))))
      (.assign "ok" (eqX (.get pa (.var "w")) (.var "sc"))))

/-- The pointers are correct for the relation `F` and the chosen list `sl`
of length `sc`. -/
def PtrOK (n sc : ℕ) (F : ℕ → ℕ → Prop) (sl : ℕ → ℕ) (P : ℕ → ℕ) : Prop :=
  ∀ w < n, P w ≤ sc ∧ ∀ j < P w, F w (sl j)

/-- The potential of the pointers. -/
noncomputable def ptrPot (n : ℕ) (pa : String) (τ : Env) : ℕ :=
  ∑ w ∈ range n, (n - (τ.arrs pa).getD w 0)

theorem ptrPot_setVar (n : ℕ) (pa : String) (τ : Env) (x : String) (v : ℕ) :
    ptrPot n pa (τ.setVar x v) = ptrPot n pa τ := rfl

theorem ptrPot_setArr_ne (n : ℕ) {pa a : String} (h : a ≠ pa) (τ : Env) (i v : ℕ) :
    ptrPot n pa (τ.setArr a i v) = ptrPot n pa τ := by
  unfold ptrPot; simp [Ne.symm h]

theorem ptrPot_incr {n : ℕ} {pa : String} {τ : Env} {w : ℕ} (hw : w < n)
    (hl : (τ.arrs pa).length = n) {v : ℕ} (hv : (τ.arrs pa)[w]? = some v) (hvn : v < n) :
    ptrPot n pa (τ.setArr pa w (v + 1)) + 1 = ptrPot n pa τ := by
  unfold ptrPot
  simp only [arrs_setArr, if_true]
  have hsplit : ∀ g : ℕ → ℕ, ∑ x ∈ range n, g x = g w + ∑ x ∈ (range n).erase w, g x :=
    fun g => (add_sum_erase _ _ (mem_range.2 hw)).symm
  rw [hsplit, hsplit (fun x => n - (τ.arrs pa).getD x 0)]
  have hrest : ∑ x ∈ (range n).erase w, (n - ((τ.arrs pa).set w (v + 1)).getD x 0) =
      ∑ x ∈ (range n).erase w, (n - (τ.arrs pa).getD x 0) := by
    refine sum_congr rfl fun x hx => ?_
    have hxw := ne_of_mem_erase hx
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hxw)]
  rw [hrest]
  have h1 : ((τ.arrs pa).set w (v + 1)).getD w 0 = v + 1 := by
    simp [List.getD_eq_getElem?_getD, hl, hw]
  have h2 : (τ.arrs pa).getD w 0 = v := by simp [List.getD_eq_getElem?_getD, hv]
  rw [h1, h2]
  omega

/-- What the pointer scans read: the scalars, the chosen list and the
lengths. -/
structure PtrCtx (n sc : ℕ) (sl : ℕ → ℕ) (pa : String) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hsc : τ.vars "sc" = sc
  hsl : ∀ j < sc, (τ.arrs "Sl")[j]? = some (sl j)
  hsln : ∀ j < sc, sl j < n
  lpa : (τ.arrs pa).length = n

/-- **The test of one vertex.** -/
theorem ptrTst_run {B n sc Kq : ℕ} {pa : String} {pt : Com} {sl : ℕ → ℕ} {F : ℕ → ℕ → Prop}
    (Ctx : Env → Prop) (hpa : pa ∉ ["Sl"]) (hnB : n + 2 < B) (hsc : sc ≤ n)
    (hC : ∀ τ, Ctx τ → PtrCtx n sc sl pa τ)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["go", "s", "ok"] → Ctx (τ.setVar x v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr pa i v))
    (hpt : ∀ τ k s, Ctx τ → τ.vars "w" = k → k < n → τ.vars "s" = s → s < n →
      ∃ τ', Run B pt τ τ' Kq ∧
      Ctx τ' ∧ τ'.vars "ok2" = ind (F k s) ∧ τ'.vars "w" = k ∧ τ'.vars "go" = τ.vars "go" ∧
      τ'.vars "fw" = τ.vars "fw" ∧ τ'.arrs pa = τ.arrs pa)
    {σ : Env} {k : ℕ} (hσ : Ctx σ) (hw : σ.vars "w" = k) (hk : k < n)
    (hP : PtrOK n sc F sl fun w => (σ.arrs pa).getD w 0) :
    ∃ σ' K, Run B (ptrTst pa pt) σ σ' K ∧ Ctx σ' ∧ σ'.vars "w" = k ∧
      σ'.vars "fw" = σ.vars "fw" ∧
      σ'.vars "ok" = ind (∀ j < sc, F k (sl j)) ∧
      PtrOK n sc F sl (fun w => (σ'.arrs pa).getD w 0) ∧
      K + (Kq + 40) * ptrPot n pa σ' ≤ 2 * Kq + 100 + (Kq + 40) * ptrPot n pa σ := by
  classical
  have hσC := hC σ hσ
  let J : Env → Prop := fun τ => Ctx τ ∧ τ.vars "w" = k ∧ τ.vars "fw" = σ.vars "fw" ∧
    PtrOK n sc F sl (fun w => (τ.arrs pa).getD w 0) ∧ τ.vars "go" ≤ 1 ∧
    (τ.vars "go" = 0 → ((τ.arrs pa).getD k 0 = sc ∨
      ((τ.arrs pa).getD k 0 < sc ∧ ¬ F k (sl ((τ.arrs pa).getD k 0)))))
  let Ψ : Env → ℕ := fun τ => (Kq + 40) * (ptrPot n pa τ + τ.vars "go")
  have hget : ∀ τ, Ctx τ → (τ.arrs pa)[k]? = some ((τ.arrs pa).getD k 0) := fun τ h => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [(hC τ h).lpa]; exact hk)]
    simp
  have hJ0 : J (σ.setVar "go" 1) :=
    ⟨hCv _ _ _ hσ (by simp), by simp [hw], by simp, hP, by simp, by simp⟩
  obtain ⟨σ1, K1, hr1, ⟨hC1, hw1, hf1, hP1, hg1, hst1⟩, hfalse, hK1⟩ :=
    Run.while_potential (B := B) (b := .eq (.var "go") (.lit 1))
      (c := .ite (.lt (.get pa (.var "w")) (.var "sc"))
        (.seq (.assign "s" (.get "Sl" (.get pa (.var "w"))))
          (.seq pt (.ite (.eq (.var "ok2") (.lit 1))
            (.store pa (.var "w") (.add (.get pa (.var "w")) (.lit 1)))
            (.assign "go" (.lit 0)))))
        (.assign "go" (.lit 0))) J Ψ
      (fun τ hJ => ⟨_, eq_lit_evalB (by have := hJ.2.2.2.2.1; omega) (by omega)⟩)
      (by
        rintro τ ⟨hCτ, hwτ, hfτ, hPτ, hgτ, hstτ⟩ hc
        have hgo : τ.vars "go" = 1 := by
          rw [eq_lit_evalB (by omega) (by omega)] at hc; simpa using hc
        have hR := hC τ hCτ
        set v := (τ.arrs pa).getD k 0 with hv
        have hvsc : v ≤ sc := (hPτ k hk).1
        have hgv : (τ.arrs pa)[k]? = some v := hget τ hCτ
        have hevp : (Expr.get pa (.var "w")).evalB B τ = some v :=
          evalB_get (evalB_var (by rw [hwτ]; omega)) (by rw [hwτ]; exact hgv) (by omega)
        by_cases hlt : v < sc
        · have hcond : (Cond.lt (.get pa (.var "w")) (.var "sc")).evalB B τ = some true := by
            rw [evalB_condLt hevp (evalB_var (by rw [hR.hsc]; omega))]; simp [hR.hsc, hlt]
          have hslv := hR.hsl v hlt
          have hsn := hR.hsln v hlt
          set τ1 := τ.setVar "s" (sl v) with hτ1
          have hr1 : Run B (.assign "s" (.get "Sl" (.get pa (.var "w")))) τ τ1 4 :=
            (Run.assign (evalB_get hevp hslv (by omega))).mono (by simp)
          have hC1 : Ctx τ1 := hCv _ _ _ hCτ (by simp)
          obtain ⟨τ2, hr2, hC2, hok2, hw2, hgo2, hf2, hpa2⟩ :=
            hpt τ1 k (sl v) hC1 (by simp [hτ1, hwτ]) hk (by simp [hτ1]) hsn
          have hgv2 : (τ2.arrs pa)[k]? = some v := by rw [hpa2]; simpa [hτ1] using hgv
          by_cases hF : F k (sl v)
          · have hok : τ2.vars "ok2" = 1 := by rw [hok2]; simp [ind, hF]
            have hev2 : (Expr.get pa (.var "w")).evalB B τ2 = some v :=
              evalB_get (evalB_var (by rw [hw2]; omega)) (by rw [hw2]; exact hgv2) (by omega)
            refine ⟨τ2.setArr pa k (v + 1), _, Run.ite_true hcond (Run.seq hr1 (Run.seq hr2
              (Run.ite_true (by rw [eq_lit_evalB (by omega) (by omega)]; simp [hok])
                (Run.store (i := .var "w") (idx := k) (by simp [hw2]; omega)
                  (evalB_bin (op := .add) hev2 (evalB_lit (by omega)) (by simp; omega))
                  (by rw [(hC τ2 hC2).lpa]; simpa [hw2] using hk))))), ?_, ?_⟩
            · refine ⟨hCa _ _ _ hC2, by simp [hw2], by simp [hf2, hτ1, hfτ], fun w hw' => ?_,
                by simp [hgo2, hτ1, hgo], by simp [hgo2, hτ1, hgo]⟩
              simp only [arrs_setArr, if_true]
              have hl2 : (τ2.arrs pa).length = n := (hC τ2 hC2).lpa
              by_cases hwk : w = k
              · subst hwk
                have : ((τ2.arrs pa).set w (v + 1)).getD w 0 = v + 1 := by
                  simp [List.getD_eq_getElem?_getD, hl2, hk]
                rw [this]
                refine ⟨hlt, fun j hj => ?_⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
                · exact (hPτ w hk).2 j hj
                · exact hF
              · have : ((τ2.arrs pa).set k (v + 1)).getD w 0 = (τ.arrs pa).getD w 0 := by
                  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hwk), hpa2, hτ1]
                rw [this]; exact hPτ w hw'
            · have hpot := ptrPot_incr (pa := pa) (τ := τ2) hk (hC τ2 hC2).lpa hgv2 (by omega)
              have hpot' : ptrPot n pa τ2 = ptrPot n pa τ := by
                unfold ptrPot; rw [hpa2]; rfl
              simp only [Ψ, Cond.size, Expr.size, vars_setArr, hgo2, hτ1, vars_setVar,
                if_neg (show "go" ≠ "s" by decide), hgo]
              rw [← hpot', ← hpot]
              nlinarith
          · have hok : τ2.vars "ok2" = 0 := by rw [hok2]; simp [ind, hF]
            refine ⟨τ2.setVar "go" 0, _, Run.ite_true hcond (Run.seq hr1 (Run.seq hr2
              (Run.ite_false (by rw [eq_lit_evalB (by omega) (by omega)]; simp [hok])
                (Run.assign (v := 0) (by simp; omega))))), ?_, ?_⟩
            · refine ⟨hCv _ _ _ hC2 (by simp), by simp [hw2], by simp [hf2, hτ1, hfτ], ?_,
                by simp, fun _ => Or.inr ?_⟩
              · simpa [hpa2, hτ1] using hPτ
              · simp only [arrs_setVar, hpa2, hτ1]; exact ⟨hlt, hF⟩
            · have hpot' : ptrPot n pa τ2 = ptrPot n pa τ := by
                unfold ptrPot; rw [hpa2]; rfl
              simp only [Ψ, Cond.size, Expr.size, vars_setVar, if_true, ptrPot_setVar, hpot', hgo]
              nlinarith
        · have hcond : (Cond.lt (.get pa (.var "w")) (.var "sc")).evalB B τ = some false := by
            rw [evalB_condLt hevp (evalB_var (by rw [hR.hsc]; omega))]; simp [hR.hsc, hlt]
          refine ⟨τ.setVar "go" 0, _, Run.ite_false hcond (Run.assign (v := 0) (by simp; omega)), ?_, ?_⟩
          · refine ⟨hCv _ _ _ hCτ (by simp), by simp [hwτ], by simp [hfτ], by simpa using hPτ,
              by simp, fun _ => Or.inl ?_⟩
            simp only [arrs_setVar]; omega
          · simp only [Ψ, Cond.size, Expr.size, vars_setVar, if_true, ptrPot_setVar, hgo]
            nlinarith)
      hJ0
  have hg0 : σ1.vars "go" = 0 := by
    rw [eq_lit_evalB (by omega) (by omega)] at hfalse
    simp at hfalse; omega
  have hR1 := hC σ1 hC1
  set v := (σ1.arrs pa).getD k 0 with hv
  have hgv : (σ1.arrs pa)[k]? = some v := hget σ1 hC1
  have hvsc : v ≤ sc := (hP1 k hk).1
  have hok : ind (v = sc) = ind (∀ j < sc, F k (sl j)) := by
    rw [ind_eq_iff]
    constructor
    · intro h j hj; exact (hP1 k hk).2 j (by show j < (σ1.arrs pa).getD k 0; omega)
    · intro h
      rcases hst1 hg0 with h1 | ⟨h1, h2⟩
      · exact h1
      · exact absurd (h _ h1) h2
  have hevp : (Expr.get pa (.var "w")).evalB B σ1 = some v :=
    evalB_get (evalB_var (by rw [hw1]; omega)) (by rw [hw1]; exact hgv) (by omega)
  have evsc : (Expr.var "sc").evalB B σ1 = some sc := by simp [hR1.hsc]; omega
  refine ⟨σ1.setVar "ok" (ind (v = sc)), _, Run.seq (Run.assign (v := 1) (by simp; omega))
    (Run.seq hr1 (Run.assign (evalB_eqX hevp evsc (by omega) (by omega) (by omega)))),
    hCv _ _ _ hC1 (by simp), by simp [hw1], by simp [hf1], by simp [hok], by simpa using hP1, ?_⟩
  simp only [Ψ, hg0, vars_setVar, if_true, add_zero] at hK1
  simp only [Cond.size, Expr.size, size_eqX, ptrPot_setVar] at hK1 ⊢
  nlinarith

/-- **The pointer scan**: the first vertex far from all chosen ones. -/
theorem ptrScan_run {B n sc Kq : ℕ} {pa : String} {pt : Com} {sl : ℕ → ℕ} {F : ℕ → ℕ → Prop}
    (Ctx : Env → Prop) (hpa : pa ∉ ["Sl"]) (hnB : n + 2 < B) (hsc : sc ≤ n)
    (hC : ∀ τ, Ctx τ → PtrCtx n sc sl pa τ)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["go", "s", "ok", "w", "fw"] → Ctx (τ.setVar x v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr pa i v))
    (hpt : ∀ τ k s, Ctx τ → τ.vars "w" = k → k < n → τ.vars "s" = s → s < n →
      ∃ τ', Run B pt τ τ' Kq ∧
      Ctx τ' ∧ τ'.vars "ok2" = ind (F k s) ∧ τ'.vars "w" = k ∧ τ'.vars "go" = τ.vars "go" ∧
      τ'.vars "fw" = τ.vars "fw" ∧ τ'.arrs pa = τ.arrs pa)
    {σ : Env} (hσ : Ctx σ) (hP : PtrOK n sc F sl fun w => (σ.arrs pa).getD w 0) :
    ∃ σ' K, Run B (scanFirst (ptrTst pa pt)) σ σ' K ∧ Ctx σ' ∧
      σ'.vars "fw" = (firstN n fun w => ∀ j < sc, F w (sl j)).getD n ∧
      PtrOK n sc F sl (fun w => (σ'.arrs pa).getD w 0) ∧
      K + (Kq + 40) * ptrPot n pa σ' ≤ n * (2 * Kq + 120) + 20 + (Kq + 40) * ptrPot n pa σ := by
  obtain ⟨σ', K, hr, ⟨hC', hP'⟩, hfw, hK⟩ :=
    scanFirst_run (B := B) (n := n) (Kt := 2 * Kq + 100) (tst := ptrTst pa pt)
      (fun τ => Ctx τ ∧ PtrOK n sc F sl fun w => (τ.arrs pa).getD w 0)
      (fun τ => (Kq + 40) * ptrPot n pa τ) (fun w => ∀ j < sc, F w (sl j)) (by omega)
      (fun τ h => (hC τ h.1).hn)
      (fun τ x h => ⟨hCv _ _ _ h.1 (by simp), h.2⟩)
      (fun τ x h => ⟨hCv _ _ _ h.1 (by simp), h.2⟩)
      (fun τ x => by simp [ptrPot_setVar]) (fun τ x => by simp [ptrPot_setVar])
      (fun τ k h hwk hk => by
        obtain ⟨τ', K, hr, hC', hw', hf', hok', hP', hK'⟩ :=
          ptrTst_run Ctx hpa hnB hsc hC (fun τ x v h hx => hCv τ x v h (by
            simp at hx ⊢; tauto)) hCa hpt h.1 hwk hk h.2
        exact ⟨τ', K, hr, ⟨hC', hP'⟩, hw', hf', hok', by nlinarith⟩)
      ⟨hσ, hP⟩
  exact ⟨σ', K, hr, hC', hfw, hP', by nlinarith⟩

end Lax185574Proofs.Chain.Ram
