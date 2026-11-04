import Lax185574Proofs.Chain.Ram.Bool01
import Lax185574Proofs.Chain.Ram.PtrScan

/-!
The tests of the predamping rules, for the labels `L` in `lab`.

* `repCom` marks the representatives: the vertices of least position in
  their part (`rep`).
* `r1Tst` decides whether `w` crosses more than `t1` parts, from the
  neighbor counts `cnt` and the part sizes `sz`.
* `hamTst` decides whether `Δ[w,s]` meets more than `t2` parts. It marks
  the labels of the vertices of `Δ[w,s]` in `mark` and clears them again.
* `btTst` decides whether at least `t3` representatives lie strictly
  between `w` and `s` in the ordering `pos`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- What the tests read. -/
structure AppCtx (n : ℕ) (G : SimpleGraph (Fin n)) (L pf : ℕ → ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hadj : Mat τ "adj" n (fun u v => ind (gA G u v))
  hlab : Vec τ "lab" n L
  hpos : Vec τ "pos" n pf
  lmark : (τ.arrs "mark").length = n

/-- The labels are least-vertex labels. -/
structure IsLabels (n : ℕ) (L : ℕ → ℕ) : Prop where
  lt : ∀ u < n, L u < n
  idem : ∀ u < n, L (L u) = L u

theorem isLabels_lbl {E : ℕ → ℕ → Prop} (hE : IsEqv n E) : IsLabels n (lbl n E) :=
  ⟨fun u hu => lbl_lt hE hu, fun u hu => by
    rw [lbl_eq_iff hE (lbl_lt hE hu) hu]; exact (lbl_spec hE hu).2.1⟩

/-! ### Representatives -/

/-- The inner test of `repCom`: a vertex of the same part at a smaller position. -/
def repB : Com :=
  .ite (.eq (.get "lab" (.var "y")) (.get "lab" (.var "z")))
    (.ite (.lt (.get "pos" (.var "y")) (.get "pos" (.var "z"))) (.assign "fl" (.lit 0)) .skip) .skip

/-- Mark the representatives in `rep`. -/
def repCom : Com :=
  forUp "z" (.var "n") (.seq (.assign "fl" (.lit 1))
    (.seq (forUp "y" (.var "n") repB) (.store "rep" (.var "z") (.var "fl"))))

theorem repCom_run {B : ℕ} {L pf : ℕ → ℕ} (Ctx : Env → Prop) (hL : IsLabels n L)
    (hpf : ∀ z < n, pf z < n) (hB : n + 2 < B)
    (hC : ∀ τ, Ctx τ → AppCtx n G L pf τ)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["z", "y", "fl"] → Ctx (τ.setVar x v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "rep" i v))
    {σ : Env} (hσ : Ctx σ) (hl : (σ.arrs "rep").length = n) :
    ∃ σ', Run B repCom σ σ' (n * (n * 30 + 30) + 10) ∧ Ctx σ' ∧
      Vec σ' "rep" n (fun z => ind (isRepN n pf L z)) := by
  classical
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ (τ.arrs "rep").length = n ∧
    ∀ z < k, (τ.arrs "rep")[z]? = some (ind (isRepN n pf L z))
  obtain ⟨σ', hr, ⟨hC', hl', hv'⟩, -⟩ :=
    forUp_run (B := B) (i := "z") (e := .var "n")
      (body := .seq (.assign "fl" (.lit 1))
        (.seq (forUp "y" (.var "n") repB) (.store "rep" (.var "z") (.var "fl"))))
      (N := n) (K := n * 30 + 20) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
      (σ := σ) ⟨hCv _ _ _ hσ (by simp), by simp [hl], fun z hz => absurd hz (Nat.not_lt_zero _)⟩
      (by
        rintro k hk τ ⟨hCτ, hlτ, hvτ⟩ hzk
        let J : ℕ → Env → Prop := fun j ρ => Ctx ρ ∧ ρ.vars "z" = k ∧ ρ.arrs "rep" = τ.arrs "rep" ∧
          ρ.vars "fl" = ind (∀ y < j, L y = L k → pf k ≤ pf y)
        obtain ⟨ρ, hrI, ⟨hCρ, hzρ, harρ, hflρ⟩, -⟩ :=
          forUp_run (B := B) (i := "y") (e := .var "n") (body := repB) (N := n) (K := 20) J
            (by omega)
            (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
            (σ := τ.setVar "fl" 1) ⟨hCv _ _ _ (hCv _ _ _ hCτ (by simp)) (by simp), by simp [hzk],
              rfl, by simp [ind]⟩
            (by
              rintro j hj ρ ⟨hCρ, hzρ, harρ, hflρ⟩ hyj
              have hR := hC ρ hCρ
              have e1 : (Expr.get "lab" (.var "y")).evalB B ρ = some (L j) :=
                hR.hlab.evalB hyj hj (by omega) (by have := hL.lt j hj; omega)
              have e2 : (Expr.get "lab" (.var "z")).evalB B ρ = some (L k) :=
                hR.hlab.evalB hzρ hk (by omega) (by have := hL.lt k hk; omega)
              have e3 : (Expr.get "pos" (.var "y")).evalB B ρ = some (pf j) :=
                hR.hpos.evalB hyj hj (by omega) (by have := hpf j hj; omega)
              have e4 : (Expr.get "pos" (.var "z")).evalB B ρ = some (pf k) :=
                hR.hpos.evalB hzρ hk (by omega) (by have := hpf k hk; omega)
              have hsucc : ∀ P : Prop, (∀ y < j + 1, L y = L k → pf k ≤ pf y) ↔
                  ((∀ y < j, L y = L k → pf k ≤ pf y) ∧ (L j = L k → pf k ≤ pf j)) := fun _ =>
                ⟨fun h => ⟨fun y hy => h y (by omega), h j (by omega)⟩, fun ⟨h1, h2⟩ y hy => by
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
                  · exact h1 y hy
                  · exact h2⟩
              by_cases hlj : L j = L k
              · by_cases hpj : pf j < pf k
                · refine ⟨ρ.setVar "fl" 0, (Run.ite_true (by rw [evalB_condEq' e1 e2]; simp [hlj])
                    (Run.ite_true (by rw [evalB_condLt e3 e4]; simp [hpj])
                      (Run.assign (v := 0) (by simp; omega)))).mono (by simp), by simp [hyj], ?_⟩
                  refine ⟨hCv _ _ _ (hCv _ _ _ hCρ (by simp)) (by simp), by simp [hzρ], harρ, ?_⟩
                  simp only [vars_setVar, if_neg (show "fl" ≠ "y" by decide), if_true]
                  symm; rw [ind, if_neg]; intro h; have := h j (by omega) hlj; omega
                · refine ⟨ρ, (Run.ite_true (by rw [evalB_condEq' e1 e2]; simp [hlj])
                    (Run.ite_false (by rw [evalB_condLt e3 e4]; simp [hpj]) Run.skip)).mono
                    (by simp), hyj, ?_⟩
                  refine ⟨hCv _ _ _ hCρ (by simp), by simp [hzρ], harρ, ?_⟩
                  simp only [vars_setVar, if_neg (show "fl" ≠ "y" by decide), hflρ]
                  rw [ind_eq_iff, hsucc True]
                  exact ⟨fun h => ⟨h, fun _ => by omega⟩, fun h => h.1⟩
              · refine ⟨ρ, (Run.ite_false (by rw [evalB_condEq' e1 e2]; simp [hlj])
                  Run.skip).mono (by simp), hyj, ?_⟩
                refine ⟨hCv _ _ _ hCρ (by simp), by simp [hzρ], harρ, ?_⟩
                simp only [vars_setVar, if_neg (show "fl" ≠ "y" by decide), hflρ]
                rw [ind_eq_iff, hsucc True]
                exact ⟨fun h => ⟨h, fun h' => absurd h' hlj⟩, fun h => h.1⟩)
        have hfl : ρ.vars "fl" = ind (isRepN n pf L k) := hflρ
        have hfB : ind (isRepN n pf L k) < B := by have := ind_le_one (isRepN n pf L k); omega
        refine ⟨ρ.setArr "rep" k (ind (isRepN n pf L k)),
          (Run.seq (Run.assign (v := 1) (by simp; omega)) (Run.seq hrI
            (Run.store (i := .var "z") (idx := k) (by simp [hzρ]; omega)
              (by simp [hfl]; omega) (by rw [harρ, hlτ]; omega)))).mono
            (by simp [repB]; nlinarith), by simp [hzρ], ?_⟩
        refine ⟨hCv _ _ _ (hCa _ _ _ hCρ) (by simp), by simp [harρ, hlτ], fun z hz => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hz | rfl
        · rw [List.getElem?_set_ne (by omega), harρ]; exact hvτ z hz
        · rw [List.getElem?_set_self (by rw [harρ, hlτ]; omega)])
  exact ⟨σ', hr.mono (by simp; nlinarith), hC', ⟨hl', hv'⟩⟩

/-! ### Between -/

/-- `hz` lies strictly between `w` and `s` in the ordering. -/
def btwE : Expr :=
  .or (.mul (ltX (.get "pos" (.var "w")) (.get "pos" (.var "hz")))
      (ltX (.get "pos" (.var "hz")) (.get "pos" (.var "s"))))
    (.mul (ltX (.get "pos" (.var "s")) (.get "pos" (.var "hz")))
      (ltX (.get "pos" (.var "hz")) (.get "pos" (.var "w"))))

/-- The pair test of rule (R3). -/
def btTst : Com :=
  .seq (sumLoop "hz" "h" (.mul (.get "rep" (.var "hz")) btwE))
    (.assign "ok2" (notX (ltX (.var "h") (.var "t3"))))

theorem btTst_run {B ζ : ℕ} {L pf : ℕ → ℕ} (Ctx : Env → Prop) (hL : IsLabels n L)
    (hpf : ∀ z < n, pf z < n) (hB : n + 2 < B) (hζ : ζ < B)
    (hC : ∀ τ, Ctx τ → AppCtx n G L pf τ)
    (hrep : ∀ τ, Ctx τ → Vec τ "rep" n (fun z => ind (isRepN n pf L z)))
    (ht3 : ∀ τ, Ctx τ → τ.vars "t3" = ζ)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["hz", "h", "ok2"] → Ctx (τ.setVar x v))
    {σ : Env} {w s : ℕ} (hσ : Ctx σ) (hw : σ.vars "w" = w) (hs : σ.vars "s" = s) (hwn : w < n)
    (hsn : s < n) :
    ∃ σ', Run B btTst σ σ' (n * 80 + 40) ∧ Ctx σ' ∧
      σ'.vars "ok2" = ind (ζ ≤ betwN n pf L w s) ∧ σ'.arrs = σ.arrs ∧
      ∀ x, x ∉ ["hz", "h", "ok2"] → σ'.vars x = σ.vars x := by
  classical
  let P : ℕ → Prop := fun z => isRepN n pf L z ∧
    ((pf w < pf z ∧ pf z < pf s) ∨ (pf s < pf z ∧ pf z < pf w))
  have hsum : ∑ k ∈ range n, ind (P k) = betwN n pf L w s := by
    rw [sum_ind_eq_card]; rfl
  have hsumle : ∑ k ∈ range n, ind (P k) ≤ n := by
    rw [sum_ind_eq_card]; exact card_filter_range_le _ _
  obtain ⟨σ1, hr1, ⟨hC1, hw1, hs1, hfr1⟩, hh1, harr1, -⟩ :=
    sumLoop_run (B := B) (n := n) (K := 60) (i := "hz") (acc := "h")
      (e := .mul (.get "rep" (.var "hz")) btwE) (by decide)
      (fun τ => Ctx τ ∧ τ.vars "w" = w ∧ τ.vars "s" = s ∧
        ∀ x, x ∉ ["hz", "h", "ok2"] → τ.vars x = σ.vars x) (fun k => ind (P k))
      (by omega) (by omega) (fun τ h => (hC τ h.1).hn)
      (fun τ x h => ⟨hCv _ _ _ h.1 (by simp), by simp [h.2.1], by simp [h.2.2.1],
        fun y hy => by
          have : y ≠ "hz" := by intro e; subst e; simp at hy
          simp [this, h.2.2.2 y hy]⟩)
      (fun τ x h => ⟨hCv _ _ _ h.1 (by simp), by simp [h.2.1], by simp [h.2.2.1],
        fun y hy => by
          have : y ≠ "h" := by intro e; subst e; simp at hy
          simp [this, h.2.2.2 y hy]⟩)
      (fun τ k h hk hkn => by
        have hR := hC τ h.1
        have pz := hR.hpos.evalB (B := B) hk hkn (by omega) (by have := hpf k hkn; omega)
        have pw := hR.hpos.evalB (B := B) h.2.1 hwn (by omega) (by have := hpf w hwn; omega)
        have ps := hR.hpos.evalB (B := B) h.2.2.1 hsn (by omega) (by have := hpf s hsn; omega)
        have hpk := hpf k hkn; have hpw := hpf w hwn; have hps := hpf s hsn
        have e1 := evalB_ltX pw pz (by omega) (by omega) (by omega)
        have e2 := evalB_ltX pz ps (by omega) (by omega) (by omega)
        have e3 := evalB_ltX ps pz (by omega) (by omega) (by omega)
        have e4 := evalB_ltX pz pw (by omega) (by omega) (by omega)
        have e5 := evalB_or01 (evalB_and01 e1 e2 (by omega)) (evalB_and01 e3 e4 (by omega))
          (by omega)
        have er := (hrep τ h.1).evalB (B := B) hk hkn (by omega)
          (by have := ind_le_one (isRepN n pf L k); omega)
        exact evalB_and01 er e5 (by omega))
      (by simp [btwE]) ⟨hσ, hw, hs, fun _ _ => rfl⟩
  have hhB : betwN n pf L w s < B := by omega
  have e := evalB_notX (evalB_ltX (B := B) (σ := σ1) (evalB_var (x := "h") (by rw [hh1]; omega))
    (evalB_var (x := "t3") (by rw [ht3 σ1 hC1]; omega)) (by rw [hh1]; omega)
    (by rw [ht3 σ1 hC1]; omega) (by omega)) (by omega)
  refine ⟨σ1.setVar "ok2" _, (Run.seq hr1 (Run.assign e)).mono (by simp [btwE]; omega),
    hCv _ _ _ hC1 (by simp), ?_, by simp [harr1], fun x hx => ?_⟩
  · simp only [vars_setVar, if_true, hh1, ht3 σ1 hC1, ← hsum]
    rw [ind_eq_iff, not_lt]
  · have : x ≠ "ok2" := by intro e; subst e; simp at hx
    simp [this, hfr1 x hx]

/-! ### Crossing parts -/

/-- The part `rc` is crossed by `w`. -/
def crossE : Expr :=
  .mul (.mul (.mul (eqX (.get "lab" (.var "rc")) (.var "rc"))
      (notX (eqX (.get "lab" (.var "w")) (.var "rc"))))
      (notX (eqX (.get "cnt" (rm "w" "rc")) (.lit 0))))
    (notX (eqX (.get "cnt" (rm "w" "rc")) (.get "sz" (.var "rc"))))

/-- The test of rule (R1). -/
def r1Tst : Com := .seq (sumLoop "rc" "h" crossE) (.assign "ok" (ltX (.var "t1") (.var "h")))

theorem r1Tst_run {B t : ℕ} {L pf : ℕ → ℕ} (Ctx : Env → Prop) (hL : IsLabels n L)
    (hB : n * n + n + 2 < B) (htB : t < B)
    (hC : ∀ τ, Ctx τ → AppCtx n G L pf τ)
    (hcnt : ∀ τ, Ctx τ → Mat τ "cnt" n (fun u c => cntN G L u c))
    (hsz : ∀ τ, Ctx τ → Vec τ "sz" n (fun c => szN n L c))
    (ht1 : ∀ τ, Ctx τ → τ.vars "t1" = t)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["rc", "h", "ok"] → Ctx (τ.setVar x v))
    {σ : Env} {w : ℕ} (hσ : Ctx σ) (hw : σ.vars "w" = w) (hwn : w < n) :
    ∃ σ', Run B r1Tst σ σ' (n * 120 + 40) ∧ Ctx σ' ∧
      σ'.vars "ok" = ind (t < crossN G L w) ∧ σ'.arrs = σ.arrs ∧
      ∀ x, x ∉ ["rc", "h", "ok"] → σ'.vars x = σ.vars x := by
  classical
  let P : ℕ → Prop := fun c => L c = c ∧ L w ≠ c ∧ cntN G L w c ≠ 0 ∧ cntN G L w c ≠ szN n L c
  have hsum : ∑ k ∈ range n, ind (P k) = crossN G L w := by
    rw [sum_ind_eq_card]; rfl
  have hsumle : ∑ k ∈ range n, ind (P k) ≤ n := by
    rw [sum_ind_eq_card]; exact card_filter_range_le _ _
  obtain ⟨σ1, hr1, ⟨hC1, hw1, hfr1⟩, hh1, harr1, -⟩ :=
    sumLoop_run (B := B) (n := n) (K := 100) (i := "rc") (acc := "h") (e := crossE) (by decide)
      (fun τ => Ctx τ ∧ τ.vars "w" = w ∧ ∀ x, x ∉ ["rc", "h", "ok"] → τ.vars x = σ.vars x)
      (fun k => ind (P k)) (by omega) (by omega) (fun τ h => (hC τ h.1).hn)
      (fun τ x h => ⟨hCv _ _ _ h.1 (by simp), by simp [h.2.1],
        fun y hy => by
          have : y ≠ "rc" := by intro e; subst e; simp at hy
          simp [this, h.2.2 y hy]⟩)
      (fun τ x h => ⟨hCv _ _ _ h.1 (by simp), by simp [h.2.1],
        fun y hy => by
          have : y ≠ "h" := by intro e; subst e; simp at hy
          simp [this, h.2.2 y hy]⟩)
      (fun τ k h hk hkn => by
        have hR := hC τ h.1
        have hLk := hL.lt k hkn; have hLw := hL.lt w hwn
        have hck := cntN_le (G := G) L w k
        have hsk := szN_le (n := n) L k
        have l1 := hR.hlab.evalB (B := B) hk hkn (by omega) (by omega)
        have l2 := hR.hlab.evalB (B := B) h.2.1 hwn (by omega) (by omega)
        have vk : (Expr.var "rc").evalB B τ = some k := by simp [hk]; omega
        have c1 := (hcnt τ h.1).evalB (B := B) hR.hn h.2.1 hk hwn hkn (by omega) (by omega)
          (by omega)
        have s1 := (hsz τ h.1).evalB (B := B) hk hkn (by omega) (by omega)
        have e1 := evalB_eqX l1 vk (by omega) (by omega) (by omega)
        have e2 := evalB_notX (evalB_eqX l2 vk (by omega) (by omega) (by omega)) (by omega)
        have e3 := evalB_notX (evalB_eqX c1 (evalB_lit (n := 0) (by omega)) (by omega) (by omega)
          (by omega)) (by omega)
        have e4 := evalB_notX (evalB_eqX c1 s1 (by omega) (by omega) (by omega)) (by omega)
        have := evalB_and01 (evalB_and01 (evalB_and01 e1 e2 (by omega)) e3 (by omega)) e4
          (by omega)
        unfold crossE
        rw [this]
        congr 1
        rw [ind_eq_iff]
        simp only [P]; tauto)
      (by simp [crossE, rm]) ⟨hσ, hw, fun _ _ => rfl⟩
  have e := evalB_ltX (B := B) (σ := σ1) (evalB_var (x := "t1") (by rw [ht1 σ1 hC1]; omega))
    (evalB_var (x := "h") (by rw [hh1]; omega)) (by rw [ht1 σ1 hC1]; omega)
    (by rw [hh1]; omega) (by omega)
  refine ⟨σ1.setVar "ok" _, (Run.seq hr1 (Run.assign e)).mono (by simp [crossE, rm]; omega),
    hCv _ _ _ hC1 (by simp), ?_, by simp [harr1], fun x hx => ?_⟩
  · simp only [vars_setVar, if_true, hh1, ht1 σ1 hC1, ← hsum]
  · have : x ≠ "ok" := by intro e; subst e; simp at hx
    simp [this, hfr1 x hx]

/-! ### Parts meeting the symmetric difference -/

/-- `hy ∈ Δ[w,s]`. -/
def sdE : Expr :=
  .mul (notX (eqX (.var "w") (.var "s")))
    (.or (.or (eqX (.var "hy") (.var "w")) (eqX (.var "hy") (.var "s")))
      (.xor (.get "adj" (rm "w" "hy")) (.get "adj" (rm "s" "hy"))))

/-- Mark the part of `hy` if `hy ∈ Δ[w,s]`, counting new parts. -/
def hamB1 : Com :=
  .ite (.eq sdE (.lit 1))
    (.ite (.eq (.get "mark" (.get "lab" (.var "hy"))) (.lit 0))
      (.seq (.store "mark" (.get "lab" (.var "hy")) (.lit 1)) (.assign "h" (.add (.var "h") (.lit 1))))
      .skip) .skip

/-- Clear the marks. -/
def hamB2 : Com := .ite (.eq sdE (.lit 1)) (.store "mark" (.get "lab" (.var "hy")) (.lit 0)) .skip

/-- The pair test of rule (R2). -/
def hamTst : Com :=
  .seq (.assign "h" (.lit 0)) (.seq (forUp "hy" (.var "n") hamB1)
    (.seq (forUp "hy" (.var "n") hamB2) (.assign "ok2" (ltX (.var "t2") (.var "h")))))

theorem evalB_sdE {B : ℕ} {L pf : ℕ → ℕ} {τ : Env} (hR : AppCtx n G L pf τ) (hB : n * n + n + 2 < B)
    {w s y : ℕ} (hw : τ.vars "w" = w) (hs : τ.vars "s" = s) (hy : τ.vars "hy" = y) (hwn : w < n)
    (hsn : s < n) (hyn : y < n) :
    sdE.evalB B τ = some (ind (sdN G w s y)) := by
  have vw : (Expr.var "w").evalB B τ = some w := by simp [hw]; omega
  have vs : (Expr.var "s").evalB B τ = some s := by simp [hs]; omega
  have vy : (Expr.var "hy").evalB B τ = some y := by simp [hy]; omega
  have a1 := hR.hadj.evalB (B := B) hR.hn hw hy hwn hyn (by nlinarith) (by omega)
    (by have := ind_le_one (gA G w y); omega)
  have a2 := hR.hadj.evalB (B := B) hR.hn hs hy hsn hyn (by nlinarith) (by omega)
    (by have := ind_le_one (gA G s y); omega)
  have e := evalB_and01 (evalB_notX (evalB_eqX vw vs (by omega) (by omega) (by omega)) (by omega))
    (evalB_or01 (evalB_or01 (evalB_eqX vy vw (by omega) (by omega) (by omega))
      (evalB_eqX vy vs (by omega) (by omega) (by omega)) (by omega))
      (evalB_xor01 a1 a2 (by omega)) (by omega)) (by omega)
  unfold sdE; rw [e]
  congr 1; rw [ind_eq_iff]; unfold sdN; tauto

open Classical in
/-- The parts met by the first `k` vertices of `Δ[w,s]`. -/
noncomputable def hamT (G : SimpleGraph (Fin n)) (L : ℕ → ℕ) (w s k : ℕ) : Finset ℕ :=
  (range n).filter fun c => ∃ y < k, sdN G w s y ∧ L y = c

theorem hamT_succ {L : ℕ → ℕ} {w s k : ℕ} (hLk : L k < n) :
    hamT G L w s (k + 1) = open Classical in
      if sdN G w s k then insert (L k) (hamT G L w s k) else hamT G L w s k := by
  classical
  have hlt : ∀ c, (∃ y < k + 1, sdN G w s y ∧ L y = c) ↔
      ((∃ y < k, sdN G w s y ∧ L y = c) ∨ (sdN G w s k ∧ L k = c)) := fun c =>
    ⟨fun ⟨y, hy, h1, h2⟩ => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
      · exact Or.inl ⟨y, hy, h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩,
     fun h => h.elim (fun ⟨y, hy, h1, h2⟩ => ⟨y, by omega, h1, h2⟩)
       (fun ⟨h1, h2⟩ => ⟨k, by omega, h1, h2⟩)⟩
  ext c
  split_ifs with hsd
  · simp only [hamT, mem_insert, mem_filter, mem_range, hlt]
    constructor
    · rintro ⟨hc, h | ⟨-, h⟩⟩
      · exact Or.inr ⟨hc, h⟩
      · exact Or.inl h.symm
    · rintro (rfl | ⟨hc, h⟩)
      · exact ⟨hLk, Or.inr ⟨hsd, rfl⟩⟩
      · exact ⟨hc, Or.inl h⟩
  · simp only [hamT, mem_filter, mem_range, hlt]
    constructor
    · rintro ⟨hc, h | ⟨h, -⟩⟩
      · exact ⟨hc, h⟩
      · exact absurd h hsd
    · rintro ⟨hc, h⟩; exact ⟨hc, Or.inl h⟩

theorem hamTst_run {B μ : ℕ} {L pf : ℕ → ℕ} (Ctx : Env → Prop) (hL : IsLabels n L)
    (hB : n * n + n + 2 < B) (hμ : μ < B)
    (hC : ∀ τ, Ctx τ → AppCtx n G L pf τ)
    (ht2 : ∀ τ, Ctx τ → τ.vars "t2" = μ)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["hy", "h", "ok2"] → Ctx (τ.setVar x v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "mark" i v))
    {σ : Env} {w s : ℕ} (hσ : Ctx σ) (hw : σ.vars "w" = w) (hs : σ.vars "s" = s) (hwn : w < n)
    (hsn : s < n) (hz : Vec σ "mark" n (fun _ => 0)) :
    ∃ σ', Run B hamTst σ σ' (n * 300 + 40) ∧ Ctx σ' ∧
      σ'.vars "ok2" = ind (μ < hamN G L w s) ∧ Vec σ' "mark" n (fun _ => 0) ∧
      (∀ a, a ≠ "mark" → σ'.arrs a = σ.arrs a) ∧
      ∀ x, x ∉ ["hy", "h", "ok2"] → σ'.vars x = σ.vars x := by
  classical
  have hσR := hC σ hσ
  -- the frame of the scalars
  let Fr : Env → Prop := fun τ => τ.vars "w" = w ∧ τ.vars "s" = s ∧
    ∀ x, x ∉ ["hy", "h", "ok2"] → τ.vars x = σ.vars x
  have hFr : ∀ τ x v, Fr τ → x ∈ ["hy", "h", "ok2"] → Fr (τ.setVar x v) := by
    intro τ x v h hx
    have hxw : x ≠ "w" := by intro e; subst e; simp at hx
    have hxs : x ≠ "s" := by intro e; subst e; simp at hx
    refine ⟨by simp [Ne.symm hxw, h.1], by simp [Ne.symm hxs, h.2.1], fun y hy => ?_⟩
    have : y ≠ x := by intro e; subst e; exact hy hx
    simp [this, h.2.2 y hy]
  -- first loop
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ Fr τ ∧
    (∀ a, a ≠ "mark" → τ.arrs a = σ.arrs a) ∧ (τ.arrs "mark").length = n ∧
    (∀ c < n, (τ.arrs "mark")[c]? = some (ind (c ∈ hamT G L w s k))) ∧
    τ.vars "h" = (hamT G L w s k).card
  have hT0 : hamT G L w s 0 = ∅ := by ext c; simp [hamT]
  have hTle : ∀ k, (hamT G L w s k).card ≤ n := fun k => by
    unfold hamT; exact card_filter_range_le _ _
  obtain ⟨σ1, hr1, ⟨hC1, hF1, ha1, hl1, hm1, hh1⟩, -⟩ :=
    forUp_run (B := B) (i := "hy") (e := .var "n") (body := hamB1) (N := n) (K := 150) I
      (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
      (σ := σ.setVar "h" 0) ⟨hCv _ _ _ (hCv _ _ _ hσ (by simp)) (by simp),
        hFr _ _ _ (hFr _ _ _ ⟨hw, hs, fun _ _ => rfl⟩ (by simp)) (by simp), fun _ _ => rfl,
        by simp [hz.len], fun c hc => by simp [hT0, ind, hz.get c hc], by simp [hT0]⟩
      (by
        rintro k hk τ ⟨hCτ, hFτ, haτ, hlτ, hmτ, hhτ⟩ hyk
        have hR := hC τ hCτ
        have hLk := hL.lt k hk
        have hsd := evalB_sdE (B := B) hR hB hFτ.1 hFτ.2.1 hyk hwn hsn hk
        have el : (Expr.get "lab" (.var "hy")).evalB B τ = some (L k) :=
          hR.hlab.evalB hyk hk (by omega) (by omega)
        have hmk := hmτ (L k) hLk
        have em : (Expr.get "mark" (.get "lab" (.var "hy"))).evalB B τ =
            some (ind (L k ∈ hamT G L w s k)) :=
          evalB_get el hmk (by have := ind_le_one (L k ∈ hamT G L w s k); omega)
        have hsucc := hamT_succ (G := G) (w := w) (s := s) hLk
        have hhB := hTle k
        by_cases hsdk : sdN G w s k
        · have c1 : (Cond.eq sdE (.lit 1)).evalB B τ = some true := by
            rw [evalB_condEq' hsd (evalB_lit (by omega))]; simp [ind, hsdk]
          by_cases hin : L k ∈ hamT G L w s k
          · have c2 : (Cond.eq (.get "mark" (.get "lab" (.var "hy"))) (.lit 0)).evalB B τ =
                some false := by
              rw [evalB_condEq' em (evalB_lit (by omega))]; simp [ind, hin]
            refine ⟨τ, (Run.ite_true c1 (Run.ite_false c2 Run.skip)).mono (by simp [sdE, rm]),
              hyk, hCv _ _ _ hCτ (by simp), hFr _ _ _ hFτ (by simp), haτ, by simp [hlτ],
              fun c hc => ?_, ?_⟩
            · simp only [arrs_setVar, hmτ c hc, hsucc, if_pos hsdk, insert_eq_of_mem hin]
            · simp only [vars_setVar, if_neg (show "h" ≠ "hy" by decide), hhτ, hsucc,
                if_pos hsdk, insert_eq_of_mem hin]
          · have c2 : (Cond.eq (.get "mark" (.get "lab" (.var "hy"))) (.lit 0)).evalB B τ =
                some true := by
              rw [evalB_condEq' em (evalB_lit (by omega))]; simp [ind, hin]
            refine ⟨(τ.setArr "mark" (L k) 1).setVar "h" ((hamT G L w s k).card + 1),
              (Run.ite_true c1 (Run.ite_true c2 (Run.seq
                (Run.store (a := "mark") (e := .lit 1) el (by simp; omega) (by rw [hlτ]; omega))
                (Run.assign (by simp [hhτ]; omega))))).mono (by simp [sdE, rm]),
              by simp [hyk], ?_⟩
            refine ⟨hCv _ _ _ (hCv _ _ _ (hCa _ _ _ hCτ) (by simp)) (by simp),
              hFr _ _ _ (hFr _ _ _ hFτ (by simp)) (by simp), fun a ha => by
                simp only [arrs_setVar, arrs_setArr, if_neg ha]; exact haτ a ha, by simp [hlτ],
                fun c hc => ?_, ?_⟩
            · simp only [arrs_setVar, arrs_setArr, if_true, hsucc, if_pos hsdk, List.getElem?_set]
              by_cases hcL : L k = c
              · subst hcL; simp [hlτ, hLk, ind]
              · rw [if_neg hcL, hmτ c hc]
                congr 1; rw [ind_eq_iff, mem_insert]
                exact ⟨fun h => Or.inr h, fun h => h.resolve_left (Ne.symm hcL)⟩
            · simp only [vars_setVar, if_neg (show "h" ≠ "hy" by decide), if_true, hsucc,
                if_pos hsdk, card_insert_of_notMem hin]
        · have c1 : (Cond.eq sdE (.lit 1)).evalB B τ = some false := by
            rw [evalB_condEq' hsd (evalB_lit (by omega))]; simp [ind, hsdk]
          refine ⟨τ, (Run.ite_false c1 Run.skip).mono (by simp [sdE, rm]), hyk, hCv _ _ _ hCτ (by simp),
            hFr _ _ _ hFτ (by simp), haτ, by simp [hlτ], fun c hc => ?_, ?_⟩
          · simp only [arrs_setVar, hmτ c hc, hsucc, if_neg hsdk]
          · simp only [vars_setVar, if_neg (show "h" ≠ "hy" by decide), hhτ, hsucc, if_neg hsdk])
  -- the count is the number of parts
  have hcount : (hamT G L w s n).card = hamN G L w s := by
    unfold hamN hamT
    congr 1
    refine filter_congr fun c hc => ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    obtain ⟨y, hy, -, rfl⟩ := h
    exact hL.idem y hy
  -- second loop
  let I2 : ℕ → Env → Prop := fun k τ => Ctx τ ∧ Fr τ ∧ τ.vars "h" = hamN G L w s ∧
    (∀ a, a ≠ "mark" → τ.arrs a = σ.arrs a) ∧ (τ.arrs "mark").length = n ∧
    (∀ c < n, (τ.arrs "mark")[c]? = some 0 ∨ ∃ y, k ≤ y ∧ y < n ∧ sdN G w s y ∧ L y = c)
  obtain ⟨σ2, hr2, ⟨hC2, hF2, hh2, ha2, hl2, hm2⟩, -⟩ :=
    forUp_run (B := B) (i := "hy") (e := .var "n") (body := hamB2) (N := n) (K := 100) I2
      (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
      (σ := σ1) ⟨hCv _ _ _ hC1 (by simp), hFr _ _ _ hF1 (by simp), by simp [hh1, hcount],
        fun a ha => by simp [ha1 a ha], by simp [hl1], fun c hc => by
          simp only [arrs_setVar, hm1 c hc]
          by_cases hmem : c ∈ hamT G L w s n
          · right
            obtain ⟨-, y, hy, h1, h2⟩ := mem_filter.1 hmem
            exact ⟨y, Nat.zero_le _, hy, h1, h2⟩
          · left; simp [ind, hmem]⟩
      (by
        rintro k hk τ ⟨hCτ, hFτ, hhτ, haτ, hlτ, hmτ⟩ hyk
        have hR := hC τ hCτ
        have hLk := hL.lt k hk
        have hsd := evalB_sdE (B := B) hR hB hFτ.1 hFτ.2.1 hyk hwn hsn hk
        have el : (Expr.get "lab" (.var "hy")).evalB B τ = some (L k) :=
          hR.hlab.evalB hyk hk (by omega) (by omega)
        by_cases hsdk : sdN G w s k
        · have c1 : (Cond.eq sdE (.lit 1)).evalB B τ = some true := by
            rw [evalB_condEq' hsd (evalB_lit (by omega))]; simp [ind, hsdk]
          refine ⟨τ.setArr "mark" (L k) 0, (Run.ite_true c1
            (Run.store (a := "mark") (e := .lit 0) el (by simp; omega)
              (by rw [hlτ]; omega))).mono (by simp [sdE, rm]), by simp [hyk], ?_⟩
          refine ⟨hCv _ _ _ (hCa _ _ _ hCτ) (by simp), hFr _ _ _ hFτ (by simp), by simp [hhτ],
            fun a ha => by simp only [arrs_setVar, arrs_setArr, if_neg ha]; exact haτ a ha,
            by simp [hlτ], fun c hc => ?_⟩
          simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
          by_cases hcL : L k = c
          · subst hcL; left; simp [hlτ, hLk]
          · rw [if_neg hcL]
            rcases hmτ c hc with h | ⟨y, hy1, hy2, hy3, hy4⟩
            · left; exact h
            · right
              refine ⟨y, ?_, hy2, hy3, hy4⟩
              rcases Nat.lt_or_ge y (k + 1) with h' | h'
              · have : y = k := by omega
                subst this; exact absurd hy4 hcL
              · exact h'
        · have c1 : (Cond.eq sdE (.lit 1)).evalB B τ = some false := by
            rw [evalB_condEq' hsd (evalB_lit (by omega))]; simp [ind, hsdk]
          refine ⟨τ, (Run.ite_false c1 Run.skip).mono (by simp [sdE, rm]), hyk, hCv _ _ _ hCτ (by simp),
            hFr _ _ _ hFτ (by simp), by simp [hhτ], haτ, by simp [hlτ], fun c hc => ?_⟩
          simp only [arrs_setVar]
          rcases hmτ c hc with h | ⟨y, hy1, hy2, hy3, hy4⟩
          · left; exact h
          · right
            refine ⟨y, ?_, hy2, hy3, hy4⟩
            rcases Nat.lt_or_ge y (k + 1) with h' | h'
            · have : y = k := by omega
              subst this; exact absurd hy3 hsdk
            · exact h')
  have hhB : hamN G L w s ≤ n := by rw [← hcount]; exact hTle n
  have e := evalB_ltX (B := B) (σ := σ2) (evalB_var (x := "t2") (by rw [ht2 σ2 hC2]; omega))
    (evalB_var (x := "h") (by rw [hh2]; omega)) (by rw [ht2 σ2 hC2]; omega)
    (by rw [hh2]; omega) (by omega)
  refine ⟨σ2.setVar "ok2" _, (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq hr1
    (Run.seq hr2 (Run.assign e)))).mono (by simp [hamB1, hamB2, sdE, rm]; nlinarith),
    hCv _ _ _ hC2 (by simp), by simp [hh2, ht2 σ2 hC2], ⟨by simp [hl2], fun c hc => ?_⟩,
    fun a ha => by simp [ha2 a ha], fun x hx => ?_⟩
  · simp only [arrs_setVar]
    rcases hm2 c hc with h | ⟨y, hy1, hy2, -⟩
    · exact h
    · omega
  · have : x ≠ "ok2" := by intro e; subst e; simp at hx
    simp only [vars_setVar, if_neg this]
    exact (hF2.2.2 x hx)

end Lax185574Proofs.Chain.Ram
