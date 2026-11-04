import Lax185574Proofs.Chain.Ram.PdLoop
import Lax185574Proofs.Chain.Algorithm

/-!
The damping step.

`dampCom` computes `damp G r o q A` into `inS` (with its size in `sc`),
for the set `A` in `inA` with its size in `ca`. If `|A| ≥ 6(q+1)` it
runs the predamping procedure for `κ = 1, 2, …, n` until
`q |S| ≤ |A|` (`kf` is set), and clears `inS` if no `κ` passes.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-! ### The first `κ` -/

theorem firstFrom_eq_some_of {p : ℕ → Bool} {k f a : ℕ} (hka : k ≤ a) (haf : a < k + f)
    (hp : p a) (hmin : ∀ b, k ≤ b → b < a → p b = false) : firstFrom p k f = some a := by
  obtain ⟨a', ha'⟩ := firstFrom_isSome (p := p) hka haf hp
  obtain ⟨h1, h2, h3⟩ := firstFrom_some ha'
  rw [ha']
  congr 1
  rcases lt_trichotomy a' a with h | h | h
  · have := hmin a' h2 h; rw [h1] at this; exact absurd this (by simp)
  · exact h
  · have := h3 a hka h; rw [hp] at this; exact absurd this (by simp)

theorem firstFrom_eq_none_of {p : ℕ → Bool} {k f : ℕ} (h : ∀ b, k ≤ b → b < k + f → p b = false) :
    firstFrom p k f = none := by
  cases hf : firstFrom p k f with
  | none => rfl
  | some a =>
    obtain ⟨h1, h2, -⟩ := firstFrom_some hf
    have := firstFrom_lt hf
    rw [h a h2 this] at h1
    exact absurd h1 (by simp)

/-! ### The thresholds -/

theorem PdFix.setThr {r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ} {t1 t2 t3 : ℕ} {τ : Env}
    (h : PdFix n r G A pf t1 t2 t3 τ) (u1 u2 u3 : ℕ) :
    PdFix n r G A pf u1 u2 u3 (((τ.setVar "t1" u1).setVar "t2" u2).setVar "t3" u3) :=
  ⟨by simp [h.hn], by simp [h.hM], by simp [h.htr], by simp, by simp, by simp,
    h.hadj.of_eq rfl, h.hpos.of_eq rfl, h.hinA.of_eq rfl, fun a ha => by simpa using h.lvec a ha,
    by simpa using h.ltab, by simpa using h.lcnt⟩

/-- Clearing an array of length `n` that is not fixed. -/
theorem zeroFill_run {B' r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ} {t1 t2 t3 : ℕ} (hnB : n < B')
    {arr : String} (harr : arr ∉ fixArrs) {σ : Env} (hF : PdFix n r G A pf t1 t2 t3 σ)
    (hl : (σ.arrs arr).length = n) :
    ∃ σ', Run B' (rowFill arr (.var "b") (.lit 0)) σ σ' (n * 11 + 6) ∧
      PdFix n r G A pf t1 t2 t3 σ' ∧ (∀ a, a ≠ arr → σ'.arrs a = σ.arrs a) ∧
      Vec σ' arr n (fun _ => 0) ∧ (∀ x, x ≠ "b" → σ'.vars x = σ.vars x) := by
  obtain ⟨σ', hr, ⟨hF', hk, hv⟩, hl', hg'⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := 3) (arr := arr) (ie := .var "b")
      (e := .lit 0) (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ (∀ a, a ≠ arr → τ.arrs a = σ.arrs a) ∧
        ∀ x, x ≠ "b" → τ.vars x = σ.vars x) (fun _ => 0) hnB (fun τ h => h.1.hn)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, fun a ha => by simpa using h.2.1 a ha,
        fun y hy => by simp [hy, h.2.2 y hy]⟩)
      (fun τ i x h => ⟨h.1.setArr harr _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2.1 a ha, fun y hy => by simp [h.2.2 y hy]⟩)
      (fun τ k h hb hk => by simp [hb]; omega) (fun τ k h hb hk => by simp; omega) (by simp)
      ⟨hF, fun _ _ => rfl, fun _ _ => rfl⟩ (by omega)
  exact ⟨σ', hr.mono (by simp), hF', hk, ⟨by rw [hl', hl], fun u hu => by rw [hg' u]; simp [hu]⟩,
    hv⟩

theorem ptrPot_zero {pa : String} {τ : Env} (h : Vec τ pa n (fun _ => 0)) :
    ptrPot n pa τ = n * n := by
  unfold ptrPot
  rw [sum_congr rfl (g := fun _ => n) fun w hw => by
    rw [List.getD_eq_getElem?_getD, h.get w (mem_range.1 hw)]; simp]
  simp

/-! ### One `κ` -/

/-- `3 (q + 1)`. -/
def q3E : Expr := .mul (.lit 3) (.add (.var "q") (.lit 1))

/-- The thresholds for `κ` in `kp`. -/
def setThr : Com :=
  .seq (.assign "t1" (.mul q3E (.var "kp")))
    (.seq (.assign "t2" (.mul (.mul (.mul (.lit 5) q3E) (.var "kp")) (.var "kp")))
      (.assign "t3" (.mul (.mul (.lit 2) q3E) (.var "kp"))))

/-- Start with `S = ∅` and pointers zero. -/
def resetS : Com :=
  .seq (rowFill "inS" (.var "b") (.lit 0)) (.seq (rowFill "p2" (.var "b") (.lit 0))
    (.seq (rowFill "p3" (.var "b") (.lit 0)) (.assign "sc" (.lit 0))))

/-- The test `q |S| ≤ |A|`. -/
def testK : Com :=
  .ite (.lt (.var "ca") (.mul (.var "q") (.var "sc"))) (.assign "kp" (.add (.var "kp") (.lit 1)))
    (.assign "kf" (.lit 1))

/-- One `κ`. -/
def kapBody : Com := .seq (.seq setThr resetS) (.seq pdLoop testK)

/-- The cost of one `κ`. -/
def kapCost (n r : ℕ) : ℕ := (n + 2) * (appCost n r + 20) + (n * 400 + 160) * (n * n) + n * 50 + 200

/-- The state between two values of `κ`: the fixed state for some
thresholds, and the scratch arrays zero. -/
structure DampSt (n r : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (pf : ℕ → ℕ) (q : ℕ)
    (τ : Env) : Prop where
  fix : ∃ t1 t2 t3, PdFix n r G A pf t1 t2 t3 τ
  hq : τ.vars "q" = q
  hca : τ.vars "ca" = A.card
  ztab : Zero τ "tab"
  zcnt : Mat τ "cnt" n (fun _ _ => 0)
  zsz : Vec τ "sz" n (fun _ => 0)
  zmark : Vec τ "mark" n (fun _ => 0)

/-- The bound on values of the damping step. -/
def DampBound (n B' : ℕ) : Prop := PdBound n B' ∧ 15 * (n + 3) * (n + 1) * (n + 1) < B'

variable {r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ}

/-- The test of `κ`. -/
noncomputable def accK (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) (o : VOrder (Fin n))
    (q : ℕ) (A : Finset (Fin n)) (κ : ℕ) : Bool :=
  decide (q * (predamp G (fun B => tpRel G B r) o A q κ).card ≤ A.card)

theorem kapPrep_run {B' : ℕ} (hB' : DampBound n B') (hrB : r < B') (o : VOrder (Fin n))
    (hpfo : pf = posN o) {q κ : ℕ} (hq : q ≤ n + 1) (hκ1 : 1 ≤ κ) (hκn : κ ≤ n) {σ : Env}
    (hst : DampSt n r G A pf q σ) (hkp : σ.vars "kp" = κ) (hkf : σ.vars "kf" = 0) :
    ∃ σ', Run B' (.seq setThr resetS) σ σ' (n * 33 + 80) ∧
      PdSt n r G A pf (3 * (q + 1) * κ) (5 * (3 * (q + 1)) * κ * κ) (2 * (3 * (q + 1)) * κ) ∅
        (fun _ => 0) σ' ∧
      pdPot n σ' = (n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n) ∧
      (∀ x, x ∉ ["t1", "t2", "t3", "b", "sc"] → σ'.vars x = σ.vars x) ∧
      3 * (q + 1) * κ < B' ∧ 5 * (3 * (q + 1)) * κ * κ < B' ∧ 2 * (3 * (q + 1)) * κ < B' := by
  obtain ⟨hB1, hB2⟩ := hB'
  have hB1' := hB1
  unfold PdBound at hB1'
  obtain ⟨⟨t1, t2, t3, hF⟩, hqv, hcav, hz, hcnt, hsz, hmark⟩ := hst
  -- the thresholds
  set u1 := 3 * (q + 1) * κ with hu1
  set u2 := 5 * (3 * (q + 1)) * κ * κ with hu2
  set u3 := 2 * (3 * (q + 1)) * κ with hu3
  have hκκ : κ * κ ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hu2B : u2 < B' := by
    have : u2 = 15 * (q + 1) * (κ * κ) := by rw [hu2]; ring
    rw [this]
    calc 15 * (q + 1) * (κ * κ) ≤ 15 * (n + 3) * ((n + 1) * (n + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hκκ
      _ < B' := by nlinarith
  have hu1B : u1 ≤ u2 := by
    rw [hu1, hu2]
    have : 3 * (q + 1) * κ ≤ 3 * (q + 1) * κ * κ := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have hu3B : u3 ≤ u2 := by
    rw [hu3, hu2]
    have : 2 * (3 * (q + 1)) * κ ≤ 5 * (3 * (q + 1)) * κ := by nlinarith
    have : 5 * (3 * (q + 1)) * κ ≤ 5 * (3 * (q + 1)) * κ * κ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hq3 : ∀ τ : Env, τ.vars "q" = q → (q3E).evalB B' τ = some (3 * (q + 1)) := by
    intro τ hτ
    simp only [q3E, evalB_bin_iff, evalB_lit_iff, evalB_var_iff, hτ]
    refine ⟨3, q + 1, ⟨rfl, by omega⟩, ⟨q, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩,
      rfl, by nlinarith⟩
  have hkB : κ < B' := by omega
  set σ1 := ((σ.setVar "t1" u1).setVar "t2" u2).setVar "t3" u3 with hσ1
  have hr1 : Run B' setThr σ σ1 60 := by
    have e1 : (Expr.mul q3E (.var "kp")).evalB B' σ = some u1 := by
      have := evalB_bin (op := .mul) (hq3 σ hqv) (evalB_var (x := "kp") (σ := σ) (B := B')
        (by rw [hkp]; omega)) (by simp [hkp]; rw [← hu1]; omega)
      simpa [hkp, hu1] using this
    have e2 : (Expr.mul (.mul (.mul (.lit 5) q3E) (.var "kp")) (.var "kp")).evalB B'
        (σ.setVar "t1" u1) = some u2 := by
      have h5 := evalB_bin (op := .mul) (evalB_lit (n := 5) (σ := σ.setVar "t1" u1) (B := B')
        (by omega)) (hq3 _ (by simp [hqv])) (by simp; nlinarith)
      have h6 := evalB_bin (op := .mul) h5 (evalB_var (x := "kp") (σ := σ.setVar "t1" u1)
        (B := B') (by simp [hkp]; omega)) (by
          simp [hkp]
          have : 5 * (3 * (q + 1)) * κ ≤ u2 := by rw [hu2]; exact Nat.le_mul_of_pos_right _ (by omega)
          omega)
      have h7 := evalB_bin (op := .mul) h6 (evalB_var (x := "kp") (σ := σ.setVar "t1" u1)
        (B := B') (by simp [hkp]; omega)) (by simp [hkp]; rw [← hu2]; omega)
      simpa [hkp, hu2] using h7
    have e3 : (Expr.mul (.mul (.lit 2) q3E) (.var "kp")).evalB B'
        ((σ.setVar "t1" u1).setVar "t2" u2) = some u3 := by
      have h5 := evalB_bin (op := .mul) (evalB_lit (n := 2)
        (σ := (σ.setVar "t1" u1).setVar "t2" u2) (B := B') (by omega)) (hq3 _ (by simp [hqv]))
        (by simp; nlinarith)
      have h6 := evalB_bin (op := .mul) h5 (evalB_var (x := "kp")
        (σ := (σ.setVar "t1" u1).setVar "t2" u2) (B := B') (by simp [hkp]; omega))
        (by simp [hkp]; rw [← hu3]; omega)
      simpa [hkp, hu3] using h6
    exact (Run.seq (Run.assign e1) (Run.seq (Run.assign e2) (Run.assign e3))).mono
      (by simp [q3E])
  have hF1 : PdFix n r G A pf u1 u2 u3 σ1 := hF.setThr u1 u2 u3
  -- reset
  obtain ⟨σ2, hr2, hF2, hk2, hv2, hx2⟩ :=
    zeroFill_run (B' := B') (arr := "inS") (by omega) (by decide) hF1 (hF1.lvec "inS" (by simp))
  obtain ⟨σ3, hr3, hF3, hk3, hv3, hx3⟩ :=
    zeroFill_run (B' := B') (arr := "p2") (by omega) (by decide) hF2 (hF2.lvec "p2" (by simp))
  obtain ⟨σ4, hr4, hF4, hk4, hv4, hx4⟩ :=
    zeroFill_run (B' := B') (arr := "p3") (by omega) (by decide) hF3 (hF3.lvec "p3" (by simp))
  set σ5 := σ4.setVar "sc" 0 with hσ5
  have hr5 : Run B' resetS σ1 σ5 (3 * (n * 11 + 6) + 2) :=
    (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.assign (v := 0) (by simp; omega))))).mono
      (by simp; omega)
  have hk5 : ∀ a, a ∉ ["inS", "p2", "p3"] → σ5.arrs a = σ.arrs a := fun a ha => by
    simp at ha
    simp only [hσ5, arrs_setVar]
    rw [hk4 a ha.2.2, hk3 a ha.2.1, hk2 a ha.1]; rfl
  have hp2 : ∀ w < n, (σ5.arrs "p2").getD w 0 = 0 := fun w hw => by
    simp only [hσ5, arrs_setVar, hk4 "p2" (by decide)]
    rw [List.getD_eq_getElem?_getD, hv3.get w hw]; simp
  have hp3 : ∀ w < n, (σ5.arrs "p3").getD w 0 = 0 := fun w hw => by
    simp only [hσ5, arrs_setVar]
    rw [List.getD_eq_getElem?_getD, hv4.get w hw]; simp
  have hst5 : PdSt n r G A pf u1 u2 u3 ∅ (fun _ => 0) σ5 := by
    refine ⟨hF4.setVar (by simp [fixVars]) _, ⟨by
        simp only [hσ5, arrs_setVar]; exact hF4.lvec "inS" (by simp), fun u hu => ?_⟩,
      by simpa using (SlOK.empty (n := n)), by simp [hσ5],
      fun j hj => absurd hj (by simp),
      fun w hw => ⟨by show (σ5.arrs "p2").getD w 0 ≤ _; rw [hp2 w hw]; simp,
        fun j hj => by
          have : j < (σ5.arrs "p2").getD w 0 := hj
          rw [hp2 w hw] at this; omega⟩,
      fun w hw => ⟨by show (σ5.arrs "p3").getD w 0 ≤ _; rw [hp3 w hw]; simp,
        fun j hj => by
          have : j < (σ5.arrs "p3").getD w 0 := hj
          rw [hp3 w hw] at this; omega⟩,
      fun t ht => by rw [hk5 "tab" (by decide)] at ht ⊢; exact hz t ht,
      hcnt.of_eq (hk5 _ (by decide)), hsz.of_eq (hk5 _ (by decide)),
      hmark.of_eq (hk5 _ (by decide))⟩
    · simp only [hσ5, arrs_setVar, hk4 "inS" (by decide), hk3 "inS" (by decide), hv2.get u hu]
      simp [ind, inBN]
  have hpot5 : pdPot n σ5 = (n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n) := by
    unfold pdPot
    rw [ptrPot_zero (pa := "p2") ⟨by simp [hσ5, hk4 "p2" (by decide), hv3.len], fun w hw => by
        simp only [hσ5, arrs_setVar, hk4 "p2" (by decide)]; exact hv3.get w hw⟩,
      ptrPot_zero (pa := "p3") (hv4.of_eq (by simp [hσ5]))]
  refine ⟨σ5, (Run.seq hr1 hr5).mono (by omega), hst5, hpot5, fun x hx => ?_, by omega, hu2B,
    by omega⟩
  simp at hx
  simp only [hσ5, vars_setVar, if_neg hx.2.2.2.2]
  rw [hx4 x hx.2.2.2.1, hx3 x hx.2.2.2.1, hx2 x hx.2.2.2.1]
  simp [hσ1, hx.1, hx.2.1, hx.2.2.1]

theorem kapBody_run {B' : ℕ} (hB' : DampBound n B') (hrB : r < B') (o : VOrder (Fin n))
    (hpfo : pf = posN o) {q κ : ℕ} (hq : q ≤ n + 1) (hκ1 : 1 ≤ κ) (hκn : κ ≤ n) {σ : Env}
    (hst : DampSt n r G A pf q σ) (hkp : σ.vars "kp" = κ) (hkf : σ.vars "kf" = 0) :
    ∃ σ', Run B' kapBody σ σ' (kapCost n r) ∧ DampSt n r G A pf q σ' ∧
      Vec σ' "inS" n (fun u => ind (inBN (predamp G (fun B => tpRel G B r) o A q κ) u)) ∧
      σ'.vars "sc" = (predamp G (fun B => tpRel G B r) o A q κ).card ∧
      (accK G r o q A κ = true → σ'.vars "kf" = 1 ∧ σ'.vars "kp" = κ) ∧
      (accK G r o q A κ = false → σ'.vars "kf" = 0 ∧ σ'.vars "kp" = κ + 1) ∧
      (∀ x, x ∉ kapBody.wvars → σ'.vars x = σ.vars x) := by
  obtain ⟨σ5, hr5, hst5, hpot5, hx5, ht1B, hu2B, ht3B⟩ :=
    kapPrep_run hB' hrB o hpfo hq hκ1 hκn hst hkp hkf
  have hB1 := hB'.1
  have hB1' := hB1
  unfold PdBound at hB1'
  have hqv := hst.hq
  have hcav := hst.hca
  -- the procedure
  obtain ⟨σ6, K6, sl6, hr6, hst6, hK6, hx6, ha6⟩ :=
    pdLoop_run hB1 hrB ht1B hu2B ht3B o hpfo q κ hκ1 rfl rfl rfl hst5
  set S := predamp G (tpP G r) o A q κ with hSdef
  clear_value S
  have hscn : S.card ≤ n := by have := card_le_univ S; simpa using this
  -- the scalars kept
  have hkeep : ∀ x, x ∈ ["q", "ca", "kp", "kf"] → σ6.vars x = σ.vars x := by
    intro x hx
    have h1 : x ∉ pdLoop.wvars := by
      simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide
    have h2 : x ∉ ["t1", "t2", "t3", "b", "sc"] := by
      simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide
    rw [hx6 x h1, hx5 x h2]
  have hq6 : σ6.vars "q" = q := by rw [hkeep "q" (by simp), hqv]
  have hca6 : σ6.vars "ca" = A.card := by rw [hkeep "ca" (by simp), hcav]
  have hkp6 : σ6.vars "kp" = κ := by rw [hkeep "kp" (by simp), hkp]
  have hkf6 : σ6.vars "kf" = 0 := by rw [hkeep "kf" (by simp), hkf]
  have hsc6 := hst6.sc
  have hqs : q * S.card < B' := by
    have h1 : q * S.card ≤ (n + 1) * n := Nat.mul_le_mul hq hscn
    have h2 : (n + 1) * n ≤ n * (n + 4) + 3 * n + 10 := by nlinarith
    omega
  have hcond : (Cond.lt (.var "ca") (.mul (.var "q") (.var "sc"))).evalB B' σ6 =
      some (decide (A.card < q * S.card)) := by
    have hAn : A.card ≤ n := by have := card_le_univ A; simpa using this
    rw [evalB_condLt (evalB_var (by rw [hca6]; omega)) (evalB_bin (op := .mul)
      (evalB_var (by rw [hq6]; omega)) (evalB_var (by rw [hsc6]; omega)) (by
        simp [hq6, hsc6]; omega))]
    simp [hca6, hq6, hsc6]
  have hacc : accK G r o q A κ = decide (q * S.card ≤ A.card) := by rw [hSdef]; rfl
  have hDst : ∀ τ, PdSt n r G A pf (3 * (q + 1) * κ) (5 * (3 * (q + 1)) * κ * κ)
      (2 * (3 * (q + 1)) * κ) S sl6 τ → τ.vars "q" = q → τ.vars "ca" = A.card →
      DampSt n r G A pf q τ := fun τ h h1 h2 =>
    ⟨⟨_, _, _, h.fix⟩, h1, h2, h.ztab, h.zcnt, h.zsz, h.zmark⟩
  by_cases hlt : A.card < q * S.card
  · have hrt : Run B' testK σ6 (σ6.setVar "kp" (κ + 1)) 14 :=
      (Run.ite_true (by rw [hcond]; simp [hlt]) (Run.assign (v := κ + 1)
        (by simp [hkp6]; omega))).mono (by simp)
    have hrun : Run B' kapBody σ (σ6.setVar "kp" (κ + 1)) (kapCost n r) := by
      have := Run.seq hr5 (Run.seq (hr6.mono (show K6 ≤ (n + 2) * (appCost n r + 20) + 10 +
        ((n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n)) by rw [← hpot5]; omega)) hrt)
      exact this.mono (by
        have hX : (n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n) ≤ (n * 400 + 160) * (n * n) := by
          rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
        simp only [kapCost]
        generalize appCost n r = a at *
        generalize (n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n) = X at *
        omega)
    have hst7 : PdSt n r G A pf (3 * (q + 1) * κ) (5 * (3 * (q + 1)) * κ * κ)
        (2 * (3 * (q + 1)) * κ) S sl6 (σ6.setVar "kp" (κ + 1)) := by
      obtain ⟨hF', hS', hsl', hsc', hsl2', hP2', hP3', hz', hc', hs', hm'⟩ := hst6
      exact ⟨hF'.setVar (by simp [fixVars]) _, hS'.of_eq rfl, hsl', by simp [hsc'], hsl2', hP2',
        hP3', hz', hc'.of_eq rfl, hs'.of_eq rfl, hm'.of_eq rfl⟩
    refine ⟨_, hrun, hDst _ hst7 (by simp [hq6]) (by simp [hca6]), by rw [show predamp G (fun B => tpRel G B r) o A q κ = S from hSdef.symm]; exact hst6.inS.of_eq rfl,
      by rw [show predamp G (fun B => tpRel G B r) o A q κ = S from hSdef.symm]; simp [hsc6], fun h => ?_, fun _ => ⟨by simp [hkf6], by simp⟩,
      fun x hx => hrun.frame_var x hx⟩
    rw [hacc] at h; simp at h; omega
  · have hrt : Run B' testK σ6 (σ6.setVar "kf" 1) 14 :=
      (Run.ite_false (by rw [hcond]; simp [hlt]) (Run.assign (v := 1)
        (by simp; omega))).mono (by simp)
    have hrun : Run B' kapBody σ (σ6.setVar "kf" 1) (kapCost n r) := by
      have := Run.seq hr5 (Run.seq (hr6.mono (show K6 ≤ (n + 2) * (appCost n r + 20) + 10 +
        ((n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n)) by rw [← hpot5]; omega)) hrt)
      exact this.mono (by
        have hX : (n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n) ≤ (n * 400 + 160) * (n * n) := by
          rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
        simp only [kapCost]
        generalize appCost n r = a at *
        generalize (n * 300 + 80) * (n * n) + (n * 80 + 80) * (n * n) = X at *
        omega)
    have hst7 : PdSt n r G A pf (3 * (q + 1) * κ) (5 * (3 * (q + 1)) * κ * κ)
        (2 * (3 * (q + 1)) * κ) S sl6 (σ6.setVar "kf" 1) := by
      obtain ⟨hF', hS', hsl', hsc', hsl2', hP2', hP3', hz', hc', hs', hm'⟩ := hst6
      exact ⟨hF'.setVar (by simp [fixVars]) _, hS'.of_eq rfl, hsl', by simp [hsc'], hsl2', hP2',
        hP3', hz', hc'.of_eq rfl, hs'.of_eq rfl, hm'.of_eq rfl⟩
    refine ⟨_, hrun, hDst _ hst7 (by simp [hq6]) (by simp [hca6]), by rw [show predamp G (fun B => tpRel G B r) o A q κ = S from hSdef.symm]; exact hst6.inS.of_eq rfl,
      by rw [show predamp G (fun B => tpRel G B r) o A q κ = S from hSdef.symm]; simp [hsc6], fun _ => ⟨by simp, by simp [hkp6]⟩, fun h => ?_,
      fun x hx => hrun.frame_var x hx⟩
    rw [hacc] at h; simp at h; omega

end Lax185574Proofs.Chain.Ram
