import Lax185574Proofs.FarRam.ScanCount


/-!
The selection of the entries of the scatter type: `scanSel` stores in
`sel[i]` whether entry `i` is selected (`selW`).
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

theorem ite_or_run {B : ℕ} {c : Cond} {d₁ d₂ : Com} {σ τ : Env} {x : String} {b b' : Bool} {K₁ K₂ : ℕ}
    (hc : c.evalB B τ = some b) (h₁ : Run B d₁ τ (σ.setVar x 1) K₁)
    (h₂ : Run B d₂ τ (σ.setVar x (bv b')) K₂) :
    Run B (.ite c d₁ d₂) τ (σ.setVar x (bv (b || b'))) (1 + c.size + K₁ + K₂) := by
  cases b
  · exact (Run.ite_false hc h₂).mono (by omega)
  · exact (Run.ite_true hc h₁).mono (by omega)

theorem ite_and_run {B : ℕ} {c : Cond} {d : Com} {σ : Env} {x : String} {b b' : Bool} {K : ℕ}
    (hc : c.evalB B (σ.setVar x 0) = some b) (h : Run B d (σ.setVar x 0) (σ.setVar x (bv b')) K) :
    Run B (.ite c d .skip) (σ.setVar x 0) (σ.setVar x (bv (b && b'))) (2 + c.size + K) := by
  cases b
  · exact (Run.ite_false hc Run.skip).mono (by omega)
  · exact (Run.ite_true hc h).mono (by omega)

def hdrSel : Com :=
  .seq (.assign "sv" (.lit 0))
    (.ite (.eq (.get "a" (.var "zo")) (.mul (.lit 4) (.var "rho")))
      (.ite (.eq (.get "a" (.add (.var "zo") (.lit 1))) (.add (.var "hk") (.lit 1)))
        (.ite (.eq (.get "a" (.add (.var "zo") (.lit 2))) (.sub (.var "hq") (.lit 1)))
          (.ite (.eq (.var "zn") (.lit 1)) (.assign "sv" (.lit 1))
            (.ite (.lt (.var "zk") (.get "a" (.sub (.add (.var "zo") (.var "zl")) (.lit 1))))
              (.assign "sv" (.lit 1)) .skip)) .skip) .skip) .skip)

theorem hdrSel_run (B : ℕ) (σ : Env) (w : List ℕ) (o k q ρ : ℕ) (bn : Bool) (cnt : ℕ)
    (h3 : 3 ≤ w.length) (ha : ∀ j < w.length, (σ.arrs "a")[o + j]? = some (xg w j))
    (hw : ∀ j, xg w j < B) (ho : o + w.length < B) (hρ : 4 * ρ < B) (hk : k + 2 < B) (hq : q + 2 < B)
    (hcnt : cnt < B) (h9 : 9 < B) (hzo : σ.vars "zo" = o) (hzl : σ.vars "zl" = w.length) (hrho : σ.vars "rho" = ρ)
    (hhk : σ.vars "hk" = k) (hhq : σ.vars "hq" = q + 1) (hzn : σ.vars "zn" = bv bn)
    (hzk : σ.vars "zk" = cnt) :
    Run B hdrSel σ (σ.setVar "sv" (bv ((xg w 0 == 4 * ρ) && (xg w 1 == k + 1) && (xg w 2 == q) &&
      (bn || decide (cnt < xg w (w.length - 1)))))) 120 := by
  set τ := σ.setVar "sv" 0
  have hv : ∀ z, z ≠ "sv" → τ.vars z = σ.vars z := fun z hz => by simp [τ, hz]
  have hget : ∀ (ie : Expr) (j : ℕ), j < w.length → ie.evalB B τ = some (o + j) →
      (Expr.get "a" ie).evalB B τ = some (xg w j) := fun ie j hj hie => by
    simp only [evalB_get_iff]; exact ⟨o + j, hie, by simpa [τ] using ha j hj, hw j⟩
  have hzoE : (Expr.var "zo").evalB B τ = some o := by
    rw [← hzo, ← hv "zo" (by decide)]; exact evalB_var (by rw [hv "zo" (by decide), hzo]; omega)
  have c1 : (Cond.eq (.get "a" (.var "zo")) (.mul (.lit 4) (.var "rho"))).evalB B τ =
      some (xg w 0 == 4 * ρ) := by
    refine evalB_condEq (hget _ 0 (by omega) (by simpa using hzoE)) ?_
    simp only [evalB_bin_iff, evalB_lit_iff, evalB_var_iff]
    exact ⟨4, ρ, ⟨rfl, by omega⟩, ⟨by rw [hv "rho" (by decide), hrho], by rw [hv "rho" (by decide), hrho]; omega⟩,
      rfl, by omega⟩
  have c2 : (Cond.eq (.get "a" (.add (.var "zo") (.lit 1))) (.add (.var "hk") (.lit 1))).evalB B τ =
      some (xg w 1 == k + 1) := by
    refine evalB_condEq (hget _ 1 (by omega) ?_) ?_
    · simp only [evalB_bin_iff, evalB_lit_iff]; exact ⟨o, 1, hzoE, ⟨rfl, by omega⟩, rfl, by omega⟩
    · simp only [evalB_bin_iff, evalB_lit_iff, evalB_var_iff]
      exact ⟨k, 1, ⟨by rw [hv "hk" (by decide), hhk], by rw [hv "hk" (by decide), hhk]; omega⟩,
        ⟨rfl, by omega⟩, rfl, by omega⟩
  have c3 : (Cond.eq (.get "a" (.add (.var "zo") (.lit 2))) (.sub (.var "hq") (.lit 1))).evalB B τ =
      some (xg w 2 == q) := by
    refine evalB_condEq (hget _ 2 (by omega) ?_) ?_
    · simp only [evalB_bin_iff, evalB_lit_iff]; exact ⟨o, 2, hzoE, ⟨rfl, by omega⟩, rfl, by omega⟩
    · simp only [evalB_bin_iff, evalB_lit_iff, evalB_var_iff]
      exact ⟨q + 1, 1, ⟨by rw [hv "hq" (by decide), hhq], by rw [hv "hq" (by decide), hhq]; omega⟩,
        ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
  have c4 : (Cond.eq (.var "zn") (.lit 1)).evalB B τ = some bn := by
    rw [eq_true_iff' (by rw [hv "zn" (by decide), hzn]; have := bv_le bn; omega) (by omega),
      hv "zn" (by decide), hzn]
    cases bn <;> rfl
  have c5 : (Cond.lt (.var "zk") (.get "a" (.sub (.add (.var "zo") (.var "zl")) (.lit 1)))).evalB B τ =
      some (decide (cnt < xg w (w.length - 1))) := by
    refine evalB_condLt ?_ (hget _ (w.length - 1) (by omega) ?_)
    · rw [← hzk, ← hv "zk" (by decide)]; exact evalB_var (by rw [hv "zk" (by decide), hzk]; exact hcnt)
    · have hzlE : (Expr.var "zl").evalB B τ = some w.length := by
        rw [← hzl, ← hv "zl" (by decide)]; exact evalB_var (by rw [hv "zl" (by decide), hzl]; omega)
      simp only [evalB_bin_iff, evalB_lit_iff]
      exact ⟨o + w.length, 1, ⟨o, w.length, hzoE, hzlE, rfl, by omega⟩, ⟨rfl, by omega⟩,
        by simp [Bop.apply]; omega, by omega⟩
  have hτ1 : τ.setVar "sv" 1 = σ.setVar "sv" 1 := setVar_setVar _ _ _ _
  have r5 : Run B (.ite (.lt (.var "zk") (.get "a" (.sub (.add (.var "zo") (.var "zl")) (.lit 1))))
      (.assign "sv" (.lit 1)) .skip) τ (σ.setVar "sv" (bv (decide (cnt < xg w (w.length - 1))))) 40 :=
    (ite_and_run (b' := true) c5 ((Run.assign (evalB_lit (by omega))).congr hτ1)).mono (by simp) |>.congr
      (by simp)
  have r4 := ite_or_run c4 ((Run.assign (evalB_lit (by omega))).congr hτ1) r5
  have r3 := ite_and_run c3 r4
  have r2 := ite_and_run c2 r3
  have r1 := ite_and_run c1 r2
  unfold hdrSel
  refine (Run.seq (Run.assign (evalB_lit (by omega))) r1).mono ?_ |>.congr (by simp [Bool.and_assoc])
  simp

def selBody : Com :=
  .seq eqFill (.seq inNC (.seq cntC (.seq (.assign "zo" (.get "st" (.var "zs")))
    (.seq (.assign "zl" (.get "ln" (.var "zs"))) (.seq hdrSel (.store "sel" (.var "zs") (.var "sv")))))))

def scanSel : Com := forUp "zs" (.var "ns") selBody

/-- The facts the scan keeps, besides the words. -/
def SelRest (X : List ℕ) (nS R r ℓ s k q ρ : ℕ) (τ : Env) : Prop :=
  Rows X r ℓ R τ ∧ BtAt X ℓ s ℓ τ ∧ τ.vars "hl" = ℓ ∧ τ.vars "rho" = ρ ∧ τ.vars "hk" = k ∧
    τ.vars "hq" = q + 1 ∧ nS ≤ (τ.arrs "sel").length

theorem stable_selRest {c : Com} (X : List ℕ) (nS R r ℓ s k q ρ : ℕ)
    (ha : ∀ a ∈ ["mt", "far", "bt"], a ∉ c.warrs) (hv : ∀ z ∈ ["hl", "rho", "hk", "hq"], z ∉ c.wvars) :
    Stable (SelRest X nS R r ℓ s k q ρ) c :=
  (stable_rows X r ℓ R (ha "mt" (by simp)) (ha "far" (by simp))).and
    ((stable_btAt X ℓ s ℓ (ha "bt" (by simp))).and ((stable_var "hl" ℓ (hv "hl" (by simp))).and
      ((stable_var "rho" ρ (hv "rho" (by simp))).and ((stable_var "hk" k (hv "hk" (by simp))).and
        ((stable_var "hq" (q + 1) (hv "hq" (by simp))).and (stable_len "sel" nS))))))

/-- The selection bits below `i`. -/
def SelAt (X : List ℕ) (W : List (List ℕ)) (nS k q r ρ ℓ s i : ℕ) (τ : Env) : Prop :=
  ∀ j < i, (τ.arrs "sel")[j]? = some (bv (selW X (W.drop nS) k q r ρ ℓ (canonW X s ℓ) (wd W j)))

theorem stable_selAt {c : Com} (X : List ℕ) (W : List (List ℕ)) (nS k q r ρ ℓ s i : ℕ)
    (ha : "sel" ∉ c.warrs) : Stable (SelAt X W nS k q r ρ ℓ s i) c :=
  fun τ τ' _ h2 _ _ _ h => by rw [SelAt, h2 "sel" ha]; exact h

def selCost (w : List ℕ) (ℓ R : ℕ) : ℕ :=
  R * (eqCost w + 10) + 10 + (R * 40 + 10) + cntCost ℓ R + 160

theorem selBody_spec (B : ℕ) (X : List ℕ) (W : List (List ℕ)) (nS R r ℓ s k q ρ i : ℕ)
    (C : Env → Prop) (hC : Stable C selBody) (hb : WordsBound B W) (hi : i < nS)
    (h3 : ∀ j < nS, 3 ≤ (wd W j).length) (hRB : R * ℓ + ℓ + nS + R + 2 < B) (hρ : 4 * ρ < B)
    (hk : k + 2 < B) (hq : q + 2 < B) (h9 : 9 < B) :
    Spec B (fun τ => C τ ∧ ScanFix W nS R τ ∧ SelRest X nS R r ℓ s k q ρ τ ∧
        SelAt X W nS k q r ρ ℓ s i τ ∧ τ.vars "zs" = i) selBody
      (fun _ τ' => C τ' ∧ ScanFix W nS R τ' ∧ SelRest X nS R r ℓ s k q ρ τ' ∧
        SelAt X W nS k q r ρ ℓ s (i + 1) τ' ∧ τ'.vars "zs" = i) (selCost (wd W i) ℓ R) := by
  rintro σ ⟨hCσ, hF, hR, hS, hzs⟩
  let C1 : Env → Prop := fun ρ' => C ρ' ∧ SelRest X nS R r ℓ s k q ρ ρ' ∧ SelAt X W nS k q r ρ ℓ s i ρ'
  have hS1 : ∀ c : Com, (∀ z ∈ c.wvars, z ∈ selBody.wvars) → (∀ a ∈ c.warrs, a ∈ selBody.warrs) →
      (∀ a ∈ ["mt", "far", "bt", "sel"], a ∉ c.warrs) → (∀ z ∈ ["hl", "rho", "hk", "hq"], z ∉ c.wvars) →
      Stable C1 c := fun c h1 h2 h3 h4 =>
    (hC.mono h1 h2).and ((stable_selRest X nS R r ℓ s k q ρ (fun a ha => h3 a (by simp at ha ⊢; tauto))
      h4).and (stable_selAt X W nS k q r ρ ℓ s i (h3 "sel" (by simp))))
  obtain ⟨σ1, r1, hC1, hF1, hzs1, hE1⟩ := eqFill_spec B W nS R i C1
    (hS1 eqFill (by decide) (by decide) (by decide) (by decide)) hb hi
    (fun j hj => by have := h3 j hj; omega) (by omega) σ ⟨⟨hCσ, hR, hS⟩, hF, hzs⟩
  let C2 : Env → Prop := fun ρ' => C1 ρ' ∧ ρ'.vars "zs" = i
  have hS2 : Stable C2 inNC := (hS1 inNC (by decide) (by decide) (by decide) (by decide)).and
    (stable_var "zs" i (by decide))
  obtain ⟨σ2, r2, hC2, hT2, hzn2⟩ := inNC_spec B X W nS R r ℓ s i C2 hS2
    (by omega) σ1 ⟨⟨hC1, hzs1⟩, hF1, hE1, hC1.2.1.1, hC1.2.1.2.1, hC1.2.1.2.2.1⟩
  set bn := inNW X (W.drop nS) r ℓ (nuPart (wd W i))
  let C3 : Env → Prop := fun ρ' => C2 ρ' ∧ ρ'.vars "zn" = bv bn
  have hS3 : Stable C3 cntC := ((hS1 cntC (by decide) (by decide) (by decide) (by decide)).and
    (stable_var "zs" i (by decide))).and (stable_var "zn" _ (by decide))
  obtain ⟨σ3, r3, ⟨⟨⟨hC3c, hR3, hSA3⟩, hzs3⟩, hzn3⟩, hT3, hzk3⟩ := cntC_spec B X W nS R r ℓ s i C3 hS3 (by omega) (by omega)
    σ2 ⟨⟨hC2, hzn2⟩, hT2⟩
  set cnt := cntW X (W.drop nS) r ℓ (canonW X s ℓ) (nuPart (wd W i))
  have hcnt : cnt ≤ ℓ := by
    have := List.length_filter_le (blkW X (W.drop nS) r ℓ (canonW X s ℓ) (nuPart (wd W i))) (List.range ℓ)
    simpa [cnt, cntW] using this
  have hWl := hF.2.2.2.1
  have hiW : i < W.length := by omega
  have hw := hT3.1.1
  obtain ⟨hRows3, hBt3, hhl3, hrho3, hhk3, hhq3, hsel3⟩ := hR3
  have hoff := off_add_le hiW
  have hlen := hb.len
  set o := off W i
  set w := W[i]
  have hw3 : 3 ≤ w.length := by have := h3 i hi; rwa [wd_eq hiW] at this
  set σ4 := (σ3.setVar "zo" o).setVar "zl" w.length
  have r4a : Run B (.assign "zo" (.get "st" (.var "zs"))) σ3 (σ3.setVar "zo" o) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    exact ⟨i, ⟨hzs3.symm, by omega⟩, hw.st i hiW, by omega⟩
  have r4b : Run B (.assign "zl" (.get "ln" (.var "zs"))) (σ3.setVar "zo" o) σ4 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    exact ⟨i, ⟨by simp [hzs3], by simp [hzs3]; omega⟩, hw.ln i hiW, by omega⟩
  have hxg : ∀ j, xg w j < B := fun j => xg_lt (fun v hv => hb.ent w (List.getElem_mem hiW) v hv) (by omega)
  have r5 := hdrSel_run B σ4 w o k q ρ bn cnt hw3
    (fun j hj => by simpa [σ4, xg_of_lt hj] using hw.a i hiW j hj) hxg (by omega) hρ hk hq (by omega) h9
    (by simp [σ4]) (by simp [σ4]) (by simp [σ4, hrho3])
    (by simp [σ4, hhk3]) (by simp [σ4, hhq3]) (by simp [σ4, hzn3])
    (by simp [σ4, hzk3])
  set sv := bv ((xg w 0 == 4 * ρ) && (xg w 1 == k + 1) && (xg w 2 == q) &&
      (bn || decide (cnt < xg w (w.length - 1))))
  have hsv : sv = bv (selW X (W.drop nS) k q r ρ ℓ (canonW X s ℓ) (wd W i)) := by
    rw [selW, lastE]; simp only [sv, bn, cnt, w, wd_eq hiW]
  set σ5 := σ4.setVar "sv" sv
  have hsl : i < (σ5.arrs "sel").length := by
    simp [σ5, σ4]; omega
  have r6 : Run B (.store "sel" (.var "zs") (.var "sv")) σ5 (σ5.setArr "sel" i sv) 3 :=
    Run.store (by simp only [evalB_var_iff]; simp [σ5, σ4, hzs3]; omega)
      (by simp only [evalB_var_iff]; simp [σ5]; have := bv_le (((xg w 0 == 4 * ρ) && (xg w 1 == k + 1) &&
        (xg w 2 == q) && (bn || decide (cnt < xg w (w.length - 1))))); omega) hsl
  have rAll : Run B selBody σ (σ5.setArr "sel" i sv) (selCost (wd W i) ℓ R) := by
    unfold selBody
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4a (Run.seq r4b (Run.seq r5 r6)))))).mono ?_
    simp only [selCost]; omega
  have hSC : Stable C selBody := hC
  refine ⟨_, rAll, hC.run rAll (by decide) (by decide) hCσ, ?_, ?_, ?_, ?_⟩
  · exact (stable_scanFix W nS R (by decide) (by decide) (by decide) (by decide) (by decide) :
      Stable _ selBody).run rAll (by decide) (by decide) hF
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [σ5, σ4, Rows, Env.setArr] using hRows3
    · simpa [σ5, σ4, BtAt, Env.setArr] using hBt3
    · simpa [σ5, σ4] using hhl3
    · simpa [σ5, σ4] using hrho3
    · simpa [σ5, σ4] using hhk3
    · simpa [σ5, σ4] using hhq3
    · simpa [σ5, σ4, Env.setArr] using hsel3
  · intro j hj
    simp only [Env.setArr, if_true]
    rcases Nat.lt_or_ge j i with h | h
    · rw [List.getElem?_set_ne (by omega)]; simpa [σ5, σ4] using hSA3 j h
    · obtain rfl : j = i := by omega
      rw [List.getElem?_set_self hsl, hsv]
  · simp [σ5, σ4, Env.setArr, hzs3]

def scanCost (W : List (List ℕ)) (ℓ R nS : ℕ) : ℕ :=
  (∑ i ∈ Finset.range nS, (selCost (wd W i) ℓ R + 8)) + 6

/-- **The scan of the scatter type.** -/
theorem scanSel_spec (B : ℕ) (X : List ℕ) (W : List (List ℕ)) (nS R r ℓ s k q ρ : ℕ)
    (C : Env → Prop) (hC : Stable C scanSel) (hb : WordsBound B W)
    (h3 : ∀ j < nS, 3 ≤ (wd W j).length) (hRB : R * ℓ + ℓ + nS + R + 2 < B) (hρ : 4 * ρ < B)
    (hk : k + 2 < B) (hq : q + 2 < B) (h9 : 9 < B) :
    Spec B (fun τ => C τ ∧ ScanFix W nS R τ ∧ SelRest X nS R r ℓ s k q ρ τ) scanSel
      (fun _ τ' => C τ' ∧ ScanFix W nS R τ' ∧ SelRest X nS R r ℓ s k q ρ τ' ∧
        SelAt X W nS k q r ρ ℓ s nS τ') (scanCost W ℓ R nS) := by
  rintro σ ⟨hCσ, hF, hR⟩
  have hns : σ.vars "ns" = nS := hF.2.1
  have hset : ∀ z, z ∈ scanSel.wvars → z ∉ ["ns", "nR", "hl", "rho", "hk", "hq"] → ∀ i τ x,
      (C τ ∧ ScanFix W nS R τ ∧ SelRest X nS R r ℓ s k q ρ τ ∧ SelAt X W nS k q r ρ ℓ s i τ) →
      (C (τ.setVar z x) ∧ ScanFix W nS R (τ.setVar z x) ∧ SelRest X nS R r ℓ s k q ρ (τ.setVar z x) ∧
        SelAt X W nS k q r ρ ℓ s i (τ.setVar z x)) := by
    intro z hz hz' i τ x ⟨h1, h2, h3', h4⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz'
    refine ⟨hC.setVar hz τ x h1, ⟨h2.1.of_arrs rfl rfl rfl, by simp [Ne.symm hz'.1, h2.2.1],
      by simp [Ne.symm hz'.2.1, h2.2.2.1], h2.2.2.2.1, by simpa using h2.2.2.2.2⟩,
      ⟨by simpa [Rows] using h3'.1, by simpa [BtAt] using h3'.2.1, by simp [Ne.symm hz'.2.2.1, h3'.2.2.1],
        by simp [Ne.symm hz'.2.2.2.1, h3'.2.2.2.1], by simp [Ne.symm hz'.2.2.2.2.1, h3'.2.2.2.2.1],
        by simp [Ne.symm hz'.2.2.2.2.2, h3'.2.2.2.2.2.1], by simpa using h3'.2.2.2.2.2.2⟩,
      by simpa [SelAt] using h4⟩
  obtain ⟨σ', hr, hI, -⟩ := forUp_run_sum (B := B) (i := "zs") (e := .var "ns") (body := selBody) (N := nS)
    (fun i => selCost (wd W i) ℓ R)
    (fun i τ => C τ ∧ ScanFix W nS R τ ∧ SelRest X nS R r ℓ s k q ρ τ ∧ SelAt X W nS k q r ρ ℓ s i τ)
    (σ := σ) (by omega)
    (fun i _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.2.1.symm, by rw [hI.2.1.2.1]; omega⟩)
    (hset "zs" (by decide) (by decide) 0 σ 0 ⟨hCσ, hF, hR, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    (fun i hi τ ⟨hCτ, hFτ, hRτ, hSτ⟩ hzs => by
      obtain ⟨τ', hr', hC', hF', hR', hS', hzs'⟩ := selBody_spec B X W nS R r ℓ s k q ρ i C
        (hC.mono (by decide) (by decide)) hb hi h3 hRB hρ hk hq h9 τ ⟨hCτ, hFτ, hRτ, hSτ, hzs⟩
      exact ⟨τ', hr', hzs', hset "zs" (by decide) (by decide) (i + 1) τ' (i + 1) ⟨hC', hF', hR', hS'⟩⟩)
  exact ⟨σ', hr.mono (le_of_eq (by simp [scanCost, Expr.size])), hI⟩

end Lax185574Proofs.FarRam
