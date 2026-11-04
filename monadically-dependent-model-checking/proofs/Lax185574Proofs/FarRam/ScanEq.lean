import Lax185574Proofs.FarRam.Exts
import Lax185574Proofs.Words.Compare


/-!
The tests of one entry of the scatter type.

For the entry `zs` of the word list `W` in the arrays `a`, `st`, `ln`,
`eqFill` stores in `eqa[e]` whether the tree of the entry is the answer
`W[ns + e]` of extension `e`, `inNC` tests whether some far extension
has this tree, and `cntC` counts the blocks met by the extensions with
this tree.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

theorem cmpCode_eq_one {u v : List ℕ} : cmpCode u v = 1 ↔ u = v := by
  unfold cmpCode
  split_ifs with h1 h2
  · simp only [zero_ne_one, false_iff]; exact ne_of_lt h1
  · simp [h2]
  · simp [h2]

/-- The fixed facts of the scan: the words, their number, and the bound
on the extensions. -/
def ScanFix (W : List (List ℕ)) (nS R : ℕ) (τ : Env) : Prop :=
  WordsAt W τ ∧ τ.vars "ns" = nS ∧ τ.vars "nR" = R ∧ W.length = nS + R ∧
    R ≤ (τ.arrs "eqa").length

theorem stable_scanFix {c : Com} (W : List (List ℕ)) (nS R : ℕ) (ha : "a" ∉ c.warrs)
    (hst : "st" ∉ c.warrs) (hln : "ln" ∉ c.warrs) (hn : "ns" ∉ c.wvars) (hR : "nR" ∉ c.wvars) :
    Stable (ScanFix W nS R) c := fun τ τ' h1 h2 h3 _ _ h =>
  ⟨h.1.of_arrs (h2 "a" ha) (h2 "st" hst) (h2 "ln" hln), by rw [h1 "ns" hn]; exact h.2.1,
    by rw [h1 "nR" hR]; exact h.2.2.1, h.2.2.2.1, by rw [h3 "eqa"]; exact h.2.2.2.2⟩

/-- The comparison of the tree of entry `zs` with the answer `ns + zu`. -/
def eqBody : Com :=
  .seq (.assign "pa" (.add (.get "st" (.var "zs")) (.lit 1)))
    (.seq (.assign "la" (.sub (.get "ln" (.var "zs")) (.lit 2)))
      (.seq (.assign "pb" (.get "st" (.add (.var "ns") (.var "zu"))))
        (.seq (.assign "lb" (.get "ln" (.add (.var "ns") (.var "zu"))))
          (.seq (.assign "k" (.lit 0)) (.seq (.assign "c" (.lit 3))
            (.seq (.while (.eq (.var "c") (.lit 3)) cmpStep)
              (.ite (.eq (.var "c") (.lit 1)) (.store "eqa" (.var "zu") (.lit 1))
                (.store "eqa" (.var "zu") (.lit 0)))))))))

def eqFill : Com := forUp "zu" (.var "nR") eqBody

/-- The answers equal to the tree of entry `i` are marked below `t`. -/
def EqAt (W : List (List ℕ)) (nS i t : ℕ) (τ : Env) : Prop :=
  ∀ e < t, (τ.arrs "eqa")[e]? = some (bv ((W.drop nS).getD e [] == nuPart (wd W i)))

theorem nuPart_entries {W : List (List ℕ)} {τ : Env} (hw : WordsAt W τ) {i : ℕ} (hi : i < W.length)
    (j : ℕ) (hj : j < (nuPart W[i]).length) :
    (τ.arrs "a")[off W i + 1 + j]? = some (nuPart W[i])[j] := by
  have hj' : 1 + j < W[i].length := by simp [nuPart] at hj; omega
  rw [Nat.add_assoc, hw.a i hi (1 + j) hj']
  simp [nuPart, Nat.add_comm]

def eqCost (w : List ℕ) : ℕ := 36 * w.length + 120

theorem eqFill_spec (B : ℕ) (W : List (List ℕ)) (nS R i : ℕ) (C : Env → Prop) (hC : Stable C eqFill)
    (hb : WordsBound B W) (hi : i < nS) (h2 : ∀ j < nS, 2 ≤ (wd W j).length) (hRB : nS + R + 1 < B) :
    Spec B (fun τ => C τ ∧ ScanFix W nS R τ ∧ τ.vars "zs" = i) eqFill
      (fun _ τ' => C τ' ∧ ScanFix W nS R τ' ∧ τ'.vars "zs" = i ∧ EqAt W nS i R τ')
      (R * (eqCost (wd W i) + 10) + 10) := by
  rintro σ ⟨hCσ, hF, hzs⟩
  have hWl := hF.2.2.2.1
  have hiW : i < W.length := by omega
  have hlen := hb.len
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := "zu") (e := .var "nR") (body := eqBody) (N := R)
    (K := eqCost (wd W i)) (fun t τ => C τ ∧ ScanFix W nS R τ ∧ τ.vars "zs" = i ∧ EqAt W nS i t τ) (σ := σ)
    (by omega)
    (fun t _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.2.2.1.symm, by rw [hI.2.1.2.2.1]; omega⟩)
    ⟨hC.setVar (by decide) _ _ hCσ, (stable_scanFix W nS R (by decide) (by decide) (by decide)
      (by decide) (by decide) : Stable _ eqFill).setVar (by decide) _ _ hF,
      by simp [hzs], fun e he => absurd he (Nat.not_lt_zero _)⟩
    (fun t ht τ ⟨hCτ, hFτ, hzsτ, hEτ⟩ hzu => by
      have hw := hFτ.1
      have hns := hFτ.2.1
      have htW : nS + t < W.length := by omega
      set u := nuPart W[i] with hu
      set v := W[nS + t] with hv
      have hoi := off_add_le hiW
      have hot := off_add_le htW
      have hvl : v.length = W[nS + t].length := by rw [hv]
      have hu2 : 2 ≤ W[i].length := by have := h2 i hi; rwa [wd_eq hiW] at this
      have hul : u.length = W[i].length - 2 := by simp [hu, nuPart]; omega
      have hent : ∀ x ∈ u, x < B := fun x hx => hb.ent _ (List.getElem_mem hiW) x
        (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      have hentv : ∀ x ∈ v, x < B := fun x hx => hb.ent _ (List.getElem_mem htW) x hx
      set τ1 := (((((τ.setVar "pa" (off W i + 1)).setVar "la" u.length).setVar "pb" (off W (nS + t))).setVar
        "lb" v.length).setVar "k" 0).setVar "c" 3 with hτ1
      have hs : CmpState B u v (off W i + 1) (off W (nS + t)) τ1 :=
        ⟨by simp [hτ1], by simp [hτ1], by simp [hτ1], by simp [hτ1], by simp [hτ1], by simp [hτ1],
          by simp [hτ1], fun j hj => by simpa [hτ1] using nuPart_entries hw hiW j hj,
          fun j hj => by simpa [hτ1] using hw.a (nS + t) htW j hj, hent, hentv, by omega, by omega,
          hb.three⟩
      obtain ⟨τ2, hr2, hc2⟩ := cmpLoop_run hs (by simp [hτ1]) (by simp [hτ1])
      have hfv : ∀ z, z ∉ ["c", "k"] → τ2.vars z = τ1.vars z := fun z hz =>
        hr2.frame_var z (by simp at hz; simp [cmpStep, Com.wvars]; exact ⟨hz.1, hz.2, hz.1⟩)
      have hfa : ∀ a, τ2.arrs a = τ1.arrs a := fun a => hr2.frame_arr a (by simp [cmpStep, Com.warrs])
      have hc2B : τ2.vars "c" < B := by rw [hc2]; have := cmpCode_le_two u v; have := hb.three; omega
      have hzu2 : τ2.vars "zu" = t := by rw [hfv "zu" (by decide)]; simp [hτ1, hzu]
      have hea1 : τ1.arrs "eqa" = τ.arrs "eqa" := by simp [hτ1]
      have hel : t < (τ2.arrs "eqa").length := by
        rw [hfa, hea1]; have := hFτ.2.2.2.2; omega
      have hval : bv (cmpCode u v == 1) = bv ((W.drop nS).getD t [] == u) := by
        have : (W.drop nS).getD t [] = v := by
          rw [hv, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_eq_getElem htW]; rfl
        rw [this]
        by_cases h : u = v
        · rw [h]; simp [cmpCode]
        · have h' : cmpCode u v ≠ 1 := fun e => h (cmpCode_eq_one.mp e)
          rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr (Ne.symm h)]
      have htB : t < B := by omega
      have hzuE : (Expr.var "zu").evalB B τ2 = some t := by
        rw [← hzu2]; exact evalB_var (by rw [hzu2]; exact htB)
      set τ3 := τ2.setArr "eqa" t (bv (cmpCode u v == 1)) with hτ3
      have r3 : Run B (.ite (.eq (.var "c") (.lit 1)) (.store "eqa" (.var "zu") (.lit 1))
          (.store "eqa" (.var "zu") (.lit 0))) τ2 τ3 10 := by
        by_cases h1 : cmpCode u v = 1
        · have : bv (cmpCode u v == 1) = 1 := by rw [h1]; rfl
          rw [show τ3 = τ2.setArr "eqa" t 1 by rw [hτ3, this]]
          exact (Run.ite_true (by rw [eq_true_iff' hc2B (by omega), hc2, h1]; rfl)
            (Run.store hzuE (evalB_lit (by omega)) hel)).mono (by simp)
        · have : bv (cmpCode u v == 1) = 0 := by rw [beq_eq_false_iff_ne.mpr h1]; rfl
          rw [show τ3 = τ2.setArr "eqa" t 0 by rw [hτ3, this]]
          exact (Run.ite_false (by rw [eq_true_iff' hc2B (by omega), hc2]; simp [h1])
            (Run.store hzuE (evalB_lit (by omega)) hel)).mono (by simp)
      have hst := hw.st
      have hln := hw.ln
      have rAll : Run B eqBody τ τ3 (eqCost (wd W i)) := by
        unfold eqBody
        refine (Run.seq (Run.assign (v := off W i + 1) ?_) (Run.seq (Run.assign (v := u.length) ?_)
          (Run.seq (Run.assign (v := off W (nS + t)) ?_) (Run.seq (Run.assign (v := v.length) ?_)
            (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit hb.three))
              (Run.seq hr2 r3))))))).mono ?_
        · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff]
          exact ⟨off W i, 1, ⟨i, ⟨hzsτ.symm, by omega⟩, hst i hiW, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
        · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff, vars_setVar, arrs_setVar]
          exact ⟨W[i].length, 2, ⟨i, ⟨by simp [hzsτ], by simp [hzsτ]; omega⟩, hln i hiW, by omega⟩,
            ⟨rfl, by omega⟩, by simp [hul, Bop.apply], by omega⟩
        · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
          exact ⟨nS + t, ⟨nS, t, ⟨by simp [hns], by simp [hns]; omega⟩, ⟨by simp [hzu], by simp [hzu]; omega⟩,
            rfl, by omega⟩, hst (nS + t) htW, by omega⟩
        · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
          exact ⟨nS + t, ⟨nS, t, ⟨by simp [hns], by simp [hns]; omega⟩, ⟨by simp [hzu], by simp [hzu]; omega⟩,
            rfl, by omega⟩, hln (nS + t) htW, by omega⟩
        · simp only [eqCost, Expr.size, Cond.size, wd_eq hiW]
          omega
      refine ⟨τ3, rAll, ?_, hC.setVar (by decide) _ _ ((hC.mono (by decide) (by decide)).run rAll
        (by decide) (by decide) hCτ), (stable_scanFix W nS R (by decide) (by decide) (by decide)
          (by decide) (by decide) : Stable _ eqFill).setVar (by decide) _ _
          ((stable_scanFix W nS R (by decide) (by decide) (by decide) (by decide) (by decide) :
            Stable _ eqBody).run rAll (by decide) (by decide) hFτ), ?_, ?_⟩
      · simp [τ3, hzu2]
      · rw [show (τ3.setVar "zu" (t + 1)).vars "zs" = τ2.vars "zs" by simp [τ3]]
        rw [hfv "zs" (by decide)]; simp [hτ1, hzsτ]
      · intro e he
        simp only [arrs_setVar, τ3, Env.setArr, if_true]
        rcases Nat.lt_or_ge e t with h | h
        · rw [List.getElem?_set_ne (by omega), hfa]; simpa [hτ1] using hEτ e h
        · obtain rfl : e = t := by omega
          rw [List.getElem?_set_self hel, hval, wd_eq hiW])
  refine ⟨σ', hr.mono ?_, hI⟩
  simp only [Expr.size]; nlinarith

end Lax185574Proofs.FarRam
