import Lax185574Proofs.EvalRam.Table

/-!
The two scans of a cell of the evaluation table.

`atScan` looks for the atom code at position `p` of `f` among the atom
codes of the node at `y`. `exScan` looks for an extension of the node at
`y` with the guard at `p + 1` whose child has the value `1` in row
`p + 3` of the table. Both leave the answer in `v`.
-/

namespace Lax185574Proofs.EvalRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding

/-- Compare the entries of an atom frame with the code at `p`. -/
def atLast : Com :=
  .ite (.eq (.var "al") (.lit 3)) (.assign "v" (.lit 1))
    (.ite (.eq (.get "x" (.add (.var "fr") (.lit 4))) (.get "f" (.add (.var "p") (.lit 3))))
      (.assign "v" (.lit 1)) .skip)

/-- Compare the first three entries, then the last one. -/
def atMatch : Com :=
  .ite (.eq (.get "x" (.add (.var "fr") (.lit 1))) (.get "f" (.var "p")))
    (.ite (.eq (.get "x" (.add (.var "fr") (.lit 2))) (.get "f" (.add (.var "p") (.lit 1))))
      (.ite (.eq (.get "x" (.add (.var "fr") (.lit 3))) (.get "f" (.add (.var "p") (.lit 2))))
        atLast .skip) .skip) .skip

/-- Test one atom frame and move to the next. -/
def atBody : Com :=
  .seq (.ite (.eq (.get "x" (.var "fr")) (.var "al")) atMatch .skip)
    (.assign "fr" (.add (.add (.var "fr") (.get "x" (.var "fr"))) (.lit 1)))

theorem atBody_spec (B : ℕ) (X F : List ℕ) (fr p al : ℕ) (hfr : fr + 1 + xg X fr ≤ X.length)
    (hal : al = 3 ∨ al = 4) (hp : p + 3 < F.length) (hX : ∀ v ∈ X, v < B) (hF : ∀ v ∈ F, v < B)
    (hXB : X.length + 1 < B) (hFB : F.length < B) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.arrs "f" = F ∧ τ.vars "fr" = fr ∧ τ.vars "p" = p ∧
        τ.vars "al" = al ∧ τ.vars "v" ≤ 1) atBody
      (fun τ τ' => τ'.vars "fr" = fr + 1 + xg X fr ∧
        τ'.vars "v" = (if fm X F fr p al then 1 else τ.vars "v")) 60 := by
  rintro τ ⟨hx, hf, hfr', hp', hal', hv⟩
  subst hx hf hfr' hp' hal'
  have hxv : ∀ i, (τ.arrs "x").getD i 0 < B := fun i => xg_lt hX (by omega)
  have hfv : ∀ i, (τ.arrs "f").getD i 0 < B := fun i => xg_lt hF (by omega)
  have h0 := hxv (τ.vars "fr")
  have h1 := hxv (τ.vars "fr" + 1)
  have h2 := hxv (τ.vars "fr" + 2)
  have h3 := hxv (τ.vars "fr" + 3)
  have h4 := hxv (τ.vars "fr" + 4)
  have g0 := hfv (τ.vars "p")
  have g1 := hfv (τ.vars "p" + 1)
  have g2 := hfv (τ.vars "p" + 2)
  have g3 := hfv (τ.vars "p" + 3)
  have hfr2 : (τ.arrs "x").getD (τ.vars "fr") 0 ≠ τ.vars "al" ∨
      τ.vars "fr" + τ.vars "al" < (τ.arrs "x").length := by
    by_cases h : (τ.arrs "x").getD (τ.vars "fr") 0 = τ.vars "al"
    · right; have : xg (τ.arrs "x") (τ.vars "fr") = τ.vars "al" := h; omega
    · left; exact h
  have hfr3 : τ.vars "fr" + (τ.arrs "x").getD (τ.vars "fr") 0 + 1 ≤ (τ.arrs "x").length := by
    unfold xg at hfr; omega
  have hal4 : τ.vars "al" ≤ 4 := by omega
  unfold atBody atMatch atLast
  run_vcg
  all_goals (try (simp; omega))
  all_goals (try (simp only [arrs_setVar, vars_setVar, if_false,
    show ("fr" : String) = "v" ↔ False by decide]; omega))
  all_goals refine ⟨by simp [xg]; omega, ?_⟩
  all_goals simp [fm, xg]
  all_goals (try split_ifs) <;> simp_all <;> omega

/-- The length of the atom codes of an opcode. -/
def alOf (o : ℕ) : ℕ := if o < 4 then 3 else 4

/-- Look for the atom code at `p` among the atom codes of the node at `y`. -/
def atScan : Com :=
  .seq (.assign "v" (.lit 0)) (.seq (.ite (.lt (.var "op") (.lit 4)) (.assign "al" (.lit 3))
    (.assign "al" (.lit 4))) (.seq (.assign "m" (.get "x" (.var "y")))
      (.seq (.assign "fr" (.add (.var "y") (.lit 1))) (forUp "j" (.var "m") atBody))))

theorem atHit_succ (X F : List ℕ) (y p al j : ℕ) :
    atHit X F y p al (j + 1) = (atHit X F y p al j || fm X F (frPos X y j) p al) := by
  simp [atHit, List.range_succ, List.any_append]

theorem atScan_spec (B : ℕ) (X F : List ℕ) (y p o : ℕ) (hL : ListFacts X y)
    (hp : p + 3 < F.length) (hX : ∀ v ∈ X, v < B) (hF : ∀ v ∈ F, v < B)
    (hXB : X.length + 5 < B) (hFB : F.length < B) (ho : o < B) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.arrs "f" = F ∧ τ.vars "y" = y ∧ τ.vars "p" = p ∧
        τ.vars "op" = o) atScan
      (fun _ τ' => τ'.vars "v" = bv (atHit X F y p (alOf o) (xg X y))) (70 * X.length + 40) := by
  rintro τ ⟨hx, hf, hy, hp', hop⟩
  have hyX : y < X.length := by have := hL.frPos_le 0 (Nat.zero_le _); have := hL.end_le; omega
  have hNX : xg X y ≤ X.length := by have := hL.frPos_le _ le_rfl; have := hL.end_le; omega
  have hal : alOf o = 3 ∨ alOf o = 4 := by unfold alOf; split_ifs <;> simp
  set N := xg X y with hN
  set τ1 := (((τ.setVar "v" 0).setVar "al" (alOf o)).setVar "m" N).setVar "fr" (y + 1) with hτ1
  have ra : Run B (.assign "v" (.lit 0)) τ (τ.setVar "v" 0) 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  have rb : Run B (.ite (.lt (.var "op") (.lit 4)) (.assign "al" (.lit 3)) (.assign "al" (.lit 4)))
      (τ.setVar "v" 0) ((τ.setVar "v" 0).setVar "al" (alOf o)) 8 := by
    have hc : (Cond.lt (.var "op") (.lit 4)).evalB B (τ.setVar "v" 0) = some (decide (o < 4)) := by
      simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff, vars_setVar]
      exact ⟨o, 4, ⟨by simp [hop], by simp [hop]; omega⟩, ⟨rfl, by omega⟩, rfl⟩
    by_cases h4 : o < 4
    · rw [show alOf o = 3 by simp [alOf, h4]]
      exact (Run.ite_true (by rw [hc]; simp [h4]) (Run.assign (by simp; omega))).mono (by simp)
    · rw [show alOf o = 4 by simp [alOf, h4]]
      exact (Run.ite_false (by rw [hc]; simp [h4]) (Run.assign (by simp; omega))).mono (by simp)
  have rc : Run B (.assign "m" (.get "x" (.var "y"))) ((τ.setVar "v" 0).setVar "al" (alOf o))
      (((τ.setVar "v" 0).setVar "al" (alOf o)).setVar "m" N) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    refine ⟨y, ⟨by simp [hy], by simp [hy]; omega⟩, ?_, xg_lt hX (by omega)⟩
    simp [hx, hN, xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hyX]
  have rd : Run B (.assign "fr" (.add (.var "y") (.lit 1)))
      (((τ.setVar "v" 0).setVar "al" (alOf o)).setVar "m" N) τ1 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, vars_setVar]
    exact ⟨y, 1, ⟨by simp [hy], by simp [hy]; omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  obtain ⟨τ2, hr2, hI2, -⟩ := forUp_run (B := B) (i := "j") (e := .var "m") (body := atBody) (N := N)
    (K := 60) (fun j ρ => ρ.arrs "x" = X ∧ ρ.arrs "f" = F ∧ ρ.vars "p" = p ∧ ρ.vars "al" = alOf o ∧
      ρ.vars "m" = N ∧ ρ.vars "fr" = frPos X y j ∧ ρ.vars "v" = bv (atHit X F y p (alOf o) j))
    (σ := τ1) (by omega) (fun j _ ρ hI _ => by simp [hI.2.2.2.2.1]; omega)
    ⟨by simp [hτ1, hx], by simp [hτ1, hf], by simp [hτ1, hp'], by simp [hτ1], by simp [hτ1],
      by simp [hτ1, frPos, skipFr], by simp [hτ1, atHit]⟩
    (fun j hj ρ hI hjv => by
      obtain ⟨hx', hf', hp'', hal', hm', hfr', hv'⟩ := hI
      have hs := skipFr_succ' X (y + 1) j
      obtain ⟨-, h1⟩ := hL.frPos_le (j + 1) (by omega)
      have h2 := hL.end_le
      obtain ⟨ρ', hr', hfr2, hv2⟩ := atBody_spec B X F (frPos X y j) p (alOf o)
        (by unfold frPos at h1 ⊢; omega) hal hp hX hF (by omega) hFB ρ
        ⟨hx', hf', hfr', hp'', hal', by rw [hv']; exact bv_le _⟩
      have hfv : ∀ z, z ∉ atBody.wvars → ρ'.vars z = ρ.vars z := fun z h => hr'.frame_var z h
      have hfa : ∀ a, a ∉ atBody.warrs → ρ'.arrs a = ρ.arrs a := fun a h => hr'.frame_arr a h
      refine ⟨ρ', hr', by rw [hfv "j" (by decide), hjv], ?_⟩
      refine ⟨by simp [hfa "x" (by decide), hx'], by simp [hfa "f" (by decide), hf'],
        by simp [hfv "p" (by decide), hp''], by simp [hfv "al" (by decide), hal'],
        by simp [hfv "m" (by decide), hm'], ?_, ?_⟩
      · simp only [vars_setVar, show ("fr" : String) = "j" ↔ False by decide, if_false, hfr2]
        unfold frPos; rw [hs]
      · simp only [vars_setVar, show ("v" : String) = "j" ↔ False by decide, if_false, hv2, hv',
          atHit_succ]
        cases atHit X F y p (alOf o) j <;> cases fm X F (frPos X y j) p (alOf o) <;> simp)
  refine ⟨τ2, ?_, hI2.2.2.2.2.2.2⟩
  unfold atScan
  refine (Run.seq ra (Run.seq rb (Run.seq rc (Run.seq rd hr2)))).mono ?_
  simp only [Expr.size]
  omega

/-- The index of the value of the child `ch + j` in row `p + 3`. -/
def chIdx : Expr :=
  .add (.mul (.add (.var "p") (.lit 3)) (.var "nn")) (.add (.var "ch") (.var "j"))

/-- Test one extension frame and move to the next. -/
def exBody : Com :=
  .seq (.ite (.eq (.get "x" (.add (.var "fr") (.lit 1))) (.get "f" (.add (.var "p") (.lit 1))))
      (.ite (.eq (.get "val" chIdx) (.lit 1)) (.assign "v" (.lit 1)) .skip) .skip)
    (.assign "fr" (.add (.add (.var "fr") (.get "x" (.var "fr"))) (.lit 1)))

theorem exBody_spec (B : ℕ) (X F VL : List ℕ) (fr p N ch j : ℕ) (hfr : fr + 1 + xg X fr ≤ X.length)
    (hfr1 : 1 ≤ xg X fr) (hp : p + 1 < F.length) (hidx : (p + 3) * N + (ch + j) < VL.length)
    (hX : ∀ v ∈ X, v < B) (hF : ∀ v ∈ F, v < B) (hV : ∀ v ∈ VL, v < B)
    (hXB : X.length + 1 < B) (hFB : F.length < B) (hVB : VL.length < B) (hpB : p + 3 < B) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.arrs "f" = F ∧ τ.arrs "val" = VL ∧ τ.vars "fr" = fr ∧
        τ.vars "p" = p ∧ τ.vars "nn" = N ∧ τ.vars "ch" = ch ∧ τ.vars "j" = j ∧ τ.vars "v" ≤ 1) exBody
      (fun τ τ' => τ'.vars "fr" = fr + 1 + xg X fr ∧
        τ'.vars "v" = (if (xg X (fr + 1) == xg F (p + 1) && xg VL ((p + 3) * N + (ch + j)) == 1)
          then 1 else τ.vars "v")) 60 := by
  rintro τ ⟨hx, hf, hvl, hfr', hp', hN, hch, hj, hv⟩
  subst hx hf hvl hfr' hp' hN hch hj
  have h0 : (τ.arrs "x").getD (τ.vars "fr") 0 < B := xg_lt hX (by omega)
  have h1 : (τ.arrs "x").getD (τ.vars "fr" + 1) 0 < B := xg_lt hX (by omega)
  have g1 : (τ.arrs "f").getD (τ.vars "p" + 1) 0 < B := xg_lt hF (by omega)
  have v1 : (τ.arrs "val").getD ((τ.vars "p" + 3) * τ.vars "nn" + (τ.vars "ch" + τ.vars "j")) 0 < B :=
    xg_lt hV (by omega)
  have hfr3 : τ.vars "fr" + (τ.arrs "x").getD (τ.vars "fr") 0 + 1 ≤ (τ.arrs "x").length := by
    unfold xg at hfr; omega
  have hfr4 : τ.vars "fr" + 1 < (τ.arrs "x").length := by unfold xg at hfr hfr1; omega
  have hidx' : (τ.vars "p" + 3) * τ.vars "nn" + (τ.vars "ch" + τ.vars "j") < B := by omega
  have hmul : (τ.vars "p" + 3) * τ.vars "nn" < B := by omega
  have hnB : τ.vars "nn" < B := by
    have := Nat.le_mul_of_pos_left (τ.vars "nn") (show 0 < τ.vars "p" + 3 by omega)
    omega
  have hchj : τ.vars "ch" + τ.vars "j" < B := by omega
  have hidx2 : (τ.vars "p" + 3) * τ.vars "nn" + (τ.vars "ch" + τ.vars "j") < (τ.arrs "val").length :=
    hidx
  unfold exBody chIdx
  run_vcg
  all_goals (try (simp; omega))
  all_goals (try (simp only [arrs_setVar, vars_setVar, if_false,
    show ("fr" : String) = "v" ↔ False by decide]; omega))
  all_goals refine ⟨by simp [xg]; omega, ?_⟩
  all_goals simp [xg]
  all_goals (try split_ifs) <;> simp_all <;> omega

/-- Look for an extension of the node at `y` with the guard at `p + 1`
whose child has value `1` in row `p + 3`. -/
def exScan : Com :=
  .seq skipList (.seq (.assign "v" (.lit 0)) (.seq (.assign "m" (.get "x" (.var "y")))
    (.seq (.assign "fr" (.add (.var "y") (.lit 1))) (.seq (.assign "ch" (.get "fc" (.var "c")))
      (forUp "j" (.var "m") exBody)))))

theorem exHit_succ (X F VL : List ℕ) (N e p ch j : ℕ) :
    exHit X F VL N e p ch (j + 1) = (exHit X F VL N e p ch j ||
      (xg X (frPos X e j + 1) == xg F (p + 1) && xg VL ((p + 3) * N + (ch + j)) == 1)) := by
  simp [exHit, List.range_succ, List.any_append]

theorem exScan_spec (B : ℕ) (X F VL FA : List ℕ) (y p N c : ℕ) (hA : ListFacts X y)
    (hE : ListFacts X (listEnd X y)) (hfr1 : ∀ j < xg X (listEnd X y), 1 ≤ xg X (frPos X (listEnd X y) j))
    (hch : ∀ j < xg X (listEnd X y), xg FA c + j < N) (hcFA : c < FA.length) (hFAN : xg FA c ≤ N) (hcN : c < N)
    (hp : p + 1 < F.length) (hidx : (p + 4) * N ≤ VL.length)
    (hX : ∀ v ∈ X, v < B) (hF : ∀ v ∈ F, v < B) (hV : ∀ v ∈ VL, v < B)
    (hXB : X.length + 5 < B) (hFB : F.length < B) (hVB : VL.length < B) (hpB : p + 3 < B) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.arrs "f" = F ∧ τ.arrs "val" = VL ∧ τ.arrs "fc" = FA ∧
        τ.vars "y" = y ∧ τ.vars "p" = p ∧ τ.vars "nn" = N ∧ τ.vars "c" = c) exScan
      (fun _ τ' => τ'.vars "v" = bv (exHit X F VL N (listEnd X y) p (xg FA c) (xg X (listEnd X y))))
      (100 * X.length + 60) := by
  rintro τ ⟨hx, hf, hvl, hfa, hy, hp', hN, hc⟩
  set e := listEnd X y with he
  obtain ⟨τ0, hr0, hy0⟩ := skipList_spec B X y hA (by omega) hX τ ⟨hx, hy⟩
  rw [← he] at hy0
  have hv0 : ∀ z, z ∉ skipList.wvars → τ0.vars z = τ.vars z := fun z h => hr0.frame_var z h
  have ha0 : ∀ a, a ∉ skipList.warrs → τ0.arrs a = τ.arrs a := fun a h => hr0.frame_arr a h
  have heX : e < X.length := by have := hE.frPos_le 0 (Nat.zero_le _); have := hE.end_le; omega
  have hMX : xg X e ≤ X.length := by have := hE.frPos_le _ le_rfl; have := hE.end_le; omega
  set M := xg X e with hM
  set ch := xg FA c with hchd
  have hNB : N < B := by
    have := Nat.le_mul_of_pos_left N (show 0 < p + 4 by omega)
    omega
  have hchB : ch < B := by omega
  set τ1 := (((τ0.setVar "v" 0).setVar "m" M).setVar "fr" (e + 1)).setVar "ch" ch with hτ1
  have hx0 : τ0.arrs "x" = X := by rw [ha0 "x" (by decide), hx]
  have ra : Run B (.assign "v" (.lit 0)) τ0 (τ0.setVar "v" 0) 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  have rb : Run B (.assign "m" (.get "x" (.var "y"))) (τ0.setVar "v" 0)
      ((τ0.setVar "v" 0).setVar "m" M) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    refine ⟨e, ⟨by simp [hy0], by simp [hy0]; omega⟩, ?_, xg_lt hX (by omega)⟩
    simp [hx0, hM, xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem heX]
  have rc : Run B (.assign "fr" (.add (.var "y") (.lit 1))) ((τ0.setVar "v" 0).setVar "m" M)
      (((τ0.setVar "v" 0).setVar "m" M).setVar "fr" (e + 1)) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, vars_setVar]
    exact ⟨e, 1, ⟨by simp [hy0], by simp [hy0]; omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  have rd : Run B (.assign "ch" (.get "fc" (.var "c"))) (((τ0.setVar "v" 0).setVar "m" M).setVar "fr" (e + 1))
      τ1 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    have hc0 : τ0.vars "c" = c := by rw [hv0 "c" (by decide), hc]
    refine ⟨c, ⟨by simp [hc0], by simp [hc0]; omega⟩, ?_, hchB⟩
    rw [ha0 "fc" (by decide), hfa, hchd, List.getElem?_eq_getElem hcFA]
    simp [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcFA]
  obtain ⟨τ2, hr2, hI2, -⟩ := forUp_run (B := B) (i := "j") (e := .var "m") (body := exBody) (N := M)
    (K := 60) (fun j ρ => ρ.arrs "x" = X ∧ ρ.arrs "f" = F ∧ ρ.arrs "val" = VL ∧ ρ.vars "p" = p ∧
      ρ.vars "nn" = N ∧ ρ.vars "ch" = ch ∧ ρ.vars "m" = M ∧ ρ.vars "fr" = frPos X e j ∧
      ρ.vars "v" = bv (exHit X F VL N e p ch j))
    (σ := τ1) (by omega) (fun j _ ρ hI _ => by simp [hI.2.2.2.2.2.2.1]; omega)
    ⟨by simp [hτ1, hx0], by simp [hτ1, ha0 "f" (by decide), hf], by simp [hτ1, ha0 "val" (by decide), hvl],
      by simp [hτ1, hv0 "p" (by decide), hp'], by simp [hτ1, hv0 "nn" (by decide), hN], by simp [hτ1],
      by simp [hτ1], by simp [hτ1, frPos, skipFr], by simp [hτ1, exHit]⟩
    (fun j hj ρ hI hjv => by
      obtain ⟨hx', hf', hvl', hp'', hN', hch', hm', hfr', hv'⟩ := hI
      have hs := skipFr_succ' X (e + 1) j
      obtain ⟨-, h1⟩ := hE.frPos_le (j + 1) (by omega)
      have h2 := hE.end_le
      have hjN := hch j hj
      obtain ⟨ρ', hr', hfr2, hv2⟩ := exBody_spec B X F VL (frPos X e j) p N ch j
        (by unfold frPos at h1 ⊢; omega) (hfr1 j hj) hp
        (by have : (p + 4) * N = (p + 3) * N + N := by ring
            omega) hX hF hV (by omega) hFB hVB hpB ρ
        ⟨hx', hf', hvl', hfr', hp'', hN', hch', hjv, by rw [hv']; exact bv_le _⟩
      have hfv : ∀ z, z ∉ exBody.wvars → ρ'.vars z = ρ.vars z := fun z h => hr'.frame_var z h
      have hfa : ∀ a, a ∉ exBody.warrs → ρ'.arrs a = ρ.arrs a := fun a h => hr'.frame_arr a h
      refine ⟨ρ', hr', by rw [hfv "j" (by decide), hjv], ?_⟩
      refine ⟨by simp [hfa "x" (by decide), hx'], by simp [hfa "f" (by decide), hf'],
        by simp [hfa "val" (by decide), hvl'], by simp [hfv "p" (by decide), hp''],
        by simp [hfv "nn" (by decide), hN'], by simp [hfv "ch" (by decide), hch'],
        by simp [hfv "m" (by decide), hm'], ?_, ?_⟩
      · simp only [vars_setVar, show ("fr" : String) = "j" ↔ False by decide, if_false, hfr2]
        unfold frPos; rw [hs]
      · simp only [vars_setVar, show ("v" : String) = "j" ↔ False by decide, if_false, hv2, hv',
          exHit_succ]
        cases exHit X F VL N e p ch j <;>
          cases (xg X (frPos X e j + 1) == xg F (p + 1) && xg VL ((p + 3) * N + (ch + j)) == 1) <;> simp)
  refine ⟨τ2, ?_, hI2.2.2.2.2.2.2.2.2⟩
  unfold exScan
  refine (Run.seq hr0 (Run.seq ra (Run.seq rb (Run.seq rc (Run.seq rd hr2))))).mono ?_
  simp only [Expr.size]
  nlinarith

end Lax185574Proofs.EvalRam
