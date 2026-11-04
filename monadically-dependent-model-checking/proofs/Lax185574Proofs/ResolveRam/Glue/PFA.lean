import Lax185574Proofs.ResolveRam.Glue.PFA1

/-!
The setup of the far filter of lem:resolve-lift.

`colSet` reads the colors `P`, `Q` from `gP`, `gQ` into `tP`, `tQ` and
looks them up in the color table (word `oc` of the library), with the
flags in `tcP`, `tcQ` (`colSet_run`). `treeSet` reads the header of the
shifted tree (word `os` of the library): the radius `rhoPlus k q` into
`ts`, the arity into `tL` and the position of its atom list into `tp1`
(`treeSet_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- Look up the colors `P` and `Q` in the color table. -/
def colSet : Com :=
  .seq (.assign "tY" (.var "gP")) (.seq ctLook (.seq (.assign "tcP" (.var "th"))
    (.seq (.assign "tY" (.var "gQ")) (.seq ctLook (.seq (.assign "tcQ" (.var "th"))
      (.seq (.assign "tP" (.var "gP")) (.assign "tQ" (.var "gQ"))))))))

/-- The scalars that `colSet` writes. -/
def colV : List String := ctV ++ ["tY", "tcP", "tcQ", "tP", "tQ"]

theorem colSet_wvars : ∀ y ∈ colSet.wvars, y ∈ colV := by decide

theorem colSet_warrs : colSet.warrs = [] := by decide

theorem colSet_reads : ¬ colSet.reads := by decide

theorem colSet_noWrite : colSet.NoWrite := by decide

/-- **The colors and their flags.** -/
theorem colSet_run {B : ℕ} {ws : List (List ℕ)} {oc P Q : ℕ} {cs : List ℕ} {f g : ℕ → ℕ} {τ : Env}
    (hw : WordsAt ws τ) (hoc : oc < ws.length) (hct : ws[oc] = cs.flatMap fun Y => [Y, f Y, g Y])
    (hocv : τ.vars "oc" = oc) (hP : τ.vars "gP" = P) (hQ : τ.vars "gQ" = Q) (hPB : P < B)
    (hQB : Q < B) (hB : total ws + ws.length + 4 < B) (hv : ∀ v ∈ ws[oc], v < B) :
    ∃ τ', Run B colSet τ τ' (40 * ws[oc].length + 100) ∧
      τ'.vars "tcP" = bv (decide (P ∈ cs)) ∧ τ'.vars "tcQ" = bv (decide (Q ∈ cs)) ∧
      τ'.vars "tP" = P ∧ τ'.vars "tQ" = Q ∧
      (∀ y, y ∉ colV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have nc : ∀ y ∈ ["oc", "gP", "gQ", "tcP"], y ∉ ctV := by decide
  set τ1 := τ.setVar "tY" P
  have r1 : Run B (.assign "tY" (.var "gP")) τ τ1 2 := Run.assign (ev_var hP hPB)
  obtain ⟨τ2, r2, h2, -, -, f2, a2, o2, i2⟩ := ctLook_run (B := B) (τ := τ1) (hw.of_arrs (by simp [τ1])
    (by simp [τ1]) (by simp [τ1])) hoc hct (by simp [τ1, hocv]) (by simp [τ1]) hPB hB hv
  have hb : τ2.vars "th" < B := by rw [h2]; exact lt_of_le_of_lt (bv_le _) (by omega)
  set τ3 := τ2.setVar "tcP" (τ2.vars "th")
  have r3 : Run B (.assign "tcP" (.var "th")) τ2 τ3 2 := Run.assign (ev_var rfl hb)
  have g3 : ∀ y ∈ ["oc", "gP", "gQ"], τ3.vars y = τ.vars y := by
    intro y hy
    have h1 : y ≠ "tcP" := by simp at hy; rcases hy with rfl | rfl | rfl <;> decide
    have h2 : y ≠ "tY" := by simp at hy; rcases hy with rfl | rfl | rfl <;> decide
    simp only [τ3, vars_setVar, h1, if_false]
    rw [f2 y (nc y (by simp at hy ⊢; tauto))]; simp [τ1, h2]
  set τ4 := τ3.setVar "tY" Q
  have r4 : Run B (.assign "tY" (.var "gQ")) τ3 τ4 2 :=
    Run.assign (ev_var (by rw [g3 "gQ" (by simp), hQ]) hQB)
  obtain ⟨τ5, r5, h5, -, -, f5, a5, o5, i5⟩ := ctLook_run (B := B) (τ := τ4)
    (hw.of_arrs (by simp [τ4, τ3, a2, τ1]) (by simp [τ4, τ3, a2, τ1]) (by simp [τ4, τ3, a2, τ1])) hoc hct
    (by simp only [τ4, vars_setVar]; simp [g3 "oc" (by simp), hocv]) (by simp [τ4]) hQB hB hv
  have hb5 : τ5.vars "th" < B := by rw [h5]; exact lt_of_le_of_lt (bv_le _) (by omega)
  set τ6 := τ5.setVar "tcQ" (τ5.vars "th")
  have r6 : Run B (.assign "tcQ" (.var "th")) τ5 τ6 2 := Run.assign (ev_var rfl hb5)
  have g6 : ∀ y ∈ ["gP", "gQ"], τ6.vars y = τ.vars y := by
    intro y hy
    have h1 : y ≠ "tcQ" := by simp at hy; rcases hy with rfl | rfl <;> decide
    have h2 : y ≠ "tY" := by simp at hy; rcases hy with rfl | rfl <;> decide
    simp only [τ6, vars_setVar, h1, if_false]
    rw [f5 y (nc y (by simp at hy ⊢; tauto))]; simp only [τ4, vars_setVar, h2, if_false]
    exact g3 y (by simp at hy ⊢; tauto)
  set τ7 := τ6.setVar "tP" P
  have r7 : Run B (.assign "tP" (.var "gP")) τ6 τ7 2 :=
    Run.assign (ev_var (by rw [g6 "gP" (by simp), hP]) hPB)
  set τ8 := τ7.setVar "tQ" Q
  have r8 : Run B (.assign "tQ" (.var "gQ")) τ7 τ8 2 :=
    Run.assign (ev_var (by simp only [τ7, vars_setVar]; simp [g6 "gQ" (by simp), hQ]) hQB)
  have hrun : Run B colSet τ τ8 (40 * ws[oc].length + 100) := by
    unfold colSet
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono
      (by omega)
  obtain ⟨fa, fo, fi⟩ := run_frame hrun colSet_warrs colSet_reads colSet_noWrite
  refine ⟨τ8, hrun, ?_, ?_, by simp [τ8, τ7], by simp [τ8], fun y hy => hrun.frame_var y
    (fun h => hy (colSet_wvars y h)), fa, fo, fi⟩
  · simp only [τ8, τ7, τ6, vars_setVar]
    simp only [show ("tcP" : String) ≠ "tQ" by decide, show ("tcP" : String) ≠ "tP" by decide,
      show ("tcP" : String) ≠ "tcQ" by decide, if_false]
    rw [f5 "tcP" (by decide)]; simp only [τ4, vars_setVar, show ("tcP" : String) ≠ "tY" by decide,
      if_false]; simp [τ3, h2]
  · simp [τ8, τ7, τ6, h5]

/-- Read the header of the shifted tree. -/
def treeSet : Com :=
  .seq (.assign "tb0" (.get "st" (.var "os")))
    (.seq (.assign "tE" (.mul (.add (.get "a" (.var "tb0")) (.get "a" (.add (.var "tb0") (.lit 1))))
      (.add (.get "a" (.add (.var "tb0") (.lit 1))) (.lit 1))))
    (.seq (powLoop "ts" "tk" "tE") (.seq (.assign "tL" (.get "a" (.add (.var "tb0") (.lit 2))))
      (.assign "tp1" (.add (.var "tb0") (.lit 3))))))

/-- The scalars that `treeSet` writes. -/
def treeV : List String := ["tb0", "tE", "ts", "tk", "tL", "tp1"]

theorem treeSet_wvars : ∀ y ∈ treeSet.wvars, y ∈ treeV := by decide

theorem treeSet_warrs : treeSet.warrs = [] := by decide

theorem treeSet_reads : ¬ treeSet.reads := by decide

theorem treeSet_noWrite : treeSet.NoWrite := by decide

theorem le_pow_nine (E : ℕ) : E < 9 ^ E := by
  induction E with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- **The header of the shifted tree.** -/
theorem treeSet_run {B : ℕ} {ws : List (List ℕ)} {os : ℕ} {σ : TypeTree} {τ : Env}
    (hw : WordsAt ws τ) (hos : os < ws.length) (hσ : ws[os] = toWord σ) (hosv : τ.vars "os" = os)
    (hB : total ws + ws.length + 4 < B) (hv : ∀ v ∈ ws[os], v < B) (hR : rhoPlus σ.k σ.q < B) (h9 : 9 < B) :
    ∃ τ', Run B treeSet τ τ' (20 * rhoPlus σ.k σ.q + 60) ∧
      τ'.vars "ts" = rhoPlus σ.k σ.q ∧ τ'.vars "tL" = σ.ℓ ∧ τ'.vars "tp1" = off ws os + 3 ∧
      (∀ y, y ∉ treeV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hoff := off_add_le hos
  have hst := hw.st os hos
  have hl3 : 3 ≤ ws[os].length := by rw [hσ, toWord_typeTree]; simp
  set c := off ws os
  have e : ∀ j (hj : j < ws[os].length), (τ.arrs "a")[c + j]? = some ws[os][j] := hw.a os hos
  have e0 : (τ.arrs "a")[c]? = some σ.k := by
    have := e 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; simp [hσ, toWord_typeTree]
  have e1 : (τ.arrs "a")[c + 1]? = some σ.q := by rw [e 1 (by omega)]; simp [hσ, toWord_typeTree]
  have e2 : (τ.arrs "a")[c + 2]? = some σ.ℓ := by rw [e 2 (by omega)]; simp [hσ, toWord_typeTree]
  have bk : σ.k < B := hv _ (by rw [hσ, toWord_typeTree]; simp)
  have bq : σ.q < B := hv _ (by rw [hσ, toWord_typeTree]; simp)
  have bl : σ.ℓ < B := hv _ (by rw [hσ, toWord_typeTree]; simp)
  set E := (σ.k + σ.q) * (σ.q + 1)
  have hE : rhoPlus σ.k σ.q = 9 ^ E := rfl
  have hEB : E < B := lt_trans (le_pow_nine E) (by rw [← hE]; exact hR)
  have hkq : σ.k + σ.q ≤ E := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : σ.q + 1 ≤ E ∨ σ.k + σ.q = 0 := by
    rcases Nat.eq_zero_or_pos (σ.k + σ.q) with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  set τ1 := τ.setVar "tb0" c
  have r1 : Run B (.assign "tb0" (.get "st" (.var "os"))) τ τ1 3 :=
    (Run.assign (evalB_get (ev_var (v := os) hosv (by omega)) hst (by omega))).mono (by simp [Expr.size])
  have a1 : τ1.arrs = τ.arrs := by simp [τ1]
  have gk : (Expr.get "a" (.var "tb0")).evalB B τ1 = some σ.k :=
    evalB_get (ev_var (v := c) (by simp [τ1]) (by omega)) (by rw [a1]; exact e0) bk
  have gq : (Expr.get "a" (.add (.var "tb0") (.lit 1))).evalB B τ1 = some σ.q :=
    evalB_get (ev_add (ev_var (v := c) (by simp [τ1]) (by omega)) (evalB_lit (by omega)) (by omega))
      (by rw [a1]; exact e1) bq
  set τ2 := τ1.setVar "tE" E
  have r2 : Run B (.assign "tE" (.mul (.add (.get "a" (.var "tb0")) (.get "a" (.add (.var "tb0") (.lit 1))))
      (.add (.get "a" (.add (.var "tb0") (.lit 1))) (.lit 1)))) τ1 τ2 20 := by
    refine (Run.assign (evalB_bin (ev_add gk gq (by omega)) (ev_add gq (evalB_lit (by omega))
      (by rcases hq1 with h | h <;> omega)) (by simp only [Bop.apply]; omega))).mono ?_
    simp [Expr.size]
  obtain ⟨τ3, r3, ⟨a3, f3⟩, s3, -⟩ := powLoop_run (B := B) (x := "ts") (i := "tk") (n := "tE")
    (fun ρ => ρ.arrs = τ.arrs ∧ ∀ y, y ≠ "ts" → y ≠ "tk" → ρ.vars y = τ2.vars y) E
    (by rw [← hE]; exact hR) h9 (by have := le_pow_nine E; omega) (by decide)
    (by decide) (by decide) (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [a, h2 y a b]⟩)
    (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [b, h2 y a b]⟩) τ2
    ⟨⟨by simp [τ2, a1], fun _ _ _ => rfl⟩, by simp [τ2]⟩
  have hb3 : τ3.vars "tb0" = c := by rw [f3 "tb0" (by decide) (by decide)]; simp [τ2, τ1]
  set τ4 := τ3.setVar "tL" σ.ℓ
  have r4 : Run B (.assign "tL" (.get "a" (.add (.var "tb0") (.lit 2)))) τ3 τ4 5 :=
    (Run.assign (evalB_get (ev_add (ev_var hb3 (by omega)) (evalB_lit (by omega)) (by omega))
      (by rw [a3]; exact e2) bl)).mono (by simp [Expr.size])
  set τ5 := τ4.setVar "tp1" (c + 3)
  have r5 : Run B (.assign "tp1" (.add (.var "tb0") (.lit 3))) τ4 τ5 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ4, hb3]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  have hrun : Run B treeSet τ τ5 (20 * rhoPlus σ.k σ.q + 60) := by
    unfold treeSet
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    have := le_pow_nine E; rw [← hE] at this; omega
  obtain ⟨fa, fo, fi⟩ := run_frame hrun treeSet_warrs treeSet_reads treeSet_noWrite
  refine ⟨τ5, hrun, by simp [τ5, τ4, s3, hE], by simp [τ5, τ4], by simp [τ5], fun y hy => hrun.frame_var y
    (fun h => hy (treeSet_wvars y h)), fa, fo, fi⟩

end Lax185574Proofs.ResolveRam.Glue
