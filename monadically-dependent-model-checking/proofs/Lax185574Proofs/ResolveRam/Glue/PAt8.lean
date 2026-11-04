import Lax185574Proofs.ResolveRam.Glue.PAt7

/-!
The setup of the atom words of lem:resolve-lift.

The item word is `p :: g :: σ`, from `st[ow]`. `atHdr` reads the rank
and the arity of the tree, computes the two radii `rhoPlus k q` and
`rhoMinus k q` by `powLoop`, and points `tp1`, `tp2` at the atom list
(`atHdr_run`). `atSet` then reads the colors and their flags (`colSet`),
the sign, the number and the start of the colors of the table, and
writes the placeholder of the count (`atSet_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.ResolveRam
open Lax3.DistFO (rhoMinus rhoPlus)

/-- Read the header of the tree of the item word `ow`. -/
def atHdr : Com :=
  .seq (.assign "tb0" (.add (.get "st" (.var "ow")) (.lit 2)))
  (.seq (.assign "tE" (.mul (.add (.get "a" (.var "tb0")) (.get "a" (.add (.var "tb0") (.lit 1))))
    (.add (.get "a" (.add (.var "tb0") (.lit 1))) (.lit 1))))
  (.seq (powLoop "tRp" "tpk" "tE")
  (.seq (.assign "tE" (.mul (.add (.add (.get "a" (.var "tb0")) (.get "a" (.add (.var "tb0") (.lit 1))))
    (.lit 1)) (.get "a" (.add (.var "tb0") (.lit 1)))))
  (.seq (powLoop "tRm" "tpk" "tE")
  (.seq (.assign "tL" (.get "a" (.add (.var "tb0") (.lit 2))))
  (.seq (.assign "tp1" (.add (.var "tb0") (.lit 3))) (.assign "tp2" (.add (.var "tb0") (.lit 3)))))))))

/-- The scalars that `atHdr` writes. -/
def atHV : List String := ["tb0", "tE", "tRp", "tpk", "tRm", "tL", "tp1", "tp2"]

theorem atHdr_wvars : ∀ y ∈ atHdr.wvars, y ∈ atHV := by decide

theorem atHdr_warrs : atHdr.warrs = [] := by decide

theorem atHdr_reads : ¬ atHdr.reads := by decide

theorem atHdr_noWrite : atHdr.NoWrite := by decide

theorem rhoMinus_le (k q : ℕ) : rhoMinus k q ≤ rhoPlus k q := by
  unfold rhoMinus rhoPlus
  apply Nat.pow_le_pow_right (by norm_num)
  nlinarith

/-- **The header of the tree.** -/
theorem atHdr_run {B : ℕ} {ws : List (List ℕ)} {ow p g : ℕ} {σ : TypeTree} {τ : Env}
    (hw : WordsAt ws τ) (how : ow < ws.length) (hit : ws[ow] = p :: g :: toWord σ)
    (howv : τ.vars "ow" = ow) (hB : total ws + ws.length + 4 < B) (hv : ∀ v ∈ ws[ow], v < B)
    (hR : rhoPlus σ.k σ.q < B) (h9 : 9 < B) :
    ∃ τ', Run B atHdr τ τ' (40 * rhoPlus σ.k σ.q + 100) ∧
      τ'.vars "tRp" = rhoPlus σ.k σ.q ∧ τ'.vars "tRm" = rhoMinus σ.k σ.q ∧ τ'.vars "tL" = σ.ℓ ∧
      τ'.vars "tp1" = off ws ow + 5 ∧ τ'.vars "tp2" = off ws ow + 5 ∧
      (∀ y, y ∉ atHV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hoff := off_add_le how
  have hst := hw.st ow how
  have hl5 : 5 ≤ ws[ow].length := by rw [hit, FarRam.toWord_typeTree]; simp
  set c := off ws ow
  have e : ∀ j (hj : j < ws[ow].length), (τ.arrs "a")[c + j]? = some ws[ow][j] := hw.a ow how
  have e0 : (τ.arrs "a")[c + 2]? = some σ.k := by rw [e 2 (by omega)]; simp [hit, FarRam.toWord_typeTree]
  have e1 : (τ.arrs "a")[c + 2 + 1]? = some σ.q := by
    rw [show c + 2 + 1 = c + 3 by omega, e 3 (by omega)]; simp [hit, FarRam.toWord_typeTree]
  have e2 : (τ.arrs "a")[c + 2 + 2]? = some σ.ℓ := by
    rw [show c + 2 + 2 = c + 4 by omega, e 4 (by omega)]; simp [hit, FarRam.toWord_typeTree]
  have bk : σ.k < B := hv _ (by rw [hit, FarRam.toWord_typeTree]; simp)
  have bq : σ.q < B := hv _ (by rw [hit, FarRam.toWord_typeTree]; simp)
  have bl : σ.ℓ < B := hv _ (by rw [hit, FarRam.toWord_typeTree]; simp)
  set Ep := (σ.k + σ.q) * (σ.q + 1)
  set Em := (σ.k + σ.q + 1) * σ.q
  have hEp : rhoPlus σ.k σ.q = 9 ^ Ep := rfl
  have hEm : rhoMinus σ.k σ.q = 9 ^ Em := rfl
  have hRm := rhoMinus_le σ.k σ.q
  have hEpB : Ep < B := lt_trans (le_pow_nine Ep) (by rw [← hEp]; exact hR)
  have hEmB : Em < B := lt_of_lt_of_le (le_pow_nine Em) (by rw [← hEm]; omega)
  have hkq : σ.k + σ.q ≤ Ep := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : σ.q + 1 ≤ Ep ∨ σ.k + σ.q = 0 := by
    rcases Nat.eq_zero_or_pos (σ.k + σ.q) with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  have hkq1 : σ.k + σ.q + 1 ≤ Em ∨ σ.q = 0 := by
    rcases Nat.eq_zero_or_pos σ.q with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_right _ h)
  have hkq2 : σ.k + σ.q + 1 < B := by
    rcases Nat.eq_zero_or_pos Ep with h | h
    · have : σ.k + σ.q = 0 := by omega
      omega
    · have h1 := le_pow_nine (Ep - 1)
      have h2 : 9 ^ Ep = 9 * 9 ^ (Ep - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h3 : 9 ^ Ep < B := by rw [← hEp]; exact hR
      omega
  set τ1 := τ.setVar "tb0" (c + 2)
  have r1 : Run B (.assign "tb0" (.add (.get "st" (.var "ow")) (.lit 2))) τ τ1 5 :=
    (Run.assign (ev_add (evalB_get (ev_var (v := ow) howv (by omega)) hst (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  have a1 : τ1.arrs = τ.arrs := by simp [τ1]
  have gk : ∀ ρ : Env, ρ.arrs = τ.arrs → ρ.vars "tb0" = c + 2 →
      (Expr.get "a" (.var "tb0")).evalB B ρ = some σ.k := fun ρ ha hb =>
    evalB_get (ev_var hb (by omega)) (by rw [ha]; exact e0) bk
  have gq : ∀ ρ : Env, ρ.arrs = τ.arrs → ρ.vars "tb0" = c + 2 →
      (Expr.get "a" (.add (.var "tb0") (.lit 1))).evalB B ρ = some σ.q := fun ρ ha hb =>
    evalB_get (ev_add (ev_var hb (by omega)) (evalB_lit (by omega)) (by omega)) (by rw [ha]; exact e1) bq
  set τ2 := τ1.setVar "tE" Ep
  have r2 : Run B (.assign "tE" (.mul (.add (.get "a" (.var "tb0")) (.get "a" (.add (.var "tb0") (.lit 1))))
      (.add (.get "a" (.add (.var "tb0") (.lit 1))) (.lit 1)))) τ1 τ2 20 := by
    refine (Run.assign (evalB_bin (ev_add (gk τ1 a1 (by simp [τ1])) (gq τ1 a1 (by simp [τ1])) (by omega))
      (ev_add (gq τ1 a1 (by simp [τ1])) (evalB_lit (by omega)) (by rcases hq1 with h | h <;> omega))
      (by simp only [Bop.apply]; omega))).mono ?_
    simp [Expr.size]
  obtain ⟨τ3, r3, ⟨a3, f3⟩, s3, n3⟩ := powLoop_run (B := B) (x := "tRp") (i := "tpk") (n := "tE")
    (fun ρ => ρ.arrs = τ.arrs ∧ ∀ y, y ≠ "tRp" → y ≠ "tpk" → ρ.vars y = τ2.vars y) Ep
    (by rw [← hEp]; exact hR) h9 (by have := le_pow_nine Ep; omega) (by decide)
    (by decide) (by decide) (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [a, h2 y a b]⟩)
    (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [b, h2 y a b]⟩) τ2
    ⟨⟨by simp [τ2, a1], fun _ _ _ => rfl⟩, by simp [τ2]⟩
  have hb3 : τ3.vars "tb0" = c + 2 := by rw [f3 "tb0" (by decide) (by decide)]; simp [τ2, τ1]
  set τ4 := τ3.setVar "tE" Em
  have r4 : Run B (.assign "tE" (.mul (.add (.add (.get "a" (.var "tb0")) (.get "a" (.add (.var "tb0") (.lit 1))))
      (.lit 1)) (.get "a" (.add (.var "tb0") (.lit 1))))) τ3 τ4 20 := by
    refine (Run.assign (evalB_bin (ev_add (ev_add (gk τ3 a3 hb3) (gq τ3 a3 hb3) (by omega))
      (evalB_lit (by omega)) (by omega)) (gq τ3 a3 hb3)
      (by simp only [Bop.apply]; exact hEmB))).mono ?_
    simp [Expr.size]
  obtain ⟨τ5, r5, ⟨a5, f5⟩, s5, n5⟩ := powLoop_run (B := B) (x := "tRm") (i := "tpk") (n := "tE")
    (fun ρ => ρ.arrs = τ.arrs ∧ ∀ y, y ≠ "tRm" → y ≠ "tpk" → ρ.vars y = τ4.vars y) Em
    (by rw [← hEm]; omega) h9 (by have := le_pow_nine Em; omega) (by decide)
    (by decide) (by decide) (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [a, h2 y a b]⟩)
    (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [b, h2 y a b]⟩) τ4
    ⟨⟨by simp [τ4, a3], fun _ _ _ => rfl⟩, by simp [τ4]⟩
  have hb5 : τ5.vars "tb0" = c + 2 := by rw [f5 "tb0" (by decide) (by decide)]; simp [τ4, hb3]
  set τ6 := τ5.setVar "tL" σ.ℓ
  have r6 : Run B (.assign "tL" (.get "a" (.add (.var "tb0") (.lit 2)))) τ5 τ6 5 :=
    (Run.assign (evalB_get (ev_add (ev_var hb5 (by omega)) (evalB_lit (by omega)) (by omega))
      (by rw [a5]; exact e2) bl)).mono (by simp [Expr.size])
  set τ7 := τ6.setVar "tp1" (c + 5)
  have r7 : Run B (.assign "tp1" (.add (.var "tb0") (.lit 3))) τ6 τ7 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ6, hb5]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size]) |>.congr rfl
  set τ8 := τ7.setVar "tp2" (c + 5)
  have r8 : Run B (.assign "tp2" (.add (.var "tb0") (.lit 3))) τ7 τ8 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ7, τ6, hb5]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  have hrun : Run B atHdr τ τ8 (40 * rhoPlus σ.k σ.q + 100) := by
    unfold atHdr
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono ?_
    have := le_pow_nine Ep; rw [← hEp] at this
    have := le_pow_nine Em; rw [← hEm] at this
    omega
  obtain ⟨fa, fo, fi⟩ := run_frame hrun atHdr_warrs atHdr_reads atHdr_noWrite
  refine ⟨τ8, hrun, ?_, ?_, by simp [τ8, τ7, τ6], by simp [τ8, τ7], by simp [τ8],
    fun y hy => hrun.frame_var y (fun h => hy (atHdr_wvars y h)), fa, fo, fi⟩
  · simp only [τ8, τ7, τ6, vars_setVar]
    simp only [show ("tRp" : String) ≠ "tp2" by decide, show ("tRp" : String) ≠ "tp1" by decide,
      show ("tRp" : String) ≠ "tL" by decide, if_false]
    rw [f5 "tRp" (by decide) (by decide)]; simp [τ4, s3, hEp]
  · simp [τ8, τ7, τ6, s5, hEm]

/-- Read the colors, the sign and the color table, and write the placeholder of the count. -/
def atSet : Com :=
  .seq colSet (.seq (.assign "tsg" (.var "gS")) (.seq (.assign "tnc" (.div (.get "ln" (.var "oc")) (.lit 3)))
    (.seq (.assign "tcb0" (.get "st" (.var "oc"))) (.seq (.assign "fp" (.var "po"))
      (.seq (push1 "OB" "po" (.lit 0)) (.assign "fc" (.lit 0)))))))

/-- The scalars that `atSet` writes. -/
def atSV : List String := colV ++ ["tsg", "tnc", "tcb0", "fp", "po", "fc"]

theorem length_ct (cs : List ℕ) (f g : ℕ → ℕ) :
    (cs.flatMap fun Y => [Y, f Y, g Y]).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons a l ih => simp [ih]; ring

/-- **The colors, the sign, the table and the placeholder.** -/
theorem atSet_run {W : ℕ} {ws : List (List ℕ)} {oc P Q sg : ℕ} {cs : List ℕ} {f g : ℕ → ℕ}
    {pre : List ℕ} {τ : Env}
    (hw : WordsAt ws τ) (hoc : oc < ws.length) (hct : ws[oc] = cs.flatMap fun Y => [Y, f Y, g Y])
    (hocv : τ.vars "oc" = oc) (hP : τ.vars "gP" = P) (hQ : τ.vars "gQ" = Q) (hS : τ.vars "gS" = sg)
    (hPB : P ≤ W) (hQB : Q ≤ W) (hsg : sg ≤ 1) (hB : total ws + ws.length + 4 < W + 1)
    (hv : ∀ v ∈ ws[oc], v < W + 1) (hF : Filled "OB" "po" pre τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hpre : pre.length + 1 ≤ W) :
    ∃ τ', Run (W + 1) atSet τ τ' (40 * ws[oc].length + 140) ∧
      τ'.vars "tcP" = bv (decide (P ∈ cs)) ∧ τ'.vars "tcQ" = bv (decide (Q ∈ cs)) ∧
      τ'.vars "tP" = P ∧ τ'.vars "tQ" = Q ∧ τ'.vars "tsg" = sg ∧ τ'.vars "tnc" = cs.length ∧
      τ'.vars "tcb0" = off ws oc ∧ τ'.vars "fp" = pre.length ∧ Em pre [] τ' ∧ OFr τ τ' atSV := by
  obtain ⟨τ1, r1, cP1, cQ1, P1, Q1, f1, a1, o1, i1⟩ := colSet_run (B := W + 1) hw hoc hct hocv hP hQ
    (by omega) (by omega) hB hv
  have o1' : OFr τ τ1 colV := ⟨f1, fun b _ => by rw [a1], by rw [a1], o1, i1⟩
  have k1 : ∀ y ∈ ["oc", "gS", "po"], τ1.vars y = τ.vars y := fun y hy => f1 y (by
    simp at hy; rcases hy with rfl | rfl | rfl <;> decide)
  have hoff := off_add_le hoc
  have hlen : ws[oc].length = 3 * cs.length := by rw [hct, length_ct]
  set τ2 := τ1.setVar "tsg" sg
  have r2 : Run (W + 1) (.assign "tsg" (.var "gS")) τ1 τ2 2 :=
    Run.assign (ev_var (by rw [k1 "gS" (by simp), hS]) (by omega))
  set τ3 := τ2.setVar "tnc" cs.length
  have r3 : Run (W + 1) (.assign "tnc" (.div (.get "ln" (.var "oc")) (.lit 3))) τ2 τ3 5 := by
    have e := evalB_bin (op := .div) (B := W + 1) (σ := τ2) (e := .get "ln" (.var "oc")) (f := .lit 3)
      (m := ws[oc].length) (n := 3)
      (evalB_get (ev_var (v := oc) (by simp [τ2, k1 "oc" (by simp), hocv]) (by omega))
        (by simp only [τ2, arrs_setVar, a1]; exact hw.ln oc hoc) (by omega)) (evalB_lit (by omega))
      (by simp only [Bop.apply]; omega)
    simp only [Bop.apply, hlen, Nat.mul_div_cancel_left _ (show 0 < 3 by norm_num)] at e
    exact (Run.assign e).mono (by simp [Expr.size])
  set τ4 := τ3.setVar "tcb0" (off ws oc)
  have r4 : Run (W + 1) (.assign "tcb0" (.get "st" (.var "oc"))) τ3 τ4 3 :=
    (Run.assign (evalB_get (ev_var (v := oc) (by simp [τ3, τ2, k1 "oc" (by simp), hocv]) (by omega))
      (by simp only [τ3, τ2, arrs_setVar, a1]; exact hw.st oc hoc) (by omega))).mono
      (by simp [Expr.size])
  set τ5 := τ4.setVar "fp" pre.length
  have r5 : Run (W + 1) (.assign "fp" (.var "po")) τ4 τ5 2 :=
    Run.assign (ev_var (by simp [τ4, τ3, τ2, k1 "po" (by simp), hF.pos]) (by omega))
  have F4 : Filled "OB" "po" pre τ5 :=
    hF.congr (by simp [τ5, τ4, τ3, τ2, k1 "po" (by simp)]) (by simp [τ5, τ4, τ3, τ2, a1])
  obtain ⟨τ6, r6, F6, o6⟩ := push1_ofr (W := W) (e := .lit 0) (v := 0) F4 (evalB_lit (by omega))
    (by simp [τ5, τ4, τ3, τ2, a1, hOB]; omega) (by omega)
  set τ7 := τ6.setVar "fc" 0
  have r7 : Run (W + 1) (.assign "fc" (.lit 0)) τ6 τ7 2 := Run.assign (evalB_lit (by omega))
  have oall : OFr τ τ7 atSV := ((((((o1'.trans (OFr.setVar τ1 "tsg" sg)).trans (OFr.setVar τ2 "tnc" _)).trans
    (OFr.setVar τ3 "tcb0" _)).trans (OFr.setVar τ4 "fp" _)).trans o6).trans (OFr.setVar τ6 "fc" 0)).mono
    (by intro y hy; simp only [atSV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢;
        tauto)
  have g6 : ∀ y, y ≠ "po" → y ≠ "fc" → τ7.vars y = τ5.vars y := fun y h1 h2 => by
    simp only [τ7, vars_setVar, h2, if_false]; exact o6.vars y (by simpa using h1)
  refine ⟨τ7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, by simp [τ7]⟩, oall⟩
  · unfold atSet
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono
      (by simp [Expr.size])
  · rw [g6 _ (by decide) (by decide)]; simp [τ5, τ4, τ3, τ2, cP1]
  · rw [g6 _ (by decide) (by decide)]; simp [τ5, τ4, τ3, τ2, cQ1]
  · rw [g6 _ (by decide) (by decide)]; simp [τ5, τ4, τ3, τ2, P1]
  · rw [g6 _ (by decide) (by decide)]; simp [τ5, τ4, τ3, τ2, Q1]
  · rw [g6 _ (by decide) (by decide)]; simp [τ5, τ4, τ3, τ2]
  · rw [g6 _ (by decide) (by decide)]; simp [τ5, τ4, τ3]
  · rw [g6 _ (by decide) (by decide)]; simp [τ5, τ4]
  · rw [g6 _ (by decide) (by decide)]; simp [τ5]
  · simpa [frames] using F6.congr (τ' := τ7) (by simp [τ7]) (by simp [τ7])

end Lax185574Proofs.ResolveRam.Glue
