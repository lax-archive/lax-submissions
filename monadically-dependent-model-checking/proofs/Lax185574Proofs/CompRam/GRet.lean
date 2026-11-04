import Lax185574Proofs.CompRam.GRetStep

/-!
Round `j ≥ 1` of the glue command of lem:compose: the input of the round
in `x` (`img_facts`), the scalars before the step by phase (`roundJ_pre1`,
`roundJ_pre2`),
and the output of the round (`roundJ_run`).
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### The round -/

theorem img_facts {X : List ℕ} {j : ℕ} {S : List Fr} {o : List ℕ}
    (hX : X.take (imgJ j S o).length = imgJ j S o) :
    X.drop 2 = toWord (stWords S) ++ (toWord o ++ X.drop (imgJ j S o).length) ∧
      X[1]? = some j ∧ X[2]? = some (stWords S).length ∧
      X[(stWord j S).length]? = some o.length ∧
      X.drop ((stWord j S).length + 1) = o ++ X.drop (imgJ j S o).length := by
  have hX' : X = imgJ j S o ++ X.drop (imgJ j S o).length := by
    conv_lhs => rw [← List.take_append_drop (imgJ j S o).length X]
    rw [hX]
  set D := X.drop (imgJ j S o).length
  have hL := length_stWord j S
  have hli : (imgJ j S o).length = (stWord j S).length + (o.length + 1) := by
    simp [imgJ, toWord_listNat] <;> omega
  have hgetI : ∀ i v, (imgJ j S o).getD i 0 = v → i < (imgJ j S o).length → X[i]? = some v := by
    intro i v hv hi
    rw [hX', List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hv
    simpa using hv
  refine ⟨?_, hgetI 1 j (imgJ_get1 j S o) (by omega), hgetI 2 _ (imgJ_get2 j S o) (by omega), ?_, ?_⟩
  · rw [hX', List.drop_append_of_le_length (by omega), imgJ_drop2, List.append_assoc]
  · have h1 := imgJ_dropL j S o
    have h2 : X.drop (stWord j S).length = (o.length :: o) ++ D := by
      rw [hX', List.drop_append_of_le_length (by omega), h1]
    exact getElem_of_drop_cons h2
  · have h1 := imgJ_dropL j S o
    rw [hX', ← List.drop_drop, List.drop_append_of_le_length (by omega), h1]
    simp

/-- The first scalars of round `j ≥ 1`. -/
theorem roundJ_pre1 {W M j : ℕ} {σ : Env} {S : List Fr} {o : List ℕ} (hC : Ctx W M σ)
    (hX : (σ.arrs "x").take (imgJ j S o).length = imgJ j S o) (himg : (imgJ j S o).length + 512 ≤ M)
    (hL : σ.vars "L" = (stWord j S).length) (h7 : 7 ≤ (stWords S).length) :
    ∃ σ7, Run (W + 1) (seqs [asg "jr" (X (N 1)), asg "j1" (.add (V "jr") (N 1)), asg "n" (X (N 2)),
        .ite (.lt (V "n") (N 14)) (asg "nb" (V "n")) (asg "nb" (N 14)), locW,
        asg "oS" (.add (V "L") (N 1)), asg "oL" (X (V "L"))]) σ σ7 650 ∧
      Ctx W M σ7 ∧ σ7.arrs "x" = σ.arrs "x" ∧ σ7.vars "jr" = j ∧ σ7.vars "j1" = j + 1 ∧
      σ7.vars "n" = (stWords S).length ∧ σ7.vars "oS" = (stWord j S).length + 1 ∧
      σ7.vars "oL" = o.length ∧
      (∀ i < min (stWords S).length 14, (σ7.arrs "wp").getD i 0 = frPos (σ.arrs "x") 2 i) ∧
      (∀ z, z ∉ ["jr", "j1", "n", "nb", "y", "wi", "oS", "oL"] → σ7.vars z = σ.vars z) ∧
      (σ7.arrs "OB").length = (σ.arrs "OB").length ∧ σ7.out = σ.out := by
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨hx2, hx1, hxn, hxL, -⟩ := img_facts hX
  have hLw := length_stWord j S
  have hli : (imgJ j S o).length = (stWord j S).length + (o.length + 1) := by
    simp [imgJ, toWord_listNat] <;> omega
  have hwl := count_lt_toWord (stWords S)
  have hxl := hC.xl
  have hjM := hC.xv _ (List.mem_of_getElem? hx1)
  set σ1 := σ.setVar "jr" j
  set σ2 := σ1.setVar "j1" (j + 1)
  set σ3 := σ2.setVar "n" (stWords S).length
  set σ4 := σ3.setVar "nb" (min (stWords S).length 14)
  have r1 : Run (W + 1) (asg "jr" (X (N 1))) σ σ1 3 :=
    (Run.assign (evalB_get (evalB_lit (by omega)) hx1 (by omega))).mono (by simp)
  have r2 : Run (W + 1) (asg "j1" (.add (V "jr") (N 1))) σ1 σ2 4 :=
    (Run.assign (by simp [σ1]; omega)).mono (by simp)
  have r3 : Run (W + 1) (asg "n" (X (N 2))) σ2 σ3 3 :=
    (Run.assign (evalB_get (evalB_lit (by omega)) (by simpa [σ2, σ1] using hxn) (by omega))).mono
      (by simp)
  have c : (Cond.lt (V "n") (N 14)).evalB (W + 1) σ3 = some (decide ((stWords S).length < 14)) :=
    condLt_var_lit_eq (by simp [σ3]) (by omega) (by omega)
  have r4 : Run (W + 1) (.ite (.lt (V "n") (N 14)) (asg "nb" (V "n")) (asg "nb" (N 14))) σ3 σ4 6 := by
    by_cases h14 : (stWords S).length < 14
    · have e : σ4 = σ3.setVar "nb" (stWords S).length := by simp [σ4, min_eq_left h14.le]
      rw [e]
      exact (Run.ite_true (by rw [c]; simpa using h14) (Run.assign (by simp [σ3]; omega))).mono
        (by simp [Cond.size, Expr.size])
    · have e : σ4 = σ3.setVar "nb" 14 := by simp only [σ4]; congr 1; omega
      rw [e]
      exact (Run.ite_false (by rw [c]; simpa using h14) (Run.assign (by simp <;> omega))).mono
        (by simp [Cond.size, Expr.size])
  have fr4 : OFr σ σ4 ["jr", "j1", "n", "nb"] :=
    (((OFr.setVar σ "jr" _).trans (OFr.setVar σ1 "j1" _)).trans (OFr.setVar σ2 "n" _)).trans
      (OFr.setVar σ3 "nb" _)
  have hC4 : Ctx W M σ4 := hC.ofr fr4 (by decide)
  have hx4' : σ4.arrs "x" = σ.arrs "x" := fr4.arrs "x" (by decide)
  obtain ⟨σ5, r5, hwp5, hv5, ha5, hwl5, ho5, -⟩ := locW_run hC4 (ws := stWords S)
    (r := toWord o ++ (σ.arrs "x").drop (imgJ j S o).length) (by rw [hx4']; exact hx2)
    (by simp [σ4]) (by simp [σ4]) (by omega)
  have hx5 : σ5.arrs "x" = σ.arrs "x" := by rw [ha5 "x" (by decide), hx4']
  have hC5 : Ctx W M σ5 := ⟨by rw [hv5 "W" (by decide), hC4.hW], by rw [hx5]; exact hxl,
    by rw [ha5 "OB" (by decide), hC4.ol], by rw [hwl5, hC4.wl], by rw [hx5]; exact hC.xv, hm, hR⟩
  have hnb : σ4.vars "nb" = min (stWords S).length 14 := by simp [σ4]
  have hL5 : σ5.vars "L" = (stWord j S).length := by
    rw [hv5 "L" (by decide), fr4.vars "L" (by decide), hL]
  set σ6 := σ5.setVar "oS" ((stWord j S).length + 1)
  set σ7 := σ6.setVar "oL" o.length
  have rb : Run (W + 1) (seqs [asg "oS" (.add (V "L") (N 1)), asg "oL" (X (V "L"))]) σ5 σ7 7 :=
    (Run.seqs_cons (by simp) (Run.assign (by simp [hL5]; omega)) (Run.seqs_one (Run.assign
      (evalB_get (evalB_var (by simp [σ6, hL5]; omega)) (by simpa [σ6, hL5, hx5] using hxL)
        (by omega))))).mono (by simp)
  have hv7 : ∀ z, z ∉ ["jr", "j1", "n", "nb", "y", "wi", "oS", "oL"] → σ7.vars z = σ.vars z := by
    intro z hz
    have : z ≠ "oS" ∧ z ≠ "oL" := by simp at hz; tauto
    simp only [σ7, σ6, Env.setVar, if_neg this.1, if_neg this.2]
    rw [hv5 z (by simp at hz ⊢; tauto), fr4.vars z (by simp at hz ⊢; tauto)]
  refine ⟨σ7, (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
    (Run.seqs_cons (by simp) r4 (Run.seqs_cons (by simp) r5 rb))))).mono (by omega),
    (hC5.setVar (by decide) _).setVar (by decide) _, by simp [σ7, σ6, hx5],
    by simp [σ7, σ6, hv5 "jr" (by decide), σ4, σ3, σ2, σ1],
    by simp [σ7, σ6, hv5 "j1" (by decide), σ4, σ3, σ2], by simp [σ7, σ6, hv5 "n" (by decide), σ4, σ3],
    by simp [σ7, σ6], by simp [σ7], fun i hi => ?_, hv7, by simp [σ7, σ6, ha5 "OB" (by decide), fr4.len],
    by simp [σ7, σ6, ho5, fr4.out]⟩
  rw [show σ7.arrs "wp" = σ5.arrs "wp" by simp [σ7, σ6], hwp5 i (by rw [hnb]; exact hi), hx4']


/-- The top frame, the part of the answer and the rest of the stack. -/
theorem roundJ_pre2 {W M j : ℕ} {σ σ7 : Env} {f : Fr} {S' : List Fr} {o b : List ℕ}
    (hC7 : Ctx W M σ7) (hx7 : σ7.arrs "x" = σ.arrs "x")
    (hX : (σ.arrs "x").take (imgJ j (f :: S') o).length = imgJ j (f :: S') o)
    (himg : (imgJ j (f :: S') o).length + 512 ≤ M) (hx4 : ∀ v ∈ σ.arrs "x", 4 * v + 4 < M)
    (hj1 : σ7.vars "j1" = j + 1) (hjM : j + 1 < M) (hn : σ7.vars "n" = (stWords (f :: S')).length)
    (hL : σ7.vars "L" = (stWord j (f :: S')).length) (hoS : σ7.vars "oS" = (stWord j (f :: S')).length + 1)
    (hoL : σ7.vars "oL" = o.length)
    (hwp : ∀ i < min (stWords (f :: S')).length 14,
      (σ7.arrs "wp").getD i 0 = frPos (σ.arrs "x") 2 i) (hpo : σ7.vars "po" = 0)
    (hpick : pick f.ph o = b) :
    ∃ σ12, Run (W + 1) (seqs [ldG 0, asg "tp" (V "gp"), asg "td" (V "gd"), pickCmd, ldRest 1]) σ7 σ12 400 ∧
      Top W M j f S' b σ12 ∧ Keep σ7 σ12 := by
  have hR := hC7.room
  have hm := hC7.m16
  obtain ⟨hx2, -, -, -, hxo⟩ := img_facts hX
  have hLw := length_stWord j (f :: S')
  have hli : (imgJ j (f :: S') o).length = (stWord j (f :: S')).length + (o.length + 1) := by
    simp [imgJ, toWord_listNat] <;> omega
  have hwl := count_lt_toWord (stWords (f :: S'))
  have hw7 : 7 ≤ (stWords (f :: S')).length := by rw [length_stWords]; simp
  rw [← hx7] at hx2 hxo hx4 hwp
  obtain ⟨σ8, r8, hg8, hgx8, fr8⟩ := ldG_run hC7 hx2 (by omega) 0 f
    (by omega) (by rw [List.drop_zero, stWords_take7]) (fun i hi => hwp i (by omega))
  set σ9 := σ8.setVar "tp" f.ph
  set σ10 := σ9.setVar "td" f.d
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := hg8.nums
  have rc : Run (W + 1) (seqs [asg "tp" (V "gp"), asg "td" (V "gd")]) σ8 σ10 4 :=
    (Run.seqs_cons (by simp) (Run.assign (by simp [hg8.ph]; omega))
      (Run.seqs_one (Run.assign (by simp [σ9, hg8.d]; omega)))).mono (by simp)
  have fr10 : OFr σ8 σ10 ["tp", "td"] := (OFr.setVar σ8 "tp" _).trans (OFr.setVar σ9 "td" _)
  have fr810 := fr8.trans fr10
  have hC10 : Ctx W M σ10 := hC7.ofr fr810 (by decide)
  have hx10 : σ10.arrs "x" = σ7.arrs "x" := fr810.arrs "x" (by decide)
  obtain ⟨σ11, r11, hb11, hbs11, fr11⟩ := pick_run (ph := f.ph) (o := o)
    (rest := (σ7.arrs "x").drop (imgJ j (f :: S') o).length) hC10 (by simp [σ10, σ9]) (by omega)
    (by rw [fr810.vars "oS" (by decide), hoS]) (by rw [fr810.vars "oL" (by decide), hoL])
    (by rw [hx10]; exact hxo) (by omega)
  rw [hpick] at hb11
  have fr811 := fr810.trans fr11
  have hC11 := hC10.ofr fr11 (by decide)
  have hx11 : σ11.arrs "x" = σ7.arrs "x" := fr811.arrs "x" (by decide)
  obtain ⟨σ12, r12, hrest12, hcnt12, fr12⟩ := ldRest_run hC11 (ws := stWords (f :: S'))
    (by rw [hx11]; exact hx2) (by omega) 1 (by omega) (by omega)
    (by rw [fr811.vars "L" (by decide), hL, hLw]) (by rw [fr811.vars "n" (by decide), hn])
    (by rw [fr811.arrs "wp" (by decide), hx11]; exact hwp 6 (by omega))
  have fr := fr811.trans fr12
  have hx12 : σ12.arrs "x" = σ7.arrs "x" := fr.arrs "x" (by decide)
  rw [stWords_drop7] at hrest12
  refine ⟨σ12, Run.seqs_cons (by simp) r8 (Run.seqs_app2 (a := [asg "tp" (V "gp"), asg "td" (V "gd")])
    (by simp) (by simp) rc (Run.seqs_cons (by simp) r11 (Run.seqs_one r12))) |>.mono (by norm_num), ?_,
    Keep.of_ofr fr (by decide) (by decide) (by decide)⟩
  exact ⟨hC11.ofr fr12 (by decide), by rw [hx12]; exact hx4, ⟨_, by rw [hx12]; exact hx2⟩,
    by omega, ⟨by rw [fr.vars "po" (by decide), hpo]; rfl, fun i hi => absurd hi (by simp)⟩,
    ((hg8.ofr fr10 (by decide)).ofr fr11 (by decide)).ofr fr12 (by decide), hb11.ofr fr12 (by decide)
      (by decide), by rw [fr12.vars "bs" (by decide)]; omega, hrest12,
    by rw [hcnt12, stWords_cons]; simp [frWords],
    by rw [fr.vars "j1" (by decide), hj1], hjM,
    by rw [fr.vars "n" (by decide), hn], by rw [fr.vars "L" (by decide), hL, hLw],
    fun i hi => by rw [fr.arrs "wp" (by decide), hx12]; exact hwp i hi,
    by rw [fr12.vars "td" (by decide), fr11.vars "td" (by decide)]; simp [σ10],
    by rw [fr12.vars "tp" (by decide), fr11.vars "tp" (by decide)]; simp [σ10, σ9],
    by rw [fr12.vars "gx" (by decide), fr11.vars "gx" (by decide), fr10.vars "gx" (by decide), hgx8]⟩


theorem toWord_stWords_ge (f : Fr) (S : List Fr) : 14 ≤ (toWord (stWords (f :: S))).length := by
  rw [toWord_words, stWords_cons, frames_append]
  simp [frWords, frames]
  omega

/-- **Round `j ≥ 1`.** -/
theorem roundJ_run {W M : ℕ} {σ : Env} (P : SzP) {j : ℕ} {f : Fr} {S' : List Fr} {qq : Qry}
    {b o : List ℕ} (hC : Ctx W M σ) (hx4 : ∀ v ∈ σ.arrs "x", 4 * v + 4 < M)
    (hX : (σ.arrs "x").take (imgJ j (f :: S') o).length = imgJ j (f :: S') o)
    (himg : (imgJ j (f :: S') o).length + 512 ≤ M) (hL : σ.vars "L" = (stWord j (f :: S')).length)
    (hF : Filled "OB" "po" [] σ) (hcur : ROKs P (.call (f :: S') qq)) (hfit : Fits f.ph qq)
    (hpick : pick f.ph o = b) (hnext : ROKs P (round (f :: S') b)) (hj : j + 1 < M) :
    ∃ σ' ob K, Run (W + 1) roundJ σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      σ'.vars "jr" = j ∧ 16 * ob.length ≤ W ∧
      K ≤ 1000 * ((imgJ j (f :: S') o).length + ob.length + 1) ∧
      σ'.vars "W" = σ.vars "W" ∧ σ'.vars "ovf" = σ.vars "ovf" ∧ σ'.arrs "x" = σ.arrs "x" ∧
      (σ'.arrs "OB").length = (σ.arrs "OB").length ∧ σ'.out = σ.out := by
  have hR := hC.room
  obtain ⟨⟨-, hSf, hS3⟩, f', S'', hfS, hQ⟩ := hcur
  obtain ⟨rfl, rfl⟩ := List.cons.inj hfS
  have hf := hSf f (by simp)
  have hpar : ∀ p S'', S' = p :: S'' → FOK P p ∧ p.ph = 3 := fun p S'' e =>
    ⟨hSf p (by simp [e]), hS3 p (by simp [e])⟩
  have hq : f.ph = 0 ∨ f.ph = 1 ∨ f.ph = 2 ∨ f.ph = 4 ∨ f.ph = 5 := by
    rcases hQ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hw7 : 7 ≤ (stWords (f :: S')).length := by rw [length_stWords]; simp
  obtain ⟨σ7, r7, hC7, hx7, hjr7, hj17, hn7, hoS7, hoL7, hwp7, hv7, hob7, hout7⟩ :=
    roundJ_pre1 hC hX himg hL hw7
  obtain ⟨σ12, r12, hT, kp12⟩ := roundJ_pre2 (f := f) (S' := S') (b := b) hC7 hx7 hX himg hx4 hj17 hj hn7
    (by rw [hv7 "L" (by decide), hL]) hoS7 hoL7 hwp7 (by rw [hv7 "po" (by decide), hF.pos]; rfl) hpick
  obtain ⟨σ13, ob, K13, r13, B13, hl13, hK13, kp13⟩ := disp_run P hT hf hq hpar hnext
  have hLw := length_stWord j (f :: S')
  have hli : (imgJ j (f :: S') o).length = (stWord j (f :: S')).length + (o.length + 1) := by
    simp [imgJ, toWord_listNat] <;> omega
  have hT14 := toWord_stWords_ge f S'
  refine ⟨σ13, ob, 650 + (400 + K13), ?_, B13, by rw [kp13.jr, kp12.jr, hjr7], by omega, ?_,
    by rw [kp13.W, kp12.W, hv7 "W" (by decide)], by rw [kp13.ovf, kp12.ovf, hv7 "ovf" (by decide)],
    by rw [kp13.x, kp12.x, hx7], by rw [kp13.ob, kp12.ob, hob7], by rw [kp13.out, kp12.out, hout7]⟩
  · exact Run.seqs_app2 (a := [asg "jr" (X (N 1)), asg "j1" (.add (V "jr") (N 1)), asg "n" (X (N 2)),
      .ite (.lt (V "n") (N 14)) (asg "nb" (V "n")) (asg "nb" (N 14)), locW,
      asg "oS" (.add (V "L") (N 1)), asg "oL" (X (V "L"))]) (by simp) (by simp) r7
      (Run.seqs_app2 (a := [ldG 0, asg "tp" (V "gp"), asg "td" (V "gd"), pickCmd, ldRest 1])
        (by simp) (by simp) r12 (Run.seqs_one (c := dispCmd) r13))
  · clear * - hK13 hli hLw hT14
    omega

end Lax185574Proofs.CompRam
