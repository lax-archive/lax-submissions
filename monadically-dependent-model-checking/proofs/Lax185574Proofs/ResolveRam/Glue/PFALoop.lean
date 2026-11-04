import Lax185574Proofs.ResolveRam.Glue.PFA

/-!
The loop of the far filter of lem:resolve-lift over the members of the
answer of the far tree.

The answer, the word of the list `L` of tree words, is in `y` from `yo`.
`memLoop` runs the member test `passC` on every member and appends the
frames of the members that pass to the buffer, with their number in `pc`
(`memLoop_run`). The test is `memP` (`passW` on the words, with the radius
and the atoms of the shifted tree fixed).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- The test of a member word, for the shifted tree with arity `ℓσ`,
atoms `Aσ` and radius `R`. -/
def memP (Dw : DW) (ℓσ : ℕ) (Aσ : List (List ℕ)) (R : ℕ) (w : List ℕ) : Bool :=
  (w.getD 2 0 == 1) && (List.range ℓσ).any fun i => hop2W Dw Aσ i (listWords w 3) 0 R

theorem memP_tree (Dw : DW) (ℓσ : ℕ) (Aσ : List (List ℕ)) (R : ℕ) (ν : TypeTree) :
    memP Dw ℓσ Aσ R (toWord ν) = ((ν.ℓ == 1) && (List.range ℓσ).any fun i =>
      hop2W Dw Aσ i (Node.atoms ν.root).words 0 R) := by
  unfold memP; rw [listWords_tree_root, toWord_typeTree]; rfl

/-- Copy the frame at `tf` of `y` and count it. -/
def cpFr : Com :=
  .seq (.assign "tl" (.add (.get "y" (.var "tf")) (.lit 1)))
    (.seq (cpSeg "y" "tf" "tl") (.assign "pc" (.add (.var "pc") (.lit 1))))

/-- One member. -/
def faBody : Com :=
  .seq passC (.seq (.ite (.eq (.var "tF") (.lit 1)) cpFr .skip)
    (.assign "tf" (.add (.add (.var "tf") (.get "y" (.var "tf"))) (.lit 1))))

/-- The loop over the members. -/
def memLoop : Com :=
  .seq (.assign "pc" (.lit 0)) (.seq (.assign "tf" (.add (.var "yo") (.lit 1)))
    (.seq (.assign "tN" (.get "y" (.var "yo"))) (forUp "tm" (.var "tN") faBody)))

/-- The scalars that `memLoop` writes. -/
def loopV : List String := passV ++ ["tl", "pc", "po", "ci", "tf", "tN", "tm"]

theorem le_maxLen' {L : List (List ℕ)} {w : List ℕ} (h : w ∈ L) : w.length ≤ maxLen L := by
  induction L with
  | nil => simp at h
  | cons a l ih =>
    simp only [maxLen, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem filter_take_succ {L : List (List ℕ)} {k : ℕ} (hk : k < L.length) (p : List ℕ → Bool) :
    (L.take (k + 1)).filter p = (L.take k).filter p ++ (if p L[k] then [L[k]] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.filter_append]
  by_cases h : p L[k] <;> simp [h]

theorem passK_mono {ℓ L L' R : ℕ} (h : L ≤ L') : passK ℓ L R ≤ passK ℓ L' R := by
  unfold passK hopK
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) 500)) 30)) 40

theorem PassAt.of {Xa Y : List ℕ} {p₁ : ℕ} {Dw : DW} {ℓσ R : ℕ} {τ τ' : Env}
    (h : PassAt Xa Y p₁ Dw ℓσ R τ) (hv : ∀ y ∈ paN, τ'.vars y = τ.vars y)
    (ha : τ'.arrs "a" = τ.arrs "a") (hy : τ'.arrs "y" = τ.arrs "y") : PassAt Xa Y p₁ Dw ℓσ R τ' := by
  obtain ⟨a, y, p1, P, Q, cP, cQ, L, s⟩ := h
  exact ⟨by rw [ha, a], by rw [hy, y], by rw [hv _ (by simp [paN]), p1], by rw [hv _ (by simp [paN]), P],
    by rw [hv _ (by simp [paN]), Q], by rw [hv _ (by simp [paN]), cP], by rw [hv _ (by simp [paN]), cQ],
    by rw [hv _ (by simp [paN]), L], by rw [hv _ (by simp [paN]), s]⟩

/-- **The loop over the members.** -/
theorem memLoop_run {W : ℕ} {Xa Y : List ℕ} {p₁ yo : ℕ} {Aσ : List (List ℕ)} {r₁ : List ℕ}
    {Dw : DW} {ℓσ R : ℕ} {L : List (List ℕ)} {pre : List ℕ} {τ : Env}
    (hP : PassAt Xa Y p₁ Dw ℓσ R τ) (hd₁ : Xa.drop p₁ = toWord Aσ ++ r₁) (hyo : τ.vars "yo" = yo)
    (hY : YAt (toWord L) yo τ) (hL : ∀ w ∈ L, ∃ ν : TypeTree, w = toWord ν)
    (hF : Filled "OB" "po" pre τ) (hOB : (τ.arrs "OB").length = W + 1) (hYl : (τ.arrs "y").length = W + 1)
    (hB₁ : p₁ + (toWord Aσ).length + 6 < W + 1) (hv₁ : ∀ v ∈ toWord Aσ, v < W + 1)
    (hB₂ : yo + (toWord L).length + pre.length + 8 < W + 1) (hv₂ : ∀ v ∈ toWord L, v < W + 1)
    (hPB : Dw.P < W + 1) (hQB : Dw.Q < W + 1) (hℓ : ℓσ + 1 < W + 1) (hR : 2 * R + 4 < W + 1) :
    ∃ τ', Run (W + 1) memLoop τ τ'
        (L.length * (passK ℓσ (Aσ.length + maxLen L) R + 20 * maxLen L + 120) + 30) ∧
      Filled "OB" "po" (pre ++ frames (L.filter (memP Dw ℓσ Aσ R))) τ' ∧
      τ'.vars "pc" = (L.filter (memP Dw ℓσ Aσ R)).length ∧ OFr τ τ' loopV := by
  have hdy := drop_yAt hY
  rw [hP.y] at hdy
  obtain ⟨h0, hpos, hfr, -, -⟩ := listAt hdy
  have hLB : (toWord L).length = (frames L).length + 1 := by rw [toWord_words]; simp
  have hLl : L.length < (toWord L).length := by rw [toWord_words, List.length_cons, length_frames]; omega
  have hyo0 : (τ.arrs "y")[yo]? = some L.length := by
    have := getElem?_of_drop (i := 0) hdy (by simp; omega)
    rw [hP.y]; simpa [toWord_words] using this
  set τ1 := τ.setVar "pc" 0
  set τ2 := τ1.setVar "tf" (yo + 1)
  set τ3 := τ2.setVar "tN" L.length
  have r1 : Run (W + 1) (.assign "pc" (.lit 0)) τ τ1 2 := Run.assign (evalB_lit (by omega))
  have r2 : Run (W + 1) (.assign "tf" (.add (.var "yo") (.lit 1))) τ1 τ2 4 :=
    (Run.assign (ev_add (ev_var (v := yo) (by simp [τ1, hyo]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  have r3 : Run (W + 1) (.assign "tN" (.get "y" (.var "yo"))) τ2 τ3 3 :=
    (Run.assign (evalB_get (ev_var (v := yo) (by simp [τ2, τ1, hyo]) (by omega))
      (by simp [τ2, τ1, hyo0]) (by omega))).mono (by simp [Expr.size])
  have o3 : OFr τ τ3 loopV :=
    (((OFr.setVar τ "pc" 0).trans (OFr.setVar τ1 "tf" _)).trans (OFr.setVar τ2 "tN" _)).mono
      (by decide)
  set p := memP Dw ℓσ Aσ R
  set K := passK ℓσ (Aσ.length + maxLen L) R + 20 * maxLen L + 100
  have kP : ∀ y ∈ paN, y ∉ loopV := by decide
  let I : ℕ → Env → Prop := fun k ρ =>
    Filled "OB" "po" (pre ++ frames ((L.take k).filter p)) ρ ∧
    ρ.vars "pc" = ((L.take k).filter p).length ∧ ρ.vars "tf" = yo + 1 + (frames (L.take k)).length ∧
    ρ.vars "tN" = L.length ∧ OFr τ ρ loopV
  have hF0 : Filled "OB" "po" pre (τ3.setVar "tm" 0) :=
    (((hF.setVar (y := "pc") (by decide) 0).setVar (y := "tf") (by decide) _).setVar (y := "tN") (by decide)
      _).setVar (y := "tm") (by decide) 0
  have hI0 : I 0 (τ3.setVar "tm" 0) :=
    ⟨by simpa [frames] using hF0, by simp [τ3, τ2, τ1], by simp [τ3, τ2, frames], by simp [τ3],
      (o3.trans (OFr.setVar τ3 "tm" 0)).mono (by decide)⟩
  obtain ⟨τ4, r4, ⟨F4, c4, -, -, o4⟩, -⟩ := forUp_run (B := W + 1) (i := "tm") (e := .var "tN")
    (body := faBody) (N := L.length) (K := K) I (σ := τ3) (by omega)
    (fun k _ ρ hI _ => ev_var hI.2.2.2.1 (by omega)) hI0
    (by
      rintro k hk ρ ⟨Fρ, cρ, tρ, nρ, oρ⟩ hkρ
      have hPρ : PassAt Xa Y p₁ Dw ℓσ R ρ :=
        hP.of (fun y hy => oρ.vars y (kP y hy)) (oρ.arrs "a" (by decide)) (oρ.arrs "y" (by decide))
      obtain ⟨ν, hν⟩ := hL L[k] (List.getElem_mem hk)
      obtain ⟨hf1, hd⟩ := hpos k hk.le
      rw [frames_drop hk] at hd
      have hfl := frames_take_le L (k + 1)
      rw [length_frames_take_succ hk] at hfl
      set tf := yo + 1 + (frames (L.take k)).length
      have hdr : Y.drop tf = (toWord ν).length :: (toWord ν ++
          (frames (L.drop (k + 1)) ++ Y.drop (yo + (toWord L).length))) := by
        rw [← hν, ← hf1, hd]; simp
      have hwB : tf + (toWord ν).length + 8 < W + 1 := by rw [← hν]; omega
      have hwv : ∀ v ∈ toWord ν, v < W + 1 := fun v hv => hv₂ v (by
        rw [toWord_words]; apply List.mem_cons_of_mem
        rw [frames_split L k, frames_drop hk, hν]; simp [hv])
      obtain ⟨ρ1, r1', b1, f1, a1, o1, i1⟩ := passC_run (B := W + 1) hPρ hd₁ tρ hdr hB₁ hv₁ hwB hwv hPB hQB hℓ hR
      rw [← memP_tree] at b1
      rw [← hν] at b1
      have hp1 : ∀ y, y ∉ passV → ρ1.vars y = ρ.vars y := f1
      have hyt : (ρ1.arrs "y")[tf]? = some L[k].length := by
        rw [a1, oρ.arrs "y" (by decide), hP.y]
        have := getElem?_of_drop hdr (i := 0) (by simp); simpa [hν] using this
      have htf1 : ρ1.vars "tf" = tf := by rw [hp1 _ (by decide), tρ]
      have hlen : L[k].length < W + 1 := by rw [hν]; omega
      have F1 : Filled "OB" "po" (pre ++ frames ((L.take k).filter p)) ρ1 :=
        Fρ.congr (hp1 _ (by decide)) (by rw [a1])
      have hsub := size_sub (List.filter_sublist : ((L.take k).filter p).Sublist (L.take k))
      rw [← Words.length_frames, ← Words.length_frames] at hsub
      have hwB' : tf + L[k].length + 8 < W + 1 := by rw [hν]; exact hwB
      have hpre : (pre ++ frames ((L.take k).filter p)).length + L[k].length + 1 ≤ W := by
        rw [List.length_append]
        omega
      have hcnt : ((L.take k).filter p).length + 1 < W + 1 := by
        have := Words.length_frames ((L.take k).filter p)
        rw [List.length_append] at hpre; omega
      -- the copy
      have cF : (Cond.eq (.var "tF") (.lit 1)).evalB (W + 1) ρ1 = some (p L[k]) := by
        rw [evalB_condEq (ev_var b1 (lt_of_le_of_lt (bv_le _) (by omega))) (evalB_lit (by omega))]
        cases h : memP Dw ℓσ Aσ R L[k] <;> simp [p, h, bv]
      have mv : ∀ ρ' : Env, ρ'.vars "tf" = tf → ρ'.arrs "y" = ρ1.arrs "y" →
          Run (W + 1) (.assign "tf" (.add (.add (.var "tf") (.get "y" (.var "tf"))) (.lit 1))) ρ'
            (ρ'.setVar "tf" (tf + L[k].length + 1)) 7 := fun ρ' h1 h2 =>
        (Run.assign (ev_add (ev_add (ev_var h1 (by omega)) (evalB_get (ev_var h1 (by omega))
          (by rw [h2]; exact hyt) hlen) (by omega)) (evalB_lit (by omega)) (by omega))).mono
          (by simp [Expr.size])
      have htf' : tf + L[k].length + 1 = yo + 1 + (frames (L.take (k + 1))).length := by
        rw [length_frames_take_succ hk]; omega
      have fsucc := filter_take_succ hk p
      by_cases hpk : p L[k] = true
      · set ρ2 := ρ1.setVar "tl" (L[k].length + 1)
        have r2' : Run (W + 1) (.assign "tl" (.add (.get "y" (.var "tf")) (.lit 1))) ρ1 ρ2 5 :=
          (Run.assign (ev_add (evalB_get (ev_var htf1 (by omega)) hyt hlen) (evalB_lit (by omega))
            (by omega))).mono (by simp [Expr.size])
        have hseg : seg (ρ2.arrs "y") tf (L[k].length + 1) = L[k].length :: L[k] := by
          simp only [ρ2, arrs_setVar, seg]
          rw [a1, oρ.arrs "y" (by decide), hP.y, hdr, ← hν]; simp
        obtain ⟨ρ3, r3', F3, o3'⟩ := cpSeg_ofr (W := W) (src := "y") (s := "tf") (l := "tl")
          (a := tf) (N := L[k].length + 1) (σ := ρ2) (by decide) (by simp [ρ2, htf1]) (by simp [ρ2])
          (by decide) (by decide) (by decide) (by decide) (F1.setVar (by decide) _)
          (by simp [ρ2, a1, oρ.arrs "y" (by decide), hYl]; omega)
          (by simp [ρ2, a1, oρ.len, hOB]; omega) (by omega) (by omega)
          (by
            rw [hseg]; intro v hv
            rcases List.mem_cons.1 hv with rfl | hv
            · omega
            · have := hwv v (by rw [← hν]; exact hv); omega)
        rw [hseg] at F3
        have hpc3 : ρ3.vars "pc" = ((L.take k).filter p).length := by
          rw [o3'.vars _ (by decide)]; simp [ρ2, hp1 _ (by decide : "pc" ∉ passV), cρ]
        set ρ4 := ρ3.setVar "pc" (((L.take k).filter p).length + 1)
        have r4' : Run (W + 1) (.assign "pc" (.add (.var "pc") (.lit 1))) ρ3 ρ4 4 :=
          (Run.assign (ev_add (ev_var hpc3 (by omega)) (evalB_lit (by omega)) (by omega))).mono
            (by simp [Expr.size])
        have h4tf : ρ4.vars "tf" = tf := by
          simp only [ρ4, vars_setVar, show ("tf" : String) ≠ "pc" by decide, if_false]
          rw [o3'.vars _ (by decide)]; simp [ρ2, htf1]
        have h4y : ρ4.arrs "y" = ρ1.arrs "y" := by simp [ρ4]; rw [o3'.arrs _ (by decide)]; simp [ρ2]
        have r5' := mv ρ4 h4tf h4y
        refine ⟨ρ4.setVar "tf" (tf + L[k].length + 1), ?_, ?_, ?_⟩
        · unfold faBody cpFr
          refine (Run.seq r1' (Run.seq (Run.ite_true (by rw [cF, hpk]) (Run.seq r2' (Run.seq r3' r4')))
            r5')).mono ?_
          have := passK_mono (ℓ := ℓσ) (R := R) (show Aσ.length + (toWord ν).length ≤
            Aσ.length + maxLen L by have := le_maxLen' (List.getElem_mem hk); rw [hν] at this; omega)
          have hml := le_maxLen' (List.getElem_mem hk)
          simp only [K, Cond.size, Expr.size]; omega
        · simp only [vars_setVar, show ("tf" : String) ≠ "tm" by decide, show ("tm" : String) ≠ "tf" by decide,
            if_false, ρ4]
          rw [o3'.vars _ (by decide)]; simp [ρ2, hp1 _ (by decide : "tm" ∉ passV), hkρ]
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [fsucc, if_pos hpk, frames_append, frames_single, ← List.append_assoc]
            exact ((F3.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
          · simp [ρ4, fsucc, hpk]
          · simp [htf']
          · simp only [vars_setVar, show ("tN" : String) ≠ "tm" by decide, show ("tN" : String) ≠ "tf" by decide,
              show ("tN" : String) ≠ "pc" by decide, if_false, ρ4]
            rw [o3'.vars _ (by decide)]; simp [ρ2, hp1 _ (by decide : "tN" ∉ passV), nρ]
          · refine (oρ.trans ((ofr_of_test f1 a1 o1 i1).trans ((OFr.setVar ρ1 "tl" _).trans (o3'.trans
              ((OFr.setVar ρ3 "pc" _).trans ((OFr.setVar ρ4 "tf" _).trans (OFr.setVar _ "tm" _))))))).mono ?_
            decide
      · have hpk' : p L[k] = false := by simpa using hpk
        have r5' := mv ρ1 htf1 rfl
        refine ⟨ρ1.setVar "tf" (tf + L[k].length + 1), ?_, ?_, ?_⟩
        · unfold faBody
          refine (Run.seq r1' (Run.seq (Run.ite_false (by rw [cF, hpk']) Run.skip) r5')).mono ?_
          have := passK_mono (ℓ := ℓσ) (R := R) (show Aσ.length + (toWord ν).length ≤
            Aσ.length + maxLen L by have := le_maxLen' (List.getElem_mem hk); rw [hν] at this; omega)
          simp only [K, Cond.size, Expr.size]; omega
        · simp [hp1 _ (by decide : "tm" ∉ passV), hkρ]
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [fsucc, if_neg hpk, List.append_nil]
            exact (F1.setVar (by decide) _).setVar (by decide) _
          · simp [fsucc, hpk', hp1 _ (by decide : "pc" ∉ passV), cρ]
          · simp [htf']
          · simp [hp1 _ (by decide : "tN" ∉ passV), nρ]
          · refine (oρ.trans ((ofr_of_test f1 a1 o1 i1).trans ((OFr.setVar ρ1 "tf" _).trans
              (OFr.setVar _ "tm" _)))).mono ?_
            decide)
  refine ⟨τ4, ?_, by rwa [List.take_length] at F4, by rw [c4, List.take_length], o4⟩
  · unfold memLoop
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono ?_
    have hK : K + 1 + 7 ≤ passK ℓσ (Aσ.length + maxLen L) R + 20 * maxLen L + 120 := by
      simp only [K]; omega
    have := Nat.mul_le_mul_left L.length hK
    simp only [Expr.size]
    omega

end Lax185574Proofs.ResolveRam.Glue
