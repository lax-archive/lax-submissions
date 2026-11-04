import Lax185574Proofs.CompRam.GBase

/-!
The writers of the glue command of lem:compose.

Each lemma runs one writer of `GCode` on a buffer `OB` filled with `pre`
and gives the list it appends: a word of `x` with its length (`emW`),
the word of the list `EX` of a frame (`emEXc`), the frames of the words
of a frame (`emFr`) and of a new frame (`emFresh`), the head of an
output, the rest of the stack, the final word, and the parts of the
queries of a rank shift and of a canonical form. The writers that fill
in a length afterwards give the buffer with that cell set.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### Helpers -/

private theorem SegIs.ofr {M : ℕ} {σ σ' : Env} {xs : List String} {s l : String} {w : List ℕ}
    (h : SegIs M σ s l w) (hf : OFr σ σ' xs) (hs : s ∉ xs) (hl : l ∉ xs) : SegIs M σ' s l w := by
  unfold SegIs at *
  rw [hf.vars s hs, hf.vars l hl, hf.arrs "x" (by decide)]
  exact h

private theorem SegIs.setVar {M : ℕ} {σ : Env} {s l : String} {w : List ℕ} (h : SegIs M σ s l w)
    {y : String} (hs : s ≠ y) (hl : l ≠ y) (v : ℕ) : SegIs M (σ.setVar y v) s l w := by
  unfold SegIs at *
  simp only [vars_setVar, if_neg hs, if_neg hl, arrs_setVar]
  exact h

theorem seg_cons {X : List ℕ} {a n h : ℕ} {t : List ℕ} (hs : seg X a n = h :: t) :
    X[a]? = some h ∧ seg X (a + 1) (n - 1) = t := by
  unfold seg at hs ⊢
  cases hd : X.drop a with
  | nil => rw [hd] at hs; simp at hs
  | cons y ys =>
    rw [hd] at hs
    cases n with
    | zero => simp at hs
    | succ m =>
      simp only [List.take_succ_cons, List.cons.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨?_, ?_⟩
      · have : (X.drop a)[0]? = some y := by rw [hd]; rfl
        simpa using this
      · have := drop_add_of_drop (u := [y]) (r := ys) (by rw [hd]; rfl)
        simp only [List.length_singleton] at this
        rw [this]; simp

theorem toWord_snoc (E0 : List (List ℕ)) (u : List ℕ) :
    toWord (E0 ++ [u]) = (E0.length + 1) :: (frames E0 ++ (u.length :: u)) := by
  rw [toWord_words, frames_append]; simp [frames]

theorem set_mid (pre r : List ℕ) (k v : ℕ) :
    (pre ++ r).set (pre.length + k) v = pre ++ r.set k v := by
  rw [List.set_append_right _ _ (by omega)]; simp

theorem pv_run {W : ℕ} {σ : Env} {pre : List ℕ} {e : Expr} {v : ℕ} (hF : Filled "OB" "po" pre σ)
    (he : e.evalB (W + 1) σ = some v) (hOB : (σ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 ≤ W) :
    ∃ σ', Run (W + 1) (pv e) σ σ' (6 + e.size) ∧ Filled "OB" "po" (pre ++ [v]) σ' ∧
      OFr σ σ' ["po"] :=
  push1_ofr hF he (by omega) hB

theorem asg_run {W : ℕ} {σ : Env} {x : String} {e : Expr} {v : ℕ}
    (he : e.evalB (W + 1) σ = some v) :
    Run (W + 1) (asg x e) σ (σ.setVar x v) (1 + e.size) ∧ OFr σ (σ.setVar x v) [x] :=
  ⟨Run.assign he, OFr.setVar σ x v⟩

theorem ev_var {W : ℕ} {σ : Env} {x : String} (h : σ.vars x ≤ W) :
    (V x).evalB (W + 1) σ = some (σ.vars x) := evalB_var (by omega)

theorem ev_lit {W : ℕ} {σ : Env} {n : ℕ} (h : n ≤ W) : (N n).evalB (W + 1) σ = some n :=
  evalB_lit (by omega)

/-! ### Segments and words -/

theorem emSeg_run {W M : ℕ} {σ : Env} {pre w : List ℕ} {s l : String} (hs : s ∉ ["po", "ci"])
    (hl : l ∉ ["po", "ci"]) (hC : Ctx W M σ) (hF : Filled "OB" "po" pre σ) (hseg : SegIs M σ s l w)
    (hpre : pre.length + M ≤ W) :
    ∃ σ', Run (W + 1) (emSeg s l) σ σ' (20 * w.length + 6) ∧
      Filled "OB" "po" (pre ++ w) σ' ∧ OFr σ σ' ["ci", "po"] := by
  obtain ⟨h1, h2, h3⟩ := hseg
  have hM := hC.room
  obtain ⟨σ', r, F, o⟩ := cpSeg_ofr (W := W) (src := "x") (s := s) (l := l) (a := σ.vars s)
    (N := σ.vars l) (by decide) rfl rfl (fun h => hs (by simp [h])) (fun h => hs (by simp [h]))
    (fun h => hl (by simp [h])) (fun h => hl (by simp [h])) hF (by rw [hC.xl]; omega)
    (by rw [hC.ol]; omega) (by omega) (by omega) (fun v hv => by have := hC.xv v (mem_seg hv); omega)
  rw [h1, h3] at F
  exact ⟨σ', r.mono (by rw [h1]; omega), F, o⟩

theorem emW_run {W M : ℕ} {σ : Env} {pre w : List ℕ} {s l : String} (hs : s ∉ ["po", "ci"])
    (hl : l ∉ ["po", "ci"]) (hC : Ctx W M σ) (hF : Filled "OB" "po" pre σ) (hseg : SegIs M σ s l w)
    (hpre : pre.length + 2 * M ≤ W) :
    ∃ σ', Run (W + 1) (emW s l) σ σ' (20 * w.length + 30) ∧
      Filled "OB" "po" (pre ++ w.length :: w) σ' ∧ OFr σ σ' ["ci", "po"] := by
  have hM := hC.room; have h16 := hC.m16
  obtain ⟨hs1, hs2, -⟩ := id hseg
  have hl1 : σ.vars l ≤ W := by omega
  obtain ⟨σ1, r1, F1, o1⟩ := pv_run hF (ev_var hl1) hC.ol (by omega)
  have hseg1 := hseg.ofr o1 (fun h => hs (by simp_all)) (fun h => hl (by simp_all))
  obtain ⟨σ2, r2, F2, o2⟩ := emSeg_run hs hl (hC.ofr o1 (by decide)) F1 hseg1
    (by simp; omega)
  refine ⟨σ2, (Run.seq r1 r2).mono (by simp [Expr.size]; omega), ?_, (o1.trans o2).mono (by decide)⟩
  rw [hseg.1] at F2; simpa using F2

theorem emRest_run {W M : ℕ} {σ : Env} {pre w : List ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hseg : SegIs M σ "rS" "rL" w) (hpre : pre.length + M ≤ W) :
    ∃ σ', Run (W + 1) emRest σ σ' (20 * w.length + 10) ∧ Filled "OB" "po" (pre ++ w) σ' ∧
      OFr σ σ' ["ci", "po"] := by
  obtain ⟨σ', r, F, o⟩ := emSeg_run (by decide) (by decide) hC hF hseg hpre
  exact ⟨σ', r.mono (by omega), F, o⟩

/-! ### Heads and fixed parts -/

theorem emHd_run {W M : ℕ} {σ : Env} {pre : List ℕ} (hC : Ctx W M σ) (hF : Filled "OB" "po" pre σ)
    (hj : σ.vars "j1" ≤ W) (hc : σ.vars "cnt" ≤ W) (hpre : pre.length + 8 ≤ W) :
    ∃ σ', Run (W + 1) emHd σ σ' 100 ∧
      Filled "OB" "po" (pre ++ [1, 0, 0, 0, σ.vars "j1", σ.vars "cnt"]) σ' ∧ OFr σ σ' ["po"] := by
  obtain ⟨σ1, r1, F1, o1⟩ := pushLits_run (W := W) (l := [1, 0, 0, 0]) hF (by simp; omega)
    (by rw [hC.ol]; simp; omega) (by simp; omega)
  have hj1 : σ1.vars "j1" = σ.vars "j1" := o1.vars _ (by decide)
  have hc1 : σ1.vars "cnt" = σ.vars "cnt" := o1.vars _ (by decide)
  obtain ⟨σ2, r2, F2, o2⟩ := pushVars_run (W := W) (xs := ["j1", "cnt"]) (by decide) F1
    (by simp [hj1, hc1]; omega) (by rw [o1.len, hC.ol]; simp; omega) (by simp; omega)
  refine ⟨σ2, (Run.seq r1 r2).mono (by simp), ?_, (o1.trans o2).mono (by decide)⟩
  simpa [hj1, hc1] using F2

theorem patchL_run {W : ℕ} {σ : Env} {l : List ℕ} (hF : Filled "OB" "po" l σ) (hl : 3 ≤ l.length)
    (hW : l.length ≤ W) :
    ∃ σ', Run (W + 1) patchL σ σ' 10 ∧ Filled "OB" "po" (l.set 1 (l.length - 3)) σ' ∧ OFr σ σ' [] := by
  have hp := hF.pos
  have he := evalB_bin (op := .sub) (B := W + 1) (ev_var (σ := σ) (x := "po") (by rw [hF.pos]; omega))
    (ev_lit (n := 3) (by omega)) (by simp; omega)
  rw [Bop.apply_sub, hF.pos] at he
  obtain ⟨σ', r, F, o⟩ := store_filled hF (ev_lit (n := 1) (by omega)) he (by omega)
  exact ⟨σ', r.mono (by decide), F, o⟩

theorem emCaHd_run {W M : ℕ} {σ : Env} {pre : List ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hpre : pre.length + 16 ≤ W) :
    ∃ σ', Run (W + 1) emCaHd σ σ' 100 ∧
      Filled "OB" "po" (pre ++ [5, lDSq, 0, 0, 0, 0, 0, 0]) σ' ∧ σ'.vars "sp" = pre.length + 8 ∧
      σ'.vars "qa" = pre.length + 8 ∧ σ'.vars "dq" = 1 ∧ OFr σ σ' ["po", "sp", "dq", "qa"] := by
  have hM := hC.room; have h16 := hC.m16
  obtain ⟨σ1, r1, F1, o1⟩ := pushLits_run (W := W) (l := [5, lDSq, 0, 0, 0, 0, 0, 0]) hF
    (by simp [lDSq]; omega) (by rw [hC.ol]; simp; omega) (by simp; omega)
  have hp : σ1.vars "po" = pre.length + 8 := by rw [F1.pos]; simp
  obtain ⟨r2, o2⟩ := asg_run (x := "sp") (ev_var (σ := σ1) (x := "po") (W := W) (by omega))
  set σ2 := σ1.setVar "sp" (σ1.vars "po")
  obtain ⟨r3, o3⟩ := asg_run (x := "dq") (ev_lit (σ := σ2) (n := 1) (W := W) (by omega))
  set σ3 := σ2.setVar "dq" 1
  have hp3 : σ3.vars "po" = pre.length + 8 := by simp [σ3, σ2, hp]
  obtain ⟨r4, o4⟩ := asg_run (x := "qa") (ev_var (σ := σ3) (x := "po") (W := W) (by omega))
  refine ⟨σ3.setVar "qa" (σ3.vars "po"), ?_, ?_, by simp [σ3, σ2, hp], by simp [hp3],
    by simp [σ3], ((o1.trans o2).trans (o3.trans o4)).mono (by decide)⟩
  · unfold emCaHd; simp only [seqs]
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by simp)
  · exact ((F1.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _

theorem emCaEnd_run {W : ℕ} {σ : Env} {pre Q : List ℕ} (hF : Filled "OB" "po" (pre ++ Q) σ)
    (hqa : σ.vars "qa" = pre.length) (h8 : 8 ≤ pre.length) (hW : pre.length + Q.length ≤ W) :
    ∃ σ', Run (W + 1) emCaEnd σ σ' 20 ∧
      Filled "OB" "po" ((pre ++ Q).set (pre.length - 6) Q.length) σ' ∧ σ'.vars "ql" = Q.length ∧
      σ'.vars "qk" = 2 ∧ OFr σ σ' ["ql", "qk"] := by
  have hpo : σ.vars "po" = pre.length + Q.length := by rw [hF.pos]; simp
  have he := evalB_bin (op := .sub) (B := W + 1) (ev_var (σ := σ) (x := "po") (by omega))
    (ev_var (σ := σ) (x := "qa") (by omega)) (by simp; omega)
  rw [Bop.apply_sub, hpo, hqa, show pre.length + Q.length - pre.length = Q.length by omega] at he
  obtain ⟨r1, o1⟩ := asg_run (x := "ql") he
  set σ1 := σ.setVar "ql" Q.length
  have hq1 : σ1.vars "qa" = pre.length := by simp [σ1, hqa]
  have hi := evalB_bin (op := .sub) (B := W + 1) (ev_var (σ := σ1) (x := "qa") (by rw [hq1]; omega))
    (ev_lit (n := 6) (by omega)) (by simp [hq1]; omega)
  rw [Bop.apply_sub] at hi
  rw [hq1] at hi
  obtain ⟨σ2, r2, F2, o2⟩ := store_filled (hF.setVar (by decide) Q.length) hi
    (ev_var (σ := σ1) (x := "ql") (W := W) (by simp [σ1]; omega)) (by simp; omega)
  have hql : σ1.vars "ql" = Q.length := by simp [σ1]
  rw [hql] at F2
  obtain ⟨r3, o3⟩ := asg_run (x := "qk") (ev_lit (σ := σ2) (n := 2) (W := W) (by omega))
  refine ⟨σ2.setVar "qk" 2, ?_, F2.setVar (by decide) _, ?_, by simp,
    ((o1.trans o2).trans o3).mono (by decide)⟩
  · unfold emCaEnd; simp only [seqs]
    exact (Run.seq r1 (Run.seq r2 r3)).mono (by simp)
  · simp only [vars_setVar, if_neg (show ("ql" : String) ≠ "qk" by decide)]
    rw [o2.vars "ql" (by simp)]; exact hql


/-! ### The final word and the query of a rank shift -/

theorem emDone_run {W M : ℕ} {σ : Env} {pre R1 R2 : List ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hk : σ.vars "hk" < 2 * M) (hd : σ.vars "hd" < 2 * M)
    (hl : σ.vars "hl" < 2 * M) (h1 : SegIs M σ "r1s" "r1l" R1) (h2 : SegIs M σ "r2s" "r2l" R2)
    (hpre : pre.length + 4 * M ≤ W) :
    ∃ σ', Run (W + 1) emDone σ σ' (20 * (R1.length + R2.length) + 100) ∧
      Filled "OB" "po" (pre ++ [0, σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ R1 ++ R2) σ' ∧
      σ'.vars "sp" = pre.length + 4 + R1.length + R2.length ∧ σ'.vars "dq" = 0 ∧ σ'.vars "qk" = 3 ∧
      OFr σ σ' ["ci", "po", "sp", "dq", "qk"] := by
  have hM := hC.room; have h16 := hC.m16
  have hR1 := h1.2.1; have hR2 := h2.2.1
  obtain ⟨σ1, r1, F1, o1⟩ := pv_run hF (ev_lit (σ := σ) (n := 0) (W := W) (by omega)) hC.ol (by omega)
  have C1 := hC.ofr o1 (by decide)
  have ek : σ1.vars "hk" = σ.vars "hk" := o1.vars _ (by decide)
  have ed : σ1.vars "hd" = σ.vars "hd" := o1.vars _ (by decide)
  have el : σ1.vars "hl" = σ.vars "hl" := o1.vars _ (by decide)
  obtain ⟨σ2, r2, F2, o2⟩ := pushVars_run (W := W) (xs := ["hk", "hd", "hl"]) (by decide) F1
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> omega)
    (by rw [C1.ol]; simp; omega) (by simp; omega)
  have C2 := C1.ofr o2 (by decide)
  obtain ⟨σ3, r3, F3, o3⟩ := emSeg_run (by decide) (by decide) C2 F2
    ((h1.ofr o1 (by decide) (by decide)).ofr o2 (by decide) (by decide)) (by simp; omega)
  have C3 := C2.ofr o3 (by decide)
  obtain ⟨σ4, r4, F4, o4⟩ := emSeg_run (by decide) (by decide) C3 F3
    (((h2.ofr o1 (by decide) (by decide)).ofr o2 (by decide) (by decide)).ofr o3 (by decide)
      (by decide)) (by simp; omega)
  have hp4 : σ4.vars "po" = pre.length + 4 + R1.length + R2.length := by rw [F4.pos]; simp; omega
  obtain ⟨r5, o5⟩ := asg_run (x := "sp") (ev_var (σ := σ4) (x := "po") (W := W) (by omega))
  obtain ⟨r6, o6⟩ := asg_run (x := "dq") (ev_lit (σ := σ4.setVar "sp" (σ4.vars "po")) (n := 0)
    (W := W) (by omega))
  obtain ⟨r7, o7⟩ := asg_run (x := "qk") (ev_lit (σ := (σ4.setVar "sp" (σ4.vars "po")).setVar "dq" 0)
    (n := 3) (W := W) (by omega))
  refine ⟨_, ?_, ?_, by simp [hp4], by simp, by simp,
    ((((o1.trans o2).trans o3).trans o4).trans ((o5.trans o6).trans o7)).mono (by decide)⟩
  · unfold emDone; simp only [seqs]
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono
      (by simp [Expr.size]; omega)
  · have F := ((F4.setVar (y := "sp") (by decide) (σ4.vars "po")).setVar (y := "dq") (by decide)
      0).setVar (y := "qk") (by decide) 3
    simpa [ek, ed, el] using F

theorem emSh_run {W M : ℕ} {σ : Env} {pre Wd : List ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hk : σ.vars "hk" < 2 * M) (hd : σ.vars "hd" < 2 * M)
    (hl : σ.vars "hl" < 2 * M) (hs : SegIs M σ "hs" "hw" Wd) (hpre : pre.length + 4 * M ≤ W) :
    ∃ σ', Run (W + 1) emSh σ σ' (20 * Wd.length + 200) ∧
      Filled "OB" "po" (pre ++ [5, Wd.length + 3, 1, 0, 0, 0, 0, 0] ++
        ([σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ Wd) ++ [0]) σ' ∧
      σ'.vars "qa" = pre.length + 8 ∧ σ'.vars "ql" = Wd.length + 3 ∧
      σ'.vars "sp" = pre.length + 8 + Wd.length + 3 + 1 ∧ σ'.vars "dq" = 0 ∧ σ'.vars "qk" = 1 ∧
      OFr σ σ' ["ci", "po", "qa", "ql", "sp", "dq", "qk"] := by
  have hM := hC.room; have h16 := hC.m16
  have hW1 := hs.2.1
  obtain ⟨σ1, r1, F1, o1⟩ := pushLits_run (W := W) (l := [5, 0, 1, 0, 0, 0, 0, 0]) hF
    (by simp; omega) (by rw [hC.ol]; simp; omega) (by simp; omega)
  have hp1 : σ1.vars "po" = pre.length + 8 := by rw [F1.pos]; simp
  obtain ⟨r2, o2⟩ := asg_run (x := "qa") (ev_var (σ := σ1) (x := "po") (W := W) (by omega))
  have F2 := F1.setVar (y := "qa") (by decide) (σ1.vars "po")
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "qa" (σ1.vars "po") := ⟨_, rfl⟩
  rw [← hσ2] at r2 o2 F2
  have o12 := o1.trans o2
  have C2 := hC.ofr o12 (by decide)
  have ek : σ2.vars "hk" = σ.vars "hk" := o12.vars _ (by decide)
  have ed : σ2.vars "hd" = σ.vars "hd" := o12.vars _ (by decide)
  have el : σ2.vars "hl" = σ.vars "hl" := o12.vars _ (by decide)
  have hqa : σ2.vars "qa" = pre.length + 8 := by simp [hσ2, hp1]
  obtain ⟨σ3, r3, F3, o3⟩ := pushVars_run (W := W) (xs := ["hk", "hd", "hl"]) (by decide) F2
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> omega)
    (by rw [C2.ol]; simp; omega) (by simp; omega)
  have C3 := C2.ofr o3 (by decide)
  obtain ⟨σ4, r4, F4, o4⟩ := emSeg_run (by decide) (by decide) C3 F3
    ((hs.ofr o12 (by decide) (by decide)).ofr o3 (by decide) (by decide)) (by simp; omega)
  have o34 := o3.trans o4
  have hq4 : σ4.vars "qa" = pre.length + 8 := by rw [o34.vars "qa" (by decide), hqa]
  have hp4 : σ4.vars "po" = pre.length + 8 + 3 + Wd.length := by rw [F4.pos]; simp; omega
  have he := evalB_bin (op := .sub) (B := W + 1) (ev_var (σ := σ4) (x := "po") (W := W) (by omega))
    (ev_var (σ := σ4) (x := "qa") (W := W) (by omega)) (by simp; omega)
  rw [Bop.apply_sub, hp4, hq4, show pre.length + 8 + 3 + Wd.length - (pre.length + 8) =
    Wd.length + 3 by omega] at he
  obtain ⟨r5, o5⟩ := asg_run (x := "ql") he
  set σ5 := σ4.setVar "ql" (Wd.length + 3) with hσ5
  have hq5 : σ5.vars "qa" = pre.length + 8 := by simp [σ5, hq4]
  have hi := evalB_bin (op := .sub) (B := W + 1) (ev_var (σ := σ5) (x := "qa") (W := W)
    (by rw [hq5]; omega)) (ev_lit (n := 7) (by omega)) (by simp [hq5]; omega)
  rw [Bop.apply_sub, hq5, show pre.length + 8 - 7 = pre.length + 1 by omega] at hi
  obtain ⟨σ6, r6, F6, o6⟩ := store_filled (F4.setVar (by decide) (Wd.length + 3)) hi
    (ev_var (σ := σ5) (x := "ql") (W := W) (by simp [σ5]; omega)) (by simp)
  have hql5 : σ5.vars "ql" = Wd.length + 3 := by simp [σ5]
  rw [hql5] at F6
  have hL : ((pre ++ [5, 0, 1, 0, 0, 0, 0, 0] ++ [σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++
      Wd).set (pre.length + 1) (Wd.length + 3)) = pre ++ [5, Wd.length + 3, 1, 0, 0, 0, 0, 0] ++
      [σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ Wd := by
    simp only [List.append_assoc]; rw [set_mid]; simp
  have F6' : Filled "OB" "po" (pre ++ [5, Wd.length + 3, 1, 0, 0, 0, 0, 0] ++
      [σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ Wd) σ6 := by
    rw [← hL]; simpa [ek, ed, el] using F6
  have C6 := (C3.ofr o4 (by decide)).setVar (y := "ql") (by decide) (Wd.length + 3) |>.ofr o6 (by decide)
  obtain ⟨σ7, r7, F7, o7⟩ := pv_run F6' (ev_lit (σ := σ6) (n := 0) (W := W) (by omega)) C6.ol
    (by simp; omega)
  have hp7 : σ7.vars "po" = pre.length + 8 + Wd.length + 3 + 1 := by rw [F7.pos]; simp; omega
  obtain ⟨r8, o8⟩ := asg_run (x := "sp") (ev_var (σ := σ7) (x := "po") (W := W) (by omega))
  obtain ⟨r9, o9⟩ := asg_run (x := "dq") (ev_lit (σ := σ7.setVar "sp" (σ7.vars "po")) (n := 0)
    (W := W) (by omega))
  obtain ⟨r10, o10⟩ := asg_run (x := "qk") (ev_lit (σ := (σ7.setVar "sp" (σ7.vars "po")).setVar "dq" 0)
    (n := 1) (W := W) (by omega))
  have o610 := (o6.trans o7).trans ((o8.trans o9).trans o10)
  refine ⟨_, ?_, ?_, ?_, ?_, by simp [hp7], by simp, by simp,
    ((o12.trans o34).trans (o5.trans o610)).mono (by decide)⟩
  · unfold emSh; simp only [seqs]
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
      (Run.seq r8 (Run.seq r9 r10))))))))).mono (by simp [Expr.size]; omega)
  · have F := ((F7.setVar (y := "sp") (by decide) (σ7.vars "po")).setVar (y := "dq") (by decide)
      0).setVar (y := "qk") (by decide) 1
    simpa using F
  · simp only [vars_setVar]; simp only [if_neg (show ("qa" : String) ≠ "qk" by decide),
      if_neg (show ("qa" : String) ≠ "dq" by decide), if_neg (show ("qa" : String) ≠ "sp" by decide)]
    rw [o7.vars "qa" (by decide), o6.vars "qa" (by simp)]; exact hq5
  · simp only [vars_setVar]; simp only [if_neg (show ("ql" : String) ≠ "qk" by decide),
      if_neg (show ("ql" : String) ≠ "dq" by decide), if_neg (show ("ql" : String) ≠ "sp" by decide)]
    rw [o7.vars "ql" (by decide), o6.vars "ql" (by simp)]; exact hql5


/-! ### The word of `EX` -/

/-- The scalars written by `emFr`. -/
def emFrVars : List String := ["ci", "po", "u1", "u2", "gEL"]

private theorem ExIs.ofr {M : ℕ} {σ σ' : Env} {xs : List String} {EX : List (List ℕ)} (h : ExIs M σ EX)
    (hf : OFr σ σ' xs)
    (hxs : ∀ y ∈ ["gx", "gg", "gEs", "gEl", "r1s", "r1l", "r2s", "r2l"], y ∉ xs) : ExIs M σ' EX := by
  have e : ∀ y ∈ ["gx", "gg", "gEs", "gEl", "r1s", "r1l", "r2s", "r2l"], σ'.vars y = σ.vars y :=
    fun y hy => hf.vars y (hxs y hy)
  rcases h with ⟨h0, hs⟩ | ⟨h1, hg, E0, R1, R2, hE, hs, h1', h2'⟩
  · exact Or.inl ⟨by rw [e "gx" (by simp), h0], hs.ofr hf (hxs _ (by simp)) (hxs _ (by simp))⟩
  · refine Or.inr ⟨by rw [e "gx" (by simp), h1], by rw [e "gg" (by simp)]; exact hg, E0, R1, R2,
      by rw [e "gg" (by simp)]; exact hE, hs.ofr hf (hxs _ (by simp)) (hxs _ (by simp)),
      h1'.ofr hf (hxs _ (by simp)) (hxs _ (by simp)), h2'.ofr hf (hxs _ (by simp)) (hxs _ (by simp))⟩

theorem length_toWord_snoc (E0 : List (List ℕ)) (g : ℕ) (R1 R2 : List ℕ) :
    (toWord (E0 ++ [g :: (R1 ++ R2)])).length = (toWord E0).length + 2 + R1.length + R2.length := by
  rw [toWord_snoc, toWord_words E0]; simp; omega

theorem emEXc_run {W M : ℕ} {σ : Env} {pre : List ℕ} {EX : List (List ℕ)} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hE : ExIs M σ EX) (hpre : pre.length + 8 * M ≤ W) :
    ∃ σ', Run (W + 1) emEXc σ σ' (20 * (toWord EX).length + 100) ∧
      Filled "OB" "po" (pre ++ toWord EX) σ' ∧ (toWord EX).length ≤ 4 * M ∧ OFr σ σ' emFrVars := by
  have hM := hC.room; have h16 := hC.m16
  rcases hE with ⟨hx0, hs⟩ | ⟨hx1, hg, E0, R1, R2, rfl, hsE, h1, h2⟩
  · obtain ⟨σ', r, F, o⟩ := emSeg_run (by decide) (by decide) hC hF hs (by omega)
    refine ⟨σ', ?_, F, by have := hs.2.1; omega, o.mono (by decide)⟩
    unfold emEXc
    refine (Run.ite_true ?_ r).mono (by simp [Cond.size, Expr.size]; omega)
    rw [evalB_condEq (ev_var (x := "gx") (W := W) (by omega)) (ev_lit (n := 0) (by omega)), hx0]; rfl
  · obtain ⟨hEl, hEb, hEseg⟩ := id hsE
    have hR1 := h1.2.1; have hR2 := h2.2.1
    have hTl : (toWord E0).length = (frames E0).length + 1 := by rw [toWord_words]; simp
    have hq : seg (σ.arrs "x") (σ.vars "gEs") ((frames E0).length + 1) = E0.length :: frames E0 := by
      rw [← hTl, hEseg, toWord_words]
    obtain ⟨hk, htl⟩ := seg_cons hq
    simp only [Nat.add_sub_cancel] at htl
    have hE0 : E0.length < M := by have := count_lt_toWord E0; omega
    have e1 := evalB_bin (op := .add) (B := W + 1)
      (evalB_get (a := "x") (ev_var (σ := σ) (x := "gEs") (W := W) (by omega)) hk (by omega))
      (ev_lit (σ := σ) (n := 1) (W := W) (by omega)) (by simp; omega)
    rw [Bop.apply_add] at e1
    obtain ⟨σ1, r1, F1, o1⟩ := pv_run hF e1 hC.ol (by omega)
    have g1 : σ1.vars "gEs" = σ.vars "gEs" := o1.vars _ (by decide)
    have g1' : σ1.vars "gEl" = σ.vars "gEl" := o1.vars _ (by decide)
    have e2 := evalB_bin (op := .add) (B := W + 1) (ev_var (σ := σ1) (x := "gEs") (W := W) (by omega))
      (ev_lit (σ := σ1) (n := 1) (W := W) (by omega)) (by simp; omega)
    rw [Bop.apply_add, g1] at e2
    obtain ⟨r2, o2⟩ := asg_run (x := "u1") e2
    have F2 := F1.setVar (y := "u1") (by decide) (σ.vars "gEs" + 1)
    obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "u1" (σ.vars "gEs" + 1) := ⟨_, rfl⟩
    rw [← hσ2] at r2 o2 F2
    have e3 := evalB_bin (op := .sub) (B := W + 1) (ev_var (σ := σ2) (x := "gEl") (W := W)
      (by rw [hσ2]; simp [g1']; omega)) (ev_lit (σ := σ2) (n := 1) (W := W) (by omega))
      (by simp [hσ2, g1']; omega)
    rw [Bop.apply_sub, show σ2.vars "gEl" = (toWord E0).length by rw [hσ2]; simp [g1', hEl], hTl,
      Nat.add_sub_cancel] at e3
    obtain ⟨r3, o3⟩ := asg_run (x := "u2") e3
    have F3 := F2.setVar (y := "u2") (by decide) (frames E0).length
    obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "u2" (frames E0).length := ⟨_, rfl⟩
    rw [← hσ3] at r3 o3 F3
    have o13 := (o1.trans o2).trans o3
    have C3 := hC.ofr o13 (by decide)
    have hseg3 : SegIs M σ3 "u1" "u2" (frames E0) := by
      refine ⟨by rw [hσ3]; simp, ?_, ?_⟩
      · rw [hσ3, hσ2]; simp; omega
      · rw [o13.arrs "x" (by decide), show σ3.vars "u1" = σ.vars "gEs" + 1 by rw [hσ3, hσ2]; simp]
        exact htl
    obtain ⟨σ4, r4, F4, o4⟩ := emSeg_run (by decide) (by decide) C3 F3 hseg3 (by simp; omega)
    have o14 := o13.trans o4
    have C4 := hC.ofr o14 (by decide)
    have e5 := evalB_bin (op := .add) (B := W + 1)
      (evalB_bin (op := .add) (ev_lit (σ := σ4) (n := 1) (W := W) (by omega))
        (ev_var (σ := σ4) (x := "r1l") (W := W) (by rw [o14.vars "r1l" (by decide), h1.1]; omega))
        (by simp [o14.vars "r1l" (by decide), h1.1]; omega))
      (ev_var (σ := σ4) (x := "r2l") (W := W) (by rw [o14.vars "r2l" (by decide), h2.1]; omega))
      (by simp [o14.vars "r1l" (by decide), h1.1, o14.vars "r2l" (by decide), h2.1]; omega)
    simp only [Bop.apply_add, o14.vars "r1l" (by decide), o14.vars "r2l" (by decide), h1.1, h2.1] at e5
    obtain ⟨σ5, r5, F5, o5⟩ := pv_run F4 e5 C4.ol (by simp; omega)
    have o15 := o14.trans o5
    obtain ⟨σ6, r6, F6, o6⟩ := pv_run F5 (ev_var (σ := σ5) (x := "gg") (W := W)
      (by rw [o15.vars "gg" (by decide)]; omega)) (C4.ofr o5 (by decide)).ol (by simp; omega)
    have o16 := o15.trans o6
    obtain ⟨σ7, r7, F7, o7⟩ := emSeg_run (by decide) (by decide) (hC.ofr o16 (by decide)) F6
      (h1.ofr o16 (by decide) (by decide)) (by simp; omega)
    have o17 := o16.trans o7
    obtain ⟨σ8, r8, F8, o8⟩ := emSeg_run (by decide) (by decide) (hC.ofr o17 (by decide)) F7
      (h2.ofr o17 (by decide) (by decide)) (by simp; omega)
    have hlen := length_toWord_snoc E0 (σ.vars "gg") R1 R2
    refine ⟨σ8, ?_, ?_, by omega, (o17.trans o8).mono (by decide)⟩
    · unfold emEXc
      simp only [seqs]
      refine (Run.ite_false ?_ (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5
        (Run.seq r6 (Run.seq r7 r8)))))))).mono (by simp [Cond.size, Expr.size]; omega)
      rw [evalB_condEq (ev_var (x := "gx") (W := W) (by omega)) (ev_lit (n := 0) (by omega)), hx1]; rfl
    · rw [o15.vars "gg" (by decide)] at F8
      rw [toWord_snoc]
      have : (σ.vars "gg" :: (R1 ++ R2)).length = 1 + R1.length + R2.length := by simp; omega
      rw [this]; simpa using F8

theorem emEXw_run {W M : ℕ} {σ : Env} {pre : List ℕ} {EX : List (List ℕ)} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hE : ExIs M σ EX) (hpre : pre.length + 9 * M ≤ W) :
    ∃ σ', Run (W + 1) emEXw σ σ' (20 * (toWord EX).length + 200) ∧
      Filled "OB" "po" (pre ++ (toWord EX).length :: toWord EX) σ' ∧ (toWord EX).length ≤ 4 * M ∧
      OFr σ σ' emFrVars := by
  have hM := hC.room; have h16 := hC.m16
  have hv : Run (W + 1) (.ite (.eq (V "gx") (N 0)) (asg "gEL" (V "gEl"))
      (asg "gEL" (.add (.add (.add (V "gEl") (N 2)) (V "r1l")) (V "r2l"))))
      σ (σ.setVar "gEL" (toWord EX).length) 30 ∧ (toWord EX).length ≤ 4 * M := by
    rcases hE with ⟨hx0, hs⟩ | ⟨hx1, hg, E0, R1, R2, rfl, hsE, h1, h2⟩
    · have hl := hs.1; have hl2 := hs.2.1
      have ra : Run (W + 1) (asg "gEL" (V "gEl")) σ (σ.setVar "gEL" (toWord EX).length) 2 := by
        rw [← hl]; exact Run.assign (ev_var (by omega))
      refine ⟨(Run.ite_true ?_ ra).mono (by simp [Cond.size, Expr.size]), by omega⟩
      rw [evalB_condEq (ev_var (x := "gx") (W := W) (by omega)) (ev_lit (n := 0) (by omega)), hx0]
      rfl
    · have hl := hsE.1; have hl2 := hsE.2.1; have hr1 := h1.1; have hr1' := h1.2.1
      have hr2 := h2.1; have hr2' := h2.2.1
      have hlen := length_toWord_snoc E0 (σ.vars "gg") R1 R2
      have ra : Run (W + 1) (asg "gEL" (.add (.add (.add (V "gEl") (N 2)) (V "r1l")) (V "r2l"))) σ
          (σ.setVar "gEL" (toWord (E0 ++ [σ.vars "gg" :: (R1 ++ R2)])).length) 8 := by
        have e := evalB_bin (op := .add) (B := W + 1) (evalB_bin (op := .add) (B := W + 1)
          (evalB_bin (op := .add) (ev_var (σ := σ) (x := "gEl") (W := W) (by omega))
            (ev_lit (n := 2) (by omega)) (by simp; omega)) (ev_var (x := "r1l") (W := W) (by omega))
            (by simp; omega)) (ev_var (x := "r2l") (W := W) (by omega)) (by simp; omega)
        simp only [Bop.apply_add, hl, hr1, hr2] at e
        rw [hlen]; exact Run.assign e
      refine ⟨(Run.ite_false ?_ ra).mono (by simp [Cond.size, Expr.size]), by omega⟩
      rw [evalB_condEq (ev_var (x := "gx") (W := W) (by omega)) (ev_lit (n := 0) (by omega)), hx1]
      rfl
  obtain ⟨r1, hlen⟩ := hv
  have o1 := OFr.setVar σ "gEL" (toWord EX).length
  have F1 := hF.setVar (y := "gEL") (by decide) (toWord EX).length
  obtain ⟨σ2, r2, F2, o2⟩ := pv_run F1 (ev_var (σ := σ.setVar "gEL" (toWord EX).length) (x := "gEL")
    (W := W) (by simp; omega)) (by simp [hC.ol]) (by omega)
  have o12 := o1.trans o2
  obtain ⟨σ3, r3, F3, -, o3⟩ := emEXc_run (hC.ofr o12 (by decide)) F2
    (hE.ofr o12 (by decide)) (by simp; omega)
  refine ⟨σ3, ?_, by simpa using F3, hlen, (o12.trans o3).mono (by decide)⟩
  unfold emEXw; simp only [seqs]
  exact (Run.seq r1 (Run.seq r2 r3)).mono (by simp [Expr.size]; omega)

/-! ### Frames -/

private theorem SlotIs.ofr {M : ℕ} {σ σ' : Env} {f : Fr} (h : SlotIs M σ f) (hf : OFr σ σ' ["ci", "po"]) :
    SlotIs M σ' f where
  d := by rw [hf.vars _ (by decide)]; exact h.d
  kk := by rw [hf.vars _ (by decide)]; exact h.kk
  l1 := by rw [hf.vars _ (by decide)]; exact h.l1
  l2 := by rw [hf.vars _ (by decide)]; exact h.l2
  ph := by rw [hf.vars _ (by decide)]; exact h.ph
  i := by rw [hf.vars _ (by decide)]; exact h.i
  nums := h.nums
  A := h.A.ofr hf (by decide) (by decide)
  B := h.B.ofr hf (by decide) (by decide)
  SA := h.SA.ofr hf (by decide) (by decide)
  SB := h.SB.ofr hf (by decide) (by decide)
  AT := h.AT.ofr hf (by decide) (by decide)
  EX := h.EX.ofr hf (by decide)

theorem emFr_run {W M : ℕ} {σ : Env} {pre : List ℕ} {f : Fr} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hf : SlotIs M σ f) (hpre : pre.length + 32 * M ≤ W) :
    ∃ σ', Run (W + 1) emFr σ σ' (20 * (frames (frWords f)).length + 400) ∧
      Filled "OB" "po" (pre ++ frames (frWords f)) σ' ∧ (frames (frWords f)).length ≤ 16 * M ∧
      OFr σ σ' emFrVars := by
  have hM := hC.room; have h16 := hC.m16
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hf.nums
  have lA := hf.A.2.1; have lB := hf.B.2.1; have lS := hf.SA.2.1; have lT := hf.SB.2.1
  have lU := hf.AT.2.1
  obtain ⟨σ1, r1, F1, o1⟩ := pv_run hF (ev_lit (σ := σ) (n := 6) (W := W) (by omega)) hC.ol (by omega)
  have e1 : ∀ y ∈ ["gd", "gk", "g1", "g2", "gp", "gi"], σ1.vars y = σ.vars y :=
    fun y hy => o1.vars y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨σ2, r2, F2, o2⟩ := pushVars_run (W := W) (xs := ["gd", "gk", "g1", "g2", "gp", "gi"])
    (by decide) F1
    (by intro x hx; rw [e1 x hx]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hf.d]; omega
        · rw [hf.kk]; omega
        · rw [hf.l1]; omega
        · rw [hf.l2]; omega
        · rw [hf.ph]; omega
        · rw [hf.i]; omega)
    (by rw [o1.len, hC.ol]; simp; omega) (by simp; omega)
  have o12 := (o1.trans o2).mono (show ["po", "po"] ⊆ ["ci", "po"] by decide)
  have h2 := hf.ofr o12
  obtain ⟨σ3, r3, F3, o3⟩ := emW_run (by decide) (by decide) (hC.ofr o12 (by decide)) F2 h2.A
    (by simp; omega)
  have o13 := (o12.trans o3).mono (show ["ci", "po", "ci", "po"] ⊆ ["ci", "po"] by decide)
  obtain ⟨σ4, r4, F4, o4⟩ := emW_run (by decide) (by decide) (hC.ofr o13 (by decide)) F3
    (hf.ofr o13).B (by simp; omega)
  have o14 := (o13.trans o4).mono (show ["ci", "po", "ci", "po"] ⊆ ["ci", "po"] by decide)
  obtain ⟨σ5, r5, F5, o5⟩ := emW_run (by decide) (by decide) (hC.ofr o14 (by decide)) F4
    (hf.ofr o14).SA (by simp; omega)
  have o15 := (o14.trans o5).mono (show ["ci", "po", "ci", "po"] ⊆ ["ci", "po"] by decide)
  obtain ⟨σ6, r6, F6, o6⟩ := emW_run (by decide) (by decide) (hC.ofr o15 (by decide)) F5
    (hf.ofr o15).SB (by simp; omega)
  have o16 := (o15.trans o6).mono (show ["ci", "po", "ci", "po"] ⊆ ["ci", "po"] by decide)
  obtain ⟨σ7, r7, F7, o7⟩ := emW_run (by decide) (by decide) (hC.ofr o16 (by decide)) F6
    (hf.ofr o16).AT (by simp; omega)
  have o17 := (o16.trans o7).mono (show ["ci", "po", "ci", "po"] ⊆ ["ci", "po"] by decide)
  obtain ⟨σ8, r8, F8, hEl, o8⟩ := emEXw_run (hC.ofr o17 (by decide)) F7 (hf.ofr o17).EX
    (by simp; omega)
  have hfl : (frames (frWords f)).length = 13 + f.A.length + f.B.length + f.SA.length +
      f.SB.length + f.AT.length + (toWord f.EX).length := by
    simp [frames, frWords]; omega
  refine ⟨σ8, ?_, ?_, by omega, (o17.trans o8).mono (by decide)⟩
  · unfold emFr; simp only [seqs]
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6
      (Run.seq r7 r8))))))).mono (by simp [Expr.size]; omega)
  · simp only [List.map_cons, List.map_nil] at F8
    rw [e1 "gd" (by simp), e1 "gk" (by simp), e1 "g1" (by simp), e1 "g2" (by simp), e1 "gp" (by simp),
      e1 "gi" (by simp), hf.d, hf.kk, hf.l1, hf.l2, hf.ph, hf.i] at F8
    simpa [frames, frWords] using F8

theorem emFresh_run {W M : ℕ} {σ : Env} {pre : List ℕ} {d kk l1 l2 : ℕ} {A B : List ℕ}
    (hC : Ctx W M σ) (hF : Filled "OB" "po" pre σ) (hf : FreshIs M σ d kk l1 l2 A B)
    (hpre : pre.length + 8 * M ≤ W) :
    ∃ σ', Run (W + 1) emFresh σ σ' (20 * (A.length + B.length) + 300) ∧
      Filled "OB" "po" (pre ++ frames (frWords (fresh d kk l1 l2 A B))) σ' ∧
      (frames (frWords (fresh d kk l1 l2 A B))).length ≤ 4 * M ∧ OFr σ σ' ["ci", "po"] := by
  have hM := hC.room; have h16 := hC.m16
  obtain ⟨n1, n2, n3, n4⟩ := hf.nums
  have lA := hf.hA.2.1; have lB := hf.hB.2.1
  obtain ⟨σ1, r1, F1, o1⟩ := pv_run hF (ev_lit (σ := σ) (n := 6) (W := W) (by omega)) hC.ol (by omega)
  have e1 : ∀ y ∈ ["cd", "ck", "c1", "c2"], σ1.vars y = σ.vars y :=
    fun y hy => o1.vars y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨σ2, r2, F2, o2⟩ := pushVars_run (W := W) (xs := ["cd", "ck", "c1", "c2"]) (by decide) F1
    (by intro x hx; rw [e1 x hx]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [hf.hd]; omega
        · rw [hf.hk]; omega
        · rw [hf.h1]; omega
        · rw [hf.h2]; omega)
    (by rw [o1.len, hC.ol]; simp; omega) (by simp; omega)
  have o12 := (o1.trans o2).mono (show ["po", "po"] ⊆ ["ci", "po"] by decide)
  have C2 := hC.ofr o12 (by decide)
  obtain ⟨σ3, r3, F3, o3⟩ := pushLits_run (W := W) (l := [0, 0]) F2 (by simp)
    (by rw [C2.ol]; simp; omega) (by simp; omega)
  have o13 := (o12.trans o3).mono (show ["ci", "po", "po"] ⊆ ["ci", "po"] by decide)
  obtain ⟨σ4, r4, F4, o4⟩ := emW_run (by decide) (by decide) (hC.ofr o13 (by decide)) F3
    (hf.hA.ofr o13 (by decide) (by decide)) (by simp; omega)
  have o14 := (o13.trans o4).mono (show ["ci", "po", "ci", "po"] ⊆ ["ci", "po"] by decide)
  obtain ⟨σ5, r5, F5, o5⟩ := emW_run (by decide) (by decide) (hC.ofr o14 (by decide)) F4
    (hf.hB.ofr o14 (by decide) (by decide)) (by simp; omega)
  have o15 := (o14.trans o5).mono (show ["ci", "po", "ci", "po"] ⊆ ["ci", "po"] by decide)
  have C5 := hC.ofr o15 (by decide)
  obtain ⟨σ6, r6, F6, o6⟩ := pushLits_run (W := W) (l := [0, 0, 0, 1, 0]) F5 (by simp; omega)
    (by rw [C5.ol]; simp; omega) (by simp; omega)
  have hfl : (frames (frWords (fresh d kk l1 l2 A B))).length = 14 + A.length + B.length := by
    simp [frames, frWords, fresh, toWord_words]; omega
  refine ⟨σ6, ?_, ?_, by omega, (o15.trans o6).mono (by decide)⟩
  · unfold emFresh; simp only [seqs]
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono
      (by simp [Expr.size]; omega)
  · simp only [List.map_cons, List.map_nil] at F6
    rw [e1 "cd" (by simp), e1 "ck" (by simp), e1 "c1" (by simp), e1 "c2" (by simp), hf.hd, hf.hk,
      hf.h1, hf.h2] at F6
    simpa [frames, frWords, fresh, toWord_words] using F6

end Lax185574Proofs.CompRam
