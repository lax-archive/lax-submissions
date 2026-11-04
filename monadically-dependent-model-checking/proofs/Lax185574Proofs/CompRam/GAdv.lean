import Lax185574Proofs.CompRam.GNav
import Lax185574Proofs.CompRam.GEmit
import Lax185574Proofs.CompRam.GEmit2
import Lax185574Proofs.CompRam.GBuilt

/-!
The step `advance` of the glue command of lem:compose: the child of the
current extension of a frame (`childCmd_run`), and the output of
`advance g S` (`advCmd_run`).
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- The scalars written by `childCmd`. -/
def childVars : List String := ["cd", "ck", "c1", "c2", "y", "sk", "u", "cAs", "cAl", "cBs", "cBl"]

theorem getElem_x_of_xg {X : List ℕ} {y v : ℕ} (hy : y < X.length) (h : xg X y = v) : X[y]? = some v := by
  rw [List.getElem?_eq_getElem hy]; rw [xg_of_lt hy] at h; rw [h]

/-- The child word of extension `k` of a list of extension words at `y`. -/
theorem child_seg {X : List ℕ} {y : ℕ} {e r : List ℕ} (h : X.drop (y + 1) = e ++ r) :
    seg X (y + 1 + 1) (e.length - 1) = e.drop 1 := by
  have h1 : seg X (y + 1) e.length = e := by simp [seg, h]
  exact seg_drop_front (k := 1) h1


/-- The first branch of `childCmd`: the child of an extension of `A`. -/
theorem child1_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {f : Fr} (hg : SlotIs M σ f)
    {d kk : ℕ} (hcd : σ.vars "cd" = d) (hck : σ.vars "ck" = kk) (hd : d < 2 * M) (hk : kk < 2 * M)
    {ws : List (List ℕ)} {rr : List ℕ} (hy : (σ.arrs "x").drop (σ.vars "yA") = toWord ws ++ rr)
    (hyM : σ.vars "yA" + (toWord ws).length ≤ M) (hi : f.i < ws.length) (hne : 1 ≤ (ws[f.i]'hi).length)
    (hl : f.l1 + 1 < 2 * M) :
    ∃ σ', Run (W + 1) (seqs [asg "c1" (.add (V "g1") (N 1)), asg "c2" (V "g2"), asg "y" (V "yA"),
        extFr "gi", asg "cAs" (.add (V "y") (N 2)), asg "cAl" (.sub (X (V "y")) (N 1)),
        asg "cBs" (V "gTs"), asg "cBl" (V "gTl")]) σ σ' (20 * ws.length + 100) ∧
      FreshIs M σ' d kk (f.l1 + 1) f.l2 ((ws[f.i]'hi).drop 1) f.SB ∧ OFr σ σ' childVars := by
  have hR := hC.room
  have hgi : σ.vars "gi" = f.i := hg.i
  set σ1 := σ.setVar "c1" (f.l1 + 1) with h1
  set σ2 := σ1.setVar "c2" f.l2 with h2
  set σ3 := σ2.setVar "y" (σ.vars "yA") with h3
  have hC3 : Ctx W M σ3 := ((hC.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
  have r1 : Run (W + 1) (asg "c1" (.add (V "g1") (N 1))) σ σ1 4 :=
    (Run.assign (by simp [hg.l1]; omega)).mono (by simp)
  have r2 : Run (W + 1) (asg "c2" (V "g2")) σ1 σ2 2 :=
    (Run.assign (by simp [h1, hg.l2]; have := hg.nums; omega)).mono (by simp)
  have r3 : Run (W + 1) (asg "y" (V "yA")) σ2 σ3 2 :=
    (Run.assign (by simp [h1, h2]; omega)).mono (by simp)
  obtain ⟨σ4, r4, hy4, hxg, hdrop, hle, fr4⟩ := extFr_run (k := "gi") (by decide) hC3
    (ws := ws) (r := rr) (by simpa [h3, h2, h1] using hy) (by simpa [h3, h2, h1, hgi] using hi)
    (by simpa [h3, h2, h1] using hyM)
  have hgi3 : σ3.vars "gi" = f.i := by simp [h3, h2, h1, hgi]
  simp only [hgi3] at hxg hdrop hle
  have hx4 : σ4.arrs "x" = σ.arrs "x" := by rw [fr4.arrs "x" (by decide)]; simp [h3, h2, h1]
  set e := ws[f.i]'hi with he
  set y4 := σ4.vars "y" with hy4def
  have hy4M : y4 + 1 + e.length ≤ M := by
    have : σ3.vars "y" = σ.vars "yA" := by simp [h3]
    omega
  set σ5 := σ4.setVar "cAs" (y4 + 2) with h5
  set σ6 := σ5.setVar "cAl" (e.length - 1) with h6
  set σ7 := σ6.setVar "cBs" (σ.vars "gTs") with h7
  set σ8 := σ7.setVar "cBl" (σ.vars "gTl") with h8
  have hgT : σ4.vars "gTs" = σ.vars "gTs" ∧ σ4.vars "gTl" = σ.vars "gTl" := by
    rw [fr4.vars _ (by decide), fr4.vars _ (by decide)]; simp [h3, h2, h1]
  have hxl : (σ.arrs "x").length = W + 1 := hC.xl
  have hSB := hg.SB
  obtain ⟨hTl, hTM, hTseg⟩ := hSB
  have r5 : Run (W + 1) (asg "cAs" (.add (V "y") (N 2))) σ4 σ5 4 :=
    (Run.assign (by simp; omega)).mono (by simp)
  have r6 : Run (W + 1) (asg "cAl" (.sub (X (V "y")) (N 1))) σ5 σ6 5 := by
    refine (Run.assign ?_).mono (by simp)
    have hget : (σ5.arrs "x")[y4]? = some e.length := by
      rw [show σ5.arrs "x" = σ.arrs "x" by simp [h5, hx4]]
      exact getElem_x_of_xg (by omega) (by simpa [h3, h2, h1] using hxg)
    have hel : e.length < W + 1 := by omega
    simp only [X, V, N, Expr.sub_def]
    rw [show e.length - 1 = Bop.sub.apply e.length 1 from rfl]
    exact evalB_bin (evalB_get (evalB_var (by simp [h5]; omega)) (by simpa [h5] using hget) hel)
      (evalB_lit (by omega)) (by simp; omega)
  have r7 : Run (W + 1) (asg "cBs" (V "gTs")) σ6 σ7 2 :=
    (Run.assign (by simp [h6, h5, hgT.1]; omega)).mono (by simp)
  have r8 : Run (W + 1) (asg "cBl" (V "gTl")) σ7 σ8 2 :=
    (Run.assign (by simp [h7, h6, h5, hgT.2]; rw [hTl]; omega)).mono (by simp)
  refine ⟨σ8, ?_, ?_, ?_⟩
  · refine ((Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_cons (by simp) r4 (Run.seqs_cons (by simp) r5 (Run.seqs_cons (by simp) r6
      (Run.seqs_cons (by simp) r7 (Run.seqs_one r8)))))))).mono ?_)
    omega
  · have hv4 : ∀ z, z ∉ ["y", "sk"] → σ4.vars z = σ3.vars z := fun z hz => fr4.vars z hz
    have hx8 : σ8.arrs "x" = σ.arrs "x" := by simp [h8, h7, h6, h5, hx4]
    refine ⟨?_, ?_, ?_, ?_, ⟨hd, hk, hl, hg.nums.2.2.2.1⟩, ?_, ?_⟩
    · simp [h8, h7, h6, h5, hv4 "cd" (by decide), h3, h2, h1, hcd]
    · simp [h8, h7, h6, h5, hv4 "ck" (by decide), h3, h2, h1, hck]
    · simp [h8, h7, h6, h5, hv4 "c1" (by decide), h3, h2, h1]
    · simp [h8, h7, h6, h5, hv4 "c2" (by decide), h3, h2, h1]
    · have hne' : 1 ≤ e.length := hne
      refine segIs_of (a := y4 + 2) (by simp [h8, h7, h6, h5]) (by simp [h8, h7, h6]) (by simp; omega) ?_
      rw [hx8, show y4 + 2 = y4 + 1 + 1 by omega, List.length_drop]
      exact child_seg (r := frames (ws.drop (f.i + 1)) ++ rr) (by simpa [h3, h2, h1] using hdrop)
    · refine segIs_of (a := σ.vars "gTs") (by simp [h8, h7]) (by simp [h8, hgT.2, hTl]) hTM ?_
      rw [hx8]; exact hTseg
  · exact (((((((((OFr.setVar σ "c1" _).trans (OFr.setVar σ1 "c2" _)).trans (OFr.setVar σ2 "y" _)).trans
      fr4).trans (OFr.setVar σ4 "cAs" _)).trans (OFr.setVar σ5 "cAl" _)).trans
      (OFr.setVar σ6 "cBs" _)).trans (OFr.setVar σ7 "cBl" _))).mono (by decide)

/-- The second branch of `childCmd`: the child of an extension of `B`. -/
theorem child2_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {f : Fr} (hg : SlotIs M σ f)
    {d kk : ℕ} (hcd : σ.vars "cd" = d) (hck : σ.vars "ck" = kk) (hd : d < 2 * M) (hk : kk < 2 * M)
    {a : ℕ} (hnA : σ.vars "nA" = a) (ha : a ≤ f.i)
    {ws : List (List ℕ)} {rr : List ℕ} (hy : (σ.arrs "x").drop (σ.vars "yB") = toWord ws ++ rr)
    (hyM : σ.vars "yB" + (toWord ws).length ≤ M) (hi : f.i - a < ws.length)
    (hne : 1 ≤ (ws[f.i - a]'hi).length) (hl : f.l2 + 1 < 2 * M) :
    ∃ σ', Run (W + 1) (seqs [asg "c1" (V "g1"), asg "c2" (.add (V "g2") (N 1)), asg "y" (V "yB"),
        asg "u" (.sub (V "gi") (V "nA")), extFr "u", asg "cAs" (V "gSs"), asg "cAl" (V "gSl"),
        asg "cBs" (.add (V "y") (N 2)), asg "cBl" (.sub (X (V "y")) (N 1))]) σ σ'
        (20 * ws.length + 100) ∧
      FreshIs M σ' d kk f.l1 (f.l2 + 1) f.SA ((ws[f.i - a]'hi).drop 1) ∧ OFr σ σ' childVars := by
  have hR := hC.room
  have hgi : σ.vars "gi" = f.i := hg.i
  set σ1 := σ.setVar "c1" f.l1 with h1
  set σ2 := σ1.setVar "c2" (f.l2 + 1) with h2
  set σ3 := σ2.setVar "y" (σ.vars "yB") with h3
  set σ3' := σ3.setVar "u" (f.i - a) with h3'
  have hC3 : Ctx W M σ3' :=
    (((hC.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
  have hnAM : a < W + 1 := by have := hg.nums; omega
  have r1 : Run (W + 1) (asg "c1" (V "g1")) σ σ1 2 :=
    (Run.assign (by simp [hg.l1]; have := hg.nums; omega)).mono (by simp)
  have r2 : Run (W + 1) (asg "c2" (.add (V "g2") (N 1))) σ1 σ2 4 :=
    (Run.assign (by simp [h1, hg.l2]; omega)).mono (by simp)
  have r3 : Run (W + 1) (asg "y" (V "yB")) σ2 σ3 2 :=
    (Run.assign (by simp [h1, h2]; omega)).mono (by simp)
  have r3' : Run (W + 1) (asg "u" (.sub (V "gi") (V "nA"))) σ3 σ3' 4 := by
    refine (Run.assign ?_).mono (by simp)
    have := hg.nums
    simp [h3, h2, h1, hgi, hnA]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  obtain ⟨σ4, r4, hy4, hxg, hdrop, hle, fr4⟩ := extFr_run (k := "u") (by decide) hC3
    (ws := ws) (r := rr) (by simpa [h3', h3, h2, h1] using hy) (by simpa [h3'] using hi)
    (by simpa [h3', h3, h2, h1] using hyM)
  have hu3 : σ3'.vars "u" = f.i - a := by simp [h3']
  simp only [hu3] at hxg hdrop hle
  have hx4 : σ4.arrs "x" = σ.arrs "x" := by rw [fr4.arrs "x" (by decide)]; simp [h3', h3, h2, h1]
  set e := ws[f.i - a]'hi with he
  set y4 := σ4.vars "y" with hy4def
  have hy4M : y4 + 1 + e.length ≤ M := by
    have : σ3'.vars "y" = σ.vars "yB" := by simp [h3', h3]
    omega
  set σ5 := σ4.setVar "cAs" (σ.vars "gSs") with h5
  set σ6 := σ5.setVar "cAl" (σ.vars "gSl") with h6
  set σ7 := σ6.setVar "cBs" (y4 + 2) with h7
  set σ8 := σ7.setVar "cBl" (e.length - 1) with h8
  have hgS : σ4.vars "gSs" = σ.vars "gSs" ∧ σ4.vars "gSl" = σ.vars "gSl" := by
    rw [fr4.vars _ (by decide), fr4.vars _ (by decide)]; simp [h3', h3, h2, h1]
  have hxl : (σ.arrs "x").length = W + 1 := hC.xl
  obtain ⟨hSl, hSM, hSseg⟩ := hg.SA
  have r5 : Run (W + 1) (asg "cAs" (V "gSs")) σ4 σ5 2 :=
    (Run.assign (by simp [hgS.1]; omega)).mono (by simp)
  have r6 : Run (W + 1) (asg "cAl" (V "gSl")) σ5 σ6 2 :=
    (Run.assign (by simp [h5, hgS.2]; rw [hSl]; omega)).mono (by simp)
  have r7 : Run (W + 1) (asg "cBs" (.add (V "y") (N 2))) σ6 σ7 4 :=
    (Run.assign (by simp [h6, h5]; omega)).mono (by simp)
  have r8 : Run (W + 1) (asg "cBl" (.sub (X (V "y")) (N 1))) σ7 σ8 5 := by
    refine (Run.assign ?_).mono (by simp)
    have hget : (σ7.arrs "x")[y4]? = some e.length := by
      rw [show σ7.arrs "x" = σ.arrs "x" by simp [h7, h6, h5, hx4]]
      exact getElem_x_of_xg (by omega) (by simpa [h3', h3, h2, h1] using hxg)
    have hel : e.length < W + 1 := by omega
    simp only [X, V, N, Expr.sub_def]
    rw [show e.length - 1 = Bop.sub.apply e.length 1 from rfl]
    exact evalB_bin (evalB_get (evalB_var (by simp [h7, h6, h5]; omega)) (by simpa [h7, h6, h5] using hget) hel)
      (evalB_lit (by omega)) (by simp; omega)
  refine ⟨σ8, ?_, ?_, ?_⟩
  · refine ((Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_cons (by simp) r3' (Run.seqs_cons (by simp) r4 (Run.seqs_cons (by simp) r5
      (Run.seqs_cons (by simp) r6 (Run.seqs_cons (by simp) r7 (Run.seqs_one r8))))))))).mono ?_)
    omega
  · have hv4 : ∀ z, z ∉ ["y", "sk"] → σ4.vars z = σ3'.vars z := fun z hz => fr4.vars z hz
    have hx8 : σ8.arrs "x" = σ.arrs "x" := by simp [h8, h7, h6, h5, hx4]
    refine ⟨?_, ?_, ?_, ?_, ⟨hd, hk, hg.nums.2.2.1, hl⟩, ?_, ?_⟩
    · simp [h8, h7, h6, h5, hv4 "cd" (by decide), h3', h3, h2, h1, hcd]
    · simp [h8, h7, h6, h5, hv4 "ck" (by decide), h3', h3, h2, h1, hck]
    · simp [h8, h7, h6, h5, hv4 "c1" (by decide), h3', h3, h2, h1]
    · simp [h8, h7, h6, h5, hv4 "c2" (by decide), h3', h3, h2, h1]
    · refine segIs_of (a := σ.vars "gSs") (by simp [h8, h7, h6, h5, hgS.1])
        (by simp [h8, h7, h6, hSl]) hSM ?_
      rw [hx8]; exact hSseg
    · have hne' : 1 ≤ e.length := hne
      refine segIs_of (a := y4 + 2) (by simp [h8, h7]) (by simp [h8]) (by simp; omega) ?_
      rw [hx8, show y4 + 2 = y4 + 1 + 1 by omega, List.length_drop]
      exact child_seg (r := frames (ws.drop (f.i - a + 1)) ++ rr)
        (by simpa [h3', h3, h2, h1] using hdrop)
  · exact ((((((((((OFr.setVar σ "c1" _).trans (OFr.setVar σ1 "c2" _)).trans (OFr.setVar σ2 "y" _)).trans
      (OFr.setVar σ3 "u" _)).trans fr4).trans (OFr.setVar σ4 "cAs" _)).trans (OFr.setVar σ5 "cAl" _)).trans
      (OFr.setVar σ6 "cBs" _)).trans (OFr.setVar σ7 "cBl" _))).mono (by decide)

theorem extsOf_getD_eq {h l : ℕ} (t : Node (h + 1) l) {j : ℕ} (hj : j < (Node.exts t).words.length) :
    (extsOf (toWord t)).getD j [] = (Node.exts t).words[j] ∧ 1 ≤ ((Node.exts t).words[j]).length := by
  refine ⟨by rw [extsOf_node, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl, ?_⟩
  obtain ⟨ε, -, he⟩ := extsOf_getD t hj
  have : (extsOf (toWord t)).getD j [] = (Node.exts t).words[j] := by
    rw [extsOf_node, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [← this, he]; simp

theorem length_words_le_toWord {h l : ℕ} (t : Node (h + 1) l) :
    (toWord (Node.exts t).words).length ≤ (toWord t).length := by
  rw [toWord_node_succ, List.length_append]; omega

/-- **The child of the current extension.** -/
theorem childCmd_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {g : Fr} (hg : SlotIs M σ g) {h : ℕ}
    (hdh : g.d = h + 1) (tA : Node (h + 1) g.l1) (tB : Node (h + 1) g.l2)
    (hA : g.A = toWord tA) (hB : g.B = toWord tB)
    (hnA : σ.vars "nA" = nA g) {rA rB : List ℕ}
    (hyA : (σ.arrs "x").drop (σ.vars "yA") = toWord (Node.exts tA).words ++ rA)
    (hyAM : σ.vars "yA" + (toWord (Node.exts tA).words).length ≤ M)
    (hyB : (σ.arrs "x").drop (σ.vars "yB") = toWord (Node.exts tB).words ++ rB)
    (hyBM : σ.vars "yB" + (toWord (Node.exts tB).words).length ≤ M)
    (hi : g.i < nA g + nB g) (hnum : g.kk + g.l1 + g.l2 + 2 < M) :
    ∃ σ', Run (W + 1) childCmd σ σ' (20 * ((toWord tA).length + (toWord tB).length) + 200) ∧
      FreshIs M σ' (child g).d (child g).kk (child g).l1 (child g).l2 (child g).A (child g).B ∧
      OFr σ σ' childVars := by
  have hR := hC.room
  have hnums := hg.nums
  have hnAe : nA g = (Node.exts tA).words.length := by simp only [nA, hA, extsOf_node]
  have hnBe : nB g = (Node.exts tB).words.length := by simp only [nB, hB, extsOf_node]
  have hwA := length_words_le_toWord tA
  have hwB := length_words_le_toWord tB
  have hcA := count_lt_toWord (Node.exts tA).words
  have hcB := count_lt_toWord (Node.exts tB).words
  set σ1 := σ.setVar "cd" (g.d - 1) with h1
  set σ2 := σ1.setVar "ck" (g.kk + 1) with h2
  have r1 : Run (W + 1) (asg "cd" (.sub (V "gd") (N 1))) σ σ1 4 :=
    (Run.assign (by simp [hg.d]; omega)).mono (by simp)
  have r2 : Run (W + 1) (asg "ck" (.add (V "gk") (N 1))) σ1 σ2 4 :=
    (Run.assign (by simp [h1, hg.kk]; omega)).mono (by simp)
  have hC2 : Ctx W M σ2 := (hC.setVar (by decide) _).setVar (by decide) _
  have hg2 : SlotIs M σ2 g := (hg.setVar (by decide) _).setVar (by decide) _
  have hcd : σ2.vars "cd" = g.d - 1 := by simp [h2, h1]
  have hck : σ2.vars "ck" = g.kk + 1 := by simp [h2]
  have hnA2 : σ2.vars "nA" = nA g := by simp [h2, h1, hnA]
  have hgi2 : σ2.vars "gi" = g.i := hg2.i
  have hx2 : σ2.arrs "x" = σ.arrs "x" := by simp [h2, h1]
  have hyA2 : σ2.vars "yA" = σ.vars "yA" := by simp [h2, h1]
  have hyB2 : σ2.vars "yB" = σ.vars "yB" := by simp [h2, h1]
  have hfr12 : OFr σ σ2 ["cd", "ck"] := (OFr.setVar σ "cd" _).trans (OFr.setVar σ1 "ck" _)
  by_cases hlt : g.i < nA g
  · have hi' : g.i < (Node.exts tA).words.length := by omega
    obtain ⟨hge, hne⟩ := extsOf_getD_eq tA hi'
    obtain ⟨σ', r, hfr, fr⟩ := child1_run hC2 hg2 hcd hck (by omega) (by omega) (ws := (Node.exts tA).words)
      (rr := rA) (by rw [hx2, hyA2]; exact hyA) (by rw [hyA2]; exact hyAM) hi' hne (by omega)
    refine ⟨σ', ?_, ?_, (hfr12.trans fr).mono (by decide)⟩
    · refine (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_one
        (Run.ite_true ?_ r)))).mono ?_
      · rw [evalB_condLt (evalB_var (by rw [hgi2]; have := hg.nums; omega))
          (evalB_var (by rw [hnA2]; omega)), hgi2, hnA2]
        simp [hlt]
      · simp only [Cond.size, Expr.size, V]; omega
    · rw [child_lt g hlt]
      simp only [fresh]
      rw [hA, hge]
      exact hfr
  · have hle : nA g ≤ g.i := by omega
    have hi' : g.i - nA g < (Node.exts tB).words.length := by omega
    obtain ⟨hge, hne⟩ := extsOf_getD_eq tB hi'
    obtain ⟨σ', r, hfr, fr⟩ := child2_run hC2 hg2 hcd hck (by omega) (by omega) hnA2 hle
      (ws := (Node.exts tB).words) (rr := rB) (by rw [hx2, hyB2]; exact hyB) (by rw [hyB2]; exact hyBM)
      hi' hne (by omega)
    refine ⟨σ', ?_, ?_, (hfr12.trans fr).mono (by decide)⟩
    · refine (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_one
        (Run.ite_false ?_ r)))).mono ?_
      · rw [evalB_condLt (evalB_var (by rw [hgi2]; have := hg.nums; omega))
          (evalB_var (by rw [hnA2]; omega)), hgi2, hnA2]
        simp [hlt]
      · simp only [Cond.size, Expr.size, V]; omega
    · rw [child_ge g hlt]
      simp only [fresh]
      rw [hB, hge]
      exact hfr

/-! ### Helpers for the stages -/

theorem Run.seqs_append {B : ℕ} : ∀ {l1 l2 : List Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}, l1 ≠ [] → l2 ≠ [] →
    Run B (seqs l1) σ σ1 K1 → Run B (seqs l2) σ1 σ2 K2 → Run B (seqs (l1 ++ l2)) σ σ2 (K1 + K2)
  | [c], l2, _, _, _, _, _, _, h2, r1, r2 => Run.seqs_cons h2 r1 r2
  | c :: d :: l1, l2, σ, σ1, σ2, K1, K2, _, h2, r1, r2 => by
    obtain ⟨k, hk, hb⟩ := r1
    cases hb with
    | seq ha hb' =>
      have := Run.seqs_append (l1 := d :: l1) (by simp) h2 (Run.of_bigStepB hb') r2
      have h := Run.seq (Run.of_bigStepB ha) this
      exact h.mono (by omega)

theorem keep_of_ofr {σ σ' : Env} {xs : List String} (h : OFr σ σ' xs) (hW : "W" ∉ xs) (hj : "jr" ∉ xs)
    (ho : "ovf" ∉ xs) : Keep σ σ' :=
  ⟨h.vars _ hW, h.vars _ hj, h.vars _ ho, h.arrs _ (by decide), h.arrs _ (by decide), h.len, h.out, h.inp⟩

theorem filled_nil_ofr {σ σ' : Env} {xs : List String} (h : Filled "OB" "po" [] σ) (hf : OFr σ σ' xs)
    (hpo : "po" ∉ xs) : Filled "OB" "po" [] σ' :=
  ⟨by rw [hf.vars _ hpo]; exact h.pos, fun i hi => absurd hi (by simp)⟩

theorem len_frWords (f : Fr) : (frames (frWords f)).length =
    13 + f.A.length + f.B.length + f.SA.length + f.SB.length + f.AT.length + (toWord f.EX).length := by
  simp [frames, frWords]; omega

theorem len_frWords_fresh (d kk l1 l2 : ℕ) (A B : List ℕ) :
    (frames (frWords (fresh d kk l1 l2 A B))).length = 14 + A.length + B.length := by
  rw [len_frWords]; simp [fresh, toWord_words, frames]; omega

theorem hd0_cons (j : ℕ) (f : Fr) (S : List Fr) :
    hd0 j (f :: S) = [1, 0, 0, 0, j, 7 + (stWords S).length] ++ frames (frWords f) ++
      frames (stWords S) := by
  simp only [hd0, stWords_cons, frames_append, List.length_append, List.append_assoc]
  simp [frWords]

theorem length_hd0 (j : ℕ) (S : List Fr) : (hd0 j S).length = 6 + (frames (stWords S)).length := by
  simp [hd0]; omega

/-! ### Writing the state -/

/-- The scalars written while the state is written. -/
def stVars : List String := ["po", "ci", "u1", "u2", "gEL"]

/-- The state of a call whose new top frame is described by the scalars `g…`. -/
theorem stateOne_run {W M : ℕ} {σ : Env} {g : Fr} {Sr : List Fr} {j : ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" [] σ) (hg : SlotIs M σ g)
    (hrest : SegIs M σ "rS" "rL" (frames (stWords Sr))) (hcnt : σ.vars "cnt" = 7 + (stWords Sr).length)
    (hj1 : σ.vars "j1" = j) (hjM : j < M) :
    ∃ σ', Run (W + 1) (seqs [emHd, emFr, emRest, patchL]) σ σ'
        (20 * (hd0 j (g :: Sr)).length + 600) ∧
      Filled "OB" "po" (hdS j (g :: Sr)) σ' ∧ (hdS j (g :: Sr)).length ≤ 18 * M + 6 ∧
      OFr σ σ' stVars := by
  have hR := hC.room
  have hrest0 := hrest
  obtain ⟨hrl, hrM, -⟩ := hrest0
  have hcl : (stWords Sr).length ≤ (frames (stWords Sr)).length := by
    rw [frames, List.length_flatten, List.map_map]
    calc (stWords Sr).length = ((stWords Sr).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum (fun u _ => by simp)
  obtain ⟨σ1, r1, F1, fr1⟩ := emHd_run hC hF (by omega) (by omega) (by simp; omega)
  have hC1 := hC.ofr fr1 (by decide)
  obtain ⟨σ2, r2, F2, hl2, fr2⟩ := emFr_run hC1 F1
    (hg.ofr fr1 (by intro y hy; simp only [List.mem_singleton]; intro h; subst h; exact absurd hy (by decide)))
    (by simp; omega)
  have hC2 := hC1.ofr fr2 (by decide)
  have hrest2 : SegIs M σ2 "rS" "rL" (frames (stWords Sr)) :=
    (hrest.ofr fr1 (by decide) (by decide)).ofr fr2 (by decide) (by decide)
  obtain ⟨σ3, r3, F3, fr3⟩ := emRest_run hC2 F2 hrest2 (by simp; omega)
  have hL : [] ++ [1, 0, 0, 0, σ.vars "j1", σ.vars "cnt"] ++ frames (frWords g) ++ frames (stWords Sr) =
      hd0 j (g :: Sr) := by rw [hd0_cons, hj1, hcnt]; simp
  rw [hL] at F3
  have hlen := length_hd0 j (g :: Sr)
  have hfs : (frames (stWords (g :: Sr))).length = (frames (frWords g)).length + (frames (stWords Sr)).length := by
    rw [stWords_cons, frames_append, List.length_append]
  obtain ⟨σ4, r4, F4, fr4⟩ := patchL_run (W := W) F3 (by omega) (by omega)
  refine ⟨σ4, ?_, F4, by rw [length_hdS]; omega, ?_⟩
  · refine (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_one r4)))).mono ?_
    omega
  · exact (((fr1.trans fr2).trans fr3).trans fr4).mono (by decide)

/-- The state of a call with a new frame above the frame described by the scalars `g…`. -/
theorem stateTwo_run {W M : ℕ} {σ : Env} {g : Fr} {Sr : List Fr} {j d kk l1 l2 : ℕ} {A B : List ℕ}
    (hC : Ctx W M σ) (hF : Filled "OB" "po" [] σ) (hc : FreshIs M σ d kk l1 l2 A B) (hg : SlotIs M σ g)
    (hrest : SegIs M σ "rS" "rL" (frames (stWords Sr))) (hcnt : σ.vars "cnt" = 14 + (stWords Sr).length)
    (hj1 : σ.vars "j1" = j) (hjM : j < M) :
    ∃ σ', Run (W + 1) (seqs [emHd, emFresh, emFr, emRest, patchL]) σ σ'
        (20 * (hd0 j (fresh d kk l1 l2 A B :: g :: Sr)).length + 900) ∧
      Filled "OB" "po" (hdS j (fresh d kk l1 l2 A B :: g :: Sr)) σ' ∧
      (hdS j (fresh d kk l1 l2 A B :: g :: Sr)).length ≤ 22 * M + 6 ∧ OFr σ σ' stVars := by
  have hR := hC.room
  have hrest0 := hrest
  obtain ⟨hrl, hrM, -⟩ := hrest0
  have hcl : (stWords Sr).length ≤ (frames (stWords Sr)).length := by
    rw [frames, List.length_flatten, List.map_map]
    calc (stWords Sr).length = ((stWords Sr).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum (fun u _ => by simp)
  have hpo1 : ∀ y ∈ freshVars, y ∉ ["po"] := by decide
  obtain ⟨σ1, r1, F1, fr1⟩ := emHd_run hC hF (by omega) (by omega) (by simp; omega)
  have hC1 := hC.ofr fr1 (by decide)
  obtain ⟨σ2, r2, F2, hl2, fr2⟩ := emFresh_run hC1 F1 (hc.ofr fr1 hpo1) (by simp; omega)
  have hC2 := hC1.ofr fr2 (by decide)
  have hg2 : SlotIs M σ2 g := (hg.ofr fr1 (by decide)).ofr fr2 (by decide)
  obtain ⟨σ3, r3, F3, hl3, fr3⟩ := emFr_run hC2 F2 hg2 (by simp; omega)
  have hC3 := hC2.ofr fr3 (by decide)
  have hrest3 : SegIs M σ3 "rS" "rL" (frames (stWords Sr)) :=
    ((hrest.ofr fr1 (by decide) (by decide)).ofr fr2 (by decide) (by decide)).ofr fr3 (by decide) (by decide)
  obtain ⟨σ4, r4, F4, fr4⟩ := emRest_run hC3 F3 hrest3 (by simp; omega)
  have hL : [] ++ [1, 0, 0, 0, σ.vars "j1", σ.vars "cnt"] ++ frames (frWords (fresh d kk l1 l2 A B)) ++
      frames (frWords g) ++ frames (stWords Sr) = hd0 j (fresh d kk l1 l2 A B :: g :: Sr) := by
    rw [hd0_cons, hj1, hcnt, stWords_cons, frames_append]; simp [frWords]; omega
  rw [hL] at F4
  have hlen := length_hd0 j (fresh d kk l1 l2 A B :: g :: Sr)
  have hfs : (frames (stWords (fresh d kk l1 l2 A B :: g :: Sr))).length =
      (frames (frWords (fresh d kk l1 l2 A B))).length + (frames (frWords g)).length +
        (frames (stWords Sr)).length := by
    rw [stWords_cons, stWords_cons, frames_append, frames_append]; simp; omega
  obtain ⟨σ5, r5, F5, fr5⟩ := patchL_run (W := W) F4 (by omega) (by omega)
  refine ⟨σ5, ?_, F5, by rw [length_hdS]; omega, ?_⟩
  · have hfa := len_frWords_fresh d kk l1 l2 A B
    refine (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_cons (by simp) r4 (Run.seqs_one r5))))).mono ?_
    omega
  · exact ((((fr1.trans fr2).trans fr3).trans fr4).trans fr5).mono (by decide)

/-! ### The query of the canonical form -/

/-- The scalars written by the query of the canonical form. -/
def caVars : List String :=
  ["po", "sp", "dq", "qa", "y", "sn", "sk", "u1", "u2", "ci", "nr", "rk", "fl", "ft", "fk", "fb", "gEL",
    "ql", "qk"]

/-- The query of the canonical form of the atoms of a new frame. -/
theorem caAtoms_run {W M : ℕ} {σ : Env} {j : ℕ} {S : List Fr} {d kk l1 l2 : ℕ} {A B rA rB : List ℕ}
    (hC : Ctx W M σ) (hF : Filled "OB" "po" (hdS j S) σ) (hlen : (hdS j S).length ≤ 22 * M + 6)
    (hc : FreshIs M σ d kk l1 l2 A B) (hA : A = toWord (atomsOf A) ++ rA)
    (hB : B = toWord (atomsOf B) ++ rB) (hl : l1 < M) :
    ∃ σ' ob, Run (W + 1) (seqs [emCaHd, emAtoms, emCaEnd]) σ σ'
        (60 * (A.length + B.length) + 300) ∧
      Built j (.call S (.ca (atomsOf A ++ (atomsOf B).map (renAtom l1)))) ob σ' ∧
      ob.length ≤ (hdS j S).length + 8 + A.length + B.length ∧ (hdS j S).length + 8 ≤ ob.length ∧
      OFr σ σ' caVars := by
  have hR := hC.room
  obtain ⟨-, hAM, -⟩ := hc.hA
  obtain ⟨-, hBM, -⟩ := hc.hB
  obtain ⟨σ1, r1, F1, hsp, hqa, hdq, fr1⟩ := emCaHd_run hC hF (by omega)
  have hC1 := hC.ofr fr1 (by decide)
  obtain ⟨σ2, r2, F2, hl2, fr2⟩ := emAtoms_run hC1 F1 (hc.ofr fr1 (by decide)) hA hB hl
    (by simp; omega)
  have hqa2 : σ2.vars "qa" = (hdS j S ++ [5, lDSq, 0, 0, 0, 0, 0, 0]).length := by
    rw [fr2.vars _ (by decide), hqa]; simp
  obtain ⟨σ3, r3, F3, hql, hqk, fr3⟩ := emCaEnd_run (W := W) F2 hqa2 (by simp) (by simp; omega)
  have e6 : (hdS j S ++ [5, lDSq, 0, 0, 0, 0, 0, 0]).length - 6 = (hdS j S).length + 2 := by simp
  rw [e6] at F3
  have hv : ∀ z, z ∉ ["ql", "qk"] → z ∉ emAtomsVars → σ3.vars z = σ1.vars z := fun z h1 h2 => by
    rw [fr3.vars z h1, fr2.vars z h2]
  refine ⟨σ3, _, ?_, built_ca F3 ?_ ?_ hqk ?_ hql, ?_, by simp, ?_⟩
  · refine (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_one r3))).mono ?_
    omega
  · rw [hv _ (by decide) (by decide), hsp]
  · rw [hv _ (by decide) (by decide), hdq]
  · rw [hv _ (by decide) (by decide), hqa]
  · simp; omega
  · exact ((fr1.trans fr2).trans fr3).mono (by decide)

/-- The query of the canonical form of the extensions of the frame described by `g…`. -/
theorem caEX_run {W M : ℕ} {σ : Env} {j : ℕ} {S : List Fr} {EX : List (List ℕ)}
    (hC : Ctx W M σ) (hF : Filled "OB" "po" (hdS j S) σ) (hlen : (hdS j S).length ≤ 22 * M + 6)
    (hE : ExIs M σ EX) :
    ∃ σ' ob, Run (W + 1) (seqs [emCaHd, emEXc, emCaEnd]) σ σ' (20 * (toWord EX).length + 300) ∧
      Built j (.call S (.ca EX)) ob σ' ∧ ob.length ≤ (hdS j S).length + 8 + 4 * M ∧
      (hdS j S).length + 8 ≤ ob.length ∧ (toWord EX).length ≤ 4 * M ∧ OFr σ σ' caVars := by
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨σ1, r1, F1, hsp, hqa, hdq, fr1⟩ := emCaHd_run hC hF (by omega)
  have hC1 := hC.ofr fr1 (by decide)
  obtain ⟨σ2, r2, F2, hl2, fr2⟩ := emEXc_run hC1 F1 (hE.ofr fr1 (by decide)) (by simp; omega)
  have hqa2 : σ2.vars "qa" = (hdS j S ++ [5, lDSq, 0, 0, 0, 0, 0, 0]).length := by
    rw [fr2.vars _ (by decide), hqa]; simp
  obtain ⟨σ3, r3, F3, hql, hqk, fr3⟩ := emCaEnd_run (W := W) F2 hqa2 (by simp) (by simp; omega)
  have e6 : (hdS j S ++ [5, lDSq, 0, 0, 0, 0, 0, 0]).length - 6 = (hdS j S).length + 2 := by simp
  rw [e6] at F3
  have hv : ∀ z, z ∉ ["ql", "qk"] → z ∉ emFrVars → σ3.vars z = σ1.vars z := fun z h1 h2 => by
    rw [fr3.vars z h1, fr2.vars z h2]
  refine ⟨σ3, _, ?_, built_ca F3 ?_ ?_ hqk ?_ hql, ?_, by simp, hl2, ?_⟩
  · refine (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_one r3))).mono ?_
    omega
  · rw [hv _ (by decide) (by decide), hsp]
  · rw [hv _ (by decide) (by decide), hdq]
  · rw [hv _ (by decide) (by decide), hqa]
  · simp; omega
  · exact ((fr1.trans fr2).trans fr3).mono (by decide)

theorem push_cost (x1 x2 x3 x4 a x5 : ℕ) (h1 : x1 + x2 ≤ a) (h2 : x3 + x4 ≤ a) (h3 : a + 8 ≤ x5) :
    20 * (x1 + x2) + 200 + (2 + (4 + (20 * a + 900 + (60 * (x3 + x4) + 300)))) ≤ 120 * x5 + 2000 := by
  omega

/-! ### The two branches of `advance` -/

theorem child_eta (g : Fr) :
    child g = fresh (child g).d (child g).kk (child g).l1 (child g).l2 (child g).A (child g).B := by
  unfold child; split <;> rfl

theorem child_nw {g : Fr} {h : ℕ} (hdh : g.d = h + 1) (tA : Node (h + 1) g.l1) (tB : Node (h + 1) g.l2)
    (hA : g.A = toWord tA) (hB : g.B = toWord tB) (hi : g.i < nA g + nB g)
    (hSB : g.i < nA g → NW h g.l2 g.SB) (hSA : nA g ≤ g.i → g.i < nA g + nB g → NW h g.l1 g.SA) :
    (child g).d = h ∧ NW h (child g).l1 (child g).A ∧ NW h (child g).l2 (child g).B := by
  by_cases hlt : g.i < nA g
  · rw [child_lt g hlt]
    exact ⟨by simp [fresh]; omega, (nw_child (d := h) ⟨tA, hA⟩ hlt).1, hSB hlt⟩
  · rw [child_ge g hlt]
    exact ⟨by simp [fresh]; omega, hSA (by omega) hi,
      (nw_child (d := h) ⟨tB, hB⟩ (j := g.i - nA g) (by simp only [nB] at hi ⊢; omega)).1⟩

theorem atoms_split {d l : ℕ} {w : List ℕ} (h : NW d l w) : ∃ r, w = toWord (atomsOf w) ++ r := by
  obtain ⟨r, hr⟩ := atomsOf_prefix h
  exact ⟨r, hr.symm⟩

theorem frames_le_hd0_one (j : ℕ) (f : Fr) (S : List Fr) :
    (frames (frWords f)).length + (frames (stWords S)).length ≤ (hd0 j (f :: S)).length := by
  rw [length_hd0, stWords_cons, frames_append, List.length_append]; omega

theorem frames_le_hd0_two (j : ℕ) (c f : Fr) (S : List Fr) :
    (frames (frWords c)).length + (frames (frWords f)).length ≤ (hd0 j (c :: f :: S)).length := by
  rw [length_hd0, stWords_cons, stWords_cons, frames_append, frames_append]; simp; omega

/-- The facts at the test of `advCmd`. -/
structure AdvIn (W M : ℕ) (σ : Env) (g : Fr) (Sr : List Fr) (j h : ℕ) (tA : Node (h + 1) g.l1)
    (tB : Node (h + 1) g.l2) : Prop where
  hC : Ctx W M σ
  hF : Filled "OB" "po" [] σ
  hg : SlotIs M σ g
  hrest : SegIs M σ "rS" "rL" (frames (stWords Sr))
  hcnt : σ.vars "cnt" = (stWords Sr).length
  hj1 : σ.vars "j1" = j
  hjM : j < M
  hdh : g.d = h + 1
  hA : g.A = toWord tA
  hB : g.B = toWord tB
  hnA : σ.vars "nA" = nA g
  hnB : σ.vars "nB" = nB g
  hyA : (σ.arrs "x").drop (σ.vars "yA") = toWord (Node.exts tA).words ++ (σ.arrs "x").drop (σ.vars "gAs" + g.A.length)
  hyAM : σ.vars "yA" + (toWord (Node.exts tA).words).length ≤ M
  hyB : (σ.arrs "x").drop (σ.vars "yB") = toWord (Node.exts tB).words ++ (σ.arrs "x").drop (σ.vars "gBs" + g.B.length)
  hyBM : σ.vars "yB" + (toWord (Node.exts tB).words).length ≤ M
  hSB : g.i < nA g → NW h g.l2 g.SB
  hSA : nA g ≤ g.i → g.i < nA g + nB g → NW h g.l1 g.SA
  hnum : g.kk + g.l1 + g.l2 + 2 < M

/-- The scalars written by the branches of `advCmd`. -/
def advVars : List String := childVars ++ ["gp", "cnt"] ++ stVars ++ caVars

/-- **Opening the child.** -/
theorem advPush_run {W M : ℕ} {σ : Env} {g : Fr} {Sr : List Fr} {j h : ℕ} {tA : Node (h + 1) g.l1}
    {tB : Node (h + 1) g.l2} (H : AdvIn W M σ g Sr j h tA tB) (hi : g.i < nA g + nB g) :
    ∃ σ' ob K, Run (W + 1) (seqs [childCmd, asg "gp" (N 3), asg "cnt" (.add (V "cnt") (N 14)), emHd,
        emFresh, emFr, emRest, patchL, emCaHd, emAtoms, emCaEnd]) σ σ' K ∧
      Built j (advance g Sr) ob σ' ∧ ob.length ≤ 64 * M ∧ K ≤ 120 * ob.length + 2000 ∧
      (toWord tA).length + (toWord tB).length ≤ ob.length ∧ OFr σ σ' advVars := by
  have hC := H.hC
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨σ1, r1, hc1, fr1⟩ := childCmd_run hC H.hg H.hdh tA tB H.hA H.hB H.hnA H.hyA H.hyAM H.hyB
    H.hyBM hi H.hnum
  obtain ⟨hcd, hnwA, hnwB⟩ := child_nw H.hdh tA tB H.hA H.hB hi H.hSB H.hSA
  have hcl1 : (child g).l1 ≤ g.l1 + 1 := by unfold child; split <;> (simp only [fresh]; omega)
  have hnum := H.hnum
  set c := child g with hcdef
  have hrl := H.hrest.1
  have hrM := H.hrest.2.1
  have hcl : (stWords Sr).length ≤ (frames (stWords Sr)).length := by
    rw [frames, List.length_flatten, List.map_map]
    calc (stWords Sr).length = ((stWords Sr).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum (fun u _ => by simp)
  have hxs1 : ∀ y ∈ slotVars, y ∉ childVars := by decide
  set σ2 := σ1.setVar "gp" 3 with h2
  set σ3 := σ2.setVar "cnt" ((stWords Sr).length + 14) with h3
  have r2 : Run (W + 1) (asg "gp" (N 3)) σ1 σ2 2 := (Run.assign (by simp; omega)).mono (by simp)
  have hcnt1 : σ1.vars "cnt" = (stWords Sr).length := by rw [fr1.vars _ (by decide), H.hcnt]
  have r3 : Run (W + 1) (asg "cnt" (.add (V "cnt") (N 14))) σ2 σ3 4 :=
    (Run.assign (by simp [h2, hcnt1]; omega)).mono (by simp)
  have hC3 : Ctx W M σ3 := ((hC.ofr fr1 (by decide)).setVar (by decide) _).setVar (by decide) _
  have hF3 : Filled "OB" "po" [] σ3 :=
    ((filled_nil_ofr H.hF fr1 (by decide)).setVar (by decide) _).setVar (by decide) _
  have hc3 : FreshIs M σ3 c.d c.kk c.l1 c.l2 c.A c.B :=
    (hc1.setVar (by decide) _).setVar (by decide) _
  have hg3 : SlotIs M σ3 { g with ph := 3 } :=
    (((H.hg.ofr fr1 hxs1).set_ph (by omega))).setVar (by decide) _
  have hrest3 : SegIs M σ3 "rS" "rL" (frames (stWords Sr)) :=
    ((H.hrest.ofr fr1 (by decide) (by decide)).setVar (by decide) (by decide) _).setVar (by decide)
      (by decide) _
  have hj3 : σ3.vars "j1" = j := by simp [h3, h2, fr1.vars "j1" (by decide), H.hj1]
  obtain ⟨σ4, r4, F4, hl4, fr4⟩ := stateTwo_run hC3 hF3 hc3 hg3 hrest3 (by simp [h3]; omega) hj3 H.hjM
  rw [← child_eta g] at F4 hl4 r4
  have hC4 := hC3.ofr fr4 (by decide)
  obtain ⟨rA, hrA⟩ := atoms_split hnwA
  obtain ⟨rB, hrB⟩ := atoms_split hnwB
  obtain ⟨σ5, ob, r5, B5, hob, hob', fr5⟩ := caAtoms_run hC4 F4 hl4 (hc3.ofr fr4 (by decide)) hrA hrB
    (by omega)
  have hAB := hc1.hA.2.1
  have hBB := hc1.hB.2.1
  have hle2 := frames_le_hd0_two j c { g with ph := 3 } Sr
  have hfc := len_frWords_fresh c.d c.kk c.l1 c.l2 c.A c.B
  rw [← child_eta g] at hfc
  have hfg := len_frWords { g with ph := 3 }
  have hgA : (toWord tA).length + (toWord tB).length ≤ (hdS j (c :: { g with ph := 3 } :: Sr)).length := by
    rw [length_hdS, ← H.hA, ← H.hB]; simp only at hfg; omega
  have hrun := Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_append (l1 := [emHd, emFresh, emFr, emRest, patchL]) (by simp) (by simp) r4 r5)))
  have e1 := length_hdS j (c :: { g with ph := 3 } :: Sr)
  try rw [← hcdef] at hfc
  try rw [← hcdef] at hob'
  try rw [← hcdef] at hle2
  have hca : c.A.length + c.B.length ≤ (hd0 j (c :: { g with ph := 3 } :: Sr)).length := by omega
  have hta : (toWord tA).length + (toWord tB).length ≤ (hd0 j (c :: { g with ph := 3 } :: Sr)).length := by
    omega
  have hob8 : (hd0 j (c :: { g with ph := 3 } :: Sr)).length + 8 ≤ ob.length := by omega
  refine ⟨σ5, ob, 120 * ob.length + 2000,
    hrun.mono (push_cost _ _ _ _ _ _ hta hca hob8), ?_, by omega, le_rfl, by omega, ?_⟩
  · rw [advance_lt g Sr hi]; exact B5
  · exact ((((((fr1.trans (OFr.setVar σ1 "gp" _)).trans (OFr.setVar σ2 "cnt" _)).trans fr4).trans
      fr5)).mono (by decide))

theorem else_cost (a b x5 : ℕ) (h1 : b ≤ a) (h3 : a + 8 ≤ x5) :
    2 + (4 + (20 * a + 600 + (20 * b + 300))) ≤ 120 * x5 + 2000 := by
  omega

/-- **Asking for the canonical form of the extensions.** -/
theorem advElse_run {W M : ℕ} {σ : Env} {g : Fr} {Sr : List Fr} {j h : ℕ} {tA : Node (h + 1) g.l1}
    {tB : Node (h + 1) g.l2} (H : AdvIn W M σ g Sr j h tA tB) (hi : ¬ g.i < nA g + nB g) :
    ∃ σ' ob K, Run (W + 1) (seqs [asg "gp" (N 5), asg "cnt" (.add (V "cnt") (N 7)), emHd, emFr, emRest,
        patchL, emCaHd, emEXc, emCaEnd]) σ σ' K ∧
      Built j (advance g Sr) ob σ' ∧ ob.length ≤ 64 * M ∧ K ≤ 120 * ob.length + 2000 ∧
      (toWord tA).length + (toWord tB).length ≤ ob.length ∧ OFr σ σ' advVars := by
  have hC := H.hC
  have hR := hC.room
  have hm := hC.m16
  have hrl := H.hrest.1
  have hrM := H.hrest.2.1
  have hcl : (stWords Sr).length ≤ (frames (stWords Sr)).length := by
    rw [frames, List.length_flatten, List.map_map]
    calc (stWords Sr).length = ((stWords Sr).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum (fun u _ => by simp)
  set σ2 := σ.setVar "gp" 5 with h2
  set σ3 := σ2.setVar "cnt" ((stWords Sr).length + 7) with h3
  have r2 : Run (W + 1) (asg "gp" (N 5)) σ σ2 2 := (Run.assign (by simp; omega)).mono (by simp)
  have r3 : Run (W + 1) (asg "cnt" (.add (V "cnt") (N 7))) σ2 σ3 4 :=
    (Run.assign (by simp [h2, H.hcnt]; omega)).mono (by simp)
  have hC3 : Ctx W M σ3 := (hC.setVar (by decide) _).setVar (by decide) _
  have hF3 : Filled "OB" "po" [] σ3 := (H.hF.setVar (by decide) _).setVar (by decide) _
  have hg3 : SlotIs M σ3 { g with ph := 5 } := (H.hg.set_ph (by omega)).setVar (by decide) _
  have hrest3 : SegIs M σ3 "rS" "rL" (frames (stWords Sr)) :=
    (H.hrest.setVar (by decide) (by decide) _).setVar (by decide) (by decide) _
  have hj3 : σ3.vars "j1" = j := by simp [h3, h2, H.hj1]
  obtain ⟨σ4, r4, F4, hl4, fr4⟩ := stateOne_run hC3 hF3 hg3 hrest3 (by simp [h3]; omega) hj3 H.hjM
  have hC4 := hC3.ofr fr4 (by decide)
  obtain ⟨σ5, ob, r5, B5, hob, hob', hEX, fr5⟩ := caEX_run hC4 F4 (by omega) (hg3.EX.ofr fr4 (by decide))
  have hrun := Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_append (l1 := [emHd, emFr, emRest, patchL]) (by simp) (by simp) r4 r5))
  have e1 := length_hdS j ({ g with ph := 5 } :: Sr)
  have hle := frames_le_hd0_one j { g with ph := 5 } Sr
  have hfg := len_frWords { g with ph := 5 }
  have hb : (toWord g.EX).length ≤ (hd0 j ({ g with ph := 5 } :: Sr)).length := by
    simp only at hfg; omega
  have hob8 : (hd0 j ({ g with ph := 5 } :: Sr)).length + 8 ≤ ob.length := by omega
  have hab : (toWord tA).length + (toWord tB).length ≤ ob.length := by
    rw [← H.hA, ← H.hB]; simp only at hfg; omega
  refine ⟨σ5, ob, 120 * ob.length + 2000, hrun.mono (else_cost _ _ _ hb hob8), ?_, by omega, le_rfl,
    hab, ?_⟩
  · rw [advance_ge g Sr hi]; exact B5
  · exact (((((OFr.setVar σ "gp" _).trans (OFr.setVar σ2 "cnt" _)).trans fr4).trans fr5)).mono
      (by decide)

theorem adv_cost (a b x5 K c : ℕ) (h1 : a + b ≤ x5) (hK : K ≤ 120 * x5 + 2000) (hc : c ≤ 10) :
    40 * a + 80 + (2 + (40 * b + 80 + (2 + (1 + c + K)))) ≤ 300 * x5 + 5000 := by
  omega

theorem length_toWord_node_succ {h l : ℕ} (t : Node (h + 1) l) :
    (toWord t).length = (toWord (Node.atoms t).words).length + (toWord (Node.exts t).words).length := by
  rw [toWord_node_succ, List.length_append]

/-- **Advancing a frame.** -/
theorem advCmd_run {W M : ℕ} {σ : Env} {g : Fr} {Sr : List Fr} {j h : ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" [] σ) (hg : SlotIs M σ g)
    (hrest : SegIs M σ "rS" "rL" (frames (stWords Sr))) (hcnt : σ.vars "cnt" = (stWords Sr).length)
    (hj1 : σ.vars "j1" = j) (hjM : j < M)
    (hdh : g.d = h + 1) (tA : Node (h + 1) g.l1) (tB : Node (h + 1) g.l2)
    (hA : g.A = toWord tA) (hB : g.B = toWord tB)
    (hSB : g.i < nA g → NW h g.l2 g.SB) (hSA : nA g ≤ g.i → g.i < nA g + nB g → NW h g.l1 g.SA)
    (hnum : g.kk + g.l1 + g.l2 + 2 < M) :
    ∃ σ' ob K, Run (W + 1) advCmd σ σ' K ∧ Built j (advance g Sr) ob σ' ∧ ob.length ≤ 64 * M ∧
      K ≤ 300 * ob.length + 5000 ∧ Keep σ σ' := by
  have hR := hC.room
  have hgA := hg.A
  have hgB := hg.B
  have hxA : (σ.arrs "x").drop (σ.vars "gAs") = toWord tA ++ (σ.arrs "x").drop (σ.vars "gAs" + g.A.length) := by
    rw [hgA.drop_eq, hA]
  have hxB : (σ.arrs "x").drop (σ.vars "gBs") = toWord tB ++ (σ.arrs "x").drop (σ.vars "gBs" + g.B.length) := by
    rw [hgB.drop_eq, hB]
  have hAM : σ.vars "gAs" + (toWord tA).length ≤ M := by rw [← hA]; exact hgA.2.1
  have hBM : σ.vars "gBs" + (toWord tB).length ≤ M := by rw [← hB]; exact hgB.2.1
  have hlA := length_toWord_node_succ tA
  have hlB := length_toWord_node_succ tB
  obtain ⟨σ1, r1, hy1, hn1, hd1, fr1⟩ := extsAt_run (s := "gAs") (cnt := "nA") (by decide) hC tA hxA hAM
  set σ2 := σ1.setVar "yA" (σ1.vars "y") with h2
  have r2 : Run (W + 1) (asg "yA" (V "y")) σ1 σ2 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  have hC2 : Ctx W M σ2 := (hC.ofr fr1 (by decide)).setVar (by decide) _
  have hx2 : σ2.arrs "x" = σ.arrs "x" := by rw [h2]; simp [fr1.arrs "x" (by decide)]
  have hgBs2 : σ2.vars "gBs" = σ.vars "gBs" := by rw [h2]; simp [fr1.vars "gBs" (by decide)]
  obtain ⟨σ3, r3, hy3, hn3, hd3, fr3⟩ := extsAt_run (s := "gBs") (cnt := "nB") (by decide) hC2 tB
    (by rw [hx2, hgBs2]; exact hxB) (by rw [hgBs2]; exact hBM)
  set σ4 := σ3.setVar "yB" (σ3.vars "y") with h4
  have r4 : Run (W + 1) (asg "yB" (V "y")) σ3 σ4 2 :=
    (Run.assign (by simp; rw [hy3, hgBs2]; omega)).mono (by simp)
  have fr14 : OFr σ σ4 (["y", "sn", "sk", "nA"] ++ ["yA"] ++ ["y", "sn", "sk", "nB"] ++ ["yB"]) :=
    ((fr1.trans (OFr.setVar σ1 "yA" _)).trans fr3).trans (OFr.setVar σ3 "yB" _)
  have hx4 : σ4.arrs "x" = σ.arrs "x" := fr14.arrs "x" (by decide)
  have hv4 : ∀ z, z ∉ ["y", "sn", "sk", "nA", "yA", "nB", "yB"] → σ4.vars z = σ.vars z :=
    fun z hz => fr14.vars z (by simp at hz ⊢; tauto)
  have hnA4 : σ4.vars "nA" = nA g := by
    rw [h4]; simp [fr3.vars "nA" (by decide), h2, hn1, nA, hA, extsOf_node]
  have hnB4 : σ4.vars "nB" = nB g := by rw [h4]; simp [hn3, nB, hB, extsOf_node]
  have hyA4 : σ4.vars "yA" = σ.vars "gAs" + (toWord (Node.atoms tA).words).length := by
    rw [h4]; simp [fr3.vars "yA" (by decide), h2, hy1]
  have hyB4 : σ4.vars "yB" = σ.vars "gBs" + (toWord (Node.atoms tB).words).length := by
    rw [h4]; simp [hy3, hgBs2]
  have H : AdvIn W M σ4 g Sr j h tA tB := by
    refine ⟨hC2.ofr ((fr3.trans (OFr.setVar σ3 "yB" _))) (by decide), filled_nil_ofr hF fr14 (by decide),
      hg.ofr fr14 (by decide), hrest.ofr fr14 (by decide) (by decide), by rw [hv4 _ (by decide), hcnt],
      by rw [hv4 _ (by decide), hj1], hjM, hdh, hA, hB, hnA4, hnB4, ?_, ?_, ?_, ?_, hSB, hSA, hnum⟩
    · rw [hx4, hyA4, hv4 _ (by decide)]
      have := hd1; rw [hy1] at this; exact this
    · rw [hyA4]; omega
    · rw [hx4, hyB4, hv4 _ (by decide)]
      have := hd3; rw [hy3, hx2, hgBs2] at this; exact this
    · rw [hyB4]; omega
  have hgi4 : σ4.vars "gi" = g.i := H.hg.i
  have hnum' := hg.nums
  have hcnd : (Cond.lt (V "gi") (.add (V "nA") (V "nB"))).evalB (W + 1) σ4 =
      some (decide (g.i < nA g + nB g)) := by
    have hcA := count_lt_toWord (Node.exts tA).words
    have hcB := count_lt_toWord (Node.exts tB).words
    have hnAe : nA g = (Node.exts tA).words.length := by simp only [nA, hA, extsOf_node]
    have hnBe : nB g = (Node.exts tB).words.length := by simp only [nB, hB, extsOf_node]
    rw [evalB_condLt (evalB_var (by rw [hgi4]; omega))
      (evalB_bin (evalB_var (by rw [hnA4]; omega)) (evalB_var (by rw [hnB4]; omega)) (by
        simp only [Bop.apply_add]; rw [hnA4, hnB4]; omega)), hgi4, hnA4, hnB4]
    rfl
  by_cases hi : g.i < nA g + nB g
  · obtain ⟨σ', ob, K, r5, B, hob, hK, hab, fr5⟩ := advPush_run H hi
    have r : Run (W + 1) advCmd σ σ' _ := Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2
      (Run.seqs_cons (by simp) r3 (Run.seqs_cons (by simp) r4
        (Run.seqs_one (Run.ite_true (by rw [hcnd]; simp [hi]) r5)))))
    refine ⟨σ', ob, _, r.mono (adv_cost _ _ _ _ _ hab hK (by simp [Cond.size, Expr.size])), B, hob, le_rfl, ?_⟩
    exact keep_of_ofr (fr14.trans fr5) (by decide) (by decide) (by decide)
  · obtain ⟨σ', ob, K, r5, B, hob, hK, hab, fr5⟩ := advElse_run H hi
    have r : Run (W + 1) advCmd σ σ' _ := Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2
      (Run.seqs_cons (by simp) r3 (Run.seqs_cons (by simp) r4
        (Run.seqs_one (Run.ite_false (by rw [hcnd]; simp [hi]) r5)))))
    refine ⟨σ', ob, _, r.mono (adv_cost _ _ _ _ _ hab hK (by simp [Cond.size, Expr.size])), B, hob, le_rfl, ?_⟩
    exact keep_of_ofr (fr14.trans fr5) (by decide) (by decide) (by decide)

end Lax185574Proofs.CompRam
