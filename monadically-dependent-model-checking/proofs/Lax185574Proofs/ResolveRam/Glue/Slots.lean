import Lax185574Proofs.ResolveRam.Glue.Query

/-!
The slots of the query in a later round of the glue program of
lem:resolve-lift.

`cpPart ix d` appends word `ix` of the library without its first `d`
entries (`cpPart_run`). The real query of the rank shift is the tree
word of an item (its word without the parent and the guard), that of a
composition the answer of the rank shift followed by a word of the
filtered far tree, and that of the far tree the tree word followed by the
word of the entries of the scatter type whose first rank is large enough
(`filterCp` with the test `cutT`, `cutT_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- Append word `ix` of the library without its first `d` entries. -/
def cpPart (ix : String) (d : ℕ) : Com :=
  .seq (.assign "wa" (.add (.get "st" (.var ix)) (.lit d)))
    (.seq (.assign "wl" (.sub (.get "ln" (.var ix)) (.lit d))) (cpSeg "a" "wa" "wl"))

/-- **Copying part of a word.** -/
theorem cpPart_run {W : ℕ} {ix : String} {d : ℕ} {ws : List (List ℕ)} {i : ℕ} {σ : Env} {pre : List ℕ}
    (hw : WordsAt ws σ) (hi : σ.vars ix = i) (hil : i < ws.length) (hx : ix ≠ "wa") (hd : d ≤ ws[i].length)
    (hF : Filled "OB" "po" pre σ) (hcap : (σ.arrs "OB").length = W + 1)
    (hB : total ws + ws.length + d + 1 ≤ W) (hP : pre.length + (ws[i].length - d) ≤ W)
    (hv : ∀ v ∈ ws[i], v ≤ W) (ha : total ws ≤ (σ.arrs "a").length) :
    ∃ σ', Run (W + 1) (cpPart ix d) σ σ' ((ws[i].length - d) * 20 + 20) ∧
      Filled "OB" "po" (pre ++ ws[i].drop d) σ' ∧ OFr σ σ' ["wa", "wl", "ci", "po"] := by
  have hoi := off_add_le hil
  have hoff : off ws i + ws[i].length ≤ total ws := hoi
  obtain ⟨σ1, r1, o1⟩ := asg_run (x := "wa") (B := W + 1) (σ := σ)
    (ev_add (evalB_get (ev_var hi (by omega)) (hw.st i hil) (by omega))
      (evalB_lit (n := d) (by omega)) (by omega))
  obtain ⟨σ2, r2, o2⟩ := asg_run (x := "wl") (B := W + 1) (σ := σ1)
    (ev_sub (evalB_get (ev_var (by rw [o1.vars _ hx, hi]) (by omega)) (by rw [o1.arrs]; exact hw.ln i hil)
      (by omega)) (evalB_lit (n := d) (by omega)) (by omega))
  have hF2 : Filled "OB" "po" pre σ2 :=
    hF.congr (by rw [o2.vars "po" (by decide), o1.vars "po" (by decide)]) (by rw [o2.arrs, o1.arrs])
  have ha2 : σ2.arrs "a" = σ.arrs "a" := by rw [o2.arrs, o1.arrs]
  -- the segment is the word without its first d entries
  have hseg : seg (σ2.arrs "a") (off ws i + d) (ws[i].length - d) = ws[i].drop d := by
    rw [ha2]
    apply List.ext_getElem?
    intro j
    simp only [seg, List.getElem?_take, List.getElem?_drop]
    split_ifs with hj
    · rw [show off ws i + d + j = off ws i + (d + j) by omega, hw.a i hil (d + j) (by omega),
        List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_eq_none (by omega)]
  obtain ⟨σ3, r3, F3, O3⟩ := cpSeg_ofr (W := W) (src := "a") (s := "wa") (l := "wl") (σ := σ2)
    (a := off ws i + d) (N := ws[i].length - d) (by decide)
    (by rw [o2.vars "wa" (by decide), o1.self]) o2.self (by decide) (by decide) (by decide) (by decide) hF2
    (by rw [ha2]; omega) (by rw [o2.arrs, o1.arrs, hcap]; omega) (by omega) (by omega)
    (by rw [hseg]; intro v hv'; exact hv v (List.mem_of_mem_drop hv'))
  rw [hseg] at F3
  refine ⟨σ3, ?_, F3, ?_⟩
  · unfold cpPart
    exact (Run.seq r1 (Run.seq r2 r3)).mono (by simp [Expr.size]; omega)
  · have e1 : OFr σ σ2 ["wa", "wl"] := ⟨fun y hy => by
        simp at hy; rw [o2.vars y hy.2, o1.vars y hy.1], fun b _ => by rw [o2.arrs, o1.arrs],
        by rw [o2.arrs, o1.arrs], by rw [o2.out, o1.out], by rw [o2.inp, o1.inp]⟩
    exact (e1.trans O3).mono (by decide)

/-- The test `cutSel m` on word `ow`, with `m` in `ck`. -/
def cutT : Com :=
  .seq (.assign "fb" (.lit 0)) (.ite (.lt (.lit 1) (.get "ln" (.var "ow")))
    (.ite (.lt (.get "a" (.add (.get "st" (.var "ow")) (.lit 1))) (.var "ck")) .skip (.assign "fb" (.lit 1)))
    .skip)

/-- **The test of the far tree query.** -/
theorem cutT_ok {W m : ℕ} {ws : List (List ℕ)} (hm : 1 ≤ m) (hmW : m ≤ W)
    (hB : total ws + ws.length + 2 ≤ W) (hv : ∀ w ∈ ws, ∀ v ∈ w, v ≤ W) :
    TestOK W cutT ws (cutSel m) ["fb"] (fun τ => τ.vars "ck" = m) 20 := by
  intro τ i hi hw hck how
  have hoi := off_add_le hi
  have hoff : off ws i + ws[i].length ≤ total ws := hoi
  obtain ⟨τ1, r1, o1⟩ := asg_run (x := "fb") (B := W + 1) (σ := τ) (evalB_lit (n := 0) (by omega))
  have hln : (Expr.get "ln" (.var "ow")).evalB (W + 1) τ1 = some ws[i].length :=
    evalB_get (ev_var (by rw [o1.vars "ow" (by decide), how]) (by omega)) (by rw [o1.arrs]; exact hw.ln i hi)
      (by omega)
  have hc1 := evalB_condLt (evalB_lit (B := W + 1) (σ := τ1) (n := 1) (by omega)) hln
  have hframe : ∀ τ', Only "fb" (if cutSel m ws[i] then 1 else 0) τ τ' →
      (τ'.vars "fb" = (if cutSel m ws[i] then 1 else 0) ∧ (∀ y, y ∉ ["fb"] → τ'.vars y = τ.vars y) ∧
        τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp) := fun τ' o =>
    ⟨o.self, fun y hy => o.vars y (by simpa using hy), o.arrs, o.out, o.inp⟩
  by_cases h1 : 1 < ws[i].length
  · have ha : (Expr.get "a" (.add (.get "st" (.var "ow")) (.lit 1))).evalB (W + 1) τ1 = some ws[i][1] :=
      evalB_get (ev_add (evalB_get (ev_var (by rw [o1.vars "ow" (by decide), how]) (by omega))
        (by rw [o1.arrs]; exact hw.st i hi) (by omega)) (evalB_lit (by omega)) (by omega))
        (by rw [o1.arrs]; exact hw.a i hi 1 h1) (by have := hv _ (List.getElem_mem hi) _ (List.getElem_mem h1); omega)
    have hc2 := evalB_condLt ha (ev_var (B := W + 1) (σ := τ1) (by rw [o1.vars "ck" (by decide), hck]) (by omega))
    have hsel : cutSel m ws[i] = decide (m ≤ ws[i][1]) := by
      simp [cutSel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    by_cases h2 : ws[i][1] < m
    · refine ⟨τ1, (Run.seq r1 (Run.ite_true (by rw [hc1]; simp [h1]) (Run.ite_true (by rw [hc2]; simp [h2])
        Run.skip))).mono (by simp [Expr.size, Cond.size]), (hframe τ1 ?_)⟩
      rw [hsel, show decide (m ≤ ws[i][1]) = false by simp; omega]; exact o1
    · obtain ⟨τ2, r2, o2⟩ := asg_run (x := "fb") (B := W + 1) (σ := τ1) (evalB_lit (n := 1) (by omega))
      refine ⟨τ2, (Run.seq r1 (Run.ite_true (by rw [hc1]; simp [h1]) (Run.ite_false (by rw [hc2]; simp [h2])
        r2))).mono (by simp [Expr.size, Cond.size]), (hframe τ2 ?_)⟩
      rw [hsel, show decide (m ≤ ws[i][1]) = true by simp; omega]
      exact ⟨o2.self, fun y hy => by rw [o2.vars y hy, o1.vars y hy], by rw [o2.arrs, o1.arrs],
        by rw [o2.out, o1.out], by rw [o2.inp, o1.inp]⟩
  · refine ⟨τ1, (Run.seq r1 (Run.ite_false (by rw [hc1]; simp [h1]) Run.skip)).mono
      (by simp [Expr.size, Cond.size]), (hframe τ1 ?_)⟩
    have : cutSel m ws[i] = false := by
      simp only [cutSel, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ws[i].length ≤ 1 by omega)]
      simp; omega
    rw [this]; exact o1

/-- The library in the query phase. -/
structure LibOK (W : ℕ) (L : List (List ℕ)) (σ : Env) : Prop where
  at_ : WordsAt L σ
  arr : ArrW W σ
  w : σ.vars "W" = W

theorem LibOK.ofr {W : ℕ} {L : List (List ℕ)} {σ σ' : Env} {xs : List String} (h : LibOK W L σ)
    (o : OFr σ σ' xs) (hW : "W" ∉ xs) : LibOK W L σ' :=
  ⟨h.at_.of_arrs (o.arrs _ (by decide)) (o.arrs _ (by decide)) (o.arrs _ (by decide)),
    fun b => by
      by_cases hb : b = "OB"
      · subst hb; rw [o.len]; exact h.arr _
      · rw [o.arrs b hb]; exact h.arr b, by rw [o.vars _ hW, h.w]⟩

/-- The library is small. -/
def LibSmall (W : ℕ) (L : List (List ℕ)) : Prop :=
  total L + L.length + 8 ≤ W ∧ ∀ w ∈ L, ∀ v ∈ w, v ≤ W

/-- The slot of the rank shift. -/
def slotA : Com := cpPart "ox" 2

/-- **The slot of the rank shift.** -/
theorem slotA_ok {W Xm : ℕ} {L : List (List ℕ)} {iw : ℕ} {B : Env → Prop} (hiw : iw < L.length)
    (h2 : 2 ≤ L[iw].length) (hs : LibSmall W L)
    (hB : ∀ σ σ', B σ → OFr σ σ' ["wa", "wl", "ci", "po"] → B σ') :
    SlotRun W (total L + L.length + 8) Xm slotA (L[iw].drop 2)
      (fun σ => B σ ∧ LibOK W L σ ∧ σ.vars "ox" = iw) B (L[iw].length * 20 + 20) := by
  rintro σ X ⟨hBσ, hl, hox⟩ hF hc hX -
  obtain ⟨σ', r, F, O⟩ := cpPart_run (W := W) (d := 2) hl.at_ hox hiw (by decide) h2 hF hc
    (by have := hs.1; omega) (by simp at hX; omega) (hs.2 _ (List.getElem_mem hiw))
    (by rw [hl.arr]; omega)
  exact ⟨σ', r.mono (by omega), F, hB σ σ' hBσ O, fun y hy => O.vars y (by revert hy; revert y; decide),
    O.len, O.out⟩

/-- The slot of a composition. -/
def slotC : Com := .seq (cpPart "os" 0) (cpPart "of" 0)

/-- **The slot of a composition.** -/
theorem slotC_ok {W Xm : ℕ} {L : List (List ℕ)} {is jf : ℕ} {B : Env → Prop} (his : is < L.length)
    (hjf : jf < L.length) (hs : LibSmall W L)
    (hB : ∀ σ σ', B σ → OFr σ σ' ["wa", "wl", "ci", "po"] → B σ') :
    SlotRun W (total L + L.length + 8) Xm slotC (L[is] ++ L[jf])
      (fun σ => B σ ∧ LibOK W L σ ∧ σ.vars "os" = is ∧ σ.vars "of" = jf) B
      (L[is].length * 20 + L[jf].length * 20 + 40) := by
  rintro σ X ⟨hBσ, hl, hos, hof⟩ hF hc hX -
  simp only [List.length_append] at hX
  obtain ⟨σ1, r1, F1, O1⟩ := cpPart_run (W := W) (d := 0) hl.at_ hos his (by decide) (by omega) hF hc
    (by have := hs.1; omega) (by omega) (hs.2 _ (List.getElem_mem his)) (by rw [hl.arr]; omega)
  have hl1 := hl.ofr O1 (by decide)
  obtain ⟨σ2, r2, F2, O2⟩ := cpPart_run (W := W) (d := 0) hl1.at_
    (by rw [O1.vars "of" (by decide), hof]) hjf (by decide) (by omega) F1 (by rw [O1.len, hc])
    (by have := hs.1; omega) (by simp; omega) (hs.2 _ (List.getElem_mem hjf)) (by rw [hl1.arr]; omega)
  simp only [List.drop_zero, List.append_assoc] at F2
  refine ⟨σ2, ?_, F2, hB σ1 σ2 (hB σ σ1 hBσ O1) O2, fun y hy => ?_, by rw [O2.len, O1.len], by rw [O2.out, O1.out]⟩
  · unfold slotC; exact (Run.seq r1 r2).mono (by simp; omega)
  · rw [O2.vars y (by revert hy; revert y; decide), O1.vars y (by revert hy; revert y; decide)]

/-- The slot of the far tree. -/
def slotB : Com := .seq (cpPart "ox" 2) (filterCp cutT)

/-- **The slot of the far tree.** -/
theorem slotB_ok {W Xm : ℕ} {L : List (List ℕ)} {iw lo N m : ℕ} {B : Env → Prop} (hiw : iw < L.length)
    (h2 : 2 ≤ L[iw].length) (hr : lo + N ≤ L.length) (hm : 1 ≤ m) (hmW : m ≤ W) (hs : LibSmall W L)
    (hB : ∀ σ σ', B σ → OFr σ σ' (["wa", "wl", "ci", "po"] ++ (["fb"] ++ fV)) → B σ') :
    SlotRun W (total L + L.length + 8) Xm slotB (L[iw].drop 2 ++ toWord (selW L lo N (cutSel m)))
      (fun σ => B σ ∧ LibOK W L σ ∧ σ.vars "ox" = iw ∧ σ.vars "flo" = lo ∧ σ.vars "fN" = N ∧
        σ.vars "ck" = m) B
      (L[iw].length * 20 + 20 + (N * (20 + 50) + 20 * total ((L.drop lo).take N) + 50)) := by
  rintro σ X ⟨hBσ, hl, hox, hlo, hN, hck⟩ hF hc hX -
  simp only [List.length_append, List.length_drop] at hX
  obtain ⟨σ1, r1, F1, O1⟩ := cpPart_run (W := W) (d := 2) hl.at_ hox hiw (by decide) h2 hF hc
    (by have := hs.1; omega) (by omega) (hs.2 _ (List.getElem_mem hiw)) (by rw [hl.arr]; omega)
  have hl1 := hl.ofr O1 (by decide)
  obtain ⟨σ2, r2, F2, w2, c2, O2⟩ := filterCp_run (W := W) (lo := lo) (N := N) (test := cutT) (ws := L)
    (p := cutSel m) (tv := ["fb"]) (C := fun τ => τ.vars "ck" = m) (σ := σ1)
    (by decide) (fun τ τ' h o => by rw [o.vars "ck" (by decide), h])
    (cutT_ok hm hmW (by have := hs.1; omega) hs.2) hl1.at_ (by rw [O1.vars "ck" (by decide), hck])
    (by rw [O1.vars "flo" (by decide), hlo]) (by rw [O1.vars "fN" (by decide), hN]) hr F1
    (by rw [O1.len, hc]; simp only [List.length_append, List.length_drop]; have := hs.1; omega)
    (by simp only [List.length_append, List.length_drop]; have := hs.1; omega) hs.2 (by rw [hl1.arr]; omega) hl1.w
  rw [List.append_assoc] at F2
  refine ⟨σ2, ?_, F2, hB σ σ2 hBσ ((O1.trans O2).mono (fun y hy => hy)), fun y hy => ?_,
    by rw [O2.len, O1.len], by rw [O2.out, O1.out]⟩
  · unfold slotB; exact (Run.seq r1 r2).mono (by omega)
  · rw [O2.vars y (by revert hy; revert y; decide), O1.vars y (by revert hy; revert y; decide)]

open Lax185574.TypeTrees Lax185574Proofs.TreeAlgo in
/-- **The slot of the atom words, from the piece.** -/
theorem slotAt_ok {cmd : Com} {tv : List String} (hspec : AtSpec cmd tv) (hq : ∀ y ∈ qN, y ∉ tv) :
    ∃ cP aP : ℕ, ∀ {W S Xm : ℕ} {L : List (List ℕ)} {oc ow P Q sg p g : ℕ} {σt : TypeTree}
      {B : Env → Prop} (hoc : oc < L.length) (how : ow < L.length),
      P ≤ W → Q ≤ W → sg ≤ 1 → IsCT L[oc] → L[ow] = itemW ((p, g), σt) →
      Room W (Lax3.DistFO.rhoPlus σt.k σt.q) (ySz (toWord L) + Xm + σt.ℓ) →
      (∀ σ σ', B σ → PFr tv σ σ' → B σ') →
      SlotRun W S Xm cmd (toWord ((candW σt.k σt.q σt.ℓ (ctCols L[oc])).filter
          (newAtomW (dwOf P Q sg L[oc]) (listWords (toWord σt) 3))))
        (fun σ => B σ ∧ LibOK W L σ ∧ σ.vars "oc" = oc ∧ σ.vars "ow" = ow ∧ σ.vars "gP" = P ∧
          σ.vars "gQ" = Q ∧ σ.vars "gS" = sg) B
        (cP * (L[oc].length + 1) * (L[ow].length + σt.ℓ + Lax3.DistFO.rhoPlus σt.k σt.q + 1) ^ aP) := by
  obtain ⟨cP, aP, h⟩ := hspec
  refine ⟨cP, aP, fun {W S Xm L oc ow P Q sg p g σt B} hoc how hP hQ hsg hct hiw hroom hB => ?_⟩
  rintro σ X ⟨hBσ, hl, hoc', how', hP', hQ', hS'⟩ hF hc hX hXm
  obtain ⟨σ', r, F, fr⟩ := h W σ L X oc ow P Q sg p g σt hoc how hl.w hl.arr hl.at_ hoc' how' hP' hQ' hP hQ
    hS' hsg hct hiw hF (by unfold Room at hroom ⊢; exact le_trans (by gcongr) hroom)
  exact ⟨σ', r, F, hB σ σ' hBσ fr, fun y hy => fr.vars y (hq y hy), fr.len "OB", fr.out⟩

open Lax185574.TypeTrees Lax185574Proofs.TreeAlgo in
/-- **The slot of the children words, from the piece.** -/
theorem slotKid_ok {cmd : Com} {tv : List String} (hspec : KidSpec cmd tv) (hq : ∀ y ∈ qN, y ∉ tv) :
    ∃ cP aP : ℕ, ∀ {W S Xm : ℕ} {L : List (List ℕ)} {ow kl kn ol i p g k q ℓ : ℕ} {t : Node (q + 1) ℓ}
      {B : Env → Prop} (how : ow < L.length),
      kl + kn ≤ L.length → ol + kn ≤ L.length → L[ow] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩) →
      Room W 0 (ySz (toWord L) + i + Xm) → (∀ σ σ', B σ → PFr tv σ σ' → B σ') →
      SlotRun W S Xm cmd (toWord (kidW q ℓ i
          (((L.drop kl).take kn).map fun w => (w.getD 0 0, w.getD 1 0)) ((L.drop ol).take kn)))
        (fun σ => B σ ∧ LibOK W L σ ∧ σ.vars "ow" = ow ∧ σ.vars "ii" = i ∧ σ.vars "kl" = kl ∧
          σ.vars "kn" = kn ∧ σ.vars "ol" = ol) B
        (cP * (kn + total ((L.drop kl).take kn) + total ((L.drop ol).take kn) + 1) *
          (L[ow].length + 1) ^ aP) := by
  obtain ⟨cP, aP, h⟩ := hspec
  refine ⟨cP, aP, fun {W S Xm L ow kl kn ol i p g k q ℓ t B} how hk ho hiw hroom hB => ?_⟩
  rintro σ X ⟨hBσ, hl, how', hi', hkl, hkn, hol⟩ hF hc hX hXm
  obtain ⟨σ', r, F, fr⟩ := h W σ L X ow kl kn ol i p g k q ℓ t how hl.w hl.arr hl.at_ how' hi' hkl hkn hol
    hk ho hiw hF (by unfold Room at hroom ⊢; exact le_trans (by gcongr) hroom)
  exact ⟨σ', r, F, hB σ σ' hBσ fr, fun y hy => fr.vars y (hq y hy), fr.len "OB", fr.out⟩

/-- **A slot that copies part of a library word.** -/
theorem slotP_ok {W Xm : ℕ} {ix : String} {d : ℕ} {L : List (List ℕ)} {iw : ℕ} {B : Env → Prop}
    (hx : ix ≠ "wa") (hxq : ix ∉ ["wa", "wl", "ci", "po"]) (hiw : iw < L.length) (h2 : d ≤ L[iw].length)
    (hd : d ≤ 2) (hs : LibSmall W L)
    (hB : ∀ σ σ', B σ → OFr σ σ' ["wa", "wl", "ci", "po"] → B σ') :
    SlotRun W (total L + L.length + 8) Xm (cpPart ix d) (L[iw].drop d)
      (fun σ => B σ ∧ LibOK W L σ ∧ σ.vars ix = iw) B (L[iw].length * 20 + 20) := by
  rintro σ X ⟨hBσ, hl, hox⟩ hF hc hX -
  obtain ⟨σ', r, F, O⟩ := cpPart_run (W := W) (d := d) hl.at_ hox hiw hx h2 hF hc
    (by have := hs.1; omega) (by simp at hX; omega) (hs.2 _ (List.getElem_mem hiw))
    (by rw [hl.arr]; omega)
  exact ⟨σ', r.mono (by omega), F, hB σ σ' hBσ O, fun y hy => O.vars y (by revert hy; revert y; decide),
    O.len, O.out⟩

theorem SlotRun.pre {W S Xm K : ℕ} {c : Com} {w : List ℕ} {P Q P' : Env → Prop}
    (h : SlotRun W S Xm c w Q P' K) (hPQ : ∀ σ, P σ → Q σ) : SlotRun W S Xm c w P P' K :=
  fun σ X hP => h σ X (hPQ σ hP)

theorem SlotRun.post {W S Xm K : ℕ} {c : Com} {w : List ℕ} {P Q P' : Env → Prop}
    (h : SlotRun W S Xm c w P Q K) (hQP : ∀ σ, Q σ → P' σ) : SlotRun W S Xm c w P P' K := by
  intro σ X hP hF hc hX hXm
  obtain ⟨σ', r, F, H, q, l, u⟩ := h σ X hP hF hc hX hXm
  exact ⟨σ', r, F, hQP σ' H, q, l, u⟩

/-- **A slot chosen by the kind of the call.** -/
theorem slot_ite {W S Xm K K' j : ℕ} {c c' : Com} {w w' : List ℕ} {P P' : Env → Prop}
    (h1 : SlotRun W S Xm c w (fun σ => P σ ∧ σ.vars "qk" = j) P' K)
    (h2 : SlotRun W S Xm c' w' (fun σ => P σ ∧ σ.vars "qk" ≠ j) P' K')
    (hk : ∀ σ, P σ → σ.vars "qk" ≤ W) (b : Bool) (hb : ∀ σ, P σ → (σ.vars "qk" = j ↔ b = true))
    (hj : j ≤ W) :
    SlotRun W S Xm (.ite (.eq (.var "qk") (.lit j)) c c') (if b then w else w') P P' (K + K' + 5) := by
  intro σ X hP hF hc hX hXm
  have he := evalB_condEq (B := W + 1) (σ := σ) (e := .var "qk") (f := .lit j)
    (ev_var rfl (by have := hk σ hP; omega)) (evalB_lit (by omega))
  cases b with
  | true =>
    have hq : σ.vars "qk" = j := (hb σ hP).2 rfl
    obtain ⟨σ', r, F, P1, q, l, u⟩ := h1 σ X ⟨hP, hq⟩ hF hc (by simpa using hX) hXm
    refine ⟨σ', (Run.ite_true (by rw [he]; simp [hq]) r).mono (by simp [Cond.size, Expr.size]; omega),
      by simpa using F, P1, q, l, u⟩
  | false =>
    have hne : σ.vars "qk" ≠ j := fun h => by simpa using (hb σ hP).1 h
    obtain ⟨σ', r, F, P1, q, l, u⟩ := h2 σ X ⟨hP, hne⟩ hF hc (by simpa using hX) hXm
    refine ⟨σ', (Run.ite_false (by rw [he]; simp [hne]) r).mono (by simp [Cond.size, Expr.size]; omega),
      by simpa using F, P1, q, l, u⟩

end Lax185574Proofs.ResolveRam.Glue
