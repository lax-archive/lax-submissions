import Lax185574Proofs.Chain.Ram.PdTests

/-!
The state of the predamping procedure, and the first phase of one
application of its rules.

`PdFix` collects what stays fixed during a run for one `A` and `κ`: the
scalars `n`, `M`, `tr` and the thresholds `t1`, `t2`, `t3`, the arrays
`adj`, `pos` and `inA`, and the lengths of all arrays. The phase
`prepCom` computes, for the current `S`, the membership `inB` of
`A ∪ S`, the labels `lab` of `tpRel G (A ∪ S) r`, the neighbor counts
and part sizes for these labels, and the representatives `rep`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- The scalars that stay fixed. -/
def fixVars : List String := ["n", "M", "tr", "t1", "t2", "t3"]

/-- The arrays that stay fixed. -/
def fixArrs : List String := ["adj", "pos", "inA"]

/-- What stays fixed during the procedure for one `A` and `κ`. -/
structure PdFix (n r : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (pf : ℕ → ℕ)
    (t1 t2 t3 : ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hM : τ.vars "M" = n + 4
  htr : τ.vars "tr" = r
  ht1 : τ.vars "t1" = t1
  ht2 : τ.vars "t2" = t2
  ht3 : τ.vars "t3" = t3
  hadj : Mat τ "adj" n (fun u v => ind (gA G u v))
  hpos : Vec τ "pos" n pf
  hinA : Vec τ "inA" n (fun u => ind (inBN A u))
  lvec : ∀ a ∈ ["inB", "inS", "Sl", "p2", "p3", "mark", "rep", "lab", "key", "lab2", "labk",
    "sz"], (τ.arrs a).length = n
  ltab : n * (n + 4) ≤ (τ.arrs "tab").length
  lcnt : (τ.arrs "cnt").length = n * n

variable {r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ} {t1 t2 t3 : ℕ}

theorem PdFix.setVar {τ : Env} (h : PdFix n r G A pf t1 t2 t3 τ) {x : String}
    (hx : x ∉ fixVars) (v : ℕ) : PdFix n r G A pf t1 t2 t3 (τ.setVar x v) := by
  simp only [fixVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  exact ⟨by simp [Ne.symm h1, h.hn], by simp [Ne.symm h2, h.hM], by simp [Ne.symm h3, h.htr],
    by simp [Ne.symm h4, h.ht1], by simp [Ne.symm h5, h.ht2], by simp [Ne.symm h6, h.ht3],
    h.hadj.of_eq rfl, h.hpos.of_eq rfl, h.hinA.of_eq rfl, fun a ha => by simpa using h.lvec a ha,
    by simpa using h.ltab, by simpa using h.lcnt⟩

theorem PdFix.setArr {τ : Env} (h : PdFix n r G A pf t1 t2 t3 τ) {a : String}
    (ha : a ∉ fixArrs) (i v : ℕ) : PdFix n r G A pf t1 t2 t3 (τ.setArr a i v) := by
  simp only [fixArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
  obtain ⟨h1, h2, h3⟩ := ha
  exact ⟨by simp [h.hn], by simp [h.hM], by simp [h.htr], by simp [h.ht1], by simp [h.ht2],
    by simp [h.ht3], h.hadj.of_eq (by simp [Ne.symm h1]), h.hpos.of_eq (by simp [Ne.symm h2]),
    h.hinA.of_eq (by simp [Ne.symm h3]), fun b hb => by
      rw [length_arrs_setArr]; exact h.lvec b hb,
    by rw [length_arrs_setArr]; exact h.ltab, by rw [length_arrs_setArr]; exact h.lcnt⟩

/-- The arrays `ks` are those of `σ`. -/
def Keep (σ : Env) (ks : List String) (τ : Env) : Prop := ∀ a ∈ ks, τ.arrs a = σ.arrs a

theorem Keep.setVar {σ τ : Env} {ks : List String} (h : Keep σ ks τ) (x : String) (v : ℕ) :
    Keep σ ks (τ.setVar x v) := h

theorem Keep.setArr {σ τ : Env} {ks : List String} (h : Keep σ ks τ) {a : String} (ha : a ∉ ks)
    (i v : ℕ) : Keep σ ks (τ.setArr a i v) := fun b hb => by
  have : b ≠ a := fun e => ha (e ▸ hb)
  simp only [arrs_setArr, if_neg this]; exact h b hb

theorem Keep.of_run {B K : ℕ} {c : Com} {σ τ τ' : Env} {ks : List String} (h : Keep σ ks τ)
    (hr : Run B c τ τ' K) (hks : ∀ a ∈ ks, a ∉ c.warrs) : Keep σ ks τ' := fun a ha => by
  rw [hr.frame_arr a (hks a ha)]; exact h a ha

/-- The base of the types phase, from the fixed state. -/
theorem tbase_of_fix {τ : Env} (h : PdFix n r G A pf t1 t2 t3 τ) {Bs : Finset (Fin n)}
    (hinB : Vec τ "inB" n (fun u => ind (inBN Bs u))) : TBase n r G Bs τ :=
  ⟨h.hn, h.hM, h.htr, h.hadj, hinB, h.lvec _ (by simp), h.lvec _ (by simp), h.lvec _ (by simp),
    h.lvec _ (by simp), h.ltab, h.lcnt, h.lvec _ (by simp)⟩

theorem inBN_union {S : Finset (Fin n)} {u : ℕ} : inBN (A ∪ S) u ↔ inBN A u ∨ inBN S u :=
  ⟨fun ⟨h, hm⟩ => (mem_union.1 hm).elim (fun h' => Or.inl ⟨h, h'⟩) (fun h' => Or.inr ⟨h, h'⟩),
    fun h => h.elim (fun ⟨h, hm⟩ => ⟨h, mem_union_left _ hm⟩)
      (fun ⟨h, hm⟩ => ⟨h, mem_union_right _ hm⟩)⟩

/-! ### The first phase -/

/-- The membership of `A ∪ S`. -/
def fillInB : Com := rowFill "inB" (.var "b") (.or (.get "inA" (.var "b")) (.get "inS" (.var "b")))

/-- Labels, counts and representatives for the current `S`. -/
def prepCom : Com :=
  .seq fillInB (.seq tpCom (.seq (rowFill "labk" (.var "b") (.get "lab" (.var "b")))
    (.seq cntPhase (.seq szPhase repCom))))

/-- The arrays the first phase writes. -/
def prepArrs : List String := ["inB", "lab", "key", "lab2", "tab", "labk", "cnt", "sz", "rep"]

/-- The cost of the first phase. -/
def prepCost (n r : ℕ) : ℕ := tpCost n r + n * (n * 200 + 200) + 200

theorem prepCom_run {B' : ℕ} (hB' : TpBound n B') (hrB : r < B') {S : Finset (Fin n)}
    (hpf : ∀ z < n, pf z < n) {σ : Env} (hF : PdFix n r G A pf t1 t2 t3 σ)
    (hS : Vec σ "inS" n (fun u => ind (inBN S u))) (hz : Zero σ "tab")
    (hcnt : Mat σ "cnt" n (fun _ _ => 0)) (hsz : Vec σ "sz" n (fun _ => 0)) :
    ∃ σ', Run B' prepCom σ σ' (prepCost n r) ∧ PdFix n r G A pf t1 t2 t3 σ' ∧
      (∀ a, a ∉ prepArrs → σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ∉ prepCom.wvars → σ'.vars x = σ.vars x) ∧
      Vec σ' "lab" n (lbl n (tpN G (A ∪ S) r)) ∧
      Mat σ' "cnt" n (fun u c => cntN G (lbl n (tpN G (A ∪ S) r)) u c) ∧
      Vec σ' "sz" n (fun c => szN n (lbl n (tpN G (A ∪ S) r)) c) ∧
      Vec σ' "rep" n (fun z => ind (isRepN n pf (lbl n (tpN G (A ∪ S) r)) z)) ∧
      Zero σ' "tab" := by
  unfold TpBound at hB'
  set L := lbl n (tpN G (A ∪ S) r) with hLdef
  have hLab : IsLabels n L := isLabels_lbl (tpN_isEqv r)
  -- membership of `A ∪ S`
  obtain ⟨σ1, hr1, ⟨hF1, hk1⟩, hl1, hg1⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := 8) (arr := "inB") (ie := .var "b")
      (e := .or (.get "inA" (.var "b")) (.get "inS" (.var "b")))
      (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ ∀ a, a ≠ "inB" → τ.arrs a = σ.arrs a)
      (fun u => ind (inBN (A ∪ S) u)) (by omega) (fun τ h => h.1.hn)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, fun a ha => by simpa using h.2 a ha⟩)
      (fun τ i x h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ k h hb hk => by simp [hb]; omega)
      (fun τ k h hb hk => by
        have e1 := h.1.hinA.evalB (B := B') hb hk (by omega)
          (by have := ind_le_one (inBN A k); omega)
        have e2 := (hS.of_eq (h.2 "inS" (by decide))).evalB (B := B') hb hk (by omega)
          (by have := ind_le_one (inBN S k); omega)
        have := evalB_or01 e1 e2 (by omega)
        rw [this]; congr 1; rw [ind_eq_iff, inBN_union])
      (by simp) ⟨hF, fun _ _ => rfl⟩ (by rw [hF.lvec "inB" (by simp)]; omega)
  have hB1 : Vec σ1 "inB" n (fun u => ind (inBN (A ∪ S) u)) :=
    ⟨by rw [hl1, hF.lvec "inB" (by simp)], fun u hu => by rw [hg1 u]; simp [hu]⟩
  -- types
  obtain ⟨σ2, hr2, ⟨hF2, hk2⟩, hv2, hz2, hc2, hs2⟩ :=
    tpCom_run (B' := B') (n := n) (r := r) (G := G) (B := A ∪ S)
      (Ctx := fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ τ.arrs "inB" = σ1.arrs "inB")
      ⟨fun τ h => tbase_of_fix h.1 (hB1.of_eq h.2),
        fun τ x v h hx => ⟨h.1.setVar (by
          simp [tpVars] at hx; simp [fixVars]; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;> decide) _, h.2⟩,
        fun τ a i v h ha => ⟨h.1.setArr (by
          simp [tpArrs] at ha; simp [fixArrs]; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl |
            rfl <;> decide) _ _, by
          have : "inB" ≠ a := by
            simp [tpArrs] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          simp [this, h.2]⟩⟩
      (by unfold TpBound; omega) hrB ⟨hF1, rfl⟩
      (fun t ht => by rw [hk1 "tab" (by decide)] at ht ⊢; exact hz t ht)
      (hcnt.of_eq (hk1 "cnt" (by decide))) (hsz.of_eq (hk1 "sz" (by decide)))
  rw [← hLdef] at hv2
  -- copy the labels
  obtain ⟨σ3, hr3, ⟨hF3, hk3⟩, hl3, hg3⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := 4) (arr := "labk") (ie := .var "b")
      (e := .get "lab" (.var "b"))
      (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ ∀ a, a ≠ "labk" → τ.arrs a = σ2.arrs a) L (by omega)
      (fun τ h => h.1.hn)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, fun a ha => by simpa using h.2 a ha⟩)
      (fun τ i x h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ k h hb hk => by simp [hb]; omega)
      (fun τ u h hbu hu => (hv2.of_eq (h.2 _ (by decide))).evalB hbu hu (by omega)
        (by have := hLab.lt u hu; omega)) (by simp)
      ⟨hF2, fun _ _ => rfl⟩ (by rw [hF2.lvec "labk" (by simp)]; omega)
  have hK3 : Vec σ3 "labk" n L :=
    ⟨by rw [hl3, hF2.lvec "labk" (by simp)], fun u hu => by rw [hg3 u]; simp [hu]⟩
  -- counts
  obtain ⟨σ4, hr4, ⟨hF4, hk4⟩, hm4⟩ :=
    cntPhase_run (B := B') (G := G) (L := L)
      (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ ∀ a, a ≠ "cnt" → τ.arrs a = σ3.arrs a) hLab.lt
      (by have : n * (n + 4) = n * n + 4 * n := by ring
          omega)
      (fun τ h => ⟨h.1.hn, h.1.hadj, hK3.of_eq (h.2 _ (by decide))⟩)
      (fun τ v h => ⟨h.1.setVar (by simp [fixVars]) _, by simpa using h.2⟩)
      (fun τ v h => ⟨h.1.setVar (by simp [fixVars]) _, by simpa using h.2⟩)
      (fun τ i v h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      ⟨hF3, fun _ _ => rfl⟩ (hc2.of_eq (hk3 _ (by decide)))
  have hK4 : Vec σ4 "labk" n L := hK3.of_eq (hk4 _ (by decide))
  obtain ⟨σ5, hr5, ⟨hF5, hk5⟩, hs5⟩ :=
    szPhase_run (B := B') (G := G) (L := L)
      (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ ∀ a, a ≠ "sz" → τ.arrs a = σ4.arrs a) hLab.lt
      (by omega)
      (fun τ h => ⟨h.1.hn, h.1.hadj, hK4.of_eq (h.2 _ (by decide))⟩)
      (fun τ v h => ⟨h.1.setVar (by simp [fixVars]) _, by simpa using h.2⟩)
      (fun τ i v h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      ⟨hF4, fun _ _ => rfl⟩ ((hs2.of_eq (hk3 _ (by decide))).of_eq (hk4 _ (by decide)))
  have hv5 : Vec σ5 "lab" n L :=
    ((hv2.of_eq (hk3 _ (by decide))).of_eq (hk4 _ (by decide))).of_eq (hk5 _ (by decide))
  have hm5 : Mat σ5 "cnt" n (fun u c => cntN G L u c) := hm4.of_eq (hk5 _ (by decide))
  -- representatives
  obtain ⟨σ6, hr6, ⟨hF6, hk6⟩, hrep6⟩ :=
    repCom_run (B := B') (G := G) (L := L) (pf := pf)
      (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ ∀ a, a ≠ "rep" → τ.arrs a = σ5.arrs a) hLab hpf
      (by omega)
      (fun τ h => ⟨h.1.hn, h.1.hadj, hv5.of_eq (h.2 _ (by decide)), h.1.hpos,
        h.1.lvec "mark" (by simp)⟩)
      (fun τ x v h hx => ⟨h.1.setVar (by
        simp at hx; simp [fixVars]; rcases hx with rfl | rfl | rfl <;> decide) _,
        by simpa using h.2⟩)
      (fun τ i v h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      ⟨hF5, fun _ _ => rfl⟩ (hF5.lvec "rep" (by simp))
  have hrun : Run B' prepCom σ σ6 (prepCost n r) :=
    (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq hr5 hr6))))).mono (by
      unfold prepCost; simp; nlinarith)
  have hsub : ∀ a ∈ prepCom.warrs, a ∈ prepArrs := by decide
  refine ⟨σ6, hrun, hF6, fun a ha => hrun.frame_arr a (fun h => ha (hsub a h)),
    fun x hx => hrun.frame_var x hx, hv5.of_eq (hk6 _ (by decide)),
    hm5.of_eq (hk6 _ (by decide)), hs5.of_eq (hk6 _ (by decide)), hrep6, fun t ht => ?_⟩
  rw [hk6 _ (by decide), hk5 _ (by decide), hk4 _ (by decide), hk3 _ (by decide)] at ht ⊢
  exact hz2 t ht

end Lax185574Proofs.Chain.Ram
