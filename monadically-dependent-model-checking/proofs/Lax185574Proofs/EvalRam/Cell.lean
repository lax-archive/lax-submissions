import Lax185574Proofs.EvalRam.Scan

/-!
One cell of the evaluation table.

The command `cellCmd` computes the value of the subformula at position
`p` of `f` at the node `c` and stores it into `val[p · nn + c]`. It reads
the opcode at `p` and either scans the atoms of the node, negates or
conjoins entries of later rows, or scans the extensions of the node. The
value it stores is `cellVal`.
-/

namespace Lax185574Proofs.EvalRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding

/-- The index of the entry of row `p + 1` at node `c`. -/
def nextIdx : Expr := .add (.mul (.add (.var "p") (.lit 1)) (.var "nn")) (.var "c")

/-- The index of the entry of the row `en[p + 1]` at node `c`. -/
def sndIdx : Expr := .add (.mul (.get "en" (.add (.var "p") (.lit 1))) (.var "nn")) (.var "c")

/-- Negation. -/
def notCmd : Com :=
  .ite (.eq (.get "val" nextIdx) (.lit 1)) (.assign "v" (.lit 0)) (.assign "v" (.lit 1))

/-- Conjunction. -/
def andCmd : Com :=
  .ite (.eq (.get "val" nextIdx) (.lit 1))
    (.ite (.eq (.get "val" sndIdx) (.lit 1)) (.assign "v" (.lit 1)) (.assign "v" (.lit 0)))
    (.assign "v" (.lit 0))

/-- The local existential quantifier. -/
def exCmd : Com := .ite (.eq (.var "hh") (.lit 0)) (.assign "v" (.lit 0)) exScan

/-- The case distinction on the opcode. -/
def opCmd : Com :=
  .ite (.lt (.var "op") (.lit 6)) atScan
    (.ite (.eq (.var "op") (.lit 6)) notCmd
      (.ite (.eq (.var "op") (.lit 7)) andCmd
        (.ite (.eq (.var "op") (.lit 8)) exCmd (.assign "v" (.lit 0)))))

/-- One cell. -/
def cellCmd : Com :=
  .seq (.assign "y" (.get "pos" (.var "c"))) (.seq (.assign "hh" (.sub (.var "hq") (.get "dep" (.var "c"))))
    (.seq (.assign "op" (.get "f" (.var "p")))
      (.seq opCmd (.store "val" (.add (.mul (.var "p") (.var "nn")) (.var "c")) (.var "v")))))

/-- The facts about the arrays that a cell needs. -/
structure Ctx (B : ℕ) (X F PA DA FA EN VL : List ℕ) (q N L : ℕ) : Prop where
  hX : ∀ v ∈ X, v < B
  hF : ∀ v ∈ F, v < B
  hV : ∀ v ∈ VL, v ≤ 1
  hEN : ∀ v ∈ EN, v ≤ L
  hXB : X.length + 5 < B
  hFL : L + 4 ≤ F.length
  hFB : F.length < B
  hENl : L + 4 ≤ EN.length
  hVL : (L + 4) * N ≤ VL.length
  hVB : VL.length < B
  hPA : N ≤ PA.length
  hDA : N ≤ DA.length
  hFA : N ≤ FA.length
  hqB : q < B
  hLB : L + 4 < B
  h9 : 9 < B

/-- The arrays and scalars of a cell. -/
def CellEnv (X F PA DA FA EN VL : List ℕ) (q N p c : ℕ) (ρ : Env) : Prop :=
  ρ.arrs "x" = X ∧ ρ.arrs "f" = F ∧ ρ.arrs "pos" = PA ∧ ρ.arrs "dep" = DA ∧ ρ.arrs "fc" = FA ∧
    ρ.arrs "en" = EN ∧ ρ.arrs "val" = VL ∧ ρ.vars "hq" = q ∧ ρ.vars "nn" = N ∧ ρ.vars "p" = p ∧
    ρ.vars "c" = c

theorem condLt_var_lit {B : ℕ} {ρ : Env} {x : String} {a n : ℕ} (h : ρ.vars x = a) (ha : a < B)
    (hn : n < B) : (Cond.lt (.var x) (.lit n)).evalB B ρ = some (decide (a < n)) := by
  simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
  exact ⟨a, n, ⟨h.symm, by omega⟩, ⟨rfl, hn⟩, rfl⟩

theorem condEq_var_lit {B : ℕ} {ρ : Env} {x : String} {a n : ℕ} (h : ρ.vars x = a) (ha : a < B)
    (hn : n < B) : (Cond.eq (.var x) (.lit n)).evalB B ρ = some (a == n) := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
  exact ⟨a, n, ⟨h.symm, by omega⟩, ⟨rfl, hn⟩, rfl⟩

theorem mem_le_of_xg {L : List ℕ} {b : ℕ} (h : ∀ v ∈ L, v ≤ b) (i : ℕ) : xg L i ≤ b := by
  unfold xg
  rw [List.getD_eq_getElem?_getD]
  cases hi : L[i]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? hi)

theorem notCmd_spec (B : ℕ) (X F PA DA FA EN VL : List ℕ) (q N L p c : ℕ)
    (hC : Ctx B X F PA DA FA EN VL q N L) (hp : p < L) (hc : c < N) :
    Spec B (CellEnv X F PA DA FA EN VL q N p c) notCmd
      (fun _ ρ' => ρ'.vars "v" = (if xg VL ((p + 1) * N + c) = 1 then 0 else 1)) 20 := by
  rintro ρ ⟨-, -, -, -, -, -, hvl, -, hN, hp', hc'⟩
  subst hvl hN hp' hc'
  have hVL := hC.hVL
  have hVB := hC.hVB
  have hLB := hC.hLB
  have hidx : (ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c" < (ρ.arrs "val").length := by
    have : (ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c" < (L + 4) * ρ.vars "nn" := by nlinarith
    omega
  have hmulB : (ρ.vars "p" + 1) * ρ.vars "nn" < B := by omega
  have hnB : ρ.vars "nn" < B := by
    have := Nat.le_mul_of_pos_left (ρ.vars "nn") (show 0 < ρ.vars "p" + 1 by omega); omega
  have hvB : (ρ.arrs "val").getD ((ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c") 0 < B := by
    have := mem_le_of_xg hC.hV ((ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c")
    unfold xg at *; omega
  unfold notCmd nextIdx
  run_vcg
  all_goals simp_all [xg]

theorem andCmd_spec (B : ℕ) (X F PA DA FA EN VL : List ℕ) (q N L p c : ℕ)
    (hC : Ctx B X F PA DA FA EN VL q N L) (hp : p < L) (hc : c < N) :
    Spec B (CellEnv X F PA DA FA EN VL q N p c) andCmd
      (fun _ ρ' => ρ'.vars "v" = (if xg VL ((p + 1) * N + c) = 1 then
        (if xg VL (xg EN (p + 1) * N + c) = 1 then 1 else 0) else 0)) 40 := by
  rintro ρ ⟨-, -, -, -, -, hen, hvl, -, hN, hp', hc'⟩
  subst hen hvl hN hp' hc'
  have hVL := hC.hVL
  have hVB := hC.hVB
  have hLB := hC.hLB
  have hENl := hC.hENl
  have hidx : (ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c" < (ρ.arrs "val").length := by
    have : (ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c" < (L + 4) * ρ.vars "nn" := by nlinarith
    omega
  have hmulB : (ρ.vars "p" + 1) * ρ.vars "nn" < B := by omega
  have hnB : ρ.vars "nn" < B := by
    have := Nat.le_mul_of_pos_left (ρ.vars "nn") (show 0 < ρ.vars "p" + 1 by omega); omega
  have hvB : (ρ.arrs "val").getD ((ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c") 0 < B := by
    have := mem_le_of_xg hC.hV ((ρ.vars "p" + 1) * ρ.vars "nn" + ρ.vars "c")
    unfold xg at *; omega
  have henl : ρ.vars "p" + 1 < (ρ.arrs "en").length := by omega
  have henv : (ρ.arrs "en").getD (ρ.vars "p" + 1) 0 ≤ L := mem_le_of_xg hC.hEN _
  have henB : (ρ.arrs "en").getD (ρ.vars "p" + 1) 0 < B := by omega
  have hidx2 : (ρ.arrs "en").getD (ρ.vars "p" + 1) 0 * ρ.vars "nn" + ρ.vars "c" <
      (ρ.arrs "val").length := by
    have : (ρ.arrs "en").getD (ρ.vars "p" + 1) 0 * ρ.vars "nn" + ρ.vars "c" < (L + 4) * ρ.vars "nn" := by
      nlinarith
    omega
  have hmul2B : (ρ.arrs "en").getD (ρ.vars "p" + 1) 0 * ρ.vars "nn" < B := by omega
  have hv2B : (ρ.arrs "val").getD ((ρ.arrs "en").getD (ρ.vars "p" + 1) 0 * ρ.vars "nn" + ρ.vars "c") 0 < B := by
    have := mem_le_of_xg hC.hV ((ρ.arrs "en").getD (ρ.vars "p" + 1) 0 * ρ.vars "nn" + ρ.vars "c")
    unfold xg at *; omega
  unfold andCmd nextIdx sndIdx
  run_vcg
  all_goals simp_all [xg]

theorem opCmd_spec (B : ℕ) (X F PA DA FA EN VL : List ℕ) (q N L p c : ℕ)
    (hC : Ctx B X F PA DA FA EN VL q N L) (hp : p < L) (hc : c < N) (hn : NodeOK X PA DA FA q N c) :
    Spec B (fun ρ => CellEnv X F PA DA FA EN VL q N p c ρ ∧ ρ.vars "y" = xg PA c ∧
        ρ.vars "hh" = q - xg DA c ∧ ρ.vars "op" = xg F p) opCmd
      (fun _ ρ' => ρ'.vars "v" = cellVal X F PA DA FA EN VL q N p c) (100 * X.length + 150) := by
  rintro ρ ⟨hE, hy, hh, hop⟩
  obtain ⟨hx, hf, hpa, hda, hfa, hen, hvl, hq, hN, hp', hc'⟩ := hE
  set o := xg F p with ho
  have hoB : o < B := xg_lt hC.hF (by have := hC.hFB; omega)
  have hFB := hC.hFB
  have hFL := hC.hFL
  have hXB := hC.hXB
  have hLB := hC.hLB
  have h9 := hC.h9
  obtain ⟨ws, r0, hws⟩ := hn.node.atomList
  have hA := listFacts_of hws
  by_cases h6 : o < 6
  · obtain ⟨ρ', hr, hv⟩ := atScan_spec B X F (xg PA c) p o hA (by omega) hC.hX hC.hF hXB hFB hoB ρ
      ⟨hx, hf, hy, hp', hop⟩
    refine ⟨ρ', (Run.ite_true (by rw [condLt_var_lit hop hoB (by omega)]; simp [h6]) hr).mono
      (by simp <;> omega), ?_⟩
    show ρ'.vars "v" = _
    simp only [hv, cellVal, ← ho, if_pos h6]; rfl
  have hc6 : (Cond.lt (.var "op") (.lit 6)).evalB B ρ = some false := by
    rw [condLt_var_lit hop hoB (by omega)]; simp [h6]
  by_cases h6' : o = 6
  · obtain ⟨ρ', hr, hv⟩ := notCmd_spec B X F PA DA FA EN VL q N L p c hC hp hc ρ
      ⟨hx, hf, hpa, hda, hfa, hen, hvl, hq, hN, hp', hc'⟩
    refine ⟨ρ', (Run.ite_false hc6 (Run.ite_true (by rw [condEq_var_lit hop hoB (by omega)]; simp [h6'])
      hr)).mono (by simp <;> omega), ?_⟩
    show ρ'.vars "v" = _
    simp only [hv, cellVal, ← ho, if_neg h6, if_pos h6']
  have hc6' : (Cond.eq (.var "op") (.lit 6)).evalB B ρ = some false := by
    rw [condEq_var_lit hop hoB (by omega)]; simp [h6']
  by_cases h7 : o = 7
  · obtain ⟨ρ', hr, hv⟩ := andCmd_spec B X F PA DA FA EN VL q N L p c hC hp hc ρ
      ⟨hx, hf, hpa, hda, hfa, hen, hvl, hq, hN, hp', hc'⟩
    refine ⟨ρ', (Run.ite_false hc6 (Run.ite_false hc6' (Run.ite_true
      (by rw [condEq_var_lit hop hoB (by omega)]; simp [h7]) hr))).mono (by simp <;> omega), ?_⟩
    show ρ'.vars "v" = _
    simp only [hv, cellVal, ← ho, if_neg h6, if_neg h6', if_pos h7]
  have hc7 : (Cond.eq (.var "op") (.lit 7)).evalB B ρ = some false := by
    rw [condEq_var_lit hop hoB (by omega)]; simp [h7]
  by_cases h8 : o = 8
  · have hc8 : (Cond.eq (.var "op") (.lit 8)).evalB B ρ = some true := by
      rw [condEq_var_lit hop hoB (by omega)]; simp [h8]
    have hhB : q - xg DA c < B := by have := hC.hqB; omega
    by_cases h0 : q - xg DA c = 0
    · refine ⟨ρ.setVar "v" 0, (Run.ite_false hc6 (Run.ite_false hc6' (Run.ite_false hc7
        (Run.ite_true hc8 (Run.ite_true (by rw [condEq_var_lit hh hhB (by omega)]; simp [h0])
          (Run.assign (v := 0) (by simp <;> omega))))))).mono (by simp <;> omega), ?_⟩
      simp only [cellVal, ← ho, if_neg h6, if_neg h6', if_neg h7, if_pos h8, if_pos h0, vars_setVar,
        if_true]
    · obtain ⟨h, hh1⟩ : ∃ h, q - xg DA c = h + 1 := ⟨q - xg DA c - 1, by omega⟩
      have hlt : xg DA c < q := by omega
      have hnode := hn.node
      rw [hh1] at hnode
      obtain ⟨hfr, -, -⟩ := hnode.exts
      obtain ⟨ℓ', t, r1, hx1⟩ := hnode
      have hEL := listFacts_of (nodeSplit hx1).2
      have hch := hn.child hlt
      have hcFA : c < FA.length := by have := hC.hFA; omega
      have hFAN : xg FA c ≤ N := hn.fc_le
      obtain ⟨ρ', hr, hv⟩ := exScan_spec B X F VL FA (xg PA c) p N c hA hEL
        (fun j hj => (hfr j hj).2.2) (fun j hj => (hch j hj).1) hcFA hFAN hc (by omega)
        (by have := hC.hVL; nlinarith) hC.hX hC.hF (fun v hv => by have := hC.hV v hv; omega) hXB hFB
        hC.hVB (by omega) ρ ⟨hx, hf, hvl, hfa, hy, hp', hN, hc'⟩
      refine ⟨ρ', (Run.ite_false hc6 (Run.ite_false hc6' (Run.ite_false hc7
        (Run.ite_true hc8 (Run.ite_false (by rw [condEq_var_lit hh hhB (by omega)]; simp [h0])
          hr))))).mono (by simp <;> omega), ?_⟩
      show ρ'.vars "v" = _
      simp only [hv, cellVal, ← ho, if_neg h6, if_neg h6', if_neg h7, if_pos h8, if_neg h0]
  · have hc8 : (Cond.eq (.var "op") (.lit 8)).evalB B ρ = some false := by
      rw [condEq_var_lit hop hoB (by omega)]; simp [h8]
    refine ⟨ρ.setVar "v" 0, (Run.ite_false hc6 (Run.ite_false hc6' (Run.ite_false hc7
      (Run.ite_false hc8 (Run.assign (v := 0) (by simp <;> omega)))))).mono (by simp <;> omega), ?_⟩
    simp only [cellVal, ← ho, if_neg h6, if_neg h6', if_neg h7, if_neg h8, vars_setVar, if_true]

theorem CellEnv.setVar {X F PA DA FA EN VL : List ℕ} {q N p c : ℕ} {ρ : Env}
    (h : CellEnv X F PA DA FA EN VL q N p c ρ) {x : String} (h1 : x ≠ "hq") (h2 : x ≠ "nn")
    (h3 : x ≠ "p") (h4 : x ≠ "c") (v : ℕ) : CellEnv X F PA DA FA EN VL q N p c (ρ.setVar x v) := by
  obtain ⟨hx, hf, hpa, hda, hfa, hen, hvl, hq, hN, hp, hc⟩ := h
  exact ⟨by simpa using hx, by simpa using hf, by simpa using hpa, by simpa using hda,
    by simpa using hfa, by simpa using hen, by simpa using hvl, by simp [h1.symm, hq],
    by simp [h2.symm, hN], by simp [h3.symm, hp], by simp [h4.symm, hc]⟩

/-- **One cell.** -/
theorem cellCmd_spec (B : ℕ) (X F PA DA FA EN VL : List ℕ) (q N L p c : ℕ)
    (hC : Ctx B X F PA DA FA EN VL q N L) (hp : p < L) (hc : c < N) (hn : NodeOK X PA DA FA q N c) :
    Spec B (CellEnv X F PA DA FA EN VL q N p c) cellCmd
      (fun _ ρ' => ρ'.arrs "val" = VL.set (p * N + c) (cellVal X F PA DA FA EN VL q N p c))
      (100 * X.length + 200) := by
  intro ρ hE
  obtain ⟨hx, hf, hpa, hda, hfa, hen, hvl, hq, hN, hp', hc'⟩ := hE
  have hXB := hC.hXB
  have hFB := hC.hFB
  have hFL := hC.hFL
  have hqB := hC.hqB
  have hy : xg PA c < B := by
    obtain ⟨ℓ, t, r, hx1⟩ := hn.node
    have := le_of_drop_eq hx1 (toWord_node_ne_nil t)
    have := List.length_pos_iff.mpr (toWord_node_ne_nil t)
    omega
  have hcPA : c < PA.length := by have := hC.hPA; omega
  have hcDA : c < DA.length := by have := hC.hDA; omega
  set ρ1 := ρ.setVar "y" (xg PA c) with hρ1
  set ρ2 := ρ1.setVar "hh" (q - xg DA c) with hρ2
  set ρ3 := ρ2.setVar "op" (xg F p) with hρ3
  have r1 : Run B (.assign "y" (.get "pos" (.var "c"))) ρ ρ1 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    refine ⟨c, ⟨hc'.symm, by have := hC.hVB; have := hC.hVL; rw [hc']; nlinarith⟩, ?_, hy⟩
    rw [hpa, List.getElem?_eq_getElem hcPA]; simp [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcPA]
  have r2 : Run B (.assign "hh" (.sub (.var "hq") (.get "dep" (.var "c")))) ρ1 ρ2 6 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, hρ1, vars_setVar, arrs_setVar]
    have hd : xg DA c ≤ q := hn.dep_le
    refine ⟨q, xg DA c, ⟨by simp [hq], by simp [hq]; omega⟩,
      ⟨c, ⟨by simp [hc'], by simp [hc']; have := hC.hVB; have := hC.hVL; nlinarith⟩, ?_, by omega⟩,
      rfl, by omega⟩
    rw [hda, List.getElem?_eq_getElem hcDA]; simp [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcDA]
  have r3 : Run B (.assign "op" (.get "f" (.var "p"))) ρ2 ρ3 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff, hρ2, hρ1, vars_setVar, arrs_setVar]
    have hpF : p < F.length := by omega
    refine ⟨p, ⟨by simp [hp'], by simp [hp']; have := hC.hLB; omega⟩, ?_, xg_lt hC.hF (by omega)⟩
    rw [hf, List.getElem?_eq_getElem hpF]; simp [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpF]
  have hE3 : CellEnv X F PA DA FA EN VL q N p c ρ3 :=
    (((show CellEnv X F PA DA FA EN VL q N p c ρ from
      ⟨hx, hf, hpa, hda, hfa, hen, hvl, hq, hN, hp', hc'⟩).setVar (by decide) (by decide) (by decide)
        (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _).setVar (by decide)
        (by decide) (by decide) (by decide) _
  obtain ⟨ρ4, r4, hv4⟩ := opCmd_spec B X F PA DA FA EN VL q N L p c hC hp hc hn ρ3
    ⟨hE3, by simp [hρ3, hρ2, hρ1], by simp [hρ3, hρ2], by simp [hρ3]⟩
  have hv4' : ∀ z, z ∉ opCmd.wvars → ρ4.vars z = ρ3.vars z := fun z h => r4.frame_var z h
  have ha4 : ∀ a, a ∉ opCmd.warrs → ρ4.arrs a = ρ3.arrs a := fun a h => r4.frame_arr a h
  have hval4 : ρ4.arrs "val" = VL := by rw [ha4 "val" (by decide)]; exact hE3.2.2.2.2.2.2.1
  have hidx : p * N + c < VL.length := by
    have := hC.hVL
    have : p * N + c < (L + 4) * N := by nlinarith
    omega
  have hp4 : ρ4.vars "p" = p := by rw [hv4' "p" (by decide)]; exact hE3.2.2.2.2.2.2.2.2.2.1
  have hN4 : ρ4.vars "nn" = N := by rw [hv4' "nn" (by decide)]; exact hE3.2.2.2.2.2.2.2.2.1
  have hc4 : ρ4.vars "c" = c := by rw [hv4' "c" (by decide)]; exact hE3.2.2.2.2.2.2.2.2.2.2
  have hVB := hC.hVB
  have hpN : p * N < B := by omega
  have hvB : cellVal X F PA DA FA EN VL q N p c < B := by
    have := cellVal_le X F PA DA FA EN VL q N p c; omega
  refine ⟨ρ4.setArr "val" (p * N + c) (cellVal X F PA DA FA EN VL q N p c), ?_, by simp [hval4]⟩
  unfold cellCmd
  refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.store ?_ ?_ ?_))))).mono ?_
  · simp only [evalB_bin_iff, evalB_var_iff]
    refine ⟨p * N, c, ⟨p, N, ⟨hp4.symm, by omega⟩, ⟨hN4.symm, ?_⟩, rfl, hpN⟩, ⟨hc4.symm, by omega⟩, rfl,
      by omega⟩
    have := Nat.le_mul_of_pos_left N (show 0 < p + 4 by omega)
    have := hC.hVL
    have : N ≤ (L + 4) * N := Nat.le_mul_of_pos_left N (by omega)
    omega
  · simp only [evalB_var_iff]; exact ⟨hv4.symm, by rw [hv4]; exact hvB⟩
  · rw [hval4]; exact hidx
  · simp only [Expr.size]; omega

end Lax185574Proofs.EvalRam
