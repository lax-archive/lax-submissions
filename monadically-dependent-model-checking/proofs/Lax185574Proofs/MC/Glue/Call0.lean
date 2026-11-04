import Lax185574Proofs.MC.Glue.Sched

/-!
The first call of the glue program of thm:mc, issued by round 0.

After round 0 (`round0_run`, state `R0Out`), `r0Fields` sets the fields
of call `0`: the evaluation if the script has no steps, otherwise the
first call of step `0`, read from `U` at `off = n + 3` (`r0Step`). All
initial trees have the same length, so the tree of vertex `0` is the
segment of length `(|fw| - 1) / n` from position `1`. Then `tagSet` and
the writer `outCmd` follow. `r0Call_run` gives the output `hd 0 ++ callQ c₀`
with the checks, by `out0_eq`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionModelChecking
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

variable {n : ℕ}

/-! ### The fields of the first call -/

/-- The first call of the pipeline. -/
def call0 (hn : 0 < n) : List Step → PCall n
  | [] => .eval ⟨0, hn⟩
  | st :: _ => firstCall hn st

theorem pcalls_zero (hn : 0 < n) (steps : List Step) :
    (pcalls n steps)[0]? = some (call0 hn steps) := by
  cases steps with
  | nil => exact pcalls_zero_nil hn
  | cons st r => exact pcalls_zero_cons hn st r

/-- Read the first step. -/
def r0Step : Com :=
  .seq (.assign "op" (.get "U" (.var "off"))) (.seq (.assign "cP" (.get "U" (.add (.var "off") (.lit 1))))
  (.seq (.assign "cQ" (.get "U" (.add (.var "off") (.lit 2))))
  (.ite (.eq (.var "op") (.lit 0))
    (.ite (.eq (.var "cP") (.var "cQ")) (.assign "ck" (.lit 3)) (.assign "ck" (.lit 0)))
    (.seq (.assign "ck" (.lit 1))
      (.ite (.eq (.var "op") (.lit 1)) (.assign "cs" (.lit 1)) (.assign "cs" (.lit 0)))))))

/-- The evaluation as the first call. -/
def r0Ev : Com := .seq (.assign "ck" (.lit 2)) (.seq (.assign "cP" (.lit 0)) (.assign "cQ" (.lit 0)))

/-- The fields of the first call. -/
def r0Fields : Com :=
  .seq (.assign "cv" (.lit 0)) (.seq (.assign "ct" (.lit 0)) (.seq (.assign "cs" (.lit 0))
  (.seq (.assign "tl" (.div (.sub (.var "pf") (.lit 1)) (.var "gn"))) (.seq (.assign "ta" (.lit 1))
  (.seq (.ite (.eq (.var "sm") (.lit 0)) r0Ev r0Step) tagSet)))))

theorem r0Step_run {W : ℕ} {τ : Env} {st : Step} {P Q : ℕ} (hW : 4 ≤ W)
    (hcode : stepCode st = [(stepCode st).getD 0 0, P, Q]) (hn : 0 < n)
    (h0 : (τ.arrs "U")[τ.vars "off"]? = some ((stepCode st).getD 0 0))
    (h1 : (τ.arrs "U")[τ.vars "off" + 1]? = some P) (h2 : (τ.arrs "U")[τ.vars "off" + 2]? = some Q)
    (hb : τ.vars "off" + 2 ≤ W) (hPW : P ≤ W) (hQW : Q ≤ W) (hcs : τ.vars "cs" = 0) :
    ∃ τ', Run (W + 1) r0Step τ τ' 40 ∧ τ'.vars "ck" = ckOf (firstCall hn st) ∧
      τ'.vars "cP" = cPOf (firstCall hn st) ∧ τ'.vars "cQ" = cQOf (firstCall hn st) ∧
      τ'.vars "cs" = csOf (firstCall hn st) ∧ OFr τ τ' ["op", "cP", "cQ", "ck", "cs"] := by
  have hop : (stepCode st).getD 0 0 ≤ 2 := by cases st <;> simp [stepCode]
  set o := (stepCode st).getD 0 0 with ho
  set τ₁ := τ.setVar "op" o with hτ₁
  set τ₂ := τ₁.setVar "cP" P with hτ₂
  set τ₃ := τ₂.setVar "cQ" Q with hτ₃
  have rA : Run (W + 1) (.assign "op" (.get "U" (.var "off"))) τ τ₁ 3 :=
    (Run.assign (evalB_get (ev_var rfl (by omega)) h0 (by omega))).mono (by simp [Expr.size])
  have rB : Run (W + 1) (.assign "cP" (.get "U" (.add (.var "off") (.lit 1)))) τ₁ τ₂ 5 :=
    (Run.assign (evalB_get (ev_add (ev_var (v := τ.vars "off") (by simp [hτ₁]) (by omega)) (evalB_lit (by omega))
      (by omega)) (by simpa [hτ₁] using h1) (by omega))).mono (by simp [Expr.size])
  have rC : Run (W + 1) (.assign "cQ" (.get "U" (.add (.var "off") (.lit 2)))) τ₂ τ₃ 5 :=
    (Run.assign (evalB_get (ev_add (ev_var (v := τ.vars "off") (by simp [hτ₂, hτ₁]) (by omega)) (evalB_lit (by omega))
      (by omega)) (by simpa [hτ₂, hτ₁] using h2) (by omega))).mono (by simp [Expr.size])
  have f₃ : OFr τ τ₃ ["op", "cP", "cQ"] :=
    (((OFr.setVar _ _ _).trans (OFr.setVar _ _ _)).trans (OFr.setVar _ _ _)).mono (by simp)
  have hc0 := condEq_lit (B := W + 1) (τ := τ₃) (x := "op") (a := o) (d := 0) (by simp [hτ₃, hτ₂, hτ₁])
    (by omega) (by omega)
  have hc1 := condEq_lit (B := W + 1) (τ := τ₃) (x := "op") (a := o) (d := 1) (by simp [hτ₃, hτ₂, hτ₁])
    (by omega) (by omega)
  have hPQ := evalB_condEq (B := W + 1) (σ := τ₃) (e := .var "cP") (f := .var "cQ")
    (ev_var (v := P) (by simp [hτ₃, hτ₂]) (by omega)) (ev_var (v := Q) (by simp [hτ₃]) (by omega))
  have hP₃ : τ₃.vars "cP" = P := by simp [hτ₃, hτ₂]
  have hQ₃ : τ₃.vars "cQ" = Q := by simp [hτ₃]
  have hs₃ : τ₃.vars "cs" = 0 := by simp [hτ₃, hτ₂, hτ₁, hcs]
  unfold r0Step
  cases st with
  | merge A C =>
    have hA : A = P := by simp [stepCode] at hcode; exact hcode.2.1
    have hC : C = Q := by simp [stepCode] at hcode; exact hcode.2.2
    subst hA hC
    have ho0 : o = 0 := rfl
    by_cases h : A = C
    · refine ⟨τ₃.setVar "ck" 3, (Run.seq rA (Run.seq rB (Run.seq rC (Run.ite_true
        (by rw [hc0, ho0]; rfl) (Run.ite_true (by rw [hPQ]; simp [h])
          (Run.assign (evalB_lit (by omega)))))))).mono (by simp [Cond.size, Expr.size]),
        by simp [firstCall, ckOf, h], by simp [firstCall, cPOf, hP₃], by simp [firstCall, cQOf, hQ₃],
        by simp [firstCall, csOf, hs₃], (f₃.trans (OFr.setVar _ _ _)).mono (by simp)⟩
    · refine ⟨τ₃.setVar "ck" 0, (Run.seq rA (Run.seq rB (Run.seq rC (Run.ite_true
        (by rw [hc0, ho0]; rfl) (Run.ite_false (by rw [hPQ]; simp [h])
          (Run.assign (evalB_lit (by omega)))))))).mono (by simp [Cond.size, Expr.size]),
        by simp [firstCall, ckOf, h], by simp [firstCall, cPOf, hP₃], by simp [firstCall, cQOf, hQ₃],
        by simp [firstCall, csOf, hs₃], (f₃.trans (OFr.setVar _ _ _)).mono (by simp)⟩
  | resolvePos A C =>
    have hA : A = P := by simp [stepCode] at hcode; exact hcode.2.1
    have hC : C = Q := by simp [stepCode] at hcode; exact hcode.2.2
    subst hA hC
    have ho1 : o = 1 := rfl
    refine ⟨(τ₃.setVar "ck" 1).setVar "cs" 1, (Run.seq rA (Run.seq rB (Run.seq rC (Run.ite_false
        (by rw [hc0, ho1]; rfl) (Run.seq (Run.assign (evalB_lit (by omega))) (Run.ite_true
          (by rw [condEq_lit (a := o) (d := 1) (by simp [hτ₃, hτ₂, hτ₁]) (by omega) (by omega), ho1]; rfl) (Run.assign (evalB_lit (by omega))))))))).mono
          (by simp [Cond.size, Expr.size]),
        by simp [firstCall, ckOf], by simp [firstCall, cPOf, hP₃], by simp [firstCall, cQOf, hQ₃],
        by simp [firstCall, csOf], ((f₃.trans (OFr.setVar _ _ _)).trans (OFr.setVar _ _ _)).mono
          (by simp)⟩
  | resolveNeg A C =>
    have hA : A = P := by simp [stepCode] at hcode; exact hcode.2.1
    have hC : C = Q := by simp [stepCode] at hcode; exact hcode.2.2
    subst hA hC
    have ho2 : o = 2 := rfl
    refine ⟨(τ₃.setVar "ck" 1).setVar "cs" 0, (Run.seq rA (Run.seq rB (Run.seq rC (Run.ite_false
        (by rw [hc0, ho2]; rfl) (Run.seq (Run.assign (evalB_lit (by omega))) (Run.ite_false
          (by rw [condEq_lit (a := o) (d := 1) (by simp [hτ₃, hτ₂, hτ₁]) (by omega) (by omega), ho2]; rfl) (Run.assign (evalB_lit (by omega))))))))).mono
          (by simp [Cond.size, Expr.size]),
        by simp [firstCall, ckOf], by simp [firstCall, cPOf, hP₃], by simp [firstCall, cQOf, hQ₃],
        by simp [firstCall, csOf], ((f₃.trans (OFr.setVar _ _ _)).trans (OFr.setVar _ _ _)).mono
          (by simp)⟩

theorem stepCode_eq (st : Step) :
    stepCode st = [(stepCode st).getD 0 0, (stepCode st).getD 1 0, (stepCode st).getD 2 0] := by
  cases st <;> rfl

theorem r0Fields_run {W q : ℕ} {τ : Env} (steps : List Step) (hn : 0 < n)
    (hgn : τ.vars "gn" = n) (hsm : τ.vars "sm" = steps.length) (hoff : τ.vars "off" = n + 3)
    (hpf : τ.vars "pf" = 1 + n * (iL q + 3))
    (hU : ∀ st r, steps = st :: r → ∀ i < 3,
      (τ.arrs "U")[n + 3 + i]? = some ((stepCode st).getD i 0) ∧ (stepCode st).getD i 0 ≤ W)
    (hW : n + 6 + steps.length + 1 + n * (iL q + 3) ≤ W) :
    ∃ τ', Run (W + 1) r0Fields τ τ' 150 ∧
      τ'.vars "ck" = ckOf (call0 hn steps) ∧ τ'.vars "cv" = cvOf (call0 hn steps) ∧
      τ'.vars "ct" = ctOf steps.length (call0 hn steps) ∧
      τ'.vars "cP" = cPOf (call0 hn steps) ∧ τ'.vars "cQ" = cQOf (call0 hn steps) ∧
      τ'.vars "cs" = csOf (call0 hn steps) ∧ τ'.vars "otg" = tagOf steps.length (call0 hn steps) ∧
      τ'.vars "okk" = kOf steps.length (call0 hn steps) ∧
      τ'.vars "s0" = s0Of (n + 3) steps.length (call0 hn steps) ∧
      τ'.vars "ta" = 1 ∧ τ'.vars "tl" = iL q + 3 ∧
      OFr τ τ' ["cv", "ct", "cs", "tl", "ta", "op", "cP", "cQ", "ck", "lst", "otg", "okk", "s0"] := by
  set τ₁ := τ.setVar "cv" 0 with hτ₁
  set τ₂ := τ₁.setVar "ct" 0 with hτ₂
  set τ₃ := τ₂.setVar "cs" 0 with hτ₃
  set τ₄ := τ₃.setVar "tl" (iL q + 3) with hτ₄
  set τ₅ := τ₄.setVar "ta" 1 with hτ₅
  have htl : (Expr.div (.sub (.var "pf") (.lit 1)) (.var "gn")).evalB (W + 1) τ₃ = some (iL q + 3) := by
    have := evalB_bin (B := W + 1) (op := Bop.div) (σ := τ₃) (e := .sub (.var "pf") (.lit 1))
      (f := .var "gn") (ev_sub (ev_var (v := 1 + n * (iL q + 3)) (by simp [hτ₃, hτ₂, hτ₁, hpf])
        (by omega)) (evalB_lit (by omega)) (by omega)) (ev_var (v := n) (by simp [hτ₃, hτ₂, hτ₁, hgn])
        (by omega)) (by
          show (1 + n * (iL q + 3) - 1) / n < W + 1
          rw [show 1 + n * (iL q + 3) - 1 = n * (iL q + 3) by omega, Nat.mul_div_cancel_left _ hn]
          nlinarith)
    rw [this]; congr 1
    show (1 + n * (iL q + 3) - 1) / n = _
    rw [show 1 + n * (iL q + 3) - 1 = n * (iL q + 3) by omega, Nat.mul_div_cancel_left _ hn]
  have r₁₅ : Run (W + 1) (.seq (.assign "cv" (.lit 0)) (.seq (.assign "ct" (.lit 0))
      (.seq (.assign "cs" (.lit 0)) (.seq (.assign "tl" (.div (.sub (.var "pf") (.lit 1)) (.var "gn")))
        (.assign "ta" (.lit 1)))))) τ τ₅ 20 :=
    (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign htl)
        (Run.assign (evalB_lit (by omega))))))).mono (by simp [Expr.size])
  have f₅ : OFr τ τ₅ ["cv", "ct", "cs", "tl", "ta"] :=
    (((((OFr.setVar _ _ _).trans (OFr.setVar _ _ _)).trans (OFr.setVar _ _ _)).trans
      (OFr.setVar _ _ _)).trans (OFr.setVar _ _ _)).mono (by simp)
  have v₅ : ∀ y ∈ ["gn", "sm", "off"], τ₅.vars y = τ.vars y := fun y hy => f₅.vars y (by
    simp at hy; rcases hy with rfl | rfl | rfl <;> decide)
  have hc := condEq_lit (B := W + 1) (τ := τ₅) (x := "sm") (a := steps.length) (d := 0)
    (by rw [v₅ _ (by simp), hsm]) (by omega) (by omega)
  -- the fields of the call
  obtain ⟨τ₆, r₆, hck, hcP, hcQ, hcs, f₆⟩ : ∃ τ₆, Run (W + 1) (.ite (.eq (.var "sm") (.lit 0)) r0Ev r0Step)
      τ₅ τ₆ 45 ∧ τ₆.vars "ck" = ckOf (call0 hn steps) ∧ τ₆.vars "cP" = cPOf (call0 hn steps) ∧
      τ₆.vars "cQ" = cQOf (call0 hn steps) ∧ τ₆.vars "cs" = csOf (call0 hn steps) ∧
      OFr τ₅ τ₆ ["op", "cP", "cQ", "ck", "cs"] := by
    cases steps with
    | nil =>
      refine ⟨((τ₅.setVar "ck" 2).setVar "cP" 0).setVar "cQ" 0, (Run.ite_true (by rw [hc]; rfl)
        (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
          (Run.assign (evalB_lit (by omega)))))).mono (by simp [Cond.size, Expr.size]),
        by simp [call0, ckOf], by simp [call0, cPOf], by simp [call0, cQOf],
        by simp [call0, csOf, hτ₅, hτ₄, hτ₃], (((OFr.setVar _ _ _).trans (OFr.setVar _ _ _)).trans
          (OFr.setVar _ _ _)).mono (by simp)⟩
    | cons st r =>
      have h3 := hU st r rfl
      have hoff₅ : τ₅.vars "off" = n + 3 := by rw [v₅ _ (by simp), hoff]
      obtain ⟨τ₆, r₆, a, b, c, d, e⟩ := r0Step_run (W := W) (τ := τ₅) (st := st)
        (P := (stepCode st).getD 1 0) (Q := (stepCode st).getD 2 0) (by omega) (stepCode_eq st) hn
        (by rw [hoff₅, f₅.arrs _ (by decide)]; simpa using (h3 0 (by omega)).1)
        (by rw [hoff₅, f₅.arrs _ (by decide)]; exact (h3 1 (by omega)).1)
        (by rw [hoff₅, f₅.arrs _ (by decide)]; exact (h3 2 (by omega)).1)
        (by omega) (h3 1 (by omega)).2 (h3 2 (by omega)).2 (by simp [hτ₅, hτ₄, hτ₃])
      exact ⟨τ₆, (Run.ite_false (by rw [hc]; simp) r₆).mono (by simp [Cond.size, Expr.size]),
        by simpa [call0] using a, by simpa [call0] using b, by simpa [call0] using c,
        by simpa [call0] using d, e⟩
  have hck' : ckOf (call0 hn steps) ≤ 3 := by
    cases steps with
    | nil => simp [call0, ckOf]
    | cons st r => cases st <;> simp [call0, firstCall, ckOf] <;> split_ifs <;> omega
  have hcv0 : cvOf (call0 hn steps) = 0 := by
    cases steps with
    | nil => simp [call0, cvOf]
    | cons st r => cases st <;> simp [call0, firstCall, cvOf]
  have hct0 : ctOf steps.length (call0 hn steps) = 0 := by
    cases steps with
    | nil => simp [call0, ctOf]
    | cons st r => cases st <;> simp [call0, firstCall, ctOf]
  have v₆ : ∀ y ∈ ["gn", "sm", "off", "cv", "ct", "ta", "tl"], τ₆.vars y = τ₅.vars y := fun y hy =>
    f₆.vars y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨τ₇, r₇, hg, hk, hs0, f₇⟩ := tagSet_run (W := W) (m := steps.length) (o := n + 3) (τ := τ₆)
    (call0 hn steps) hck
    (by rw [v₆ _ (by simp), hct0]; simp [hτ₅, hτ₄, hτ₃, hτ₂])
    (by rw [v₆ _ (by simp), v₅ _ (by simp), hsm])
    (by rw [v₆ _ (by simp), v₅ _ (by simp), hoff]) (by omega) (by omega) (by omega)
    (by rw [hct0]; omega)
  have v₇ : ∀ y ∈ ["ck", "cP", "cQ", "cs", "cv", "ct", "ta", "tl"], τ₇.vars y = τ₆.vars y := fun y hy =>
    f₇.vars y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨τ₇, ?_, by rw [v₇ _ (by simp), hck], ?_, ?_, by rw [v₇ _ (by simp), hcP],
    by rw [v₇ _ (by simp), hcQ], by rw [v₇ _ (by simp), hcs], hg, hk, hs0, ?_, ?_,
    (((f₅.trans f₆).trans f₇)).mono (by intro y hy; simp at hy ⊢; tauto)⟩
  · unfold r0Fields
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign htl)
        (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₆ r₇)))))).mono ?_
    simp only [Expr.size]; omega
  · rw [v₇ _ (by simp), v₆ _ (by simp), hcv0]; simp [hτ₅, hτ₄, hτ₃, hτ₂, hτ₁]
  · rw [v₇ _ (by simp), v₆ _ (by simp), hct0]; simp [hτ₅, hτ₄, hτ₃, hτ₂]
  · rw [v₇ _ (by simp), v₆ _ (by simp)]; simp [hτ₅]
  · rw [v₇ _ (by simp), v₆ _ (by simp)]; simp [hτ₅, hτ₄]

/-! ### The output of round 0 -/

theorem tree0_word (σ : Script n) (q : ℕ) (hn : 0 < n) (c : ℕ → ℕ)
    (hc : ∀ k (hk : k < n), σ.colors ⟨k, hk⟩ = c k) :
    toWord (tree (sAt σ.run 0) 1 q ![⟨0, hn⟩]) = seg (fw0 n q c) 1 (iL q + 3) := by
  rw [seg_fw0 hn, sAt_run_zero, toWord_tree_unresolved _ rfl rfl]
  simp [unresolved, hc 0 hn]

theorem nil_of_ckOf_call0 (hn : 0 < n) (steps : List Step) (h : ckOf (call0 hn steps) = 2) :
    steps = [] := by
  cases steps with
  | nil => rfl
  | cons st r =>
    exfalso
    cases st with
    | merge P Q =>
      change (if P = Q then 3 else 0) = 2 at h
      split_ifs at h <;> omega
    | resolvePos P Q => simp [call0, firstCall, ckOf] at h
    | resolveNeg P Q => simp [call0, firstCall, ckOf] at h

theorem ctOf_call0 (hn : 0 < n) (steps : List Step) : ctOf steps.length (call0 hn steps) = 0 := by
  cases steps with
  | nil => simp [call0, ctOf]
  | cons st r => cases st <;> simp [call0, firstCall, ctOf]

theorem out0_eq (σ : Script n) (q : ℕ) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n) (c : ℕ → ℕ)
    (hc : ∀ k (hk : k < n), σ.colors ⟨k, hk⟩ = c k) :
    oW (tagOf σ.steps.length (call0 hn σ.steps)) (kOf σ.steps.length (call0 hn σ.steps))
      (scOf (n + 3) σ.steps.length q (call0 hn σ.steps)) (gd0 n c) (fw0 n q c)
      (Lax185574.DistanceLogic.DistFO.code (loc q φ)) (ckOf (call0 hn σ.steps))
      (cPOf (call0 hn σ.steps)) (cQOf (call0 hn σ.steps)) (csOf (call0 hn σ.steps))
      (trOf σ.run q (call0 hn σ.steps)) =
    hdOf σ.run q (n + 3) σ.steps.length (Lax185574.DistanceLogic.DistFO.code (loc q φ))
      (call0 hn σ.steps) ++ callQ σ.run q φ (call0 hn σ.steps) := by
  have hg : gwOf σ.run σ.steps.length (call0 hn σ.steps) = gd0 n c := by
    rw [gwOf, ctOf_call0, toWord_gd_zero σ c hc]
  have hf : fwOf σ.run q σ.steps.length (call0 hn σ.steps) = fw0 n q c := by
    rw [← toWord_family_zero σ q c hc, fwOf, ctOf_call0]
  rw [oW, hdOf, ← hg, ← hf, qW_trOf]

/-! ### The first call of round 0 -/

/-- The first call after round 0: its fields, then the writer. -/
noncomputable def r0Call (eM eR eE d : ℕ) : Com := .seq r0Fields (outCmd eM eR eE d)

theorem step0_U {sc : Script n} {φ : Lax3.FirstOrder.FO 0} {U : List ℕ}
    (hU : U.take ([n] ++ toWord sc ++ toWord φ).length = [n] ++ toWord sc ++ toWord φ)
    {st : Step} {r : List Step} (hs : sc.steps = st :: r) (i : ℕ) (hi : i < 3) :
    U[n + 3 + i]? = some ((stepCode st).getD i 0) ∧
      (stepCode st).getD i 0 ∈ [n] ++ toWord sc ++ toWord φ := by
  set x := [n] ++ toWord sc ++ toWord φ with hx
  have hw := input_window [n] sc (toWord φ) (t := 0) (by rw [hs]; simp)
  simp only [List.length_singleton, Nat.mul_zero, Nat.add_zero] at hw
  have hst : sc.steps[0]'(by rw [hs]; simp) = st := by simp [hs]
  rw [hst, ← hx] at hw
  have hlen : (stepCode st).length = 3 := by cases st <;> rfl
  have hk : n + 3 + i < x.length := by
    have : ((x.drop (1 + n + 2)).take 3).length = 3 := by rw [hw, hlen]
    simp at this; omega
  have hxi : x[n + 3 + i]? = some ((stepCode st).getD i 0) := by
    rw [← hw, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_drop,
      show 1 + n + 2 + i = n + 3 + i by omega, List.getElem?_eq_getElem hk]; rfl
  refine ⟨?_, List.mem_of_getElem? hxi⟩
  rw [← hxi, ← hU, List.getElem?_take_of_lt hk]

theorem scOf_le {W off m q : ℕ} (c : PCall n) (h1 : s0Of off m c ≤ W) (h2 : n ≤ W) (h3 : m ≤ W)
    (h4 : off ≤ W) (h5 : q ≤ W) (h6 : ckOf c ≤ W) (h7 : ctOf m c ≤ W) (h8 : cvOf c ≤ W)
    (h9 : cPOf c ≤ W) (h10 : cQOf c ≤ W) (h11 : csOf c ≤ W) : ∀ v ∈ scOf off m q c, v ≤ W := by
  intro v hv
  simp only [scOf, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- **The first call.** After a successful round 0 the output is the
head and the query of call `0`, and both checks held, and `ovf` stays
`0` when the words are small and the checks hold. -/
theorem r0Call_run {W eM eR eE d : ℕ} {sc : Script n} {φ : Lax3.FirstOrder.FO 0} {τ : Env}
    (hn : 0 < n)
    (hR : R0Out W n (Lax3.FirstOrder.rank φ) ([n] ++ toWord sc ++ toWord φ) 1 sc.steps.length
      (inCol ([n] ++ toWord sc ++ toWord φ) 1)
      (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) τ)
    (hW64 : 64 ≤ W) (hx : ∀ v ∈ [n] ++ toWord sc ++ toWord φ, 64 * (v + 1) ≤ W + 1)
    (hxl : 64 * (([n] ++ toWord sc ++ toWord φ).length + 1) ≤ W + 1)
    (hOB : (τ.arrs "OB").length = W + 1)
    (hv : ∀ v ∈ gd0 n (inCol ([n] ++ toWord sc ++ toWord φ) 1) ++
      fw0 n (Lax3.FirstOrder.rank φ) (inCol ([n] ++ toWord sc ++ toWord φ) 1) ++
      Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ), v ≤ W)
    (hlw : (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length ≤ W) :
    let q := Lax3.FirstOrder.rank φ
    let c0 := call0 hn sc.steps
    let lw := Lax185574.DistanceLogic.DistFO.code (loc q φ)
    let o := hdOf sc.run q (n + 3) sc.steps.length lw c0 ++ callQ sc.run q φ c0
    let u := realQ (ckOf c0) (cPOf c0) (cQOf c0) (csOf c0) (gwOf sc.run sc.steps.length c0)
      (fwOf sc.run q sc.steps.length c0) (trOf sc.run q c0) lw
    ∃ τ', Run (W + 1) (r0Call eM eR eE d) τ τ'
        (700 * (3 * n + 3 + (1 + n * (n + 1)) + (1 + n * (iL q + 3)) + lw.length + dK) +
          60 * (eM + eR + eE + 1) + 30 * 2 ^ d + 3200) ∧
      (τ'.vars "ovf" = 0 → τ'.out = τ.out ++ o ∧ maxEntry o < W / 32 / 32 ∧
        min ((u.length + maxEntry u + 1) ^ (expOf eM eR eE (ckOf c0) + 1)) W ≤ W / min (2 ^ d) W) ∧
      (dK + (3 * n + 3 + (1 + n * (n + 1))) + (1 + n * (iL q + 3)) + lw.length < W / 8 →
        maxEntry o < W / 32 / 32 →
        min ((u.length + maxEntry u + 1) ^ (expOf eM eR eE (ckOf c0) + 1)) W ≤ W / min (2 ^ d) W →
        τ'.vars "ovf" = 0) := by
  intro q c0 lw o u
  set x := [n] ++ toWord sc ++ toWord φ with hxdef
  set c := inCol x 1 with hcdef
  have hcol : ∀ k (hk : k < n), sc.colors ⟨k, hk⟩ = c k := fun k hk => (inCol_spec [n] sc _ hk).2
  have hnx : 64 * (n + 1) ≤ W + 1 := hx n (by simp [hxdef])
  have hxlen : x.length = n + 3 + 3 * sc.steps.length + (toWord φ).length := by
    simp only [hxdef, List.length_append, toWord_script, List.length_cons, List.length_ofFn,
      length_flatten_stepCode, List.length_nil, List.length_singleton]; omega
  have hmx : sc.steps.length < x.length := by omega
  have hiL : iL q ≤ glM q := iL_le_glM q
  have hqg : q ≤ glM q := by
    have h1 : q < 2 ^ q := Nat.lt_two_pow_self
    have h2 : 2 ^ q ≤ 9 ^ q := Nat.pow_le_pow_left (by norm_num) q
    have h3 : 9 ^ q ≤ 9 ^ ((q + 1) * q) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h4 := nine_pow_le_glM q
    omega
  have hq : q = Lax3.FirstOrder.rank φ := rfl
  have hbF := hR.bF
  have hbM := hR.bM
  rw [← hq] at hbF hbM
  have hnL : n * (iL q + 3) ≤ n * (glM q + 3) := Nat.mul_le_mul_left _ (by omega)
  have hfwl : (fw0 n q c).length = 1 + n * (iL q + 3) := length_fw0 n q c
  have hgwl : (gd0 n c).length = 3 * n + 3 + (1 + n * (n + 1)) := length_gd0 n c
  have hnF : n * (glM q + 3 + n) = n * (glM q + 3) + n * n := by ring
  have hnn1 : n * (n + 1) = n * n + n := by ring
  obtain ⟨τ₁, r₁, hck, hcv, hct, hcP, hcQ, hcs, htg, hkk, hs0, hta, htl, f₁⟩ :=
    r0Fields_run (W := W) (q := q) (τ := τ) sc.steps hn hR.gn hR.sm (by rw [hR.off]; omega)
      (by rw [hR.FW.pos, hfwl])
      (fun st r hs i hi => by
        obtain ⟨h1, h2⟩ := step0_U (φ := φ) hR.U hs i hi
        exact ⟨h1, by have := hx _ h2; omega⟩)
      (by omega)
  have hg : gwOf sc.run sc.steps.length c0 = gd0 n c := by
    rw [gwOf, ctOf_call0, toWord_gd_zero sc c hcol]
  have hf : fwOf sc.run q sc.steps.length c0 = fw0 n q c := by
    rw [← toWord_family_zero sc q c hcol, fwOf, ctOf_call0]
  have hu : u = realQ (ckOf c0) (cPOf c0) (cQOf c0) (csOf c0) (gd0 n c) (fw0 n q c)
      (trOf sc.run q c0) lw := by simp only [u, hg, hf]
  have v₁ : ∀ y ∈ ["W", "ovf", "gn", "sm", "off", "rk", "pg", "pf", "lp"], τ₁.vars y = τ.vars y :=
    fun y hy => f₁.vars y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hck3 : ckOf c0 ≤ 3 := by
    cases h : sc.steps with
    | nil => simp [c0, call0, ckOf, h]
    | cons st r => cases st <;> simp [c0, call0, firstCall, ckOf, h] <;> split_ifs <;> omega
  have hPQ : cPOf c0 ≤ W ∧ cQOf c0 ≤ W ∧ csOf c0 ≤ 1 := by
    cases h : sc.steps with
    | nil => simp [c0, call0, cPOf, cQOf, csOf, h]
    | cons st r =>
      have h1 := step0_U (φ := φ) hR.U h 1 (by omega)
      have h2 := step0_U (φ := φ) hR.U h 2 (by omega)
      have b1 := hx _ h1.2
      have b2 := hx _ h2.2
      cases st <;> simp [c0, call0, firstCall, cPOf, cQOf, csOf, h, stepCode] at b1 b2 ⊢ <;>
        (try split_ifs) <;> omega
  have htag : tagOf sc.steps.length c0 ≤ 2 := by unfold tagOf; split_ifs <;> omega
  have hk3 : kOf sc.steps.length c0 ≤ 3 := by unfold kOf; split_ifs <;> omega
  have hs0b : s0Of (n + 3) sc.steps.length c0 ≤ n + 6 := by
    unfold s0Of; split_ifs <;> simp [c0, ctOf_call0] <;> omega
  have hsc : scN.map τ₁.vars = scOf (n + 3) sc.steps.length q c0 := by
    simp only [scN, scOf, List.map_cons, List.map_nil]
    rw [hs0, v₁ "gn" (by simp), v₁ "sm" (by simp), v₁ "off" (by simp), v₁ "rk" (by simp), hck,
      hct, hcv, hcP, hcQ, hcs, hR.gn, hR.sm, hR.off, hR.rk]
    simp [c0]; omega
  have hcv0 : cvOf c0 = 0 := by
    cases h : sc.steps with
    | nil => simp [c0, call0, cvOf, h]
    | cons st r => cases st <;> simp [c0, call0, firstCall, cvOf, h]
  have hscW : ∀ v ∈ scOf (n + 3) sc.steps.length q c0, v ≤ W :=
    scOf_le c0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [ctOf_call0]; omega) (by omega) hPQ.1 hPQ.2.1 (by omega)
  -- the tree of the evaluation
  have hev : ckOf c0 = 2 → 1 + (iL q + 3) ≤ (fwOf sc.run q sc.steps.length c0).length ∧
      trOf sc.run q c0 = seg (fwOf sc.run q sc.steps.length c0) 1 (iL q + 3) := by
    intro h2
    rw [hf, hfwl]
    have hs := nil_of_ckOf_call0 hn sc.steps h2
    refine ⟨by
      have : 1 * (iL q + 3) ≤ n * (iL q + 3) := Nat.mul_le_mul_right _ hn
      omega, ?_⟩
    rw [← tree0_word sc q hn c hcol]
    have e : c0 = .eval ⟨0, hn⟩ := by simp only [c0, hs, call0]
    rw [e]
    simp only [trOf, length_run, hs, List.length_nil, Nat.zero_add, Nat.add_sub_cancel]
  have hPW' : cPOf c0 ≤ W := hPQ.1
  have hQW' : cQOf c0 ≤ W := hPQ.2.1
  obtain ⟨htrl, htrv⟩ := trOf_bounds sc.run q sc.steps.length c0 hev
    (fun v h => by rw [hf] at h; exact hv v (List.mem_append_left _ (List.mem_append_right _ h)))
    hPW' hQW' (by rw [hf, hfwl]; omega)
  rw [hf] at htrl
  obtain ⟨τ₂, r₂, hS, hC⟩ := outCmd_run (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d)
    (tag := tagOf sc.steps.length c0) (k := kOf sc.steps.length c0) (c := ckOf c0) (P := cPOf c0)
    (Q := cQOf c0) (sg := csOf c0) (a := 1) (N := iL q + 3) (σ := τ₁) (gw := gd0 n c)
    (fw := fw0 n q c) (lw := lw) (tr := trOf sc.run q c0)
    (by rw [v₁ _ (by simp), hR.vW]) hW64 (by rw [v₁ _ (by simp), hR.ovf])
    (hR.GW.congr (v₁ _ (by simp)) (f₁.arrs _ (by decide)))
    (hR.FW.congr (v₁ _ (by simp)) (f₁.arrs _ (by decide)))
    (hR.lo.congr (v₁ _ (by simp)) (f₁.arrs _ (by decide)))
    htg hkk hck hcP hcQ hcs hta htl
    (by rw [← hf]; exact trOK_of sc.run q sc.steps.length c0 _ _ hev)
    (fun ts _ hfw => by
      rw [v₁ _ (by simp), hR.gn]; rw [← hf] at hfw; exact (gn_of_fwOf hfw).symm)
    htrl htrv
    (fun y hy => hscW _ (by rw [← hsc]; exact List.mem_map_of_mem hy))
    (by omega) (by omega) (by rw [f₁.len, hOB]) (by omega) (by omega) hlw hv
  have hoeq : oW (tagOf sc.steps.length c0) (kOf sc.steps.length c0) (scN.map τ₁.vars) (gd0 n c)
      (fw0 n q c) lw (ckOf c0) (cPOf c0) (cQOf c0) (csOf c0) (trOf sc.run q c0) = o := by
    rw [hsc]; exact out0_eq sc q φ hn c hcol
  rw [hoeq, ← hu] at hS hC
  rw [hgwl, hfwl] at hC
  rw [hgwl, hfwl] at r₂
  refine ⟨τ₂, (Run.seq r₁ r₂).mono ?_, fun h => ?_, hC⟩
  · generalize dK = D; omega
  · obtain ⟨ho, hE, hG⟩ := hS h
    exact ⟨by rw [ho, f₁.out], hE, hG⟩

end Lax185574Proofs.MC.Glue
