import Lax185574Proofs.MC.Glue.Apply

/-!
The fields of the next call, in a round of the glue program of thm:mc
after the first.

`nxF` sets the fields `ck ct cv cP cQ cs` of the call after the current
one (`nextCall`): the call of the next step, decoded from the window
`w0 w1 w2` by `r0Step` after storing the window into `U` at `off`, or
the evaluation. `tLoc` finds the tree of vertex `cv` in `FW` for a
merge or the evaluation (`ta`, `tl`). `evEnd` writes the answer after the
evaluation.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs Lax185574.TypeTrees

variable {n : ℕ}

/-! ### The next call -/

/-- Store the window at `off` and decode the step. -/
def stF : Com :=
  .seq (.store "U" (.var "off") (.var "w0")) (.seq (.store "U" (.add (.var "off") (.lit 1)) (.var "w1"))
    (.seq (.store "U" (.add (.var "off") (.lit 2)) (.var "w2")) r0Step))

/-- The call after the last call of step `ct`. -/
def afterF : Com :=
  .ite (.lt (.add (.var "ct") (.lit 1)) (.var "sm"))
    (.seq (.assign "ct" (.add (.var "ct") (.lit 1))) (.seq (.assign "cv" (.lit 0))
      (.seq (.assign "cs" (.lit 0)) stF)))
    (.seq (.assign "ck" (.lit 2)) (.seq (.assign "ct" (.var "sm")) (.seq (.assign "cv" (.lit 0))
      (.seq (.assign "cP" (.lit 0)) (.seq (.assign "cQ" (.lit 0)) (.assign "cs" (.lit 0)))))))

/-- The fields of the next call. -/
def nxF : Com := afterF

/-- The fields of a call are the scalars. -/
def HasFields (m : ℕ) (c : PCall n) (τ : Env) : Prop :=
  τ.vars "ck" = ckOf c ∧ τ.vars "ct" = ctOf m c ∧ τ.vars "cv" = cvOf c ∧ τ.vars "cP" = cPOf c ∧
    τ.vars "cQ" = cQOf c ∧ τ.vars "cs" = csOf c

theorem stepFirst_fields (hn : 0 < n) (t : ℕ) (st : Step) :
    ckOf (stepFirst hn t st) = ckOf (firstCall hn st) ∧
      cPOf (stepFirst hn t st) = cPOf (firstCall hn st) ∧
      cQOf (stepFirst hn t st) = cQOf (firstCall hn st) ∧
      csOf (stepFirst hn t st) = csOf (firstCall hn st) ∧
      cvOf (stepFirst hn t st) = 0 ∧ ∀ m, ctOf m (stepFirst hn t st) = t := by
  cases st <;> simp [stepFirst, firstCall, ckOf, cPOf, cQOf, csOf, cvOf, ctOf]

theorem afterF_run {W m t : ℕ} {τ : Env} (hn : 0 < n) (steps : List Step) (hm : steps.length = m)
    (hct : τ.vars "ct" = t) (hsm : τ.vars "sm" = m) (ht : t < m) (hmW : m + 1 ≤ W) (hW : 4 ≤ W)
    (hoff : τ.vars "off" + 2 < (τ.arrs "U").length) (hoffW : τ.vars "off" + 2 ≤ W)
    (hw : ∀ y ∈ ["w0", "w1", "w2"], τ.vars y ≤ W)
    (hwin : ∀ (h : t + 1 < m), τ.vars "w0" = (stepCode steps[t + 1]).getD 0 0 ∧
      τ.vars "w1" = (stepCode steps[t + 1]).getD 1 0 ∧ τ.vars "w2" = (stepCode steps[t + 1]).getD 2 0) :
    ∃ τ', Run (W + 1) afterF τ τ' 80 ∧ HasFields m (afterStep hn steps t) τ' ∧
      (∀ y, y ∉ ["ck", "ct", "cv", "cP", "cQ", "cs", "op"] → τ'.vars y = τ.vars y) ∧
      (∀ b, b ≠ "U" → τ'.arrs b = τ.arrs b) ∧ (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  have hc := evalB_condLt (B := W + 1) (σ := τ) (e := .add (.var "ct") (.lit 1)) (f := .var "sm")
    (ev_add (ev_var hct (by omega)) (evalB_lit (by omega)) (by omega)) (ev_var hsm (by omega))
  by_cases h1 : t + 1 < m
  · obtain ⟨h0', h1', h2'⟩ := hwin h1
    set st := steps[t + 1] with hst
    set τ₁ := ((τ.setVar "ct" (t + 1)).setVar "cv" 0).setVar "cs" 0 with hτ₁
    obtain ⟨o, ho⟩ : ∃ o, τ.vars "off" = o := ⟨_, rfl⟩
    set τ₂ := ((τ₁.setArr "U" o (τ.vars "w0")).setArr "U" (o + 1) (τ.vars "w1")).setArr "U" (o + 2)
      (τ.vars "w2") with hτ₂
    have hU₂ : ∀ i < 3, (τ₂.arrs "U")[o + i]? = some ((stepCode st).getD i 0) := by
      intro i hi
      have hl : o + 2 < (τ.arrs "U").length := ho ▸ hoff
      interval_cases i
      · simp [hτ₂, hτ₁, List.getElem?_set, h0']; omega
      · simp [hτ₂, hτ₁, List.getElem?_set, h1']; omega
      · simp [hτ₂, hτ₁, List.getElem?_set, h2']; omega
    have hl : o + 2 < (τ.arrs "U").length := ho ▸ hoff
    have rs1 : Run (W + 1) (.store "U" (.var "off") (.var "w0")) τ₁ (τ₁.setArr "U" o (τ.vars "w0")) 3 :=
      (Run.store (ev_var (v := o) (by simp [hτ₁, ho]) (by omega))
        (ev_var (by simp [hτ₁]) (by have := hw "w0" (by simp); omega)) (by simp [hτ₁]; omega)).mono
        (by simp [Expr.size])
    have rs2 : Run (W + 1) (.store "U" (.add (.var "off") (.lit 1)) (.var "w1"))
        (τ₁.setArr "U" o (τ.vars "w0")) ((τ₁.setArr "U" o (τ.vars "w0")).setArr "U" (o + 1)
          (τ.vars "w1")) 5 :=
      (Run.store (ev_add (ev_var (v := o) (by simp [hτ₁, ho]) (by omega)) (evalB_lit (by omega))
        (by omega)) (ev_var (by simp [hτ₁]) (by have := hw "w1" (by simp); omega))
        (by simp [hτ₁]; omega)).mono (by simp [Expr.size])
    have rs3 : Run (W + 1) (.store "U" (.add (.var "off") (.lit 2)) (.var "w2"))
        ((τ₁.setArr "U" o (τ.vars "w0")).setArr "U" (o + 1) (τ.vars "w1")) τ₂ 5 :=
      (Run.store (ev_add (ev_var (v := o) (by simp [hτ₁, ho]) (by omega)) (evalB_lit (by omega))
        (by omega)) (ev_var (by simp [hτ₁]) (by have := hw "w2" (by simp); omega))
        (by simp [hτ₁]; omega)).mono (by simp [Expr.size])
    have hoff₂ : τ₂.vars "off" = o := by simp [hτ₂, hτ₁, ho]
    have hP : (stepCode st).getD 1 0 ≤ W := by rw [← h1']; exact hw "w1" (by simp)
    have hQ : (stepCode st).getD 2 0 ≤ W := by rw [← h2']; exact hw "w2" (by simp)
    obtain ⟨τ₃, r₃, hck, hcP, hcQ, hcs, f₃⟩ := r0Step_run (W := W) (τ := τ₂) (st := st)
      (P := (stepCode st).getD 1 0) (Q := (stepCode st).getD 2 0) hW (stepCode_eq st) hn
      (by rw [hoff₂]; simpa using hU₂ 0 (by omega)) (by rw [hoff₂]; exact hU₂ 1 (by omega))
      (by rw [hoff₂]; exact hU₂ 2 (by omega)) (by rw [hoff₂]; omega) hP hQ
      (by simp [hτ₂, hτ₁])
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := stepFirst_fields hn (t + 1) st
    have hA : afterStep hn steps t = stepFirst hn (t + 1) st := by
      rw [afterStep, dif_pos (by omega)]
    have hr : Run (W + 1) afterF τ τ₃ 80 := by
      unfold afterF stF
      refine (Run.ite_true (by rw [hc, decide_eq_true h1]) (Run.seq (Run.assign (ev_add
        (ev_var hct (by omega)) (evalB_lit (by omega)) (by omega))) (Run.seq (Run.assign
        (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
        (Run.seq rs1 (Run.seq rs2 (Run.seq rs3 r₃))))))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    have v₃ : ∀ y, y ∉ ["op", "cP", "cQ", "ck", "cs"] → τ₃.vars y = τ₂.vars y := f₃.vars
    refine ⟨τ₃, hr, ?_, fun y hy => hr.frame_var_sub y (by
        simp [afterF, stF, r0Step, Com.wvars]) hy,
      fun b hb => hr.frame_arr b (by simp [afterF, stF, r0Step, Com.warrs]; exact hb),
      fun b => run_length_arrs hr b, hr.frame_inp (by simp [afterF, stF, r0Step, Com.reads]),
      hr.out_eq (by simp [afterF, stF, r0Step, Com.NoWrite])⟩
    rw [hA]
    refine ⟨by rw [hck, e1], ?_, ?_, by rw [hcP, e2], by rw [hcQ, e3], by rw [hcs, e4]⟩
    · rw [v₃ "ct" (by decide), e6]; simp [hτ₂, hτ₁]
    · rw [v₃ "cv" (by decide), e5]; simp [hτ₂, hτ₁]
  · have hA : afterStep hn steps t = .eval ⟨0, hn⟩ := by simp [afterStep]; omega
    set τ' := (((((τ.setVar "ck" 2).setVar "ct" m).setVar "cv" 0).setVar "cP" 0).setVar "cQ" 0).setVar
      "cs" 0 with hτ'
    have hr : Run (W + 1) afterF τ τ' 80 := by
      unfold afterF
      refine (Run.ite_false (by rw [hc, decide_eq_false h1]) (Run.seq (Run.assign (evalB_lit
        (by omega))) (Run.seq (Run.assign (ev_var (by simp [hsm]) (by omega))) (Run.seq
        (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
        (Run.seq (Run.assign (evalB_lit (by omega))) (Run.assign (evalB_lit (by omega))))))))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    refine ⟨τ', hr, ?_, fun y hy => hr.frame_var_sub y (by simp [afterF, stF, r0Step, Com.wvars]) hy,
      fun b hb => hr.frame_arr b (by simp [afterF, stF, r0Step, Com.warrs]; exact hb),
      fun b => run_length_arrs hr b, hr.frame_inp (by simp [afterF, stF, r0Step, Com.reads]),
      hr.out_eq (by simp [afterF, stF, r0Step, Com.NoWrite])⟩
    rw [hA]
    simp [HasFields, hτ', ckOf, ctOf, cvOf, cPOf, cQOf, csOf]

/-- **The fields of the next call.** -/
theorem nxF_run {W m : ℕ} {τ : Env} (hn : 0 < n) (steps : List Step) (hm : steps.length = m)
    (c : PCall n) (hval : Valid steps c) (hne : ∀ a, c ≠ .eval a) (hf : HasFields m c τ)
    (hgn : τ.vars "gn" = n) (hsm : τ.vars "sm" = m) (hmW : m + 1 ≤ W) (hnW : n + 1 ≤ W)
    (hW : 4 ≤ W)
    (hoff : τ.vars "off" + 2 < (τ.arrs "U").length) (hoffW : τ.vars "off" + 2 ≤ W)
    (hw : ∀ y ∈ ["w0", "w1", "w2"], τ.vars y ≤ W)
    (hwin : tagOf m c = 2 → ∀ (h : ctOf m c + 1 < m),
      τ.vars "w0" = (stepCode steps[ctOf m c + 1]).getD 0 0 ∧
      τ.vars "w1" = (stepCode steps[ctOf m c + 1]).getD 1 0 ∧
      τ.vars "w2" = (stepCode steps[ctOf m c + 1]).getD 2 0) :
    ∃ τ', Run (W + 1) nxF τ τ' 100 ∧ (∀ c', nextCall hn steps c = some c' → HasFields m c' τ') ∧
      (∀ y, y ∉ ["ck", "ct", "cv", "cP", "cQ", "cs", "op"] → τ'.vars y = τ.vars y) ∧
      (∀ b, b ≠ "U" → τ'.arrs b = τ.arrs b) ∧ (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  obtain ⟨hck, hct, hcv, hcP, hcQ, hcs⟩ := hf
  -- the step of the call exists
  have hctm : ctOf m c < m := by
    cases c with
    | merge t P Q =>
      have : steps[t]? = some (.merge P Q) := hval; simp only [ctOf]
      rw [← hm]; by_contra h; rw [List.getElem?_eq_none (by omega)] at this; simp at this
    | resolve t sg P Q =>
      have : steps[t]? = some (if sg then .resolvePos P Q else .resolveNeg P Q) := hval
      simp only [ctOf]
      rw [← hm]; by_contra h; rw [List.getElem?_eq_none (by omega)] at this; simp at this
    | eval a => exact absurd rfl (hne a)
  have hl : lastOf c := by
    cases c with
    | merge => trivial
    | resolve => trivial
    | eval a => exact absurd rfl (hne a)
  obtain ⟨τ', r, hF, f1, f2, f3, f4, f5⟩ := afterF_run (W := W) (t := ctOf m c) hn steps hm hct
    hsm hctm hmW hW hoff hoffW hw (fun h => hwin (by simp [tagOf, hl, h]) h)
  refine ⟨τ', r.mono (by omega), fun c' hc' => ?_, f1, f2, f3, f4, f5⟩
  have : nextCall hn steps c = some (afterStep hn steps (ctOf m c)) := by
    cases c with
    | merge t P Q => rfl
    | resolve t sg P Q => rfl
    | eval a => exact absurd rfl (hne a)
  rw [this] at hc'; cases hc'; exact hF

/-! ### The tree of the next call -/

/-- Find the tree of vertex `cv` in `FW`, for a merge or the evaluation. -/
def tLoc : Com :=
  .ite (.eq (.var "ck") (.lit 1)) .skip (.ite (.eq (.var "ck") (.lit 3)) .skip
    (.seq (.assign "y" (.lit 1)) (.seq (locT "FW") (.seq (.assign "ta" (.var "y"))
      (.seq (skipT "FW") (.assign "tl" (.sub (.var "y") (.var "ta"))))))))

theorem Filled.arrs_eq {a pv : String} {l : List ℕ} {τ : Env} (h : Filled a pv l τ) :
    τ.arrs a = l ++ (τ.arrs a).drop l.length := by
  conv_lhs => rw [← List.take_append_drop l.length (τ.arrs a)]
  congr 1
  apply List.ext_getElem
  · simp; exact h.length_le
  · intro i h1 h2
    have := h.get i h2
    rw [List.getElem?_eq_getElem (by simp at h1; omega)] at this
    simp only [List.getElem_take]
    exact Option.some.inj this

theorem tLoc_run {W v k : ℕ} {τ : Env} {ts : List TypeTree}
    (hck : τ.vars "ck" = k) (hk : k ≤ 3) (hcv : τ.vars "cv" = v) (hv : v < ts.length)
    (hF : Filled "FW" "pf" (ts.length :: (ts.map toWord).flatten) τ)
    (hB : 2 * (1 + ((ts.map toWord).flatten).length) + ts.length < W)
    (hvals : ∀ u ∈ τ.arrs "FW", u < W + 1) :
    ∃ τ', Run (W + 1) tLoc τ τ' (110 * (((ts.map toWord).flatten).length + ts.length) + 200) ∧
      ((k = 0 ∨ k = 2) → τ'.vars "ta" + τ'.vars "tl" ≤ 1 + ((ts.map toWord).flatten).length ∧
        seg (ts.length :: (ts.map toWord).flatten) (τ'.vars "ta") (τ'.vars "tl") = toWord ts[v]) ∧
      (∀ y, y ∉ ["y", "ta", "tl", "e1", "e2", "e3", "e4"] → τ'.vars y = τ.vars y) ∧
      τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  have hc1 := condEq_lit (B := W + 1) (d := 1) hck (by omega) (by omega)
  have hc3 := condEq_lit (B := W + 1) (d := 3) hck (by omega) (by omega)
  have hfr : ∀ τ', Run (W + 1) tLoc τ τ' (110 * (((ts.map toWord).flatten).length + ts.length) + 200) →
      (∀ y, y ∉ ["y", "ta", "tl", "e1", "e2", "e3", "e4"] → τ'.vars y = τ.vars y) ∧
      τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out := fun τ' r =>
    ⟨fun y hy => r.frame_var_sub y (by simp [tLoc, locT, skipT, skipL, forUp, Com.wvars]) hy,
      funext fun b => r.frame_arr b (by simp [tLoc, locT, skipT, skipL, forUp, Com.warrs]),
      r.frame_inp (by simp [tLoc, locT, skipT, skipL, forUp, Com.reads]),
      r.out_eq (by simp [tLoc, locT, skipT, skipL, forUp, Com.NoWrite])⟩
  by_cases h1 : k = 1
  · have r : Run (W + 1) tLoc τ τ (110 * (((ts.map toWord).flatten).length + ts.length) + 200) :=
      (Run.ite_true (by rw [hc1, decide_eq_true h1]) Run.skip).mono (by simp [Cond.size, Expr.size])
    exact ⟨τ, r, fun h => by omega, hfr τ r⟩
  by_cases h3 : k = 3
  · have r : Run (W + 1) tLoc τ τ (110 * (((ts.map toWord).flatten).length + ts.length) + 200) :=
      (Run.ite_false (by rw [hc1, decide_eq_false h1]) (Run.ite_true
        (by rw [hc3, decide_eq_true h3]) Run.skip)).mono (by simp [Cond.size, Expr.size])
    exact ⟨τ, r, fun h => by omega, hfr τ r⟩
  set X := τ.arrs "FW" with hX
  have hXe := Filled.arrs_eq hF
  rw [← hX] at hXe
  have hd1 : X.drop 1 = (ts.map toWord).flatten ++ X.drop (1 + ((ts.map toWord).flatten).length) := by
    nth_rewrite 1 [hXe]
    rw [List.cons_append, List.drop_one, List.tail_cons, List.length_cons, Nat.add_comm]
  obtain ⟨τ₂, r₂, hy₂, -⟩ := locT_run (B := W + 1) (i := v) (ar := "FW") (X := X) (p := 1) (ts := ts)
    (τ := τ.setVar "y" 1) (by simp [hX]) (by simp) (by simp [hcv]) hv.le hd1 (by omega) hvals
  obtain ⟨F, hF'⟩ : ∃ F, F = ((ts.map toWord).take v).flatten.length := ⟨_, rfl⟩
  rw [← hF'] at hy₂ r₂
  have hdv := drop_flatten_take hd1 (k := v) (by simpa using hv)
  have hgv : (ts.map toWord).getD v [] = toWord ts[v] := by
    rw [List.getD_eq_getElem _ _ (by simpa using hv)]; simp
  have hle := flatten_take_add_le (ts.map toWord) (k := v) (by simpa using hv)
  rw [hgv, ← hF'] at hdv hle
  have hX₂ : τ₂.arrs "FW" = X := by
    rw [r₂.frame_arr "FW" (by simp [locT, skipT, skipL, forUp, Com.warrs])]; simp [hX]
  obtain ⟨τ₄, r₄, hy₄⟩ := skipT_run (B := W + 1) (ar := "FW") (X := X) (p := 1 + F) (t := ts[v])
    (τ := τ₂.setVar "ta" (1 + F)) (by simp [hX₂]) (by simp [hy₂]) hdv (by omega) hvals
  have hta₄ : τ₄.vars "ta" = 1 + F := by
    rw [r₄.frame_var "ta" (by simp [skipT, skipL, Com.wvars])]; simp
  have r : Run (W + 1) tLoc τ (τ₄.setVar "tl" (toWord ts[v]).length)
      (110 * (((ts.map toWord).flatten).length + ts.length) + 200) := by
    unfold tLoc
    refine (Run.ite_false (by rw [hc1, decide_eq_false h1]) (Run.ite_false
      (by rw [hc3, decide_eq_false h3]) (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂
      (Run.seq (Run.assign (ev_var hy₂ (by omega))) (Run.seq r₄ (Run.assign (v := (toWord ts[v]).length)
        (by
          rw [show (toWord ts[v]).length = (1 + F + (toWord ts[v]).length) - (1 + F) by omega]
          exact ev_sub (ev_var hy₄ (by omega)) (ev_var hta₄ (by omega)) (by omega))))))))).mono ?_
    simp only [Cond.size, Expr.size]
    clear * - hle hv
    generalize (toWord ts[v]).length = tv at *
    generalize ((ts.map toWord).flatten).length = Lf at *
    omega
  have e1 : (τ₄.setVar "tl" (toWord ts[v]).length).vars "ta" = 1 + F := by simp [hta₄]
  have e2 : (τ₄.setVar "tl" (toWord ts[v]).length).vars "tl" = (toWord ts[v]).length := by simp
  refine ⟨_, r, fun _ => ⟨by rw [e1, e2]; omega, ?_⟩, hfr _ r⟩
  rw [e1, e2, seg, show 1 + F = F + 1 by omega, List.drop_succ_cons, hF',
    drop_flatten_take', List.drop_eq_getElem_cons (by simpa using hv), List.flatten_cons]
  simp

/-! ### The end -/

/-- The answer after the evaluation: its last entry. -/
def evEnd : Com :=
  .seq (.assign "fb" (.get "x" (.sub (.add (.var "bA") (.var "bl")) (.lit 1)))) outEnd

theorem evEnd_run {W b0 bit : ℕ} {τ : Env} {X b R : List ℕ}
    (hX : τ.arrs "x" = X) (hb : τ.vars "bA" = b0) (hbl : τ.vars "bl" = b.length)
    (hd : X.drop b0 = b ++ R) (hlast : b.getLast? = some bit) (hbit : bit ≤ 1)
    (hB : b0 + b.length ≤ W) (hW : τ.vars "W" = W) (hW64 : 64 ≤ W)
    (hcap : (τ.arrs "OB").length = W + 1) :
    ∃ τ', Run (W + 1) evEnd τ τ' 320 ∧
      τ'.vars "ovf" = (if maxEntry [0, 1, bit] < W / 32 / 32 then τ.vars "ovf" else 1) ∧
      τ'.out = τ.out ++ [0, 1, bit] := by
  have hbne : b ≠ [] := by intro h; rw [h] at hlast; simp at hlast
  have hbl1 : 1 ≤ b.length := List.length_pos_of_ne_nil hbne
  have hget : X[b0 + b.length - 1]? = some bit := by
    have := congrArg (fun l => l[b.length - 1]?) hd
    simp only [List.getElem?_drop] at this
    rw [show b0 + b.length - 1 = b0 + (b.length - 1) by omega, this,
      List.getElem?_append_left (by omega), ← List.getLast?_eq_getElem?, hlast]
  obtain ⟨τ₁, r₁, h₁, h₂⟩ := outEnd_run (W := W) (bit := bit) (σ := τ.setVar "fb" bit)
    (by simp [hW]) hW64 (by simp) hbit (by simpa using hcap)
  refine ⟨τ₁, (Run.seq (Run.assign (evalB_get (ev_sub (ev_add (ev_var hb (by omega))
    (ev_var hbl (by omega)) (by omega)) (evalB_lit (by omega)) (by omega)) (by rw [hX]; exact hget)
    (by omega))) r₁).mono (by simp [Expr.size]), by rw [h₁]; simp, by rw [h₂]; rfl⟩

end Lax185574Proofs.MC.Glue
