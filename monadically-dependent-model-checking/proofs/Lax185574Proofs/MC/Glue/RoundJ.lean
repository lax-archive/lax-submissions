import Lax185574Proofs.MC.Glue.ApAll

/-!
A round of the glue program of thm:mc after the first.

The round after call `c` gets, after its tag, the state length, the
window, the state `stOf c` and the answer `callY c` of the callee
(`winOf` is the window of the input word that the head of `c` asks for).
`roundJ` reads them (`rdIn`, `ldSc`), and either writes the answer of
the evaluation (`evEnd`), or copies the localized sentence, applies the
answer (`apAll`), sets the fields of the next call (`nxF`) and issues it
(`issue`). `roundJ_run` gives the output of the round for the next call
of `c`, or the final answer after the evaluation.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift

variable {n : ℕ}

/-! ### Sizes of the next state -/

open Lax185574.DistanceMatrix in
theorem next_lengths (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n) (c : PCall n)
    (hval : Valid σ.steps c) {c' : PCall n} (hc' : nextCall hn σ.steps c = some c') :
    (gwOf σ.run σ.steps.length c').length ≤ (gwOf σ.run σ.steps.length c).length +
        (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length ∧
    (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c').length ≤
      (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length +
        (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length := by
  set q := Lax3.FirstOrder.rank φ
  cases c with
  | merge t P Q =>
    have hst : σ.steps[t]? = some (.merge P Q) := hval
    by_cases hPQ : P = Q
    · subst hPQ
      obtain ⟨h1, h2⟩ := self_next σ q hn hst hc'
      rw [h1, h2]; omega
    · obtain ⟨h1, h2⟩ := merge_next σ q hn hst hc'
      have hb : callY σ.run q φ (.merge t P Q) =
          toWord (mans (sAt σ.run t) q P Q) ++ (zR0 ++ uE0) := by
        simp [callY, callYM, callYR, callYE, hPQ]
      have hg : (gwOf σ.run σ.steps.length (.merge t P Q)).length = 1 + n +
          (toWord (sAt σ.run t).edge ++ toWord (sAt σ.run t).nonEdge).length +
          (toWord (distMatrix (sAt σ.run t))).length := by
        show (toWord (sAt σ.run t) ++ toWord (distMatrix (sAt σ.run t))).length = _
        rw [toWord_pg]; simp; omega
      have hfr := length_frames_flatten (mans (sAt σ.run t) q P Q)
      rw [h1, h2, hb, hg, toWord_words]
      simp only [List.length_append, List.length_cons, List.length_map, List.length_ofFn]
      omega
  | resolve t sg P Q =>
    obtain ⟨h1, h2⟩ := resolve_next σ q hn hval hc'
    have hb : callY σ.run q φ (.resolve t sg P Q) = yM0 ++ (toWord (resolveBy (sAt σ.run t) sg P Q) ++
        toWord (distMatrix (resolveBy (sAt σ.run t) sg P Q)) ++
        toWord (family (resolveBy (sAt σ.run t) sg P Q) 1 q)) ++ uE0 := by
      have e3 : ∀ {α β γ : Type} [WordEncoding α] [WordEncoding β] [WordEncoding γ] (x : α) (y : β)
          (z : γ), toWord (x, y, z) = toWord x ++ (toWord y ++ toWord z) := fun _ _ _ => rfl
      simp only [callY, callYM, callYR, callYE, e3, List.append_assoc]
    rw [h1, h2, hb]; simp only [List.length_append]; omega
  | eval a => simp [nextCall] at hc'

/-! ### The command -/

/-- A round after the first, after its tag. -/
noncomputable def roundJ (eM eR eE d : ℕ) : Com :=
  .seq (.seq rdIn ldSc) (.ite (.eq (.var "ck") (.lit 2)) evEnd
    (.seq cpLo (.seq apAll (.seq nxF (issue eM eR eE d)))))

/-- The state after a call. -/
noncomputable def stOf (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) : List ℕ :=
  stW (scOf (n + 3) σ.steps.length (Lax3.FirstOrder.rank φ) c) (gwOf σ.run σ.steps.length c)
    (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c)
    (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ))

/-- The window that the head of a call asks for. -/
noncomputable def winOf (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) : List ℕ :=
  (([n] ++ toWord σ ++ toWord φ).drop (s0Of (n + 3) σ.steps.length c)).take (kOf σ.steps.length c)

theorem winOf_eq (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) :
    (tagOf σ.steps.length c = 2 → ∃ h : ctOf σ.steps.length c + 1 < σ.steps.length,
      winOf σ φ c = stepCode σ.steps[ctOf σ.steps.length c + 1]) ∧
    (tagOf σ.steps.length c ≠ 2 → winOf σ φ c = []) := by
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · have hlt : ctOf σ.steps.length c + 1 < σ.steps.length := by
      unfold tagOf at h2
      split_ifs at h2 with h
      · exact h.2
      · omega
    refine ⟨hlt, ?_⟩
    have := input_window [n] σ (toWord φ) hlt
    simp only [List.length_singleton] at this
    rw [winOf, s0Of, kOf, if_pos h2, if_pos h2, ← this]
    congr 2; omega
  · simp [winOf, kOf, h2]

theorem length_winOf (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) :
    (winOf σ φ c).length = if tagOf σ.steps.length c = 2 then 3 else 0 := by
  obtain ⟨h1, h2⟩ := winOf_eq σ φ c
  by_cases h : tagOf σ.steps.length c = 2
  · obtain ⟨hl, he⟩ := h1 h
    rw [he, if_pos h]
    generalize σ.steps[ctOf σ.steps.length c + 1] = st
    cases st <;> rfl
  · rw [h2 h, if_neg h]; rfl

theorem length_scOf (off m q : ℕ) (c : PCall n) : (scOf off m q c).length = 11 := rfl

theorem tagOf_le2 (m : ℕ) (c : PCall n) : tagOf m c ≤ 2 := by
  unfold tagOf; split_ifs <;> simp

/-! ### Reading the input -/

/-- What a round knows after reading its input. -/
structure JIn (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) (W : ℕ) (τ : Env) : Prop where
  x : ∃ R, τ.arrs "x" = stOf σ φ c ++ callY σ.run (Lax3.FirstOrder.rank φ) φ c ++ R
  xl : (τ.arrs "x").length = W + 1
  fields : HasFields σ.steps.length c τ
  gn : τ.vars "gn" = n
  sm : τ.vars "sm" = σ.steps.length
  off : τ.vars "off" = n + 3
  rk : τ.vars "rk" = Lax3.FirstOrder.rank φ
  gl : τ.vars "gl" = (gwOf σ.run σ.steps.length c).length
  fl : τ.vars "fl" = (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length
  ll : τ.vars "ll" = (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length
  gA : τ.vars "gA" = 14
  fA : τ.vars "fA" = 14 + (gwOf σ.run σ.steps.length c).length
  lA : τ.vars "lA" = 14 + (gwOf σ.run σ.steps.length c).length +
    (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length
  bA : τ.vars "bA" = (stOf σ φ c).length
  bl : τ.vars "bl" = (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length
  win : tagOf σ.steps.length c = 2 → ∀ (h : ctOf σ.steps.length c + 1 < σ.steps.length),
    τ.vars "w0" = (stepCode σ.steps[ctOf σ.steps.length c + 1]).getD 0 0 ∧
    τ.vars "w1" = (stepCode σ.steps[ctOf σ.steps.length c + 1]).getD 1 0 ∧
    τ.vars "w2" = (stepCode σ.steps[ctOf σ.steps.length c + 1]).getD 2 0

theorem roundJ_pre {W : ℕ} (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) {τ : Env}
    {rest : List ℕ} (htg : τ.vars "tg" = tagOf σ.steps.length c)
    (hinp : τ.inp = (stOf σ φ c).length :: winOf σ φ c ++ stOf σ φ c ++
      (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length :: callY σ.run (Lax3.FirstOrder.rank φ) φ c ++
        rest)
    (hxl : (τ.arrs "x").length = W + 1) (hW64 : 64 ≤ W)
    (hent : ∀ e ∈ (stOf σ φ c).length :: winOf σ φ c ++ stOf σ φ c ++
      (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length :: callY σ.run (Lax3.FirstOrder.rank φ) φ c,
      64 * (e + 1) ≤ W + 1) :
    ∃ τ', Run (W + 1) (.seq rdIn ldSc) τ τ' (16 * ((stOf σ φ c).length +
        (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length) + 150) ∧ JIn σ φ c W τ' ∧
      (∀ y ∈ ["W", "ovf", "tg"], τ'.vars y = τ.vars y) ∧ (∀ a, a ≠ "x" → τ'.arrs a = τ.arrs a) ∧
      τ'.out = τ.out := by
  set q := Lax3.FirstOrder.rank φ with hq
  set st := stOf σ φ c with hst
  set b := callY σ.run q φ c with hb
  have hstl : 64 * (st.length + 1) ≤ W + 1 := hent _ (by simp)
  have hbl : 64 * (b.length + 1) ≤ W + 1 := hent _ (by simp)
  have hvst : ∀ v ∈ st ++ b, v < W + 1 := fun v h => by
    have := hent v (by rcases List.mem_append.1 h with h | h <;> simp [h]); omega
  obtain ⟨τ₁, r₁, hsl₁, hbl₁, hx₁, -, hw₁⟩ := rdIn_run (B := W + 1) (τ := τ) (win := winOf σ φ c)
    (st := st) (b := b) (rest := rest) (by rw [htg]; exact lt_of_le_of_lt (tagOf_le2 _ _) (by omega)) (by omega)
    (by rw [htg]; exact length_winOf σ φ c) (by rw [hinp])
    (by rw [hxl]; omega) (by omega) hvst
  have hsc := length_scOf (n + 3) σ.steps.length q c
  obtain ⟨τ₂, r₂, hm₂, hg₂, hf₂, hl₂, hgA₂, hfA₂, hlA₂, hbA₂, hfr₂, ha₂, -, ho₂⟩ :=
    ldSc_run (B := W + 1) (τ := τ₁) (sc := scOf (n + 3) σ.steps.length q c)
      (gw := gwOf σ.run σ.steps.length c) (fw := fwOf σ.run q σ.steps.length c)
      (lw := Lax185574.DistanceLogic.DistFO.code (loc q φ))
      (R := b ++ (τ.arrs "x").drop (st.length + b.length)) hsc
      (by rw [hx₁, List.append_assoc]; rfl)
      (fun v h => hvst v (List.mem_append_left _ h))
      (by
        have : st.length = 11 + 3 + (gwOf σ.run σ.steps.length c).length +
            (fwOf σ.run q σ.steps.length c).length +
            (Lax185574.DistanceLogic.DistFO.code (loc q φ)).length := by
          rw [hst, stOf, length_stW, hsc]
        omega)
      (by rw [hsl₁]; omega)
  simp only [scN, scOf, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm₂
  obtain ⟨h0, hgn, hsm, hoff, hrk, hck, hct, hcv, hcP, hcQ, hcs⟩ := hm₂
  have f₂ : ∀ y, y ∉ ldNames ++ ["gA", "fA", "lA", "bA"] → τ₂.vars y = τ₁.vars y := hfr₂
  have fr : ∀ y ∈ ["W", "ovf", "tg", "bl", "w0", "w1", "w2"], y ∉ ldNames ++ ["gA", "fA", "lA", "bA"] := by
    decide
  have hr : Run (W + 1) (.seq rdIn ldSc) τ τ₂ (16 * (st.length + b.length) + 150) :=
    (Run.seq r₁ r₂).mono (by omega)
  refine ⟨τ₂, hr, ⟨⟨(τ.arrs "x").drop (st.length + b.length), by rw [ha₂, hx₁]⟩, by
      rw [run_length_arrs hr, hxl], ⟨hck, hct, hcv, hcP, hcQ, hcs⟩, hgn, hsm, hoff, hrk, hg₂, hf₂,
      hl₂, hgA₂, hfA₂, hlA₂, by rw [hbA₂, hsl₁], by rw [f₂ "bl" (fr _ (by simp)), hbl₁], ?_⟩,
    fun y hy => ?_, fun a ha => ?_, by rw [ho₂, r₁.out_eq (by simp [rdIn, rdWin, readInto, readOne,
      Com.NoWrite])]⟩
  · intro h2 hlt
    obtain ⟨hw0, hw1, hw2⟩ := hw₁ (by rw [htg]; exact h2)
    obtain ⟨_, he⟩ := (winOf_eq σ φ c).1 h2
    rw [he] at hw0 hw1 hw2
    refine ⟨?_, ?_, ?_⟩
    · rw [f₂ "w0" (fr _ (by simp)), hw0]
    · rw [f₂ "w1" (fr _ (by simp)), hw1]
    · rw [f₂ "w2" (fr _ (by simp)), hw2]
  · rw [f₂ y (fr y (by simp at hy ⊢; tauto))]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> exact r₁.frame_var _ (by decide)
  · rw [ha₂]; exact r₁.frame_arr a (by simp [rdIn, rdWin, readInto, readOne, Com.warrs]; exact ha)

/-! ### A round with a next call -/

/-- The cost of a round after the first. -/
noncomputable def roundJC (eM eR eE d L : ℕ) : ℕ := 500 * L + 2000 + issueC eM eR eE d (2 * L)

set_option maxHeartbeats 1000000 in
theorem roundJ_call {W eM eR eE d : ℕ} (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n)
    (c : PCall n) (hval : Valid σ.steps c) (hne : ∀ a, c ≠ .eval a) {c' : PCall n}
    (hc' : nextCall hn σ.steps c = some c') (hval' : Valid σ.steps c') {τ : Env}
    (hJ : JIn σ φ c W τ) (hW : τ.vars "W" = W) (hW64 : 64 ≤ W) (hovf : τ.vars "ovf" = 0)
    (hcap : ∀ a ∈ ["U", "GW", "FW", "lo", "OB"], (τ.arrs a).length = W + 1)
    (hvals : ValsLt (W + 1) τ)
    (hsz : 16 * ((stOf σ φ c).length + (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length + n +
      σ.steps.length + 1) ≤ W + 1) :
    let q := Lax3.FirstOrder.rank φ
    let lw := Lax185574.DistanceLogic.DistFO.code (loc q φ)
    let gw := gwOf σ.run σ.steps.length c'
    let fw := fwOf σ.run q σ.steps.length c'
    let o := hdOf σ.run q (n + 3) σ.steps.length lw c' ++ callQ σ.run q φ c'
    let u := workQ σ.run q φ c'
    ∃ τ', Run (W + 1) (.seq cpLo (.seq apAll (.seq nxF (issue eM eR eE d)))) τ τ'
        (400 * ((stOf σ φ c).length + (callY σ.run q φ c).length + n) + 800 +
          issueC eM eR eE d (2 * ((stOf σ φ c).length + (callY σ.run q φ c).length + n))) ∧
      (τ'.vars "ovf" = 0 → τ'.out = τ.out ++ o ∧ maxEntry o < W / 32 / 32 ∧
        min ((u.length + maxEntry u + 1) ^ (expOf eM eR eE (ckOf c') + 1)) W ≤ W / min (2 ^ d) W) ∧
      (dK + gw.length + fw.length + lw.length < W / 8 → maxEntry o < W / 32 / 32 →
        min ((u.length + maxEntry u + 1) ^ (expOf eM eR eE (ckOf c') + 1)) W ≤ W / min (2 ^ d) W →
        τ'.vars "ovf" = 0) := by
  intro q lw gw fw o u
  obtain ⟨⟨R, hX⟩, hxl, hf, hgn, hsm, hoff, hrk, hgl, hfl, hll, hgA, hfA, hlA, hbA, hbl, hwin⟩ := hJ
  set X := τ.arrs "x" with hXdef
  set st := stOf σ φ c with hst
  set b := callY σ.run q φ c with hb
  have hstl : st.length = 14 + (gwOf σ.run σ.steps.length c).length +
      (fwOf σ.run q σ.steps.length c).length + lw.length := by
    rw [hst, stOf, length_stW, length_scOf]
  have hXv : ∀ v ∈ X, v ≤ W := fun v h => by have := hvals.2.1 "x" v h; omega
  have eq1 : lw.length = (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length :=
    rfl
  have eq2 : b.length = (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length := rfl
  have eq3 : gw.length = (gwOf σ.run σ.steps.length c').length := rfl
  have eq4 : fw.length = (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c').length := rfl
  have eq6 : (fwOf σ.run q σ.steps.length c).length =
    (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length := rfl
  have hXd : X.drop 14 = gwOf σ.run σ.steps.length c ++ fwOf σ.run q σ.steps.length c ++ lw ++ b ++ R := by
    have hsc3 : (scOf (n + 3) σ.steps.length q c ++ [(gwOf σ.run σ.steps.length c).length,
        (fwOf σ.run q σ.steps.length c).length, lw.length]).length = 14 := by simp [length_scOf]
    rw [hX, hst, stOf, stW]
    have e : ∀ (A B C D E F G : List ℕ), A ++ B ++ C ++ D ++ E ++ F ++ G = (A ++ B) ++ (C ++ D ++ E ++ F ++ G) :=
      fun A B C D E F G => by simp
    rw [e, List.drop_left' hsc3]
  have hdL : X.drop (14 + (gwOf σ.run σ.steps.length c).length + (fwOf σ.run q σ.steps.length c).length) =
      lw ++ (b ++ R) := by
    have h1 := drop_add_of_drop (u := gwOf σ.run σ.steps.length c)
      (r := fwOf σ.run q σ.steps.length c ++ lw ++ b ++ R) (by rw [hXd]; simp)
    have h2 := drop_add_of_drop (u := fwOf σ.run q σ.steps.length c) (r := lw ++ b ++ R)
      (by rw [h1]; simp)
    rw [h2]; simp
  -- the localized sentence
  obtain ⟨τ₁, r₁, F₁, fv₁, fa₁, fl₁, fi₁, fo₁⟩ := cpLo_run (W := W) (σ := τ) (X := X) (lw := lw)
    (R := b ++ R) (a := 14 + (gwOf σ.run σ.steps.length c).length +
      (fwOf σ.run q σ.steps.length c).length) rfl hlA hll hdL
    (by rw [hcap "lo" (by simp)]; omega) (by omega) hXv (by omega)
  have hv₁ := Run.vals_lt r₁ hvals
  have e₁ : ∀ y, y ∉ ["ca", "cl", "ci", "lp"] → τ₁.vars y = τ.vars y := fv₁
  obtain ⟨hck, hct, hcv, hcP, hcQ, hcs⟩ := hf
  have hf₁ : HasFields σ.steps.length c τ₁ := ⟨by rw [e₁ _ (by decide), hck],
    by rw [e₁ _ (by decide), hct], by rw [e₁ _ (by decide), hcv], by rw [e₁ _ (by decide), hcP],
    by rw [e₁ _ (by decide), hcQ], by rw [e₁ _ (by decide), hcs]⟩
  have hPQ₁ : cPOf c ≤ W ∧ cQOf c ≤ W := by
    have h1 := hv₁.1 "cP"; have h2 := hv₁.1 "cQ"
    rw [hf₁.2.2.2.1] at h1; rw [hf₁.2.2.2.2.1] at h2; omega
  obtain ⟨τ₂, r₂, hFF, hx₂, fv₂, fa₂, fl₂, fi₂, fo₂⟩ := apAll_run (W := W) σ φ hn c hval hne
    (τ := τ₁) (X := X) (R := R) (by rw [fa₁ "x" (by decide)]) hf₁ (by rw [e₁ _ (by decide), hgn])
    (by rw [e₁ _ (by decide), hgA]) (by rw [e₁ _ (by decide), hfA]) (by rw [e₁ _ (by decide), hgl])
    (by rw [e₁ _ (by decide), hfl]) (by rw [e₁ _ (by decide), hbA, hstl])
    (by rw [e₁ _ (by decide), hbl]) hXd (by omega) (by rw [hxl]; omega)
    (by rw [fa₁ "GW" (by decide), hcap "GW" (by simp)]; omega)
    (by rw [fa₁ "FW" (by decide), hcap "FW" (by simp)]; omega) hXv hPQ₁
  obtain ⟨FG₂, FF₂⟩ := hFF c' hc'
  have hv₂ := Run.vals_lt r₂ hv₁
  have e₂ : ∀ y, y ∉ apVars → y ∉ ["ca", "cl", "ci", "lp"] → τ₂.vars y = τ.vars y := fun y h1 h2 => by
    rw [fv₂ y h1, e₁ y h2]
  have hf₂ : HasFields σ.steps.length c τ₂ := ⟨by rw [e₂ _ (by decide) (by decide), hck],
    by rw [e₂ _ (by decide) (by decide), hct], by rw [e₂ _ (by decide) (by decide), hcv],
    by rw [e₂ _ (by decide) (by decide), hcP], by rw [e₂ _ (by decide) (by decide), hcQ],
    by rw [e₂ _ (by decide) (by decide), hcs]⟩
  have hU₂ : (τ₂.arrs "U").length = W + 1 := by
    rw [fa₂ "U" (by decide) (by decide), fa₁ "U" (by decide), hcap "U" (by simp)]
  have hoff₂ : τ₂.vars "off" = n + 3 := by rw [e₂ _ (by decide) (by decide), hoff]
  obtain ⟨τ₃, r₃, hF₃, fv₃, fa₃, fl₃, fi₃, fo₃⟩ := nxF_run (W := W) (m := σ.steps.length) (τ := τ₂)
    hn σ.steps rfl c hval hne hf₂ (by rw [e₂ _ (by decide) (by decide), hgn])
    (by rw [e₂ _ (by decide) (by decide), hsm]) (by omega) (by omega) (by omega)
    (by rw [hoff₂, hU₂]; omega) (by rw [hoff₂]; omega)
    (fun y hy => by have := hv₂.1 y; omega)
    (fun h2 hlt => by
      obtain ⟨a1, a2, a3⟩ := hwin h2 hlt
      exact ⟨by rw [e₂ _ (by decide) (by decide), a1], by rw [e₂ _ (by decide) (by decide), a2],
        by rw [e₂ _ (by decide) (by decide), a3]⟩)
  have hv₃ := Run.vals_lt r₃ hv₂
  have e₃ : ∀ y, y ∉ ["ck", "ct", "cv", "cP", "cQ", "cs", "op"] → τ₃.vars y = τ₂.vars y := fv₃
  have hlo₃ : Filled "lo" "lp" lw τ₃ := F₁.congr (by
      rw [e₃ _ (by decide), fv₂ _ (by decide)])
    (by rw [fa₃ "lo" (by decide), fa₂ "lo" (by decide) (by decide)])
  have hGW₃ := FG₂.congr (e₃ "pg" (by decide)) (fa₃ "GW" (by decide))
  have hFW₃ := FF₂.congr (e₃ "pf" (by decide)) (fa₃ "FW" (by decide))
  obtain ⟨hgl', hfl'⟩ := next_lengths σ φ hn c hval hc'
  obtain ⟨τ₄, r₄, hS, hC⟩ := issue_run (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d) σ φ hn c'
    hval' (τ := τ₃) (by rw [e₃ _ (by decide), e₂ _ (by decide) (by decide), hrk]) (hF₃ c' hc')
    (by rw [e₃ _ (by decide), e₂ _ (by decide) (by decide), hgn])
    (by rw [e₃ _ (by decide), e₂ _ (by decide) (by decide), hsm])
    (by rw [e₃ _ (by decide), hoff₂]) (by rw [e₃ _ (by decide), e₂ _ (by decide) (by decide), hW])
    hW64 (by rw [e₃ _ (by decide), e₂ _ (by decide) (by decide), hovf]) hGW₃ hFW₃ hlo₃
    (by rw [fl₃ "OB", fl₂ "OB", fa₁ "OB" (by decide), hcap "OB" (by simp)]) hv₃ (by omega) (by omega)
  refine ⟨τ₄, ?_, fun h => ?_, hC⟩
  · refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ r₄))).mono ?_
    have hmono : issueC eM eR eE d (gw.length + fw.length + lw.length + n) ≤
        issueC eM eR eE d (2 * (st.length + b.length + n)) := by
      unfold issueC; omega
    have eqI : issueC eM eR eE d (gw.length + fw.length + lw.length + n) =
        issueC eM eR eE d ((gwOf σ.run σ.steps.length c').length +
          (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c').length +
          (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length + n) := rfl
    omega
  · obtain ⟨ho, hE, hG⟩ := hS h
    exact ⟨by rw [ho, fo₃, fo₂, fo₁], hE, hG⟩

/-! ### The round -/

theorem nextCall_some (hn : 0 < n) (steps : List Step) (c : PCall n) (hne : ∀ a, c ≠ .eval a) :
    ∃ c', nextCall hn steps c = some c' := by
  cases c with
  | merge => exact ⟨_, rfl⟩
  | resolve => exact ⟨_, rfl⟩
  | eval a => exact absurd rfl (hne a)

set_option maxHeartbeats 1000000 in
/-- **A round after the first.** -/
theorem roundJ_run {W eM eR eE d : ℕ} (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n)
    (c : PCall n) (hval : Valid σ.steps c)
    (hval' : ∀ c', nextCall hn σ.steps c = some c' → Valid σ.steps c') {τ : Env} {rest : List ℕ}
    (hW : τ.vars "W" = W) (hW64 : 64 ≤ W) (hovf : τ.vars "ovf" = 0)
    (htg : τ.vars "tg" = tagOf σ.steps.length c)
    (hinp : τ.inp = (stOf σ φ c).length :: winOf σ φ c ++ stOf σ φ c ++
      (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length :: callY σ.run (Lax3.FirstOrder.rank φ) φ c ++
        rest)
    (hcap : ∀ a ∈ ["x", "U", "GW", "FW", "lo", "OB"], (τ.arrs a).length = W + 1)
    (hvals : ValsLt (W + 1) τ)
    (hent : ∀ e ∈ (stOf σ φ c).length :: winOf σ φ c ++ stOf σ φ c ++
      (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length :: callY σ.run (Lax3.FirstOrder.rank φ) φ c,
      64 * (e + 1) ≤ W + 1)
    (hsz : 16 * ((stOf σ φ c).length + (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length + n +
      σ.steps.length + 1) ≤ W + 1) :
    ∃ τ', Run (W + 1) (roundJ eM eR eE d) τ τ' (roundJC eM eR eE d ((stOf σ φ c).length +
        (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length + n)) ∧
      (∀ c', nextCall hn σ.steps c = some c' →
        (τ'.vars "ovf" = 0 → τ'.out = τ.out ++ (hdOf σ.run (Lax3.FirstOrder.rank φ) (n + 3)
            σ.steps.length (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) c' ++
            callQ σ.run (Lax3.FirstOrder.rank φ) φ c') ∧
          maxEntry (hdOf σ.run (Lax3.FirstOrder.rank φ) (n + 3) σ.steps.length
            (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) c' ++
            callQ σ.run (Lax3.FirstOrder.rank φ) φ c') < W / 32 / 32 ∧
          min (((workQ σ.run (Lax3.FirstOrder.rank φ) φ c').length +
            maxEntry (workQ σ.run (Lax3.FirstOrder.rank φ) φ c') + 1) ^
              (expOf eM eR eE (ckOf c') + 1)) W ≤ W / min (2 ^ d) W) ∧
        (dK + (gwOf σ.run σ.steps.length c').length +
            (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c').length +
            (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length < W / 8 →
          maxEntry (hdOf σ.run (Lax3.FirstOrder.rank φ) (n + 3) σ.steps.length
            (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) c' ++
            callQ σ.run (Lax3.FirstOrder.rank φ) φ c') < W / 32 / 32 →
          min (((workQ σ.run (Lax3.FirstOrder.rank φ) φ c').length +
            maxEntry (workQ σ.run (Lax3.FirstOrder.rank φ) φ c') + 1) ^
              (expOf eM eR eE (ckOf c') + 1)) W ≤ W / min (2 ^ d) W → τ'.vars "ovf" = 0)) ∧
      (nextCall hn σ.steps c = none →
        τ'.out = τ.out ++ (0 :: finAns σ.run (Lax3.FirstOrder.rank φ) φ) ∧
        τ'.vars "ovf" = if maxEntry (0 :: finAns σ.run (Lax3.FirstOrder.rank φ) φ) < W / 32 / 32
          then 0 else 1) := by
  obtain ⟨τ₂, r₂, hJ, fv₂, fa₂, fo₂⟩ := roundJ_pre (W := W) σ φ c htg hinp (hcap "x" (by simp)) hW64
    hent
  have hv₂ := Run.vals_lt r₂ hvals
  have hck : τ₂.vars "ck" = ckOf c := hJ.fields.1
  have hc2 := condEq_lit (B := W + 1) (d := 2) hck (by have := ckOf_le c; omega) (by omega)
  have hW₂ : τ₂.vars "W" = W := by rw [fv₂ "W" (by simp), hW]
  have hovf₂ : τ₂.vars "ovf" = 0 := by rw [fv₂ "ovf" (by simp), hovf]
  have hcap₂ : ∀ a ∈ ["U", "GW", "FW", "lo", "OB"], (τ₂.arrs a).length = W + 1 := fun a ha => by
    rw [fa₂ a (by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide),
      hcap a (by simp at ha ⊢; tauto)]
  by_cases he : ∃ a, c = .eval a
  · obtain ⟨a, rfl⟩ := he
    have ha0 : a = ⟨0, hn⟩ := Fin.ext hval
    subst ha0
    have hk : ckOf (PCall.eval ⟨0, hn⟩ : PCall n) = 2 := rfl
    obtain ⟨R, hX⟩ := hJ.x
    obtain ⟨bit, hbit, hbit1⟩ : ∃ bit, callYE σ.run (Lax3.FirstOrder.rank φ) φ (.eval ⟨0, hn⟩) = [bit] ∧
        bit ≤ 1 := by
      simp only [callYE, Lax185574Proofs.Legacy.toWord_bool]; exact ⟨_, rfl, by split <;> omega⟩
    have hb : callY σ.run (Lax3.FirstOrder.rank φ) φ (.eval ⟨0, hn⟩) = yM0 ++ zR0 ++ [bit] := by
      rw [callY, hbit]; rfl
    have hfin : finAns σ.run (Lax3.FirstOrder.rank φ) φ = [1, bit] := by
      simp only [finAns, dif_pos hn, hbit]
    obtain ⟨τ₃, r₃, hov₃, ho₃⟩ := evEnd_run (W := W) (b0 := (stOf σ φ (.eval ⟨0, hn⟩)).length) (bit := bit)
      (τ := τ₂) (X := τ₂.arrs "x") (b := callY σ.run (Lax3.FirstOrder.rank φ) φ (.eval ⟨0, hn⟩)) (R := R)
      rfl hJ.bA hJ.bl (by rw [hX]; simp) (by rw [hb]; simp) hbit1
      (by omega) hW₂ hW64 (hcap₂ "OB" (by simp))
    refine ⟨τ₃, (Run.seq r₂ (Run.ite_true (by rw [hc2, hk]; rfl) r₃)).mono ?_, fun c' hc' => by
      simp [nextCall] at hc', fun _ => ⟨by rw [ho₃, fo₂, hfin], by rw [hov₃, hovf₂, hfin]⟩⟩
    unfold roundJC issueC; simp only [Cond.size, Expr.size]; omega
  · have hne : ∀ a, c ≠ .eval a := fun a h => he ⟨a, h⟩
    have hk : ckOf c ≠ 2 := by
      cases c with
      | merge t P Q => show (if P = Q then 3 else 0) ≠ 2; split_ifs <;> decide
      | resolve => simp [ckOf]
      | eval a => exact absurd rfl (hne a)
    obtain ⟨c', hc'⟩ := nextCall_some hn σ.steps c hne
    obtain ⟨τ₃, r₃, hS, hC⟩ := roundJ_call (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d) σ φ hn c
      hval hne hc' (hval' c' hc') hJ hW₂ hW64 hovf₂ hcap₂ hv₂ hsz
    refine ⟨τ₃, (Run.seq r₂ (Run.ite_false (by rw [hc2, decide_eq_false hk]) r₃)).mono ?_,
      fun c'' hc'' => ?_, fun h => by rw [hc'] at h; cases h⟩
    · unfold roundJC; simp only [Cond.size, Expr.size]; omega
    · rw [hc'] at hc''; cases hc''
      exact ⟨fun h => by obtain ⟨a1, a2, a3⟩ := hS h; exact ⟨by rw [a1, fo₂], a2, a3⟩, hC⟩

end Lax185574Proofs.MC.Glue
