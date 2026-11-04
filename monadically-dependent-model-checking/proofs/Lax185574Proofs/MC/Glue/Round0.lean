import Lax185574Proofs.MC.Glue.Init

/-!
Round 0 of the glue program of thm:mc, up to the output.

The input word is `x = g ++ toWord σ ++ toWord φ` for a prefix `g`, read
into `U`, with `gn = n`, `gL = |g|`, `sm` the number of steps and `off`
the position of the steps. For `n ≥ 1`, `r0Main` computes the
rank `q` of the sentence, the bound `zM = min (glM q) W` on the initial
trees, and checks `glM q < W / 8` and `n (glM q + 3 + n) < W / 8`, again with
`ovf` set if a check fails. Once both pass, every value of the remaining
phases fits: the table of radii, the localization of the sentence in
`lo`, the initial words of the partial graph and of its matrix of
distances in `GW`, and of the family of trees in `FW`.

The input entries are assumed below `(W + 1) / 64`, which the input
shift of the glue program provides, so that small multiples of `|x|`
need no check.
-/

namespace Lax185574Proofs.MC.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax271696.GraphEncoding
open Lax3.FirstOrder

/-! ### The command -/

/-- The phases after a passed check. -/
def r0Fill : Com :=
  .seq (.assign "zc9" (.lit 9)) (.seq rpTab
  (.seq (.assign "fp" (.add (.var "off") (.add (.var "sm") (.add (.var "sm") (.var "sm")))))
  (.seq (.assign "fm" (.lit 1)) (.seq fWalk (.seq gwInit fwInit)))))

/-- The size check of the family of initial trees. -/
def r0Chk2 : Com :=
  .seq (.assign "zx" (.add (.add (.var "zM") (.lit 3)) (.var "gn"))) (.seq (satMul "gn" "zx" "zy")
    (.ite (.lt (.var "zy") (.div (.var "W") (.lit 8))) r0Fill (.assign "ovf" (.lit 1))))

/-- Rank, bound, checks and the initial words, for `n ≥ 1`. -/
def r0Main : Com :=
  .seq (.assign "fm" (.lit 0)) (.seq fWalk (.seq mBound
    (.ite (.lt (.var "zM") (.div (.var "W") (.lit 8))) r0Chk2 (.assign "ovf" (.lit 1)))))

/-! ### Arithmetic facts -/

theorem nine_pow_le_glM (q : ℕ) : 9 ^ ((q + 1) * q) ≤ glM q := by
  have h1 : 9 ^ ((q + 1) * q) ≤ glP q :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : glP q ≤ glC q := by
    simp only [glC, glA]
    have : 1 ≤ 20 * ((q + 1) * (q + 1)) := by nlinarith
    nlinarith
  have h3 : glC q ≤ glM q := by
    simp only [glM]
    have : 1 ≤ (glA q + 1) ^ (q + 1) := Nat.one_le_pow _ _ (by simp [glA])
    nlinarith
  omega

theorem iL_le_glM (q : ℕ) : iL q ≤ glM q := lvlLen_le_glM' q

theorem condLt_div {B : ℕ} {τ : Env} {x : String} {a W d : ℕ} (hx : τ.vars x = a)
    (hW : τ.vars "W" = W) (hWB : W < B) (haB : a < B) (hdB : d < B) :
    (Cond.lt (.var x) (.div (.var "W") (.lit d))).evalB B τ = some (decide (a < W / d)) :=
  evalB_condLt (ev_var hx haB) (evalB_bin (ev_var hW hWB) (evalB_lit hdB)
    (by simp only [Bop.apply]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hWB))

theorem condEq_lit {B : ℕ} {τ : Env} {x : String} {a d : ℕ} (hx : τ.vars x = a) (haB : a < B)
    (hdB : d < B) : (Cond.eq (.var x) (.lit d)).evalB B τ = some (decide (a = d)) := by
  rw [evalB_condEq (ev_var hx haB) (evalB_lit hdB)]
  by_cases h : a = d <;> simp [h]

/-! ### The result -/

/-- The state after a successful round 0. -/
structure R0Out (W n q : ℕ) (x : List ℕ) (gl m : ℕ) (c : ℕ → ℕ) (lw : List ℕ) (τ : Env) :
    Prop where
  ovf : τ.vars "ovf" = 0
  vW : τ.vars "W" = W
  gn : τ.vars "gn" = n
  gL : τ.vars "gL" = gl
  sm : τ.vars "sm" = m
  off : τ.vars "off" = gl + n + 2
  rk : τ.vars "rk" = q
  U : (τ.arrs "U").take x.length = x
  GW : Filled "GW" "pg" (gd0 n c) τ
  FW : Filled "FW" "pf" (fw0 n q c) τ
  lo : Filled "lo" "lp" lw τ
  bM : glM q < W / 8
  bF : n * (glM q + 3 + n) < W / 8

/-- The cost of round 0 per entry of the input. -/
def r0C (q : ℕ) : ℕ :=
  1000 + 23 * ((q + 2) * (q + 1)) + 23 * (q + 1) + q * (23 * ((q + 1) * q) + 80) + initCost q

/-! ### The phases after the checks -/

theorem mem_of_getElem?_some {l : List ℕ} {i v : ℕ} (h : l[i]? = some v) : v ∈ l :=
  List.mem_of_getElem? h

theorem getElem?_append_of_some {l r : List ℕ} {i v : ℕ} (h : l[i]? = some v) :
    (l ++ r)[i]? = some v := by
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem?_append_left hi]; exact h

section fill

variable {W n : ℕ} {g : List ℕ} {sc : Script n} {φ : FO 0}
  {rU : List ℕ}

theorem r0Fill_run {τ : Env} (hW : τ.vars "W" = W)
    (hrk : τ.vars "rk" = rank φ) (hgn : τ.vars "gn" = n) (hgL : τ.vars "gL" = g.length)
    (hoff : τ.vars "off" = g.length + n + 2) (hsm : τ.vars "sm" = sc.steps.length)
    (hU : τ.arrs "U" = (g ++ toWord sc ++ toWord φ) ++ rU)
    (hcap : ∀ a ∈ ["stk", "lo", "RP", "GW", "FW", "ta", "tb"], (τ.arrs a).length = W + 1)
    (hx : ∀ v ∈ g ++ toWord sc ++ toWord φ, 64 * (v + 1) ≤ W + 1)
    (hxl : 64 * ((g ++ toWord sc ++ toWord φ).length + 1) ≤ W + 1)
    (hM : glM (rank φ) < W / 8) (hF : n * (glM (rank φ) + 3 + n) < W / 8) :
    ∃ τ', Run (W + 1) r0Fill τ τ' (rank φ * (23 * ((rank φ + 1) * rank φ) + 80) +
        124 * (g ++ toWord sc ++ toWord φ).length + n * (initCost (rank φ) + 96) + 300 +
        50 * (n + 1) ^ 2) ∧
      τ'.vars "W" = W ∧ τ'.vars "rk" = rank φ ∧ τ'.vars "gn" = n ∧ τ'.vars "gL" = g.length ∧
      τ'.vars "off" = g.length + n + 2 ∧ τ'.vars "sm" = sc.steps.length ∧
      (∀ y ∈ ["ovf"], τ'.vars y = τ.vars y) ∧ τ'.arrs "U" = τ.arrs "U" ∧
      Filled "GW" "pg" (gd0 n (inCol (g ++ toWord sc ++ toWord φ) g.length)) τ' ∧
      Filled "FW" "pf" (fw0 n (rank φ) (inCol (g ++ toWord sc ++ toWord φ) g.length)) τ' ∧
      Filled "lo" "lp" (Lax185574.DistanceLogic.DistFO.code (loc (rank φ) φ)) τ' := by
  set x := g ++ toWord sc ++ toWord φ with hxdef
  set q := rank φ with hq
  set B := W + 1 with hBdef
  have hxlen : x.length = g.length + n + 2 + 3 * sc.steps.length + (toWord φ).length := by
    simp only [hxdef, List.length_append, toWord_script, List.length_cons, List.length_ofFn,
      length_flatten_stepCode]; omega
  have hfcx : (Lax185574.InstanceEncoding.code φ).length ≤ x.length := by
    have : (toWord φ).length = (Lax185574.InstanceEncoding.code φ).length := by
      rw [Lax185574Proofs.Legacy.encode_eq_foCode]
    omega
  have hfc : (toWord φ).length = (Lax185574.InstanceEncoding.code φ).length := by
    rw [Lax185574Proofs.Legacy.encode_eq_foCode]
  have hqx : q ≤ x.length := (rank_le_code φ).trans hfcx
  have hW63 : 63 ≤ W := by omega
  have hP : 9 ^ ((q + 1) * q) ≤ W := by
    have := nine_pow_le_glM q; have := Nat.div_le_self W 8; omega
  -- the table of radii
  set τ₁ := τ.setVar "zc9" 9 with hτ₁
  obtain ⟨τ₂, r₂, hRP, fa₂⟩ := rpTab_run (B := B) (W := W) (q := q) (σ := τ₁) (by simp [hτ₁, hW])
    (by omega) (by simp [hτ₁, hrk]) (by simp [hτ₁]) (by omega) (by omega) hP
    (by simp [hτ₁, hcap "RP" (by simp)]; omega)
  have v₂ : ∀ y ∈ ["W", "rk", "gn", "gL", "off", "sm", "ovf"], τ₂.vars y = τ.vars y := by
    intro y hy
    rw [r₂.frame_var y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)]
    simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hτ₁]
  have p₀ : g.length + n + 2 + 3 * sc.steps.length < B := by omega
  set τ₄ := (τ₂.setVar "fp" (g.length + n + 2 + 3 * sc.steps.length)).setVar "fm" 1 with hτ₄
  have r₃ : Run B (.assign "fp" (.add (.var "off") (.add (.var "sm") (.add (.var "sm")
      (.var "sm"))))) τ₂ (τ₂.setVar "fp" (g.length + n + 2 + 3 * sc.steps.length)) 8 := by
    have e1 := v₂ "off" (by simp); have e2 := v₂ "sm" (by simp)
    refine (Run.assign ?_).mono (by simp)
    rw [show g.length + n + 2 + 3 * sc.steps.length = (g.length + n + 2) + (sc.steps.length +
      (sc.steps.length + sc.steps.length)) by omega]
    exact ev_add (ev_var (by rw [e1, hoff]) (by omega)) (ev_add (ev_var (by rw [e2, hsm]) (by omega))
      (ev_add (ev_var (by rw [e2, hsm]) (by omega)) (ev_var (by rw [e2, hsm]) (by omega))
        (by omega)) (by omega)) (by omega)
  -- the localization
  have hU₄ : (τ₄.arrs "U").drop (g.length + n + 2 + 3 * sc.steps.length) =
      Lax185574.InstanceEncoding.code φ ++ rU := by
    rw [show τ₄.arrs "U" = τ.arrs "U" by simp [hτ₄, fa₂ "U" (by decide), hτ₁], hU,
      List.drop_append_of_le_length (by omega), input_formula,
      Lax185574Proofs.Legacy.encode_eq_foCode]
  have hC₄ : FCtx B q φ (g.length + n + 2 + 3 * sc.steps.length) τ₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hτ₄, fa₂ "stk" (by decide), hτ₁, hcap "stk" (by simp)]; omega
    · intro _; simp [hτ₄, fa₂ "lo" (by decide), hτ₁, hcap "lo" (by simp)]; omega
    · intro _ d hd
      refine ⟨by simpa [hτ₄] using hRP d hd, ?_⟩
      rw [rhoPlus_eq_pow hd]
      show 9 ^ ((q + 1) * (q - d)) < B
      have : 9 ^ ((q + 1) * (q - d)) ≤ 9 ^ ((q + 1) * q) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
      omega
    · omega
    · simp [hτ₄]; omega
  obtain ⟨τ₅, r₅, hrk₅, -, hlo₅⟩ := fWalk_run (q := q) (R := rU) (by simp [hτ₄]) hU₄ hC₄
  have hlo₅' := hlo₅ (by simp [hτ₄])
  have v₅ : ∀ y ∈ ["W", "gn", "gL", "off", "sm", "ovf"], τ₅.vars y = τ.vars y := by
    intro y hy
    rw [r₅.frame_var y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)]
    have := v₂ y (by simp at hy ⊢; tauto)
    simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [hτ₄] using this
  have a₅ : ∀ a ∈ ["U", "GW", "FW", "ta", "tb"], τ₅.arrs a = τ.arrs a := by
    intro a ha
    have ha' : a ≠ "RP" := by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [r₅.frame_arr a (by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide)]
    simp [hτ₄, fa₂ a ha', hτ₁]
  -- the words
  set c := inCol x g.length with hc
  have hcol : ∀ k < n, (τ₅.arrs "U")[g.length + 1 + k]? = some (c k) := by
    intro k hk
    rw [a₅ "U" (by simp), hU]
    exact getElem?_append_of_some (inCol_spec g sc (toWord φ) hk).1
  have hcB : ∀ k < n, 64 * (c k + 1) ≤ W + 1 := fun k hk =>
    hx _ (mem_of_getElem?_some (inCol_spec g sc (toWord φ) hk).1)
  have hnx : n ≤ x.length := by omega
  have hFe : n * (glM q + 3 + n) + n = n * (glM q + 3) + n * (n + 1) := by ring
  obtain ⟨τ₆, r₆, F₆⟩ := gwInit_run (B := B) (n := n) (gl := g.length) (c := c) (σ := τ₅)
    (by rw [v₅ "gn" (by simp), hgn]) (by rw [v₅ "gL" (by simp), hgL]) hcol
    (fun k hk => by have := hcB k hk; omega) (by rw [a₅ "GW" (by simp), hcap "GW" (by simp)]; omega)
    (by omega) (by omega)
  have v₆ : ∀ y ∈ ["W", "gn", "gL", "off", "sm", "ovf", "rk", "lp"], τ₆.vars y = τ₅.vars y := by
    intro y hy
    exact r₆.frame_var y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)
  have hiL := iL_le_glM q
  have hnF : n * (iL q + 3) ≤ n * (glM q + 3) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨τ₇, r₇, F₇⟩ := fwInit_run (B := B) (n := n) (gl := g.length) (q := q) (cap := W + 1)
    (capF := W + 1) (c := c) (σ := τ₆)
    (by rw [v₆ "gn" (by simp), v₅ "gn" (by simp), hgn]) (by rw [v₆ "gL" (by simp), v₅ "gL" (by simp), hgL])
    (by rw [v₆ "rk" (by simp), hrk₅])
    (fun k hk => by rw [r₆.frame_arr _ (by decide)]; exact hcol k hk)
    (fun k hk => by have := hcB k hk; have := Nat.div_mul_le_self W 8; omega)
    (by rw [r₆.frame_arr _ (by decide), a₅ "ta" (by simp), hcap "ta" (by simp)])
    (by rw [r₆.frame_arr _ (by decide), a₅ "tb" (by simp), hcap "tb" (by simp)])
    (by have := Nat.div_le_self W 8; omega)
    (by rw [r₆.frame_arr _ (by decide), a₅ "FW" (by simp), hcap "FW" (by simp)])
    (by have := Nat.div_le_self W 8; omega) (by have := Nat.div_le_self W 8; omega) (by omega)
    (by omega)
  have v₇ : ∀ y ∈ ["W", "gn", "gL", "off", "sm", "ovf", "rk", "lp", "pg"], τ₇.vars y = τ₆.vars y := by
    intro y hy
    exact r₇.frame_var y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> decide)
  refine ⟨τ₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F₇, ?_⟩
  · unfold r0Fill
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂ (Run.seq r₃ (Run.seq
      (Run.assign (evalB_lit (by omega))) (Run.seq r₅ (Run.seq r₆ r₇)))))).mono ?_
    simp only [Expr.size]
    have := hfcx
    generalize (n + 1) ^ 2 = S at *
    generalize initCost q = I at *
    nlinarith
  · rw [v₇ "W" (by simp), v₆ "W" (by simp), v₅ "W" (by simp), hW]
  · rw [v₇ "rk" (by simp), v₆ "rk" (by simp), hrk₅]
  · rw [v₇ "gn" (by simp), v₆ "gn" (by simp), v₅ "gn" (by simp), hgn]
  · rw [v₇ "gL" (by simp), v₆ "gL" (by simp), v₅ "gL" (by simp), hgL]
  · rw [v₇ "off" (by simp), v₆ "off" (by simp), v₅ "off" (by simp), hoff]
  · rw [v₇ "sm" (by simp), v₆ "sm" (by simp), v₅ "sm" (by simp), hsm]
  · intro y hy
    simp at hy; subst hy
    rw [v₇ "ovf" (by simp), v₆ "ovf" (by simp), v₅ "ovf" (by simp)]
  · rw [r₇.frame_arr _ (by decide), r₆.frame_arr _ (by decide), a₅ "U" (by simp)]
  · exact F₆.congr (v₇ "pg" (by simp)) (r₇.frame_arr _ (by decide))
  · exact hlo₅'.congr (by rw [v₇ "lp" (by simp), v₆ "lp" (by simp)])
      (by rw [r₇.frame_arr _ (by decide), r₆.frame_arr _ (by decide)])

/-- **Round 0 for `n ≥ 1`, after the header.** Either `ovf` is set, or
the state of `R0Out` is reached, and `ovf` stays `0` when both bounds of
the checks hold. -/
theorem r0Main_run {τ : Env} (hW : τ.vars "W" = W) (hovf : τ.vars "ovf" = 0)
    (hgn : τ.vars "gn" = n) (hgL : τ.vars "gL" = g.length)
    (hoff : τ.vars "off" = g.length + n + 2) (hsm : τ.vars "sm" = sc.steps.length)
    (hfp : τ.vars "fp" = g.length + n + 2 + 3 * sc.steps.length)
    (hU : τ.arrs "U" = (g ++ toWord sc ++ toWord φ) ++ rU)
    (hcap : ∀ a ∈ ["stk", "lo", "RP", "GW", "FW", "ta", "tb"], (τ.arrs a).length = W + 1)
    (hx : ∀ v ∈ g ++ toWord sc ++ toWord φ, 64 * (v + 1) ≤ W + 1)
    (hxl : 64 * ((g ++ toWord sc ++ toWord φ).length + 1) ≤ W + 1) :
    ∃ τ', Run (W + 1) r0Main τ τ' (r0C (rank φ) * ((g ++ toWord sc ++ toWord φ).length + 1) +
        50 * (n + 1) ^ 2) ∧
      (τ'.vars "ovf" = 0 → R0Out W n (rank φ) (g ++ toWord sc ++ toWord φ) g.length
        sc.steps.length (inCol (g ++ toWord sc ++ toWord φ) g.length)
        (Lax185574.DistanceLogic.DistFO.code (loc (rank φ) φ)) τ') ∧
      (glM (rank φ) < W / 8 → n * (glM (rank φ) + 3 + n) < W / 8 → τ'.vars "ovf" = 0) := by
  set x := g ++ toWord sc ++ toWord φ with hxdef
  set q := rank φ with hq
  set B := W + 1 with hBdef
  have hxlen : x.length = g.length + n + 2 + 3 * sc.steps.length + (toWord φ).length := by
    simp only [hxdef, List.length_append, toWord_script, List.length_cons, List.length_ofFn,
      length_flatten_stepCode]; omega
  have hfc : (toWord φ).length = (Lax185574.InstanceEncoding.code φ).length := by
    rw [Lax185574Proofs.Legacy.encode_eq_foCode]
  have hqx : q ≤ x.length := (rank_le_code φ).trans (by omega)
  have hW63 : 63 ≤ W := by omega
  -- the rank
  set σ₁ := τ.setVar "fm" 0 with hσ₁
  have hU₁ : (σ₁.arrs "U").drop (g.length + n + 2 + 3 * sc.steps.length) =
      Lax185574.InstanceEncoding.code φ ++ rU := by
    rw [show σ₁.arrs "U" = τ.arrs "U" by simp [hσ₁], hU,
      List.drop_append_of_le_length (by omega), input_formula,
      Lax185574Proofs.Legacy.encode_eq_foCode]
  have hC₁ : FCtx B q φ (g.length + n + 2 + 3 * sc.steps.length) σ₁ :=
    ⟨by simp [hσ₁, hcap "stk" (by simp)]; omega, fun h => by simp [hσ₁] at h,
      fun h => by simp [hσ₁] at h, by omega, by simp [hσ₁, hBdef]⟩
  obtain ⟨σ₂, r₂, hrk₂, -, -⟩ := fWalk_run (q := q) (R := rU) (by simp [hσ₁, hfp]) hU₁ hC₁
  have v₂ : ∀ y ∈ ["W", "gn", "gL", "off", "sm", "ovf"], σ₂.vars y = τ.vars y := by
    intro y hy
    rw [r₂.frame_var y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)]
    simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hσ₁]
  -- the bound
  obtain ⟨σ₃, r₃, hzM⟩ := mBound_run (B := B) (W := W) (q := q) (σ := σ₂)
    (by rw [v₂ "W" (by simp), hW]) (by omega) hrk₂ (by omega) (by omega)
  have v₃ : ∀ y ∈ ["W", "gn", "gL", "off", "sm", "ovf", "rk"], σ₃.vars y = σ₂.vars y := by
    intro y hy
    exact r₃.frame_var y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)
  have a₃ : ∀ a, σ₃.arrs a = σ₂.arrs a := fun a => r₃.frame_arr a (by simp [mBound, mInit, satMul,
    satAdd, satPow, forUp, Com.warrs])
  have hW₃ : σ₃.vars "W" = W := by rw [v₃ "W" (by simp), v₂ "W" (by simp), hW]
  have hcap₃ : ∀ a ∈ ["stk", "lo", "RP", "GW", "FW", "ta", "tb"], (σ₃.arrs a).length = W + 1 := by
    intro a ha; rw [a₃, run_length_arrs r₂, show (σ₁.arrs a) = τ.arrs a by simp [hσ₁], hcap a ha]
  have hU₃ : σ₃.arrs "U" = x ++ rU := by
    rw [a₃, r₂.frame_arr _ (by decide)]; simp [hσ₁, hU]
  have hc₁ : (Cond.lt (.var "zM") (.div (.var "W") (.lit 8))).evalB B σ₃ =
      some (decide (min (glM q) W < W / 8)) :=
    condLt_div hzM hW₃ (by omega) (by omega) (by omega)
  have hfit : n ≤ x.length := by omega
  have hcost : ∀ T, T ≤ 2 + (124 * (Lax185574.InstanceEncoding.code φ).length + 160) +
      (23 * ((q + 2) * (q + 1)) + 23 * (q + 1) + 200) + 6 + (6 + 15 + 6 +
      (q * (23 * ((q + 1) * q) + 80) + 124 * x.length + n * (initCost q + 96) + 300 +
      50 * (n + 1) ^ 2)) →
      T ≤ r0C q * (x.length + 1) + 50 * (n + 1) ^ 2 := by
    intro T hT
    have h1 : n * (initCost q + 96) ≤ x.length * (initCost q + 96) := Nat.mul_le_mul_right _ hfit
    simp only [r0C]
    generalize initCost q = I at *
    generalize 23 * ((q + 2) * (q + 1)) = a at *
    generalize 23 * (q + 1) = b at *
    generalize q * (23 * ((q + 1) * q) + 80) = c at *
    generalize x.length = X at *
    generalize (n + 1) ^ 2 = S at *
    nlinarith [Nat.zero_le (X * a), Nat.zero_le (X * b), Nat.zero_le (X * c), Nat.zero_le (n * I)]
  by_cases hA : min (glM q) W < W / 8
  · have hM : glM q < W / 8 := by
      have := Nat.div_le_self W 8; rcases Nat.le_total (glM q) W with h | h
      · rwa [min_eq_left h] at hA
      · rw [min_eq_right h] at hA; omega
    have hzM' : σ₃.vars "zM" = glM q := by rw [hzM]; omega
    set σ₄ := σ₃.setVar "zx" (glM q + 3 + n) with hσ₄
    have hgn₃ : σ₃.vars "gn" = n := by rw [v₃ "gn" (by simp), v₂ "gn" (by simp), hgn]
    have r₄ : Run B (.assign "zx" (.add (.add (.var "zM") (.lit 3)) (.var "gn"))) σ₃ σ₄ 6 :=
      (Run.assign (ev_add (ev_add (ev_var hzM' (by omega)) (evalB_lit (by omega)) (by omega))
        (ev_var hgn₃ (by omega)) (by omega))).mono (by simp [Expr.size])
    have hgn₄ : σ₄.vars "gn" = n := by simp [hσ₄, v₃ "gn" (by simp), v₂ "gn" (by simp), hgn]
    have r₅ := satMul_run (B := B) (W := W) (x := "gn") (y := "zx") (z := "zy") (σ := σ₄)
      (by simp [hσ₄, hW₃]) (by omega) (by rw [hgn₄]; omega) (by simp [hσ₄]; omega)
    set σ₅ := σ₄.setVar "zy" (min (σ₄.vars "gn" * σ₄.vars "zx") W) with hσ₅
    have hzy : σ₅.vars "zy" = min (n * (glM q + 3 + n)) W := by
      simp only [hσ₅, vars_setVar, ↓reduceIte]; rw [hgn₄]; simp [hσ₄]
    have hW₅ : σ₅.vars "W" = W := by simp [hσ₅, hσ₄, hW₃]
    have hc₂ : (Cond.lt (.var "zy") (.div (.var "W") (.lit 8))).evalB B σ₅ =
        some (decide (min (n * (glM q + 3 + n)) W < W / 8)) :=
      condLt_div hzy hW₅ (by omega) (by omega) (by omega)
    have e₅ : ∀ y ∈ ["W", "gn", "gL", "off", "sm", "ovf", "rk"], σ₅.vars y = σ₂.vars y := by
      intro y hy
      have : y ≠ "zx" ∧ y ≠ "zy" := by
        simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp [hσ₅, hσ₄, this.1, this.2, v₃ y hy]
    by_cases hB' : min (n * (glM q + 3 + n)) W < W / 8
    · have hF : n * (glM q + 3 + n) < W / 8 := by
        have := Nat.div_le_self W 8; rcases Nat.le_total (n * (glM q + 3 + n)) W with h | h
        · rwa [min_eq_left h] at hB'
        · rw [min_eq_right h] at hB'; omega
      obtain ⟨τ', r₆, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
        r0Fill_run (W := W) (n := n) (g := g) (sc := sc) (φ := φ) (rU := rU) (τ := σ₅) hW₅
        (by rw [e₅ "rk" (by simp), hrk₂]) (by rw [e₅ "gn" (by simp), v₂ "gn" (by simp), hgn])
        (by rw [e₅ "gL" (by simp), v₂ "gL" (by simp), hgL])
        (by rw [e₅ "off" (by simp), v₂ "off" (by simp), hoff])
        (by rw [e₅ "sm" (by simp), v₂ "sm" (by simp), hsm])
        (by simp only [hσ₅, hσ₄, arrs_setVar, hU₃]; rfl) (fun a ha => by
          rw [show σ₅.arrs a = σ₃.arrs a by simp [hσ₅, hσ₄]]; exact hcap₃ a ha) hx hxl hM hF
      rw [← hxdef, ← hq] at r₆
      have hov : τ'.vars "ovf" = 0 := by
        rw [h7 "ovf" (by simp), e₅ "ovf" (by simp), v₂ "ovf" (by simp), hovf]
      refine ⟨τ', ?_, fun _ => ⟨hov, h1, h3, h4, h6, h5, h2, ?_, h9, h10, h11, hM, hF⟩,
        fun _ _ => hov⟩
      · unfold r0Main r0Chk2
        refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂ (Run.seq r₃
          (Run.ite_true (by rw [hc₁]; simp [hA]) (Run.seq r₄ (Run.seq r₅
          (Run.ite_true (by rw [hc₂]; simp [hB']) r₆))))))).mono ?_
        apply hcost; simp only [Expr.size, Cond.size]; omega
      · rw [h8, hσ₅, hσ₄]; simp [hU₃]
    · refine ⟨σ₅.setVar "ovf" 1, ?_, fun h => by simp at h, fun _ h => absurd (by omega) hB'⟩
      unfold r0Main r0Chk2
      refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂ (Run.seq r₃
        (Run.ite_true (by rw [hc₁]; simp [hA]) (Run.seq r₄ (Run.seq r₅
        (Run.ite_false (by rw [hc₂]; simp [hB']) (Run.assign (evalB_lit (by omega)))))))))).mono ?_
      apply hcost; simp only [Expr.size, Cond.size]; omega
  · refine ⟨σ₃.setVar "ovf" 1, ?_, fun h => by simp at h, fun h _ => absurd (by omega) hA⟩
    unfold r0Main
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂ (Run.seq r₃
      (Run.ite_false (by rw [hc₁]; simp [hA]) (Run.assign (evalB_lit (by omega))))))).mono ?_
    apply hcost; simp only [Expr.size, Cond.size]; omega

end fill

/-! ### The header and round 0 -/

/-- The header of `x = [n] ++ toWord σ ++ toWord φ` in `U`: `gn = n`,
`gL = 1`, `sm` the number of steps, `off` the position of the steps and
`fp` that of the code of the sentence. -/
def hdr1 : Com :=
  .seq (.assign "gn" (.get "U" (.lit 0))) (.seq (.assign "gL" (.lit 1))
  (.seq (.assign "sm" (.get "U" (.add (.lit 2) (.var "gn"))))
  (.seq (.assign "off" (.add (.var "gn") (.lit 3)))
  (.assign "fp" (.add (.var "off") (.add (.var "sm") (.add (.var "sm") (.var "sm"))))))))

/-- Round 0 after the tag. -/
def round0 : Com :=
  .seq read0 (.seq hdr1 (.ite (.eq (.var "gn") (.lit 0)) (.assign "ovf" (.lit 1)) r0Main))

theorem hdr1_run {B n : ℕ} {sc : Script n} {c r : List ℕ} {σ : Env}
    (hU : σ.arrs "U" = ([n] ++ toWord sc ++ c) ++ r) (hB : 4 * ([n] ++ toWord sc ++ c).length < B) :
    Run B hdr1 σ (((((σ.setVar "gn" n).setVar "gL" 1).setVar "sm" sc.steps.length).setVar
      "off" (n + 3)).setVar "fp" (n + 3 + 3 * sc.steps.length)) 30 := by
  have hlen : ([n] ++ toWord sc ++ c).length = n + 3 + 3 * sc.steps.length + c.length := by
    simp only [List.length_append, toWord_script, List.length_cons, List.length_ofFn,
      length_flatten_stepCode, List.length_nil]; omega
  have h0 : (σ.arrs "U")[0]? = some n := by rw [hU]; rfl
  have hm : (σ.arrs "U")[2 + n]? = some sc.steps.length := by
    rw [hU, List.getElem?_append_left (by omega)]
    have := input_count [n] sc c; simp only [List.length_singleton] at this
    rw [show 2 + n = 1 + 1 + n by omega]; exact this
  unfold hdr1
  refine (Run.seq (Run.assign (evalB_get (evalB_lit (by omega)) h0 (by omega)))
    (Run.seq (Run.assign (evalB_lit (by omega)))
    (Run.seq (Run.assign (evalB_get (ev_add (evalB_lit (by omega)) (ev_var (v := n) (by simp)
      (by omega)) (by omega)) (by simpa using hm) (by omega)))
    (Run.seq (Run.assign (ev_add (ev_var (v := n) (by simp) (by omega)) (evalB_lit (by omega))
      (by omega))) (Run.assign ?_))))).mono (by simp)
  rw [show n + 3 + 3 * sc.steps.length = n + 3 + (sc.steps.length + (sc.steps.length +
    sc.steps.length)) by omega]
  exact ev_add (ev_var (v := n + 3) (by simp) (by omega)) (ev_add (ev_var (v := sc.steps.length)
    (by simp) (by omega)) (ev_add (ev_var (v := sc.steps.length) (by simp) (by omega))
    (ev_var (v := sc.steps.length) (by simp) (by omega)) (by omega)) (by omega)) (by omega)

/-- **Round 0 after the tag.** Without vertices `ovf` is set. Otherwise
either `ovf` is set or the state of `R0Out` is reached, and `ovf` stays
`0` when the two bounds of the checks hold. -/
theorem round0_run {W n : ℕ} {sc : Script n} {φ : FO 0} {rest : List ℕ} {σ : Env}
    (hinp : σ.inp = ([n] ++ toWord sc ++ toWord φ).length :: (([n] ++ toWord sc ++ toWord φ) ++ rest))
    (hW : σ.vars "W" = W) (hovf : σ.vars "ovf" = 0)
    (hcap : ∀ a ∈ ["U", "stk", "lo", "RP", "GW", "FW", "ta", "tb"], (σ.arrs a).length = W + 1)
    (hx : ∀ v ∈ [n] ++ toWord sc ++ toWord φ, 64 * (v + 1) ≤ W + 1)
    (hxl : 64 * (([n] ++ toWord sc ++ toWord φ).length + 1) ≤ W + 1) :
    ∃ τ', Run (W + 1) round0 σ τ' (r0C (rank φ) * (([n] ++ toWord sc ++ toWord φ).length + 1) +
        50 * (n + 1) ^ 2 + 16 * ([n] ++ toWord sc ++ toWord φ).length + 60) ∧
      (n = 0 → τ'.vars "ovf" ≠ 0) ∧
      (τ'.vars "ovf" = 0 → R0Out W n (rank φ) ([n] ++ toWord sc ++ toWord φ) 1
        sc.steps.length (inCol ([n] ++ toWord sc ++ toWord φ) 1)
        (Lax185574.DistanceLogic.DistFO.code (loc (rank φ) φ)) τ') ∧
      (1 ≤ n → glM (rank φ) < W / 8 → n * (glM (rank φ) + 3 + n) < W / 8 → τ'.vars "ovf" = 0) := by
  set x := [n] ++ toWord sc ++ toWord φ with hxdef
  obtain ⟨σ₁, r₁, -, -, hU₁⟩ := read0_run (B := W + 1) (x := x) hinp
    (by rw [hcap "U" (by simp)]; omega) (by omega) (fun v hv => by have := hx v hv; omega)
  have hU₁' : σ₁.arrs "U" = x ++ (σ.arrs "U").drop x.length := hU₁
  have r₂ := hdr1_run (B := W + 1) (sc := sc) (c := toWord φ) hU₁'
    (by show 4 * x.length < W + 1; omega)
  have hnB : 64 * (n + 1) ≤ W + 1 := hx n (by simp [hxdef])
  set σ₂ := ((((σ₁.setVar "gn" n).setVar "gL" 1).setVar "sm" sc.steps.length).setVar
      "off" (n + 3)).setVar "fp" (n + 3 + 3 * sc.steps.length) with hσ₂
  have v₁ : ∀ y ∈ ["W", "ovf"], σ₁.vars y = σ.vars y := by
    intro y hy; simp at hy
    rcases hy with rfl | rfl <;> exact r₁.frame_var _ (by decide)
  have a₁ : ∀ a ∈ ["stk", "lo", "RP", "GW", "FW", "ta", "tb"], σ₁.arrs a = σ.arrs a := by
    intro a ha; simp at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact r₁.frame_arr _ (by decide)
  have hW₂ : σ₂.vars "W" = W := by simp [hσ₂, v₁ "W" (by simp), hW]
  have hc : (Cond.eq (.var "gn") (.lit 0)).evalB (W + 1) σ₂ = some (decide (n = 0)) :=
    condEq_lit (by simp [hσ₂]) (by omega) (by omega)
  by_cases hn : n = 0
  · refine ⟨σ₂.setVar "ovf" 1, ?_, fun _ => by simp, fun h => by simp at h,
      fun h => absurd hn (by omega)⟩
    unfold round0
    refine (Run.seq r₁ (Run.seq r₂ (Run.ite_true (by rw [hc]; simp [hn])
      (Run.assign (evalB_lit (by omega)))))).mono ?_
    simp only [Expr.size, Cond.size]
    have : 0 ≤ r0C (rank φ) * (x.length + 1) := Nat.zero_le _
    omega
  · obtain ⟨τ', r₃, hO, hT⟩ := r0Main_run (W := W) (n := n) (g := [n]) (sc := sc) (φ := φ)
      (rU := (σ.arrs "U").drop x.length) (τ := σ₂) hW₂ (by simp [hσ₂, v₁ "ovf" (by simp), hovf])
      (by simp [hσ₂]) (by simp [hσ₂]) (by simp [hσ₂]; omega) (by simp [hσ₂])
      (by simp [hσ₂]; omega) (by simp only [hσ₂, arrs_setVar, hU₁']; rfl)
      (fun a ha => by simp only [hσ₂, arrs_setVar]; rw [a₁ a ha, hcap a (by simp at ha ⊢; tauto)])
      hx hxl
    rw [← hxdef] at r₃
    refine ⟨τ', ?_, fun h => absurd h hn, hO, fun _ => hT⟩
    unfold round0
    refine (Run.seq r₁ (Run.seq r₂ (Run.ite_false (by rw [hc]; simp [hn]) r₃))).mono ?_
    simp only [Expr.size, Cond.size]
    omega

end Lax185574Proofs.MC.Glue
