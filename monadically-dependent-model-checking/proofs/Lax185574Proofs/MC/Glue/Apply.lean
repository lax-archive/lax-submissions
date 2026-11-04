import Lax185574Proofs.MC.Glue.RdIn

/-!
Applying the answer of a call, in a round of the glue program of
thm:mc after the first.

The state and the answer are in the array `x` (`rdIn`, `ldSc`). The
word of the partial graph in the state is followed by the word of its
matrix of distances. The new words of the partial graph with its matrix
and of the family of trees are built in `GW` and `FW`:

* `apJ`, after a merge with `P ≠ Q`: the colors are recolored, the
  matrix is copied, and the new family is the count followed by the
  words of the answers of the merge lift, each without its length.
* `apS`, after a merge `merge_{P,P}`: both words are copied.
* `apR`, after a resolve: the answer without its first `|yM0|` and its
  last `|uE0|` entries is the word of the new partial graph, that of
  its matrix of distances and that of the new family, split by walking
  over the partial graph and skipping the `1 + n (n + 1)` entries of the
  matrix.

`cpLo` copies the localized sentence.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees

/-- The number of entries after the merge answer in the answer of the callee. -/
noncomputable def dR : ℕ := zR0.length + uE0.length

theorem dR_le_dK : dR + yM0.length ≤ dK := by
  unfold dR dK; omega

/-! ### The word of the partial graph -/

/-- Copy the word of the partial graph and the word after it from `x`
at `gA` into `GW`, `gl` entries in all, the colors recolored if
`rc = 1`. -/
def cpGW : Com :=
  .seq (.assign "pg" (.lit 0)) (.seq (push1 "GW" "pg" (.get "x" (.var "gA")))
  (.seq (.assign "cA" (.add (.var "gA") (.lit 1))) (.seq cpCol
  (.seq (.assign "ca" (.add (.add (.var "gA") (.lit 1)) (.var "gn")))
  (.seq (.assign "cl" (.sub (.sub (.var "gl") (.lit 1)) (.var "gn"))) (cpTo "GW" "pg" "x" "ca" "cl"))))))

theorem cpGW_run {W n ρ P Q : ℕ} {σ : Env} {X R E : List ℕ} {G : PartialGraph (Fin n)} {a : ℕ}
    (hX : σ.arrs "x" = X) (ha : σ.vars "gA" = a) (hd : X.drop a = toWord G ++ E ++ R)
    (hgl : σ.vars "gl" = (toWord G).length + E.length) (hgn : σ.vars "gn" = n)
    (hρ : σ.vars "rc" = ρ)
    (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hρW : ρ ≤ W) (hPW : P ≤ W) (hQW : Q ≤ W)
    (hcap : (toWord G).length + E.length ≤ (σ.arrs "GW").length)
    (hB : a + 2 * ((toWord G).length + E.length) < W)
    (hv : ∀ v ∈ X, v ≤ W) :
    ∃ σ', Run (W + 1) cpGW σ σ' (60 * ((toWord G).length + E.length) + 60) ∧
      Filled "GW" "pg" ((n :: (List.ofFn G.color).map (recol ρ P Q)) ++
        (toWord G.edge ++ toWord G.nonEdge ++ E)) σ' := by
  have hw := toWord_pg G
  have hlen : (toWord G).length = 1 + n + (toWord G.edge ++ toWord G.nonEdge).length := by
    rw [hw]; simp; omega
  have hXl : a + (toWord G).length + E.length ≤ X.length := by
    have := congrArg List.length hd; simp at this; omega
  have hvB : ∀ v ∈ X, v < W + 1 := fun v h => by have := hv v h; omega
  -- the first entry
  have h0 : X[a]? = some n := getElem?_of_drop (by rw [hd, hw]; rfl)
  set σ₁ := σ.setVar "pg" 0 with hσ₁
  have F₁ : Filled "GW" "pg" [] σ₁ := Filled.empty "GW" "pg" σ
  obtain ⟨σ₂, r₂, F₂, fv₂, fa₂, fl₂, -, -⟩ := push1_run (B := W + 1) (e := .get "x" (.var "gA")) F₁
    (evalB_get (ev_var (v := a) (by simp [hσ₁, ha]) (by omega)) (by simp [hσ₁, hX]; exact h0)
      (by omega))
    (by rw [hσ₁, arrs_setVar]; simp; omega) (by simp; omega)
  have v₂ : ∀ y, y ≠ "pg" → σ₂.vars y = σ.vars y := fun y hy => by rw [fv₂ y hy]; simp [hσ₁, hy]
  set σ₃ := σ₂.setVar "cA" (a + 1) with hσ₃
  have r₃ : Run (W + 1) (.assign "cA" (.add (.var "gA") (.lit 1))) σ₂ σ₃ 4 :=
    (Run.assign (ev_add (ev_var (by rw [v₂ "gA" (by decide), ha]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  have hc : seg X (a + 1) n = List.ofFn G.color := by
    rw [seg_of_drop (A := toWord G) (R := E ++ R) (by rw [hd, List.append_assoc]) (by omega), hw]; simp
  obtain ⟨σ₄, r₄, F₄⟩ := cpCol_run (B := W + 1) (σ := σ₃) (pre := [n]) (X := X) (a := a + 1) (N := n)
    (ρ := ρ) (P := P) (Q := Q) (by simp [hσ₃, fa₂ "x" (by decide), hσ₁, hX]) (by simp [hσ₃])
    (by simp [hσ₃, v₂ "gn" (by decide), hgn]) (by simp [hσ₃, v₂ "rc" (by decide), hρ])
    (by simp [hσ₃, v₂ "cP" (by decide), hP]) (by simp [hσ₃, v₂ "cQ" (by decide), hQ]) (by omega) (by omega)
    (by omega) (by simpa using (F₂.setVar (y := "cA") (by decide) (a + 1))) (by omega) (by simp [hσ₃, fl₂, hσ₁]; omega) (by omega)
    (by simp; omega) hvB
  rw [hc] at F₄
  have hx₄ : σ₄.arrs "x" = X := by
    rw [r₄.frame_arr "x" (by simp [cpCol, forUp, push1, Com.warrs]), hσ₃, arrs_setVar,
      fa₂ "x" (by decide), hσ₁, arrs_setVar, hX]
  have v₄ : ∀ y ∈ ["gA", "gn", "gl"], σ₄.vars y = σ.vars y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [r₄.frame_var y (by rcases hy with rfl | rfl | rfl <;> decide), hσ₃, vars_setVar,
      if_neg (by rcases hy with rfl | rfl | rfl <;> decide), v₂ y (by rcases hy with rfl | rfl | rfl <;> decide)]
  set σ₅ := (σ₄.setVar "ca" (a + 1 + n)).setVar "cl" ((toWord G).length + E.length - 1 - n) with hσ₅
  have r₅a : Run (W + 1) (.assign "ca" (.add (.add (.var "gA") (.lit 1)) (.var "gn"))) σ₄
      (σ₄.setVar "ca" (a + 1 + n)) 6 :=
    (Run.assign (ev_add (ev_add (ev_var (by rw [v₄ _ (by simp), ha]) (by omega))
      (evalB_lit (by omega)) (by omega)) (ev_var (by rw [v₄ _ (by simp), hgn]) (by omega))
      (by omega))).mono (by simp [Expr.size])
  have r₅b : Run (W + 1) (.assign "cl" (.sub (.sub (.var "gl") (.lit 1)) (.var "gn")))
      (σ₄.setVar "ca" (a + 1 + n)) σ₅ 6 :=
    (Run.assign (ev_sub (ev_sub (ev_var (v := (toWord G).length + E.length)
      (by simp [v₄ _ (by simp : "gl" ∈ _), hgl]) (by omega)) (evalB_lit (by omega)) (by omega))
      (ev_var (v := n) (by simp [v₄ _ (by simp : "gn" ∈ _), hgn]) (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have hrest : seg X (a + 1 + n) ((toWord G).length + E.length - 1 - n) =
      toWord G.edge ++ toWord G.nonEdge ++ E := by
    have hd' : X.drop a = (toWord G ++ E) ++ R := by rw [hd, List.append_assoc]
    rw [show a + 1 + n = a + (1 + n) by omega, seg_of_drop (A := toWord G ++ E) hd' (by simp; omega)]
    have hdE : (toWord G ++ E).drop (1 + n) = toWord G.edge ++ toWord G.nonEdge ++ E := by
      rw [List.drop_append_of_le_length (by omega), hw]
      rw [List.drop_left' (by simp; omega)]
    rw [hdE, List.take_of_length_le (by simp only [List.length_append] at hlen ⊢; omega)]
  have hl₄ : ([n] ++ (List.ofFn G.color).map (recol ρ P Q)).length = 1 + n := by simp; omega
  obtain ⟨σ₆, r₆, F₆⟩ := cpTo_run (B := W + 1) (dst := "GW") (pv := "pg") (src := "x") (s := "ca")
    (l := "cl") (σ := σ₅) (a := a + 1 + n) (N := (toWord G).length + E.length - 1 - n) (by decide)
    (by simp [hσ₅]) (by simp [hσ₅]) (by decide) (by decide) (by decide) (by decide) (by decide)
    (F₄.setVar (by decide) _ |>.setVar (by decide) _) (by simp [hσ₅, hx₄]; omega)
    (by simp [hσ₅, run_length_arrs r₄, hσ₃, fl₂, hσ₁, hl₄]; omega) (by omega) (by rw [hl₄]; omega)
    (fun v h => by simp only [hσ₅, arrs_setVar, hx₄] at h; exact hvB v (mem_seg h))
  simp only [hσ₅, arrs_setVar, hx₄, hrest] at F₆
  refine ⟨σ₆, ?_, by simpa using F₆⟩
  unfold cpGW
  refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂ (Run.seq r₃ (Run.seq r₄
    (Run.seq r₅a (Run.seq r₅b r₆)))))).mono ?_
  simp only [Expr.size]; omega

/-! ### Copying a segment of `x` -/

/-- Append the cells of `x` from `eS` on, `eL` of them, to `dst`. -/
def cpX (dst pv : String) (eS eL : Expr) : Com :=
  .seq (.assign "ca" eS) (.seq (.assign "cl" eL) (cpTo dst pv "x" "ca" "cl"))

theorem cpX_run {W a N : ℕ} {dst pv : String} {eS eL : Expr} {σ : Env} {pre X : List ℕ}
    (hdst : dst ≠ "x") (hpv : pv ∉ ["ca", "cl", "ci"]) (hX : σ.arrs "x" = X)
    (hS : eS.evalB (W + 1) σ = some a) (hL : eL.evalB (W + 1) (σ.setVar "ca" a) = some N)
    (hF : Filled dst pv pre σ) (hA : a + N ≤ X.length)
    (hcap : pre.length + N ≤ (σ.arrs dst).length) (hB : a + N ≤ W) (hB' : pre.length + N ≤ W)
    (hv : ∀ v ∈ X, v ≤ W) :
    ∃ σ', Run (W + 1) (cpX dst pv eS eL) σ σ' (N * 20 + 8 + eS.size + eL.size) ∧
      Filled dst pv (pre ++ seg X a N) σ' ∧
      (∀ y, y ∉ ["ca", "cl", "ci", pv] → σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ dst → σ'.arrs b = σ.arrs b) ∧ (σ'.arrs dst).length = (σ.arrs dst).length ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hpv
  set σ₁ := (σ.setVar "ca" a).setVar "cl" N with hσ₁
  have F₁ : Filled dst pv pre σ₁ := (hF.setVar (Ne.symm hpv.1) _).setVar (Ne.symm hpv.2.1) _
  obtain ⟨σ₂, r₂, F₂⟩ := cpTo_run (B := W + 1) (dst := dst) (pv := pv) (src := "x") (s := "ca")
    (l := "cl") (σ := σ₁) (a := a) (N := N) (Ne.symm hdst) (by simp [hσ₁]) (by simp [hσ₁])
    hpv.2.2 (Ne.symm hpv.1) (by decide) (Ne.symm hpv.2.1) (by decide) F₁
    (by simp [hσ₁, hX]; omega) (by simp [hσ₁]; omega) (by omega) (by omega)
    (fun v h => by simp only [hσ₁, arrs_setVar, hX] at h; have := hv v (mem_seg h); omega)
  simp only [hσ₁, arrs_setVar, hX] at F₂
  have r : Run (W + 1) (cpX dst pv eS eL) σ σ₂ (N * 20 + 8 + eS.size + eL.size) :=
    (Run.seq (Run.assign hS) (Run.seq (Run.assign hL) r₂)).mono (by omega)
  refine ⟨σ₂, r, F₂, fun y hy => r.frame_var_sub y (l := ["ca", "cl", "ci", pv])
    (by simp [cpX, cpTo, forUp, push1, Com.wvars]) hy,
    fun b hb => r.frame_arr b (by simp [cpX, cpTo, forUp, push1, Com.warrs]; exact hb),
    run_length_arrs r dst, r.frame_inp (by simp [cpX, cpTo, forUp, push1, Com.reads]),
    r.out_eq (by simp [cpX, cpTo, forUp, push1, Com.NoWrite])⟩

/-! ### The localized sentence and the copies after `merge_{P,P}` -/

/-- Copy the localized sentence into `lo`. -/
def cpLo : Com := .seq (.assign "lp" (.lit 0)) (cpX "lo" "lp" (.var "lA") (.var "ll"))

theorem cpLo_run {W : ℕ} {σ : Env} {X lw R : List ℕ} {a : ℕ} (hX : σ.arrs "x" = X)
    (ha : σ.vars "lA" = a) (hll : σ.vars "ll" = lw.length) (hd : X.drop a = lw ++ R)
    (hcap : lw.length ≤ (σ.arrs "lo").length) (hB : a + lw.length ≤ W) (hv : ∀ v ∈ X, v ≤ W)
    (hXl : a + lw.length ≤ X.length) :
    ∃ σ', Run (W + 1) cpLo σ σ' (20 * lw.length + 20) ∧ Filled "lo" "lp" lw σ' ∧
      (∀ y, y ∉ ["ca", "cl", "ci", "lp"] → σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ "lo" → σ'.arrs b = σ.arrs b) ∧ (σ'.arrs "lo").length = (σ.arrs "lo").length ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σ', r, F, fv, fa, fl, fi, fo⟩ := cpX_run (W := W) (a := a) (N := lw.length) (dst := "lo")
    (pv := "lp") (eS := .var "lA") (eL := .var "ll") (σ := σ.setVar "lp" 0) (pre := []) (X := X)
    (by decide) (by decide) (by simpa using hX) (ev_var (v := a) (by simp [ha]) (by omega))
    (ev_var (v := lw.length) (by simp [hll]) (by omega)) (Filled.empty _ _ _) hXl (by simpa using hcap)
    (by omega) (by simp; omega) hv
  rw [List.nil_append, show seg X a lw.length = seg X (a + 0) lw.length by rfl,
    seg_of_drop (i := 0) hd (by omega)] at F
  simp only [List.drop_zero, List.take_left'] at F
  rw [List.take_of_length_le (by simp)] at F
  refine ⟨σ', (Run.seq (Run.assign (evalB_lit (by omega))) r).mono (by simp [Expr.size]; omega),
    by simpa using F, fun y hy => ?_, fun b hb => by rw [fa b hb]; rfl, by rw [fl]; rfl,
    by rw [fi]; rfl, by rw [fo]; rfl⟩
  rw [fv y hy]; simp only [vars_setVar]
  rw [if_neg (fun h => hy (by simp [h]))]

/-- After `merge_{P,P}`: copy both words. -/
def apS : Com :=
  .seq (.assign "rc" (.lit 0)) (.seq cpGW (.seq (.assign "pf" (.lit 0))
    (cpX "FW" "pf" (.var "fA") (.var "fl"))))

theorem cpGW_frame : cpGW.wvars ⊆ ["pg", "cA", "ci", "ca", "cl"] := by
  simp [cpGW, cpCol, cpTo, forUp, push1, Com.wvars]

theorem cpGW_warrs : cpGW.warrs ⊆ ["GW"] := by
  simp [cpGW, cpCol, cpTo, forUp, push1, Com.warrs]

theorem apS_run {W n P Q : ℕ} {σ : Env} {X R R' fw E : List ℕ} {G : PartialGraph (Fin n)} {a f : ℕ}
    (hX : σ.arrs "x" = X) (ha : σ.vars "gA" = a) (hd : X.drop a = toWord G ++ E ++ R)
    (hgl : σ.vars "gl" = (toWord G).length + E.length) (hgn : σ.vars "gn" = n)
    (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hPW : P ≤ W) (hQW : Q ≤ W)
    (hf : σ.vars "fA" = f) (hfl : σ.vars "fl" = fw.length) (hdf : X.drop f = fw ++ R')
    (hfX : f + fw.length ≤ X.length)
    (hcap : (toWord G).length + E.length ≤ (σ.arrs "GW").length)
    (hcapF : fw.length ≤ (σ.arrs "FW").length)
    (hB : a + 2 * ((toWord G).length + E.length) < W) (hBf : f + fw.length ≤ W)
    (hv : ∀ v ∈ X, v ≤ W) :
    ∃ σ', Run (W + 1) apS σ σ' (60 * ((toWord G).length + E.length) + 20 * fw.length + 80) ∧
      Filled "GW" "pg" (toWord G ++ E) σ' ∧ Filled "FW" "pf" fw σ' ∧ σ'.arrs "x" = X ∧
      (∀ y, y ∉ ["rc", "pg", "cA", "ci", "ca", "cl", "pf"] → σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ "GW" → b ≠ "FW" → σ'.arrs b = σ.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  set σ₁ := σ.setVar "rc" 0 with hσ₁
  obtain ⟨σ₂, r₂, F₂⟩ := cpGW_run (W := W) (ρ := 0) (P := P) (Q := Q) (σ := σ₁) (G := G) (a := a)
    (by simp [hσ₁, hX]) (by simp [hσ₁, ha]) hd (by simp [hσ₁, hgl]) (by simp [hσ₁, hgn]) (by simp [hσ₁])
    (by simp [hσ₁, hP]) (by simp [hσ₁, hQ]) (by omega) hPW hQW (by simpa [hσ₁] using hcap) hB hv
  have e : (n :: List.ofFn G.color) ++ (toWord G.edge ++ toWord G.nonEdge ++ E) = toWord G ++ E := by
    rw [toWord_pg]; simp only [List.append_assoc, List.cons_append]
  rw [recol_zero, List.map_id, e] at F₂
  have v₂ : ∀ y, y ∉ ["pg", "cA", "ci", "ca", "cl"] → σ₂.vars y = σ₁.vars y :=
    fun y hy => r₂.frame_var_sub y cpGW_frame hy
  have a₂ : ∀ b, b ≠ "GW" → σ₂.arrs b = σ₁.arrs b :=
    fun b hb => r₂.frame_arr b (fun h => hb (by simpa using cpGW_warrs h))
  obtain ⟨σ₃, r₃, F₃, fv₃, fa₃, fl₃, fi₃, fo₃⟩ := cpX_run (W := W) (a := f) (N := fw.length)
    (dst := "FW") (pv := "pf") (eS := .var "fA") (eL := .var "fl") (σ := σ₂.setVar "pf" 0) (pre := [])
    (X := X) (by decide) (by decide) (by simp [a₂ "x" (by decide), hσ₁, hX])
    (ev_var (v := f) (by simp [v₂ "fA" (by decide), hσ₁, hf]) (by omega))
    (ev_var (v := fw.length) (by simp [v₂ "fl" (by decide), hσ₁, hfl]) (by omega))
    (Filled.empty _ _ _) hfX (by simp [a₂ "FW" (by decide), hσ₁]; omega) hBf (by simp; omega) hv
  rw [List.nil_append, show seg X f fw.length = seg X (f + 0) fw.length by rfl,
    seg_of_drop (i := 0) hdf (by omega), List.drop_zero, List.take_of_length_le (by simp)] at F₃
  have r : Run (W + 1) apS σ σ₃ (60 * ((toWord G).length + E.length) + 20 * fw.length + 80) := by
    unfold apS
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂ (Run.seq
      (Run.assign (evalB_lit (by omega))) r₃))).mono ?_
    simp [Expr.size]; omega
  refine ⟨σ₃, r, F₂.congr ?_ ?_, F₃, ?_, fun y hy => ?_, fun b h1 h2 => ?_, fun b => ?_,
    by rw [fi₃]; simp [r₂.frame_inp (by simp [cpGW, cpCol, cpTo, forUp, push1, Com.reads]), hσ₁],
    by rw [fo₃]; simp [r₂.out_eq (by simp [cpGW, cpCol, cpTo, forUp, push1, Com.NoWrite]), hσ₁]⟩
  · rw [fv₃ "pg" (by decide)]; simp
  · rw [fa₃ "GW" (by decide)]; rfl
  · rw [fa₃ "x" (by decide)]; simp [a₂ "x" (by decide), hσ₁, hX]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [fv₃ y (by simp; tauto)]; simp only [vars_setVar, if_neg hy.2.2.2.2.2.2]
    rw [v₂ y (by simp; tauto)]; simp [hσ₁, hy.1]
  · rw [fa₃ b h2]; simp [a₂ b h1, hσ₁]
  · by_cases hb : b = "FW"
    · subst hb; rw [fl₃]; simp [run_length_arrs r₂, hσ₁]
    · rw [fa₃ b hb]; simp [run_length_arrs r₂, hσ₁]

/-! ### After a resolve -/

theorem evB_mul {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ} (he : e.evalB B σ = some m)
    (hf : f.evalB B σ = some n) (h : m * n < B) : (Expr.mul e f).evalB B σ = some (m * n) :=
  evalB_bin he hf h

/-- After a resolve: split the answer into the partial graph with its
matrix of distances and the family. -/
noncomputable def apR : Com :=
  .seq (.assign "gS" (.add (.var "bA") (.lit yM0.length))) (.seq (.assign "y" (.var "gS"))
  (.seq (skipPG "x") (.seq (.assign "gE" (.add (.var "y")
    (.add (.lit 1) (.mul (.var "gn") (.add (.var "gn") (.lit 1))))))
  (.seq (.assign "pg" (.lit 0))
  (.seq (cpX "GW" "pg" (.var "gS") (.sub (.var "gE") (.var "gS"))) (.seq (.assign "pf" (.lit 0))
  (cpX "FW" "pf" (.var "gE") (.sub (.sub (.add (.var "bA") (.var "bl")) (.lit uE0.length))
    (.var "gE")))))))))

theorem apR_run {W n : ℕ} {σ : Env} {X R F E : List ℕ} {G : PartialGraph (Fin n)} {a : ℕ}
    (hX : σ.arrs "x" = X) (ha : σ.vars "bA" = a) (hgn : σ.vars "gn" = n)
    (hd : X.drop a = yM0 ++ (toWord G ++ E ++ F) ++ uE0 ++ R) (hE : E.length = 1 + n * (n + 1))
    (hbl : σ.vars "bl" = yM0.length + (toWord G).length + E.length + F.length + uE0.length)
    (hXl : a + yM0.length + (toWord G).length + E.length + F.length ≤ X.length)
    (hcap : (toWord G).length + E.length ≤ (σ.arrs "GW").length)
    (hcapF : F.length ≤ (σ.arrs "FW").length)
    (hB : a + yM0.length + 2 * ((toWord G).length + E.length + F.length) + uE0.length < W)
    (hv : ∀ v ∈ X, v ≤ W) :
    ∃ σ', Run (W + 1) apR σ σ' (100 * ((toWord G).length + E.length + F.length) + 140) ∧
      Filled "GW" "pg" (toWord G ++ E) σ' ∧ Filled "FW" "pf" F σ' ∧ σ'.arrs "x" = X ∧
      (∀ y, y ∉ ["gS", "y", "gE", "pg", "pf", "ca", "cl", "ci", "e1", "e2", "e5"] →
        σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ "GW" → b ≠ "FW" → σ'.arrs b = σ.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨g, hg⟩ : ∃ g, g = a + yM0.length := ⟨_, rfl⟩
  set σ₁ := (σ.setVar "gS" g).setVar "y" g with hσ₁
  have hdG : X.drop g = toWord G ++ (E ++ F ++ uE0 ++ R) := by
    have := drop_add_of_drop (u := yM0) (r := (toWord G ++ E ++ F) ++ uE0 ++ R) (by rw [hd]; simp)
    rw [hg, this]; simp
  have hdGE : X.drop g = (toWord G ++ E) ++ (F ++ uE0 ++ R) := by rw [hdG]; simp
  obtain ⟨σ₂, r₂, hy₂⟩ := skipPG_run (B := W + 1) G (ar := "x") (τ := σ₁) (p := g) (by simp [hσ₁, hX])
    (by simp [hσ₁]) (by simp [hσ₁, hgn]) hdG (by omega)
  have v₂ : ∀ y, y ∉ ["y", "e1", "e2", "e5"] → σ₂.vars y = σ₁.vars y := fun y hy =>
    r₂.frame_var_sub y (by simp [skipPG, skipG, skipLs, skipL, forUp, Com.wvars]) hy
  have a₂ : σ₂.arrs = σ₁.arrs := funext fun b =>
    r₂.frame_arr b (by simp [skipPG, skipG, skipLs, skipL, forUp, Com.warrs])
  obtain ⟨e, he⟩ : ∃ e, e = g + (toWord G).length + E.length := ⟨_, rfl⟩
  have hgn₂ : σ₂.vars "gn" = n := by rw [v₂ "gn" (by decide)]; simp [hσ₁, hgn]
  have hnn : n * (n + 1) < W := by omega
  have hnW : n ≤ n * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hgE : (Expr.add (.var "y") (.add (.lit 1) (.mul (.var "gn") (.add (.var "gn") (.lit 1))))).evalB
      (W + 1) σ₂ = some e := by
    rw [he, show g + (toWord G).length + E.length = (g + (toWord G).length) + (1 + n * (n + 1)) by omega]
    exact ev_add (ev_var hy₂ (by omega)) (ev_add (evalB_lit (by omega)) (evB_mul (ev_var hgn₂ (by omega))
      (ev_add (ev_var hgn₂ (by omega)) (evalB_lit (by omega)) (by omega)) (by omega)) (by omega))
      (by omega)
  set σ₃ := (σ₂.setVar "gE" e).setVar "pg" 0 with hσ₃
  have hX₃ : σ₃.arrs "x" = X := by simp [hσ₃, a₂, hσ₁, hX]
  obtain ⟨σ₄, r₄, F₄, fv₄, fa₄, fl₄, fi₄, fo₄⟩ := cpX_run (W := W) (a := g)
    (N := (toWord G).length + E.length)
    (dst := "GW") (pv := "pg") (eS := .var "gS") (eL := .sub (.var "gE") (.var "gS")) (σ := σ₃)
    (pre := []) (X := X) (by decide) (by decide) hX₃
    (ev_var (v := g) (by simp [hσ₃, v₂ "gS" (by decide), hσ₁]) (by omega))
    (by
      rw [show (toWord G).length + E.length = e - g by omega]
      exact ev_sub (B := W + 1) (σ := σ₃.setVar "ca" g) (ev_var (x := "gE") (v := e) (by simp [hσ₃])
        (by omega)) (ev_var (x := "gS") (v := g) (by simp [hσ₃, v₂ "gS" (by decide), hσ₁]) (by omega))
        (by omega))
    (Filled.empty _ _ _ |>.congr (by simp [hσ₃]) rfl) (by omega) (by simp [hσ₃, a₂, hσ₁]; omega)
    (by omega) (by simp; omega) hv
  rw [List.nil_append, show seg X g ((toWord G).length + E.length) =
      seg X (g + 0) (toWord G ++ E).length by simp,
    seg_of_drop (i := 0) hdGE (by simp), List.drop_zero, List.take_length] at F₄
  have hdF : X.drop e = F ++ (uE0 ++ R) := by
    have := drop_add_of_drop hdGE; rw [he, show g + (toWord G).length + E.length =
      g + (toWord G ++ E).length by simp; omega, this]; simp
  set σ₅ := σ₄.setVar "pf" 0 with hσ₅
  have hv₄ : ∀ y ∈ ["bA", "bl", "gE"], σ₄.vars y = σ₃.vars y := fun y hy => fv₄ y (by
    simp at hy; rcases hy with rfl | rfl | rfl <;> decide)
  obtain ⟨σ₆, r₆, F₆, fv₆, fa₆, fl₆, fi₆, fo₆⟩ := cpX_run (W := W) (a := e) (N := F.length)
    (dst := "FW") (pv := "pf") (eS := .var "gE")
    (eL := .sub (.sub (.add (.var "bA") (.var "bl")) (.lit uE0.length)) (.var "gE")) (σ := σ₅)
    (pre := []) (X := X) (by decide) (by decide) (by simp [hσ₅, fa₄ "x" (by decide), hX₃])
    (ev_var (v := e) (by simp [hσ₅, hv₄ "gE" (by simp), hσ₃]) (by omega))
    (by
      rw [show F.length = a + (yM0.length + (toWord G).length + E.length + F.length + uE0.length) -
        uE0.length - e by omega]
      exact ev_sub (B := W + 1) (σ := σ₅.setVar "ca" e) (ev_sub (B := W + 1) (ev_add (B := W + 1)
        (ev_var (x := "bA") (v := a) (by simp [hσ₅, hv₄ "bA" (by simp), hσ₃, v₂ "bA" (by decide),
          hσ₁, ha]) (by omega))
        (ev_var (x := "bl") (v := yM0.length + (toWord G).length + E.length + F.length + uE0.length)
          (by simp [hσ₅, hv₄ "bl" (by simp), hσ₃, v₂ "bl" (by decide), hσ₁, hbl]) (by omega))
        (by omega)) (evalB_lit (by omega)) (by omega)) (ev_var (x := "gE") (v := e)
        (by simp [hσ₅, hv₄ "gE" (by simp), hσ₃]) (by omega)) (by omega))
    (Filled.empty _ _ _) (by omega) (by simp [hσ₅, fa₄ "FW" (by decide), hσ₃, a₂, hσ₁]; omega)
    (by omega) (by simp; omega) hv
  rw [List.nil_append, show seg X e F.length = seg X (e + 0) F.length by rfl,
    seg_of_drop (i := 0) hdF (by simp), List.drop_zero, List.take_length] at F₆
  have r : Run (W + 1) apR σ σ₆ (100 * ((toWord G).length + E.length + F.length) + 140) := by
    have hgv : (Expr.add (.var "bA") (.lit yM0.length)).evalB (W + 1) σ = some g := by
      rw [hg]; exact ev_add (ev_var (v := a) ha (by omega)) (evalB_lit (by omega)) (by omega)
    unfold apR
    refine (Run.seq (Run.assign hgv) (Run.seq (Run.assign (ev_var (v := g) (by simp)
      (by omega))) (Run.seq r₂ (Run.seq (Run.assign hgE) (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₄ (Run.seq
      (Run.assign (evalB_lit (by omega))) r₆))))))).mono ?_
    simp only [Expr.size]; omega
  have fi₂ : σ₂.inp = σ₁.inp := r₂.frame_inp (by simp [skipPG, skipG, skipLs, skipL, forUp, Com.reads])
  have fo₂ : σ₂.out = σ₁.out := r₂.out_eq (by simp [skipPG, skipG, skipLs, skipL, forUp, Com.NoWrite])
  refine ⟨σ₆, r, F₄.congr (by rw [fv₆ "pg" (by decide)]; simp [hσ₅]) (by rw [fa₆ "GW" (by decide)]; rfl),
    F₆, by rw [fa₆ "x" (by decide)]; simp [hσ₅, fa₄ "x" (by decide), hX₃], fun y hy => ?_,
    fun b h1 h2 => ?_, fun b => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [fv₆ y (by simp; tauto)]; simp only [hσ₅, vars_setVar, if_neg hy.2.2.2.2.1]
    rw [fv₄ y (by simp; tauto)]; simp only [hσ₃, vars_setVar, if_neg hy.2.2.2.1, if_neg hy.2.2.1]
    rw [v₂ y (by simp; tauto)]; simp only [hσ₁, vars_setVar, if_neg hy.2.1, if_neg hy.1]
  · rw [fa₆ b h2]; simp only [hσ₅, arrs_setVar]; rw [fa₄ b h1]; simp [hσ₃, a₂, hσ₁]
  · by_cases hb : b = "FW"
    · subst hb; rw [fl₆]; simp only [hσ₅, arrs_setVar]; rw [fa₄ "FW" (by decide)]; simp [hσ₃, a₂, hσ₁]
    · rw [fa₆ b hb]; simp only [hσ₅, arrs_setVar]
      by_cases hb' : b = "GW"
      · subst hb'; rw [fl₄]; simp [hσ₃, a₂, hσ₁]
      · rw [fa₄ b hb']; simp [hσ₃, a₂, hσ₁]
  · rw [fi₆]; simp only [hσ₅, inp_setVar]; rw [fi₄]; simp [hσ₃, fi₂, hσ₁]
  · rw [fo₆]; simp only [hσ₅, out_setVar]; rw [fo₄]; simp [hσ₃, fo₂, hσ₁]

/-! ### After a merge on one vertex -/

theorem flatten_split (L : List (List ℕ)) (v : ℕ) :
    L.flatten = (L.take v).flatten ++ (L.drop v).flatten := by
  rw [← List.flatten_append, List.take_append_drop]

theorem take_flatten_take (L : List (List ℕ)) (v : ℕ) :
    L.flatten.take (L.take v).flatten.length = (L.take v).flatten := by
  rw [flatten_split L v]; exact List.take_left' rfl

theorem drop_flatten_take' (L : List (List ℕ)) (v : ℕ) :
    L.flatten.drop (L.take v).flatten.length = (L.drop v).flatten := by
  rw [flatten_split L v]; exact List.drop_left' rfl

/-- Copy one word of `x` at `y`, preceded by its length, to `FW`. -/
def apOne : Com :=
  .seq (.assign "e1" (.get "x" (.var "y"))) (.seq (cpX "FW" "pf" (.add (.var "y") (.lit 1)) (.var "e1"))
    (.assign "y" (.add (.add (.var "y") (.lit 1)) (.var "e1"))))

theorem apOne_run {W p : ℕ} {τ : Env} {X u R pre : List ℕ} (hX : τ.arrs "x" = X)
    (hy : τ.vars "y" = p) (hd : X.drop p = (u.length :: u) ++ R) (hF : Filled "FW" "pf" pre τ)
    (hcap : pre.length + u.length ≤ (τ.arrs "FW").length) (hB : p + 1 + u.length ≤ W)
    (hB' : pre.length + u.length ≤ W) (hv : ∀ v ∈ X, v ≤ W) :
    ∃ τ', Run (W + 1) apOne τ τ' (30 * u.length + 30) ∧ τ'.vars "y" = p + 1 + u.length ∧
      Filled "FW" "pf" (pre ++ u) τ' ∧
      (∀ y, y ∉ ["e1", "ca", "cl", "ci", "pf", "y"] → τ'.vars y = τ.vars y) ∧
      (∀ b, b ≠ "FW" → τ'.arrs b = τ.arrs b) ∧ (τ'.arrs "FW").length = (τ.arrs "FW").length := by
  have hXl : p + 1 + u.length ≤ X.length := by
    have := congrArg List.length hd; simp at this; omega
  have h0 : X[p]? = some u.length := getElem?_of_drop hd
  set τ₁ := τ.setVar "e1" u.length with hτ₁
  have r₁ : Run (W + 1) (.assign "e1" (.get "x" (.var "y"))) τ τ₁ 3 :=
    (Run.assign (evalB_get (ev_var hy (by omega)) (by rw [hX]; exact h0) (by omega))).mono
      (by simp [Expr.size])
  obtain ⟨τ₂, r₂, F₂, fv₂, fa₂, fl₂, -, -⟩ := cpX_run (W := W) (a := p + 1) (N := u.length)
    (dst := "FW") (pv := "pf") (eS := .add (.var "y") (.lit 1)) (eL := .var "e1") (σ := τ₁)
    (pre := pre) (X := X) (by decide) (by decide) (by simp [hτ₁, hX])
    (ev_add (ev_var (by simp [hτ₁, hy]) (by omega)) (evalB_lit (by omega)) (by omega))
    (ev_var (by simp [hτ₁]) (by omega)) (hF.setVar (by decide) _) hXl
    (by simp [hτ₁]; omega) (by omega) hB' hv
  have hseg : seg X (p + 1) u.length = u := by
    rw [seg_of_drop (A := u.length :: u) hd (by simp only [List.length_cons]; omega)]; simp
  rw [hseg] at F₂
  have hy₂ : τ₂.vars "y" = p := by rw [fv₂ "y" (by decide)]; simp [hτ₁, hy]
  have he₂ : τ₂.vars "e1" = u.length := by rw [fv₂ "e1" (by decide)]; simp [hτ₁]
  refine ⟨τ₂.setVar "y" (p + 1 + u.length), ?_, by simp, F₂.setVar (by decide) _, ?_, ?_, ?_⟩
  · unfold apOne
    refine (Run.seq r₁ (Run.seq r₂ (Run.assign (ev_add (ev_add (ev_var hy₂ (by omega))
      (evalB_lit (by omega)) (by omega)) (ev_var he₂ (by omega)) (by omega))))).mono ?_
    simp only [Expr.size]; omega
  · intro y hy'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    simp only [vars_setVar, if_neg hy'.2.2.2.2.2]
    rw [fv₂ y (by simp; tauto)]; simp [hτ₁, hy'.1]
  · intro b hb; simp only [arrs_setVar]; rw [fa₂ b hb]; simp [hτ₁]
  · simp only [arrs_setVar]; rw [fl₂]; simp [hτ₁]

theorem length_frames_flatten (us : List (List ℕ)) : (frames us).length = us.flatten.length + us.length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    have : frames (u :: us) = (u.length :: u) ++ frames us := rfl
    rw [this, List.length_append, ih]; simp; omega

theorem sum_getD_length (us : List (List ℕ)) :
    ∑ k ∈ Finset.range us.length, (us.getD k []).length = us.flatten.length := by
  induction us with
  | nil => simp
  | cons u us ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.flatten_cons, List.length_append]
    omega

/-- After a merge with `P ≠ Q`: the partial graph recolored with its
matrix of distances, and the family from the answers of the merge lift. -/
noncomputable def apJ : Com :=
  .seq (.assign "rc" (.lit 1)) (.seq cpGW (.seq (.assign "pf" (.lit 0))
  (.seq (push1 "FW" "pf" (.get "x" (.var "bA"))) (.seq (.assign "y" (.add (.var "bA") (.lit 1)))
  (forUp "e4" (.var "gn") apOne)))))

theorem apJ_wvars : apJ.wvars ⊆ ["rc", "pg", "cA", "ci", "ca", "cl", "pf", "y", "e1", "e4"] := by
  intro y hy
  simp only [apJ, apOne, cpGW, cpCol, cpTo, cpX, forUp, push1, Com.wvars,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  tauto

theorem apJ_warrs : apJ.warrs ⊆ ["GW", "FW"] := by
  intro y hy
  simp only [apJ, apOne, cpGW, cpCol, cpTo, cpX, forUp, push1, Com.warrs,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  tauto

theorem apJ_reads : ¬ apJ.reads := by
  simp [apJ, apOne, cpGW, cpCol, cpTo, cpX, forUp, push1, Com.reads]

theorem apJ_noWrite : apJ.NoWrite := by
  simp [apJ, apOne, cpGW, cpCol, cpTo, cpX, forUp, push1, Com.NoWrite]

theorem apJ_run {W n P Q : ℕ} {σ : Env} {X R R'' E : List ℕ} {G : PartialGraph (Fin n)}
    {us : List (List ℕ)} {a b0 : ℕ}
    (hX : σ.arrs "x" = X) (ha : σ.vars "gA" = a) (hd : X.drop a = toWord G ++ E ++ R)
    (hgl : σ.vars "gl" = (toWord G).length + E.length) (hgn : σ.vars "gn" = n)
    (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hPW : P ≤ W) (hQW : Q ≤ W)
    (hus : us.length = n) (hb : σ.vars "bA" = b0)
    (hdb : X.drop b0 = (us.length :: frames us) ++ R'')
    (hcap : (toWord G).length + E.length ≤ (σ.arrs "GW").length)
    (hcapF : 1 + us.flatten.length ≤ (σ.arrs "FW").length)
    (hB : a + 2 * ((toWord G).length + E.length) < W)
    (hBb : b0 + 1 + (frames us).length + 1 < W) (hvX : ∀ v ∈ X, v ≤ W) :
    ∃ σ', Run (W + 1) apJ σ σ' (100 * ((toWord G).length + E.length + (frames us).length) + 100) ∧
      Filled "GW" "pg" ((n :: (List.ofFn G.color).map (recol 1 P Q)) ++
        (toWord G.edge ++ toWord G.nonEdge ++ E)) σ' ∧
      Filled "FW" "pf" (n :: us.flatten) σ' ∧ σ'.arrs "x" = X ∧
      (∀ y, y ∉ ["rc", "pg", "cA", "ci", "ca", "cl", "pf", "y", "e1", "e4"] → σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ "GW" → b ≠ "FW" → σ'.arrs b = σ.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hfr := length_frames_flatten us
  set σ₁ := σ.setVar "rc" 1 with hσ₁
  obtain ⟨σ₂, r₂, F₂⟩ := cpGW_run (W := W) (ρ := 1) (P := P) (Q := Q) (σ := σ₁) (G := G) (a := a)
    (E := E) (by simp [hσ₁, hX]) (by simp [hσ₁, ha]) hd (by simp [hσ₁, hgl]) (by simp [hσ₁, hgn])
    (by simp [hσ₁]) (by simp [hσ₁, hP]) (by simp [hσ₁, hQ]) (by omega) hPW hQW
    (by simpa [hσ₁] using hcap) hB hvX
  have v₂ : ∀ y, y ∉ ["pg", "cA", "ci", "ca", "cl"] → σ₂.vars y = σ₁.vars y :=
    fun y hy => r₂.frame_var_sub y cpGW_frame hy
  have a₂ : ∀ b, b ≠ "GW" → σ₂.arrs b = σ₁.arrs b :=
    fun b hb => r₂.frame_arr b (fun h => hb (by simpa using cpGW_warrs h))
  have hX₂ : σ₂.arrs "x" = X := by rw [a₂ "x" (by decide)]; simp [hσ₁, hX]
  have hFW₂ : (σ₂.arrs "FW").length = (σ.arrs "FW").length := by rw [a₂ "FW" (by decide)]; simp [hσ₁]
  -- the count
  have h0 : X[b0]? = some us.length := getElem?_of_drop hdb
  obtain ⟨σ₃, r₃, F₃, fv₃, fa₃, fl₃, -, -⟩ := push1_run (B := W + 1) (e := .get "x" (.var "bA"))
    (Filled.empty "FW" "pf" σ₂)
    (evalB_get (ev_var (v := b0) (by simp [v₂ "bA" (by decide), hσ₁, hb]) (by omega))
      (by simp [hX₂]; exact h0) (by omega))
    (by simp [hFW₂]; omega) (by simp; omega)
  have hy₄ : (Expr.add (.var "bA") (.lit 1)).evalB (W + 1) σ₃ = some (b0 + 1) :=
    ev_add (ev_var (by rw [fv₃ _ (by decide)]; simp [v₂ "bA" (by decide), hσ₁, hb]) (by omega))
      (evalB_lit (by omega)) (by omega)
  set σ₄ := σ₃.setVar "y" (b0 + 1) with hσ₄
  -- the loop
  obtain ⟨ws, hws⟩ : ∃ ws : List (List ℕ), ws = us.map fun u => u.length :: u := ⟨_, rfl⟩
  have hwf : ws.flatten = frames us := by rw [hws]; rfl
  have hwl : ws.length = us.length := by rw [hws, List.length_map]
  have hdb1 : X.drop (b0 + 1) = ws.flatten ++ R'' := by
    have := drop_add_of_drop (u := [us.length]) (r := ws.flatten ++ R'') (by rw [hdb, hwf]; rfl)
    simpa using this
  have hwg : ∀ k < us.length, ws.getD k [] = (us.getD k []).length :: us.getD k [] := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]; simp [hws]
  have hX₃ : σ₃.arrs "x" = X := by rw [fa₃ "x" (by decide), arrs_setVar, hX₂]
  have hgn₃ : σ₃.vars "gn" = n := by
    rw [fv₃ _ (by decide), vars_setVar, if_neg (by decide), v₂ "gn" (by decide)]; simp [hσ₁, hgn]
  let I : ℕ → Env → Prop := fun k τ => τ.arrs "x" = X ∧ τ.vars "gn" = n ∧
    τ.vars "y" = b0 + 1 + (ws.take k).flatten.length ∧
    Filled "FW" "pf" ([us.length] ++ (us.take k).flatten) τ ∧
    (τ.arrs "FW").length = (σ.arrs "FW").length
  obtain ⟨σ₅, r₅, ⟨hX₅, -, -, F₅, hFW₅⟩, -⟩ := forUp_pot (B := W + 1) (i := "e4") (e := .var "gn")
    (body := apOne) (N := n) (c := 30) (fun k => (us.getD k []).length) I (σ := σ₄) (by omega)
    (fun k _ τ h _ => ev_var h.2.1 (by omega))
    ⟨by simp [hσ₄, hX₃], by simp [hσ₄, hgn₃], by simp [hσ₄],
      by simpa using ((F₃.setVar (y := "y") (by decide) (b0 + 1)).setVar (y := "e4") (by decide) 0),
      by simp [hσ₄, fl₃, hFW₂]⟩
    (by
      intro k hk τ ⟨hXτ, hgτ, hyτ, hFτ, hlτ⟩ hik
      have hku : k < us.length := by omega
      have hkw : k < ws.length := by omega
      have hdk := drop_flatten_take hdb1 hkw
      rw [hwg k hku] at hdk
      have hle := flatten_take_add_le ws hkw
      rw [hwg k hku] at hle
      simp only [List.length_cons] at hle
      have hle' := flatten_take_add_le us hku
      have hwk1 := flatten_take_succ ws hkw
      have huk1 := flatten_take_succ us hku
      rw [hwg k hku] at hwk1
      obtain ⟨τ', r', hy', F', fv', fa', fl'⟩ := apOne_run (W := W) (u := us.getD k [])
        (R := (ws.drop (k + 1)).flatten ++ R'') hXτ hyτ hdk hFτ
        (by rw [hlτ]; simp only [List.length_append, List.length_singleton]; omega)
        (by rw [hwf] at hle; omega) (by simp only [List.length_append, List.length_singleton]; omega)
        hvX
      refine ⟨τ', r', by rw [fv' "e4" (by decide), hik], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [arrs_setVar]; rw [fa' "x" (by decide), hXτ]
      · simp only [vars_setVar, show ("gn" = "e4") = False by decide, if_false]
        rw [fv' "gn" (by decide), hgτ]
      · simp only [vars_setVar, show ("y" = "e4") = False by decide, if_false]
        rw [hy', hwk1, List.length_append, List.length_cons]; omega
      · rw [huk1, ← List.append_assoc]; exact F'.setVar (by decide) _
      · simp only [arrs_setVar]; rw [fl', hlτ])
  have hFW : [us.length] ++ (us.take n).flatten = n :: us.flatten := by
    rw [List.take_of_length_le (by omega), hus]; rfl
  rw [hFW] at F₅
  have hsum : ∑ k ∈ Finset.range n, (us.getD k []).length = us.flatten.length := by
    rw [← hus]; exact sum_getD_length us
  rw [hsum] at r₅
  have rT := Run.seq (Run.assign (B := W + 1) (x := "pf") (σ := σ₂) (evalB_lit (show 0 < W + 1 by omega)))
    (Run.seq r₃ (Run.seq (Run.assign hy₄) r₅))
  have r : Run (W + 1) apJ σ σ₅ (100 * ((toWord G).length + E.length + (frames us).length) + 100) := by
    unfold apJ
    refine (Run.seq (Run.assign (evalB_lit (show 1 < W + 1 by omega))) (Run.seq r₂ rT)).mono ?_
    simp only [Expr.size]
    omega
  refine ⟨σ₅, r, F₂.congr ?_ ?_, F₅, hX₅, fun y hy => r.frame_var_sub y apJ_wvars hy,
    fun b h1 h2 => r.frame_arr b (fun h => by
      have := apJ_warrs h; simp at this; rcases this with rfl | rfl <;> simp_all),
    fun b => run_length_arrs r b, r.frame_inp apJ_reads, r.out_eq apJ_noWrite⟩
  · exact rT.frame_var "pg" (by simp [apOne, cpX, cpTo, forUp, push1, Com.wvars])
  · exact rT.frame_arr "GW" (by simp [apOne, cpX, cpTo, forUp, push1, Com.warrs])

end Lax185574Proofs.MC.Glue
