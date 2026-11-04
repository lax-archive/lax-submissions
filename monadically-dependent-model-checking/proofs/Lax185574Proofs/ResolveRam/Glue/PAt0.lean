import Lax185574Proofs.ResolveRam.Glue.PLv2

/-!
Tools for the atom words of a tree in lem:resolve-lift.

`lkG` looks up a target word of length three or four, given by five
expressions, in the atom list at `tp1` of the array `a` (`lkG_run`). The
expressions are literals or scalars outside the target, so they keep
their values while the target is written (`EvS`).

The candidate word is held in the scalars `tdL`, `td0`, …, `td3`
(`TdAt`), written by `setD3` and `setD4`. `emitC T` tests the candidate:
it looks it up, runs the extra test `T` if it is not an atom of the
tree, and appends its frame if one of the two holds (`emitC_run`). The
output so far is the placeholder of the count and the frames of the list
`L`, with `fc = |L|` (`Em`). `emLoop_run` is a counting loop whose round
`k` appends the words `g k`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-! ### Looking up a target word -/

/-- The expression `e` has the value `v` in every environment that agrees
with `τ` outside the target. -/
def EvS (B : ℕ) (e : Expr) (τ : Env) (v : ℕ) : Prop :=
  ∀ ρ : Env, (∀ y, y ∉ mN → ρ.vars y = τ.vars y) → e.evalB B ρ = some v

theorem evS_lit {B n : ℕ} (τ : Env) (h : n < B) : EvS B (.lit n) τ n := fun _ _ => evalB_lit h

theorem evS_var {B : ℕ} {y : String} {τ : Env} {v : ℕ} (hy : y ∉ mN) (h : τ.vars y = v) (hv : v < B) :
    EvS B (.var y) τ v := fun ρ hρ => ev_var (by rw [hρ y hy, h]) hv

/-- Look up the target given by the five expressions in the list at `tp1` of `a`. -/
def lkG (eL e0 e1 e2 e3 : Expr) : Com :=
  .seq (.assign "tmp" (.var "tp1")) (.seq (.assign "tmL" eL) (.seq (.assign "tm0" e0)
    (.seq (.assign "tm1" e1) (.seq (.assign "tm2" e2) (.seq (.assign "tm3" e3) (memScan "a"))))))

theorem setVar_agree {σ ρ : Env} (h : ∀ y, y ∉ mN → ρ.vars y = σ.vars y) {x : String} (hx : x ∈ mN)
    (v : ℕ) : ∀ y, y ∉ mN → (ρ.setVar x v).vars y = σ.vars y := fun y hy => by
  have : y ≠ x := fun e => hy (e ▸ hx)
  simp [this, h y hy]

/-- **A look-up.** -/
theorem lkG_run {B : ℕ} {eL e0 e1 e2 e3 : Expr} {Xa : List ℕ} {p : ℕ} {A : List (List ℕ)} {r t : List ℕ}
    {v3 : ℕ} {σ : Env} (hX : σ.arrs "a" = Xa) (hdr : Xa.drop p = toWord A ++ r) (hp : σ.vars "tp1" = p)
    (ht : t.length = 3 ∨ t.length = 4) (hL : EvS B eL σ t.length) (h0 : EvS B e0 σ (t.getD 0 0))
    (h1 : EvS B e1 σ (t.getD 1 0)) (h2 : EvS B e2 σ (t.getD 2 0)) (h3 : EvS B e3 σ v3)
    (h3' : t.length = 4 → v3 = t.getD 3 0)
    (hs : eL.size = 1 ∧ e0.size = 1 ∧ e1.size = 1 ∧ e2.size = 1 ∧ e3.size = 1)
    (htB : ∀ v ∈ t, v < B) (hB : 5 < B) (hpB : p + (toWord A).length + 2 < B)
    (hv : ∀ v ∈ toWord A, v < B) :
    ∃ σ', Run B (lkG eL e0 e1 e2 e3) σ σ' (70 * A.length + 50) ∧ σ'.vars "tmb" = bv (inW A t) ∧
      (∀ y, y ∉ mN ++ mV → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  obtain ⟨sL, s0, s1, s2, s3⟩ := hs
  have g0 : ∀ y, y ∉ mN → σ.vars y = σ.vars y := fun _ _ => rfl
  set σ1 := σ.setVar "tmp" p
  have g1 := setVar_agree g0 (x := "tmp") (by decide) p
  set σ2 := σ1.setVar "tmL" t.length
  have g2 := setVar_agree g1 (x := "tmL") (by decide) t.length
  set σ3 := σ2.setVar "tm0" (t.getD 0 0)
  have g3 := setVar_agree g2 (x := "tm0") (by decide) (t.getD 0 0)
  set σ4 := σ3.setVar "tm1" (t.getD 1 0)
  have g4 := setVar_agree g3 (x := "tm1") (by decide) (t.getD 1 0)
  set σ5 := σ4.setVar "tm2" (t.getD 2 0)
  have g5 := setVar_agree g4 (x := "tm2") (by decide) (t.getD 2 0)
  set σ6 := σ5.setVar "tm3" v3
  have hpB' : p < B := by omega
  have r1 : Run B (.assign "tmp" (.var "tp1")) σ σ1 2 := Run.assign (ev_var hp hpB')
  have r2 : Run B (.assign "tmL" eL) σ1 σ2 2 := (Run.assign (hL σ1 g1)).mono (by omega)
  have r3 : Run B (.assign "tm0" e0) σ2 σ3 2 := (Run.assign (h0 σ2 g2)).mono (by omega)
  have r4 : Run B (.assign "tm1" e1) σ3 σ4 2 := (Run.assign (h1 σ3 g3)).mono (by omega)
  have r5 : Run B (.assign "tm2" e2) σ4 σ5 2 := (Run.assign (h2 σ4 g4)).mono (by omega)
  have r6 : Run B (.assign "tm3" e3) σ5 σ6 2 := (Run.assign (h3 σ5 g5)).mono (by omega)
  have htg : TargetAt t σ6 := ⟨ht, by simp [σ6, σ5, σ4, σ3, σ2], by simp [σ6, σ5, σ4, σ3],
    by simp [σ6, σ5, σ4], by simp [σ6, σ5], fun h => by simp [σ6, h3' h]⟩
  obtain ⟨σ7, r7, b7, v7, a7, o7, i7⟩ := memScan_run (B := B) (A := "a") (σ := σ6)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hX]) hdr (by simp [σ6, σ5, σ4, σ3, σ2, σ1]) htg htB hB hpB hv
  refine ⟨σ7, ?_, ?_, fun y hy => ?_, by rw [a7]; simp [σ6, σ5, σ4, σ3, σ2, σ1],
    by rw [o7]; simp [σ6, σ5, σ4, σ3, σ2, σ1], by rw [i7]; simp [σ6, σ5, σ4, σ3, σ2, σ1]⟩
  · unfold lkG
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono
      (by omega)
  · rw [b7]; simp [inW, bv]
  · simp only [List.mem_append, not_or] at hy
    rw [v7 y hy.2]
    have : y ≠ "tm3" := by intro h; subst h; simp [mN] at hy
    simp only [σ6, vars_setVar, this, if_false]
    exact g5 y hy.1

/-! ### The candidate word -/

/-- The scalars of the candidate. -/
def tdN : List String := ["tdL", "td0", "td1", "td2", "td3"]

/-- The candidate word `c` is in the scalars `tdL`, `td0`, …, `td3`. -/
def TdAt (c : List ℕ) (τ : Env) : Prop :=
  (c.length = 3 ∨ c.length = 4) ∧ τ.vars "tdL" = c.length ∧ τ.vars "td0" = c.getD 0 0 ∧
    τ.vars "td1" = c.getD 1 0 ∧ τ.vars "td2" = c.getD 2 0 ∧ τ.vars "td3" = c.getD 3 0

theorem TdAt.congr {c : List ℕ} {τ τ' : Env} (h : TdAt c τ) (hv : ∀ y ∈ tdN, τ'.vars y = τ.vars y) :
    TdAt c τ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv "tdL" (by simp [tdN]), h2]
  · rw [hv "td0" (by simp [tdN]), h3]
  · rw [hv "td1" (by simp [tdN]), h4]
  · rw [hv "td2" (by simp [tdN]), h5]
  · rw [hv "td3" (by simp [tdN]), h6]

/-- Write the candidate `[d, y1, y2]`. -/
def setD3 (d : ℕ) (y1 y2 : String) : Com :=
  .seq (.assign "tdL" (.lit 3)) (.seq (.assign "td0" (.lit d)) (.seq (.assign "td1" (.var y1))
    (.seq (.assign "td2" (.var y2)) (.assign "td3" (.lit 0)))))

/-- Write the candidate `[d, y1, y2, y3]`. -/
def setD4 (d : ℕ) (y1 y2 y3 : String) : Com :=
  .seq (.assign "tdL" (.lit 4)) (.seq (.assign "td0" (.lit d)) (.seq (.assign "td1" (.var y1))
    (.seq (.assign "td2" (.var y2)) (.assign "td3" (.var y3)))))

theorem setD3_run {B d : ℕ} {y1 y2 : String} {τ : Env} (h1 : y1 ∉ tdN) (h2 : y2 ∉ tdN) (hd : d < B)
    (hv1 : τ.vars y1 < B) (hv2 : τ.vars y2 < B) (h4 : 4 < B) :
    ∃ τ', Run B (setD3 d y1 y2) τ τ' 10 ∧ TdAt [d, τ.vars y1, τ.vars y2] τ' ∧ OFr τ τ' tdN ∧
      τ'.arrs = τ.arrs := by
  simp only [tdN, List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2
  refine ⟨((((τ.setVar "tdL" 3).setVar "td0" d).setVar "td1" (τ.vars y1)).setVar "td2"
    (τ.vars y2)).setVar "td3" 0, ?_,
    ⟨Or.inl rfl, by simp, by simp, by simp, by simp, by simp⟩,
    (((((OFr.setVar τ "tdL" 3).trans (OFr.setVar _ "td0" d)).trans (OFr.setVar _ "td1" _)).trans
      (OFr.setVar _ "td2" _)).trans (OFr.setVar _ "td3" _)).mono (by decide), by simp⟩
  unfold setD3
  refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit hd))
    (Run.seq (Run.assign (ev_var (v := τ.vars y1) (by simp [h1.1, h1.2.1]) hv1))
      (Run.seq (Run.assign (ev_var (v := τ.vars y2) (by simp [h2.1, h2.2.1,
        h2.2.2.1]) hv2)) (Run.assign (evalB_lit (by omega))))))).mono (by simp [Expr.size])

theorem setD4_run {B d : ℕ} {y1 y2 y3 : String} {τ : Env} (h1 : y1 ∉ tdN) (h2 : y2 ∉ tdN)
    (h3 : y3 ∉ tdN) (hd : d < B) (hv1 : τ.vars y1 < B) (hv2 : τ.vars y2 < B) (hv3 : τ.vars y3 < B)
    (h4 : 4 < B) :
    ∃ τ', Run B (setD4 d y1 y2 y3) τ τ' 10 ∧ TdAt [d, τ.vars y1, τ.vars y2, τ.vars y3] τ' ∧
      OFr τ τ' tdN ∧ τ'.arrs = τ.arrs := by
  simp only [tdN, List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2 h3
  refine ⟨((((τ.setVar "tdL" 4).setVar "td0" d).setVar "td1" (τ.vars y1)).setVar "td2"
    (τ.vars y2)).setVar "td3" (τ.vars y3), ?_,
    ⟨Or.inr rfl, by simp, by simp, by simp, by simp, by simp⟩,
    (((((OFr.setVar τ "tdL" 4).trans (OFr.setVar _ "td0" d)).trans (OFr.setVar _ "td1" _)).trans
      (OFr.setVar _ "td2" _)).trans (OFr.setVar _ "td3" _)).mono (by decide), by simp⟩
  unfold setD4
  refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit hd))
    (Run.seq (Run.assign (ev_var (v := τ.vars y1) (by simp [h1.1, h1.2.1]) hv1))
      (Run.seq (Run.assign (ev_var (v := τ.vars y2) (by simp [h2.1, h2.2.1,
        h2.2.2.1]) hv2))
      (Run.assign (ev_var (v := τ.vars y3) (by simp [h3.1, h3.2.1, h3.2.2.1,
        h3.2.2.2.1]) hv3)))))).mono (by simp [Expr.size])

/-! ### Emitting a candidate -/

/-- The output: the placeholder of the count and the frames of `L`. -/
def Em (pre : List ℕ) (L : List (List ℕ)) (τ : Env) : Prop :=
  Filled "OB" "po" (pre ++ [0] ++ frames L) τ ∧ τ.vars "fc" = L.length

theorem Em.congr {pre : List ℕ} {L : List (List ℕ)} {τ τ' : Env} (h : Em pre L τ)
    (hp : τ'.vars "po" = τ.vars "po") (hf : τ'.vars "fc" = τ.vars "fc") (ha : τ'.arrs "OB" = τ.arrs "OB") :
    Em pre L τ' := ⟨h.1.congr hp ha, by rw [hf, h.2]⟩

theorem Em.setVar {pre : List ℕ} {L : List (List ℕ)} {τ : Env} (h : Em pre L τ) {y : String}
    (h1 : y ≠ "po") (h2 : y ≠ "fc") (v : ℕ) : Em pre L (τ.setVar y v) :=
  h.congr (by simp [Ne.symm h1]) (by simp [Ne.symm h2]) (by simp)

/-- Append the frame of the candidate. -/
def emPush : Com :=
  .seq (push1 "OB" "po" (.var "tdL")) (.seq (push1 "OB" "po" (.var "td0"))
    (.seq (push1 "OB" "po" (.var "td1")) (.seq (push1 "OB" "po" (.var "td2"))
      (.seq (.ite (.eq (.var "tdL") (.lit 4)) (push1 "OB" "po" (.var "td3")) .skip)
        (.assign "fc" (.add (.var "fc") (.lit 1)))))))

theorem word_of_len3 {c : List ℕ} (h : c.length = 3) : c = [c.getD 0 0, c.getD 1 0, c.getD 2 0] := by
  match c, h with
  | [a, b, d], _ => rfl

theorem word_of_len4 {c : List ℕ} (h : c.length = 4) :
    c = [c.getD 0 0, c.getD 1 0, c.getD 2 0, c.getD 3 0] := by
  match c, h with
  | [a, b, d, e], _ => rfl

theorem emPush_run {W : ℕ} {c pre : List ℕ} {L : List (List ℕ)} {τ : Env} (hc : TdAt c τ)
    (hcv : ∀ v ∈ c, v ≤ W) (hE : Em pre L τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ [c])).length ≤ W) :
    ∃ τ', Run (W + 1) emPush τ τ' 50 ∧ Em pre (L ++ [c]) τ' ∧ OFr τ τ' ["po", "fc"] := by
  obtain ⟨hl, hL, h0, h1, h2, h3⟩ := hc
  obtain ⟨hF, hfc⟩ := hE
  have hfl : (frames (L ++ [c])).length = (frames L).length + 1 + c.length := by
    rw [frames_append, frames_single]; simp; omega
  have hge : ∀ j, c.getD j 0 ≤ W := fun j => by
    rcases Nat.lt_or_ge j c.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hcv _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; omega
  have hcl : c.length ≤ 4 := by omega
  set l0 := pre ++ [0] ++ frames L
  have hl0 : l0.length = pre.length + 1 + (frames L).length := by simp [l0]; omega
  have hLl : L.length ≤ (frames L).length := by rw [Words.length_frames]; omega
  obtain ⟨τ1, r1, F1, o1⟩ := push1_ofr (W := W) (e := .var "tdL") (v := c.length) hF (ev_var hL (by omega))
    (by rw [hOB]; omega) (by omega)
  have k1 : ∀ y ∈ tdN, τ1.vars y = τ.vars y := fun y hy => o1.vars y (by
    intro h; simp at h; subst h; simp [tdN] at hy)
  obtain ⟨τ2, r2, F2, o2⟩ := push1_ofr (W := W) (e := .var "td0") (v := c.getD 0 0) F1
    (ev_var (by rw [k1 "td0" (by simp [tdN]), h0]) (by have := hge 0; omega))
    (by rw [o1.len, hOB]; simp; omega) (by simp; omega)
  have k2 : ∀ y ∈ tdN, τ2.vars y = τ.vars y := fun y hy => by
    rw [o2.vars y (by intro h; simp at h; subst h; simp [tdN] at hy), k1 y hy]
  obtain ⟨τ3, r3, F3, o3⟩ := push1_ofr (W := W) (e := .var "td1") (v := c.getD 1 0) F2
    (ev_var (by rw [k2 "td1" (by simp [tdN]), h1]) (by have := hge 1; omega))
    (by rw [o2.len, o1.len, hOB]; simp; omega) (by simp; omega)
  have k3 : ∀ y ∈ tdN, τ3.vars y = τ.vars y := fun y hy => by
    rw [o3.vars y (by intro h; simp at h; subst h; simp [tdN] at hy), k2 y hy]
  obtain ⟨τ4, r4, F4, o4⟩ := push1_ofr (W := W) (e := .var "td2") (v := c.getD 2 0) F3
    (ev_var (by rw [k3 "td2" (by simp [tdN]), h2]) (by have := hge 2; omega))
    (by rw [o3.len, o2.len, o1.len, hOB]; simp; omega) (by simp; omega)
  have k4 : ∀ y ∈ tdN, τ4.vars y = τ.vars y := fun y hy => by
    rw [o4.vars y (by intro h; simp at h; subst h; simp [tdN] at hy), k3 y hy]
  have o14 := ((o1.trans o2).trans o3).trans o4
  have hc4 := evalB_condEq (B := W + 1) (σ := τ4) (ev_var (by rw [k4 "tdL" (by simp [tdN]), hL])
    (show c.length < W + 1 by omega)) (evalB_lit (n := 4) (by omega))
  have h5 : ∃ τ5, Run (W + 1) (.ite (.eq (.var "tdL") (.lit 4)) (push1 "OB" "po" (.var "td3")) .skip)
      τ4 τ5 12 ∧ Filled "OB" "po" (l0 ++ [c.length] ++ c) τ5 ∧ OFr τ4 τ5 ["po"] := by
    rcases hl with h | h
    · refine ⟨τ4, (Run.ite_false (by rw [hc4, h]; rfl) Run.skip).mono (by simp [Cond.size, Expr.size]),
        ?_, (OFr.refl _).mono (by simp)⟩
      rw [word_of_len3 h]; simpa [List.append_assoc, h] using F4
    · obtain ⟨τ5, r5, F5, o5⟩ := push1_ofr (W := W) (e := .var "td3") (v := c.getD 3 0) F4
        (ev_var (by rw [k4 "td3" (by simp [tdN]), h3]) (by have := hge 3; omega))
        (by rw [o14.len, hOB]; simp; omega) (by simp; omega)
      refine ⟨τ5, (Run.ite_true (by rw [hc4, h]; rfl) r5).mono (by simp [Cond.size, Expr.size]), ?_, o5⟩
      rw [word_of_len4 h]; simpa [List.append_assoc, h] using F5
  obtain ⟨τ5, r5, F5, o5⟩ := h5
  have hfc5 : τ5.vars "fc" = L.length := by rw [o5.vars "fc" (by decide), o14.vars "fc" (by decide), hfc]
  refine ⟨τ5.setVar "fc" (L.length + 1), ?_, ⟨?_, by simp⟩, ((o14.trans o5).trans
    (OFr.setVar τ5 "fc" _)).mono (by decide)⟩
  · unfold emPush
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.assign
      (ev_add (ev_var hfc5 (by omega)) (evalB_lit (by omega)) (by omega)))))))).mono ?_
    simp [Expr.size]
  · have e : pre ++ [0] ++ frames (L ++ [c]) = l0 ++ [c.length] ++ c := by
      simp [l0, frames_append, frames_single]
    rw [e]; exact F5.setVar (by decide) _

/-- Test the candidate, with the extra test `T`, and append it if it passes. -/
def emitC (T : Com) : Com :=
  .seq (lkG (.var "tdL") (.var "td0") (.var "td1") (.var "td2") (.var "td3"))
    (.seq (.assign "tF" (.var "tmb")) (.seq (.ite (.eq (.var "tF") (.lit 0)) T .skip)
      (.ite (.eq (.var "tF") (.lit 1)) emPush .skip)))

/-- The scalars of the look-up and the flag. -/
def lkV : List String := mN ++ mV ++ ["tF"]

/-- **Testing and emitting a candidate.** The extra test `T` runs only if
the candidate is not an atom, and then sets `tF` to `extra`. -/
theorem emitC_run {W : ℕ} {T : Com} {A : List (List ℕ)} {Xa r : List ℕ} {p₁ : ℕ} {c pre : List ℕ}
    {L : List (List ℕ)} {extra : Bool} {KT : ℕ} {VT : List String} {τ : Env}
    (ha : τ.arrs "a" = Xa) (hd : Xa.drop p₁ = toWord A ++ r) (hp : τ.vars "tp1" = p₁)
    (hc : TdAt c τ) (hcv : ∀ v ∈ c, v ≤ W) (hB1 : p₁ + (toWord A).length + 2 < W + 1)
    (hv : ∀ v ∈ toWord A, v < W + 1) (hE : Em pre L τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ if (inW A c || extra) then [c] else [])).length ≤ W)
    (hW5 : 5 ≤ W)
    (hT : ∀ τ1, OFr τ τ1 lkV → τ1.arrs = τ.arrs → τ1.vars "tF" = 0 →
      ∃ τ2, Run (W + 1) T τ1 τ2 KT ∧ τ2.vars "tF" = bv extra ∧ OFr τ1 τ2 VT ∧ τ2.arrs = τ1.arrs)
    (hVT : ∀ y ∈ VT, y ∉ tdN ∧ y ≠ "po" ∧ y ≠ "fc") :
    ∃ τ', Run (W + 1) (emitC T) τ τ' (70 * A.length + KT + 120) ∧
      Em pre (L ++ if (inW A c || extra) then [c] else []) τ' ∧ OFr τ τ' (lkV ++ VT ++ ["po", "fc"]) := by
  have hc' := hc
  obtain ⟨hl, hL, h0, h1, h2, h3⟩ := hc
  have hge : ∀ j, c.getD j 0 ≤ W := fun j => by
    rcases Nat.lt_or_ge j c.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hcv _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; omega
  have hge' : ∀ j, c.getD j 0 < W + 1 := fun j => by have := hge j; omega
  have hcl : c.length ≤ 4 := by omega
  -- the look-up
  obtain ⟨τ1, r1, b1, f1, a1, -, -⟩ := lkG_run (B := W + 1) (t := c) (v3 := c.getD 3 0) ha hd hp hl
    (evS_var (by decide) hL (by omega)) (evS_var (by decide) h0 (hge' 0))
    (evS_var (by decide) h1 (hge' 1)) (evS_var (by decide) h2 (hge' 2))
    (evS_var (by decide) h3 (hge' 3)) (fun _ => rfl) ⟨rfl, rfl, rfl, rfl, rfl⟩
    (fun v hv' => by have := hcv v hv'; omega) (by omega) hB1 hv
  have o1 : OFr τ τ1 (mN ++ mV) := by
    refine ⟨f1, fun b _ => by rw [a1], by rw [a1], ?_, ?_⟩
    · exact (run_frame r1 (by simp [lkG, Com.warrs, memScan_warrs])
        (by have := memScan_reads "a"; simp_all [lkG, Com.reads])
        (by have := memScan_noWrite "a"; simp_all [lkG, Com.NoWrite])).2.1
    · exact (run_frame r1 (by simp [lkG, Com.warrs, memScan_warrs])
        (by have := memScan_reads "a"; simp_all [lkG, Com.reads])
        (by have := memScan_noWrite "a"; simp_all [lkG, Com.NoWrite])).2.2
  set τ2 := τ1.setVar "tF" (bv (inW A c))
  have r2 : Run (W + 1) (.assign "tF" (.var "tmb")) τ1 τ2 2 :=
    Run.assign (ev_var b1 (by have := bv_le (inW A c); omega))
  have o2 : OFr τ τ2 lkV := (o1.trans (OFr.setVar τ1 "tF" _)).mono (by decide)
  have a2 : τ2.arrs = τ.arrs := by simp [τ2, a1]
  -- the extra test
  have h3 : ∃ τ3, Run (W + 1) (.ite (.eq (.var "tF") (.lit 0)) T .skip) τ2 τ3 (KT + 5) ∧
      τ3.vars "tF" = bv (inW A c || extra) ∧ OFr τ τ3 (lkV ++ VT) ∧ τ3.arrs = τ.arrs := by
    have hcnd := evalB_condEq (B := W + 1) (σ := τ2)
      (ev_var (x := "tF") (v := bv (inW A c)) (by simp [τ2]) (by have := bv_le (inW A c); omega))
      (evalB_lit (n := 0) (by omega))
    cases hi : inW A c
    · rw [hi] at hcnd
      obtain ⟨τ3, r3, v3, o3, a3⟩ := hT τ2 o2 a2 (by simp [τ2, hi, bv])
      exact ⟨τ3, (Run.ite_true (by rw [hcnd]; rfl) r3).mono (by simp [Cond.size, Expr.size]; omega),
        by rw [v3]; rfl, o2.trans o3, by rw [a3, a2]⟩
    · rw [hi] at hcnd
      exact ⟨τ2, (Run.ite_false (by rw [hcnd]; rfl) Run.skip).mono (by simp [Cond.size, Expr.size]),
        by simp [τ2, hi], o2.mono (by simp), a2⟩
  obtain ⟨τ3, r3, v3, o3, a3⟩ := h3
  have k3 : ∀ y, y ∈ tdN ∨ y = "po" ∨ y = "fc" → y ∉ lkV ++ VT := by
    intro y hy hm
    rcases List.mem_append.1 hm with h | h
    · rcases hy with h' | rfl | rfl
      · simp [tdN] at h'; rcases h' with rfl | rfl | rfl | rfl | rfl <;> simp [lkV, mN, mV] at h
      · simp [lkV, mN, mV] at h
      · simp [lkV, mN, mV] at h
    · obtain ⟨n1, n2, n3⟩ := hVT y h
      rcases hy with h' | rfl | rfl
      · exact n1 h'
      · exact n2 rfl
      · exact n3 rfl
  have hc3 : TdAt c τ3 := hc'.congr fun y hy => o3.vars y (k3 y (Or.inl hy))
  have hE3 : Em pre L τ3 := hE.congr (o3.vars "po" (k3 _ (Or.inr (Or.inl rfl))))
    (o3.vars "fc" (k3 _ (Or.inr (Or.inr rfl)))) (by rw [a3])
  have hcnd := evalB_condEq (B := W + 1) (σ := τ3)
    (ev_var (x := "tF") (v := bv (inW A c || extra)) v3 (by have := bv_le (inW A c || extra); omega))
    (evalB_lit (n := 1) (by omega))
  have hOB3 : (τ3.arrs "OB").length = W + 1 := by rw [a3, hOB]
  cases hb : (inW A c || extra)
  · rw [hb] at hcnd
    refine ⟨τ3, ?_, by simpa using hE3, o3.mono (by simp)⟩
    unfold emitC
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.ite_false (by rw [hcnd]; rfl) Run.skip)))).mono ?_
    simp [Cond.size, Expr.size]; omega
  · rw [hb] at hcnd
    obtain ⟨τ4, r4, E4, o4⟩ := emPush_run hc3 hcv hE3 hOB3 (by simpa [hb] using hB)
    refine ⟨τ4, ?_, by simpa using E4, (o3.trans o4).mono (by simp)⟩
    unfold emitC
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.ite_true (by rw [hcnd]; rfl) r4)))).mono ?_
    simp [Cond.size, Expr.size]; omega

/-! ### A loop that appends words -/

theorem range_flatMap_succ (g : ℕ → List (List ℕ)) (k : ℕ) :
    (List.range (k + 1)).flatMap g = (List.range k).flatMap g ++ g k := by
  simp [List.range_succ, List.flatMap_append]

theorem frames_flatMap_range_le (g : ℕ → List (List ℕ)) {k N : ℕ} (h : k ≤ N) (L0 : List (List ℕ)) :
    (frames (L0 ++ (List.range k).flatMap g)).length ≤
      (frames (L0 ++ (List.range N).flatMap g)).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.flatMap_append, ← List.append_assoc, frames_append (L0 ++ _),
    List.length_append]
  omega

/-- **A counting loop that appends words.** Round `k` appends `g k`. -/
theorem emLoop_run {W N K : ℕ} {v : String} {e : Expr} {body : Com} (g : ℕ → List (List ℕ))
    (C : Env → Prop) {pre : List ℕ} {L0 : List (List ℕ)} {σ : Env}
    (hv1 : v ≠ "po") (hv2 : v ≠ "fc") (hN : N < W + 1)
    (he : ∀ τ, C τ → e.evalB (W + 1) τ = some N) (hC : ∀ τ x, C τ → C (τ.setVar v x))
    (h0 : C σ) (hE0 : Em pre L0 σ)
    (hB : pre.length + 1 + (frames (L0 ++ (List.range N).flatMap g)).length ≤ W)
    (hstep : ∀ k < N, ∀ (L : List (List ℕ)) (τ : Env), C τ → τ.vars v = k → Em pre L τ →
      pre.length + 1 + (frames (L ++ g k)).length ≤ W →
      ∃ τ', Run (W + 1) body τ τ' K ∧ τ'.vars v = k ∧ C τ' ∧ Em pre (L ++ g k) τ') :
    ∃ σ', Run (W + 1) (forUp v e body) σ σ' (N * (K + e.size + 7) + e.size + 5) ∧ C σ' ∧
      Em pre (L0 ++ (List.range N).flatMap g) σ' := by
  obtain ⟨σ', r, ⟨C', E'⟩, -⟩ := forUp_run (B := W + 1) (i := v) (e := e) (body := body) (N := N)
    (K := K) (fun k τ => C τ ∧ Em pre (L0 ++ (List.range k).flatMap g) τ) (σ := σ) hN
    (fun k _ τ hI _ => he τ hI.1) ⟨hC _ _ h0, by simpa using hE0.setVar hv1 hv2 0⟩
    (by
      rintro k hk τ ⟨Cτ, Eτ⟩ hkτ
      have hb : pre.length + 1 + (frames (L0 ++ (List.range k).flatMap g ++ g k)).length ≤ W := by
        have := frames_flatMap_range_le g (k := k + 1) (N := N) hk L0
        rw [range_flatMap_succ, ← List.append_assoc] at this; omega
      obtain ⟨τ', r', v', C', E'⟩ := hstep k hk _ τ Cτ hkτ Eτ hb
      refine ⟨τ', r', v', hC _ _ C', ?_⟩
      rw [range_flatMap_succ, ← List.append_assoc]; exact E'.setVar hv1 hv2 _)
  exact ⟨σ', r, C', E'⟩

end Lax185574Proofs.ResolveRam.Glue
