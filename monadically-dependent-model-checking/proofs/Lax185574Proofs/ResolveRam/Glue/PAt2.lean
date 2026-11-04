import Lax185574Proofs.ResolveRam.Glue.PAt1

/-!
The test `uHopW` on the atom list held in the array `a`, for the atom
words of lem:resolve-lift.

`uHopW` is `hop2W` with the second side replaced by the distances of the
class `Y` from the two colors, read from the color table. `pairU` is the
pair test `pairC` in which the two look-ups of the second side are
replaced by the table tests of the values in `tx` and `tz`
(`pairU_run`), and `uHopC` runs it over all pairs of radii, as `hop2C`
does (`uHopC_run`). Adapted from `pairC_run` and `hop2C_run`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- The table test of the entry `x` at radius `r`. -/
def tabV (x r : ℕ) : Bool := x != 0 && decide (x ≤ r + 1)

theorem tabT_eq (t : ℕ → ℕ) (Y r : ℕ) : tabT t Y r = tabV (t Y) r := rfl

/-- `out := tabV x r`. -/
def tabSet (x r out : String) : Com :=
  .seq (.assign out (.lit 0)) (flagIf (.lt (.lit 0) (.var x)) (.lt (.var x) (.add (.var r) (.lit 2))) out)

theorem tabSet_run {B : ℕ} {x r out : String} {τ : Env} {xv rv : ℕ} (hx : τ.vars x = xv)
    (hr : τ.vars r = rv) (hxo : x ≠ out) (hro : r ≠ out) (hxB : xv < B) (hrB : rv + 2 < B) :
    ∃ τ', Run B (tabSet x r out) τ τ' 20 ∧ τ'.vars out = bv (tabV xv rv) ∧
      (∀ y, y ≠ out → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  set τ1 := τ.setVar out 0
  have r1 : Run B (.assign out (.lit 0)) τ τ1 2 := Run.assign (evalB_lit (by omega))
  have ex : (Expr.var x).evalB B τ1 = some xv := ev_var (by simp [τ1, hxo, hx]) hxB
  have r2 := flagIf_run (B := B) (v := out) (evalB_condLt (evalB_lit (n := 0) (by omega)) ex)
    (fun _ => evalB_condLt ex (ev_add (ev_var (x := r) (v := rv) (by simp [τ1, hro, hr]) (by omega)) (evalB_lit (n := 2) (by omega))
      (by omega))) (by omega)
  refine ⟨_, (Run.seq r1 r2).mono (by simp [Cond.size, Expr.size]), ?_, fun y hy => ?_, ?_, ?_, ?_⟩
  · unfold tabV
    by_cases h1 : 0 < xv <;> by_cases h2 : xv < rv + 2
    · simp [h1, h2, bv]; omega
    · simp [h1, h2, τ1, bv]; omega
    · simp [h1, h2, τ1, bv]; omega
    · simp [h1, h2, τ1, bv]; omega
  · split_ifs <;> simp [τ1, hy]
  · split_ifs <;> simp [τ1]
  · split_ifs <;> simp [τ1]
  · split_ifs <;> simp [τ1]

/-- The test of one pair of radii in `uHopW`, with the table tests `tp`, `tq`. -/
def pairUB (A : List (List ℕ)) (P Q : ℕ) (cP cQ : Bool) (tp tq : ℕ → Bool) (i s s₁ s₂ : ℕ) : Bool :=
  (decide (s₁ + 1 + s₂ ≤ s) && ((nearW A P s₁ i && tq s₂) || (nearW A Q s₁ i && tp s₂))) ||
  (decide (s₁ + 2 + s₂ ≤ s) && ((nearW A P s₁ i && tp s₂ && cQ) || (nearW A Q s₁ i && tq s₂ && cP)))

theorem uHopW_pairUB (Dw : DW) (A : List (List ℕ)) (s Y i : ℕ) :
    uHopW Dw A s Y i = (List.range (s + 1)).any fun s₁ => (List.range (s + 1)).any fun s₂ =>
      pairUB A Dw.P Dw.Q Dw.cP Dw.cQ (tabV (Dw.tP Y)) (tabV (Dw.tQ Y)) i s s₁ s₂ := rfl

/-- One pair of radii `ta`, `tb`. -/
def pairU : Com :=
  .seq (nearSet "a" "tp1" "tP" "ta" "ti1" "tA") (.seq (nearSet "a" "tp1" "tQ" "ta" "ti1" "tB")
  (.seq (tabSet "tx" "tb" "tC") (.seq (tabSet "tz" "tb" "tD")
  (.seq (.assign "tv" (.lit 0)) (.seq (flagIf pc1 pc2 "tv") (flagIf pc3 pc4 "tv"))))))

theorem pairU_wvars : ∀ y ∈ pairU.wvars, y ∈ pV := by
  simp only [pairU, tabSet, nearSet, flagIf, nearC, memScan, memBody, memMatch, memLast, forUp,
    Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.append_nil, or_imp, forall_and, forall_eq]
  simp [pV, mN, mV]

/-- The data of `uHopC`. -/
structure UAt (Xa : List ℕ) (A : List (List ℕ)) (p₁ : ℕ) (Dw : DW) (i s x z : ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = Xa
  p1 : τ.vars "tp1" = p₁
  P : τ.vars "tP" = Dw.P
  Q : τ.vars "tQ" = Dw.Q
  cP : τ.vars "tcP" = bv Dw.cP
  cQ : τ.vars "tcQ" = bv Dw.cQ
  i1 : τ.vars "ti1" = i
  s : τ.vars "ts" = s
  x : τ.vars "tx" = x
  z : τ.vars "tz" = z

/-- The scalars that `UAt` reads. -/
def uN : List String := ["tp1", "tP", "tQ", "tcP", "tcQ", "ti1", "ts", "tx", "tz"]

theorem UAt.congr {Xa : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW} {i s x z : ℕ} {τ τ' : Env}
    (h : UAt Xa A p₁ Dw i s x z τ) (hv : ∀ y ∈ uN, τ'.vars y = τ.vars y) (ha : τ'.arrs = τ.arrs) :
    UAt Xa A p₁ Dw i s x z τ' := by
  obtain ⟨a, p1, P, Q, cP, cQ, i1, s, x, z⟩ := h
  exact ⟨by rw [ha, a], by rw [hv _ (by simp [uN]), p1], by rw [hv _ (by simp [uN]), P],
    by rw [hv _ (by simp [uN]), Q], by rw [hv _ (by simp [uN]), cP], by rw [hv _ (by simp [uN]), cQ],
    by rw [hv _ (by simp [uN]), i1], by rw [hv _ (by simp [uN]), s], by rw [hv _ (by simp [uN]), x],
    by rw [hv _ (by simp [uN]), z]⟩

theorem uAt_setVar {Xa : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW} {i s x z : ℕ} {τ : Env}
    (h : UAt Xa A p₁ Dw i s x z τ) {y : String} (hy : y ∉ uN) (v : ℕ) :
    UAt Xa A p₁ Dw i s x z (τ.setVar y v) :=
  h.congr (fun y' hy' => by
    have : y' ≠ y := fun e => hy (e ▸ hy')
    simp [this]) (by simp)

/-- The bounds of `uHopC`. -/
structure UB (B p₁ : ℕ) (A : List (List ℕ)) (Dw : DW) (i s x z : ℕ) : Prop where
  x1 : p₁ + (toWord A).length + 6 < B
  v1 : ∀ v ∈ toWord A, v < B
  P : Dw.P < B
  Q : Dw.Q < B
  i : i < B
  s : 2 * s + 4 < B
  x : x < B
  z : z < B

/-- **One pair of radii.** -/
theorem pairU_run {B : ℕ} {Xa : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {r₁ : List ℕ} {Dw : DW}
    {i s x z s₁ s₂ : ℕ} {τ : Env}
    (hU : UAt Xa A p₁ Dw i s x z τ) (hd : Xa.drop p₁ = toWord A ++ r₁) (hb : UB B p₁ A Dw i s x z)
    (ha : τ.vars "ta" = s₁) (hb' : τ.vars "tb" = s₂) (hs₁ : s₁ ≤ s) (hs₂ : s₂ ≤ s) :
    ∃ τ', Run B pairU τ τ' (140 * A.length + 400) ∧
      τ'.vars "tv" = bv (pairUB A Dw.P Dw.Q Dw.cP Dw.cQ (tabV x) (tabV z) i s s₁ s₂) ∧
      (∀ y, y ∉ pV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  obtain ⟨hx1, hv1, hPB, hQB, hiB, hsB, hxB, hzB⟩ := hb
  have kp : ∀ y ∈ uN ++ ["ta", "tb"], y ∉ mN ++ mV ∧ y ∉ ["tA", "tB", "tC", "tD", "tv"] := by decide
  have step : ∀ (τa τb : Env) (r : String), r ∈ ["tA", "tB", "tC", "tD"] →
      UAt Xa A p₁ Dw i s x z τa → τa.vars "ta" = s₁ → τa.vars "tb" = s₂ →
      (∀ y, y ∉ mN ++ mV → y ≠ r → τb.vars y = τa.vars y) → τb.arrs = τa.arrs →
      UAt Xa A p₁ Dw i s x z τb ∧ τb.vars "ta" = s₁ ∧ τb.vars "tb" = s₂ := by
    intro τa τb r hr hU' ha' hb'' hf hA
    have kr : ∀ y ∈ uN ++ ["ta", "tb"], τb.vars y = τa.vars y := fun y hy => by
      obtain ⟨k1, k2⟩ := kp y hy
      exact hf y k1 (fun h => k2 (by subst h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto))
    exact ⟨hU'.congr (fun y hy => kr y (List.mem_append_left _ hy)) hA,
      by rw [kr "ta" (by simp), ha'], by rw [kr "tb" (by simp), hb'']⟩
  have nn1 : ∀ y ∈ ["tp1", "tP", "ta", "ti1"], y ∉ mN := by decide
  have nn2 : ∀ y ∈ ["tp1", "tQ", "ta", "ti1"], y ∉ mN := by decide
  obtain ⟨τ1, r1, b1, f1, a1, o1, i1⟩ := nearSet_run (B := B) (r := "tA") nn1 hU.a hd hU.p1
    (by rw [hU.P]; exact hPB) (by rw [ha]; omega) (by rw [hU.i1]; exact hiB) hx1 hv1
  obtain ⟨H1, ha1, hb1⟩ := step τ τ1 "tA" (by simp) hU ha hb' f1 a1
  obtain ⟨τ2, r2, b2, f2, a2, o2, i2⟩ := nearSet_run (B := B) (r := "tB") nn2 H1.a hd H1.p1
    (by rw [H1.Q]; exact hQB) (by rw [ha1]; omega) (by rw [H1.i1]; exact hiB) hx1 hv1
  obtain ⟨H2, ha2, hb2⟩ := step τ1 τ2 "tB" (by simp) H1 ha1 hb1 f2 a2
  obtain ⟨τ3, r3, b3, f3, a3, o3, i3⟩ := tabSet_run (B := B) (out := "tC") H2.x hb2 (by decide) (by decide)
    hxB (by omega)
  obtain ⟨H3, ha3, hb3⟩ := step τ2 τ3 "tC" (by simp) H2 ha2 hb2 (fun y _ hy => f3 y hy) a3
  obtain ⟨τ4, r4, b4, f4, a4, o4, i4⟩ := tabSet_run (B := B) (out := "tD") H3.z hb3 (by decide) (by decide)
    hzB (by omega)
  obtain ⟨H4, ha4, hb4⟩ := step τ3 τ4 "tD" (by simp) H3 ha3 hb3 (fun y _ hy => f4 y hy) a4
  set nA := nearW A Dw.P s₁ i
  set nB := nearW A Dw.Q s₁ i
  set nC := tabV x s₂
  set nD := tabV z s₂
  have vA : τ4.vars "tA" = bv nA := by
    rw [f4 _ (by decide), f3 _ (by decide), f2 _ (by decide) (by decide), b1, hU.P, ha, hU.i1]
  have vB : τ4.vars "tB" = bv nB := by
    rw [f4 _ (by decide), f3 _ (by decide), b2, H1.Q, ha1, H1.i1]
  have vC : τ4.vars "tC" = bv nC := by rw [f4 _ (by decide), b3]
  have vD : τ4.vars "tD" = bv nD := b4
  set τ5 := τ4.setVar "tv" 0
  have r5 : Run B (.assign "tv" (.lit 0)) τ4 τ5 2 := Run.assign (evalB_lit (by omega))
  have bvB : ∀ b : Bool, bv b < B := fun b => lt_of_le_of_lt (bv_le b) (by omega)
  have hm : ∀ a b : Bool, bv a * bv b ≤ 1 := fun a b => by cases a <;> cases b <;> simp [bv]
  have hm3 : ∀ a b c : Bool, bv a * bv b * bv c ≤ 1 := fun a b c => by
    cases a <;> cases b <;> cases c <;> simp [bv]
  have ev : ∀ τ' : Env, (∀ y ∈ ["tA", "tB", "tC", "tD", "ta", "tb", "ts", "tcP", "tcQ"],
      τ'.vars y = τ5.vars y) →
      pc1.evalB B τ' = some (decide (s₁ + s₂ < s)) ∧
      pc2.evalB B τ' = some (decide (0 < bv nA * bv nD + bv nB * bv nC)) ∧
      pc3.evalB B τ' = some (decide (s₁ + s₂ + 1 < s)) ∧
      pc4.evalB B τ' = some (decide (0 < bv nA * bv nC * bv Dw.cQ + bv nB * bv nD * bv Dw.cP)) := by
    intro τ' hτ'
    have g : ∀ y ∈ ["tA", "tB", "tC", "tD", "ta", "tb", "ts", "tcP", "tcQ"], τ'.vars y = τ4.vars y :=
      fun y hy => by
        rw [hτ' y hy]
        have : y ≠ "tv" := by intro h; subst h; simp at hy
        simp [τ5, this]
    have eA := ev_var (B := B) (by rw [g "tA" (by simp), vA]) (bvB nA)
    have eB := ev_var (B := B) (by rw [g "tB" (by simp), vB]) (bvB nB)
    have eC := ev_var (B := B) (by rw [g "tC" (by simp), vC]) (bvB nC)
    have eD := ev_var (B := B) (by rw [g "tD" (by simp), vD]) (bvB nD)
    have ecP := ev_var (B := B) (by rw [g "tcP" (by simp), H4.cP]) (bvB Dw.cP)
    have ecQ := ev_var (B := B) (by rw [g "tcQ" (by simp), H4.cQ]) (bvB Dw.cQ)
    have ea := ev_var (B := B) (by rw [g "ta" (by simp), ha4]) (show s₁ < B by omega)
    have eb := ev_var (B := B) (by rw [g "tb" (by simp), hb4]) (show s₂ < B by omega)
    have es := ev_var (B := B) (by rw [g "ts" (by simp), H4.s]) (show s < B by omega)
    refine ⟨evalB_condLt (ev_add ea eb (by omega)) es, evalB_condLt (evalB_lit (by omega))
      (ev_add (evalB_bin eA eD (lt_of_le_of_lt (hm nA nD) (by omega)))
        (evalB_bin eB eC (lt_of_le_of_lt (hm nB nC) (by omega)))
        (lt_of_le_of_lt (Nat.add_le_add (hm nA nD) (hm nB nC)) (by omega))),
      evalB_condLt (ev_add (ev_add ea eb (by omega)) (evalB_lit (by omega)) (by omega)) es,
      evalB_condLt (evalB_lit (by omega)) (ev_add
        (evalB_bin (evalB_bin eA eC (lt_of_le_of_lt (hm nA nC) (by omega))) ecQ
          (lt_of_le_of_lt (hm3 nA nC Dw.cQ) (by omega)))
        (evalB_bin (evalB_bin eB eD (lt_of_le_of_lt (hm nB nD) (by omega))) ecP
          (lt_of_le_of_lt (hm3 nB nD Dw.cP) (by omega)))
        (lt_of_le_of_lt (Nat.add_le_add (hm3 nA nC Dw.cQ) (hm3 nB nD Dw.cP)) (by omega)))⟩
  obtain ⟨c1, c2, -, -⟩ := ev τ5 (fun _ _ => rfl)
  have r6 := flagIf_run (v := "tv") c1 (fun _ => c2) (by omega)
  set τ6 := if decide (s₁ + s₂ < s) && decide (0 < bv nA * bv nD + bv nB * bv nC) then
    τ5.setVar "tv" 1 else τ5
  have h56 : ∀ y, y ≠ "tv" → τ6.vars y = τ5.vars y := fun y hy => by
    simp only [τ6]; split_ifs <;> simp [hy]
  obtain ⟨-, -, c3, c4⟩ := ev τ6 (fun y hy => h56 y (by intro h; subst h; simp at hy))
  have r7 := flagIf_run (v := "tv") c3 (fun _ => c4) (by omega)
  set τ7 := if decide (s₁ + s₂ + 1 < s) &&
    decide (0 < bv nA * bv nC * bv Dw.cQ + bv nB * bv nD * bv Dw.cP) then τ6.setVar "tv" 1 else τ6
  have hτ6v : τ6.vars "tv" = bv (decide (s₁ + s₂ < s) && (nA && nD || nB && nC)) := by
    simp only [τ6, bv_mul_add, Bool.decide_eq_true]
    split_ifs with h
    · simp only [vars_setVar, if_true]; rw [h]; rfl
    · simp only [Bool.not_eq_true] at h; rw [h]; simp [τ5]
  have a67 : τ7.arrs = τ4.arrs := by simp only [τ7, τ6, τ5]; split_ifs <;> simp
  have o67 : τ7.out = τ4.out ∧ τ7.inp = τ4.inp := by simp only [τ7, τ6, τ5]; split_ifs <;> simp
  refine ⟨τ7, ?_, ?_, fun y hy => ?_, ?_, ?_, ?_⟩
  · unfold pairU
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono ?_
    simp only [pc1, pc2, pc3, pc4, Cond.size, Expr.size]
    omega
  · have : τ7.vars "tv" = if decide (s₁ + s₂ + 1 < s) &&
        decide (0 < bv nA * bv nC * bv Dw.cQ + bv nB * bv nD * bv Dw.cP) then 1 else τ6.vars "tv" := by
      simp only [τ7]; split_ifs <;> simp
    rw [this, hτ6v]
    simp only [bv_mul3_add, Bool.decide_eq_true]
    rw [ite_bv]
    unfold pairUB
    rw [show decide (s₁ + 1 + s₂ ≤ s) = decide (s₁ + s₂ < s) from decide_eq_decide.mpr (by omega),
      show decide (s₁ + 2 + s₂ ≤ s) = decide (s₁ + s₂ + 1 < s) from decide_eq_decide.mpr (by omega)]
  · have hp : y ∉ mN ++ mV ∧ y ≠ "tA" ∧ y ≠ "tB" ∧ y ≠ "tC" ∧ y ≠ "tD" ∧ y ≠ "tv" := by
      simp only [pV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      exact ⟨by simp only [List.mem_append, not_or]; exact ⟨hy.1.1, hy.1.2⟩, hy.2⟩
    have h7 : τ7.vars y = τ6.vars y := by simp only [τ7]; split_ifs <;> simp [hp.2.2.2.2.2]
    rw [h7, h56 y hp.2.2.2.2.2]
    simp only [τ5, vars_setVar, hp.2.2.2.2.2, if_false]
    rw [f4 y hp.2.2.2.2.1, f3 y hp.2.2.2.1, f2 y hp.1 hp.2.2.1, f1 y hp.1 hp.2.1]
  · rw [a67, a4, a3, a2, a1]
  · rw [o67.1, o4, o3, o2, o1]
  · rw [o67.2, i4, i3, i2, i1]

/-! ### All pairs of radii -/

/-- The loop over the second radius. -/
def innerU : Com := anyLoop "tb" "tn" "tu" "tv" pairU

/-- One round of the loop over the first radius. -/
def outerU : Com := .seq (.assign "tu" (.lit 0)) innerU

/-- **The test `uHopW`.** -/
def uHopC : Com :=
  .seq (.assign "tn" (.add (.var "ts") (.lit 1))) (.seq (.assign "tw" (.lit 0))
    (anyLoop "ta" "tn" "tw" "tu" outerU))

theorem uHopC_wvars : ∀ y ∈ uHopC.wvars, y ∈ hV := by
  have := pairU_wvars
  intro y hy
  by_cases hp : y ∈ pairU.wvars
  · exact List.mem_append_left _ (this y hp)
  · simp only [uHopC, outerU, innerU, anyLoop, forUp, Com.wvars, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.append_nil, hp, false_or] at hy
    simp only [hV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

theorem uHopC_warrs : uHopC.warrs = [] := by
  simp [uHopC, outerU, innerU, anyLoop, forUp, pairU, tabSet, nearSet, flagIf, Com.warrs, nearC_warrs]

theorem uHopC_reads : ¬ uHopC.reads := by
  have := nearC_reads "a" "tp1" "tP" "ta" "ti1"
  have := nearC_reads "a" "tp1" "tQ" "ta" "ti1"
  simp_all [uHopC, outerU, innerU, anyLoop, forUp, pairU, tabSet, nearSet, flagIf, Com.reads]

theorem uHopC_noWrite : uHopC.NoWrite := by
  have := nearC_noWrite "a" "tp1" "tP" "ta" "ti1"
  have := nearC_noWrite "a" "tp1" "tQ" "ta" "ti1"
  simp_all [uHopC, outerU, innerU, anyLoop, forUp, pairU, tabSet, nearSet, flagIf, Com.NoWrite]

/-- **The test `uHopW`.** -/
theorem uHopC_run {B : ℕ} {Xa : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {r₁ : List ℕ} {Dw : DW}
    {i s x z : ℕ} {τ : Env}
    (hH : UAt Xa A p₁ Dw i s x z τ) (hd₁ : Xa.drop p₁ = toWord A ++ r₁) (hb : UB B p₁ A Dw i s x z) :
    ∃ τ', Run B uHopC τ τ' (hopK (A.length + A.length) s) ∧
      τ'.vars "tw" = bv ((List.range (s + 1)).any fun s₁ => (List.range (s + 1)).any fun s₂ =>
        pairUB A Dw.P Dw.Q Dw.cP Dw.cQ (tabV x) (tabV z) i s s₁ s₂) ∧
      (∀ y, y ∉ hV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hsB := hb.s
  set L := A.length + A.length
  set N := s + 1
  set Kp := 140 * L + 400
  set f : ℕ → ℕ → Bool := fun s₁ s₂ => pairUB A Dw.P Dw.Q Dw.cP Dw.cQ (tabV x) (tabV z) i s s₁ s₂
  -- the inner loop
  have hin : ∀ (c : ℕ) (w0 : ℕ), c < N → Spec B (fun τ => UAt Xa A p₁ Dw i s x z τ ∧
        τ.vars "ta" = c ∧ τ.vars "tn" = N ∧ τ.vars "tw" = w0) outerU
      (fun τ τ' => UAt Xa A p₁ Dw i s x z τ' ∧ τ'.vars "ta" = c ∧
        τ'.vars "tn" = N ∧ τ'.vars "tw" = τ.vars "tw" ∧
        τ'.vars "tu" = bv ((List.range N).any (f c))) (N * (Kp + 20) + 9) := by
    rintro c w0 hc τ0 ⟨H0, a0, n0, w00⟩
    let C : Env → Prop := fun τ => UAt Xa A p₁ Dw i s x z τ ∧
      τ.vars "ta" = c ∧ τ.vars "tw" = w0
    have hCs : ∀ τ (z : String) x, z ∈ ["tb", "tu"] → C τ → C (τ.setVar z x) := by
      intro τ z x hz ⟨h1, h2, h3⟩
      have h4 : z ≠ "ta" := by simp at hz; rcases hz with rfl | rfl <;> decide
      have h5 : z ≠ "tw" := by simp at hz; rcases hz with rfl | rfl <;> decide
      exact ⟨uAt_setVar h1 (by simp at hz; rcases hz with rfl | rfl <;> decide) x,
        by simp [Ne.symm h4, h2], by simp [Ne.symm h5, h3]⟩
    set τ1 := τ0.setVar "tu" 0
    have r1 : Run B (.assign "tu" (.lit 0)) τ0 τ1 2 := Run.assign (evalB_lit (by omega))
    obtain ⟨τ2, r2, ⟨H2, a2, w2⟩, u2, n2⟩ := anyLoop_run (B := B) (i := "tb") (n := "tn") (flag := "tu")
      (v := "tv") (body := pairU) C (f c) N Kp (by omega) (by decide) (by decide) (by decide)
      (fun τ x h => hCs τ "tb" x (by simp) h) (fun τ x h => hCs τ "tu" x (by simp) h)
      (by
        rintro c2 hc2 τ ⟨⟨Hτ, aτ, wτ⟩, bτ, nτ, -⟩
        obtain ⟨τ', r', v', f', a', o', i'⟩ := pairU_run Hτ hd₁ hb aτ bτ (by omega) (by omega)
        have k : ∀ y ∈ uN ++ ["ta", "tb", "tn", "tu", "tw"], y ∉ pV := by decide
        exact ⟨τ', r'.mono (by omega), ⟨Hτ.congr (fun y hy => f' y (k y (List.mem_append_left _ hy))) a',
          by rw [f' _ (k _ (by simp)), aτ], by rw [f' _ (k _ (by simp)), wτ]⟩,
          by rw [f' _ (k _ (by simp)), bτ], by rw [f' _ (k _ (by simp)), nτ],
          f' _ (k _ (by simp)), v'⟩)
      τ1 ⟨hCs τ0 "tu" 0 (by simp) ⟨H0, a0, w00⟩, by simp [τ1, n0], by simp [τ1]⟩
    refine ⟨τ2, ?_, H2, a2, n2, by rw [w2, w00], u2⟩
    unfold outerU innerU
    exact (Run.seq r1 r2).mono (by omega)
  -- the outer loop
  set τ1 := τ.setVar "tn" N
  set τ2 := τ1.setVar "tw" 0
  have r1 : Run B (.assign "tn" (.add (.var "ts") (.lit 1))) τ τ1 4 :=
    (Run.assign (ev_add (ev_var hH.s (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have r2 : Run B (.assign "tw" (.lit 0)) τ1 τ2 2 := Run.assign (evalB_lit (by omega))
  have hτ2 : UAt Xa A p₁ Dw i s x z τ2 :=
    uAt_setVar (uAt_setVar hH (by decide) N) (by decide) 0
  obtain ⟨τ3, r3, H3, w3, n3⟩ := anyLoop_run (B := B) (i := "ta") (n := "tn") (flag := "tw")
    (v := "tu") (body := outerU) (UAt Xa A p₁ Dw i s x z)
    (fun c => (List.range N).any (f c)) N (N * (Kp + 20) + 9) (by omega) (by decide) (by decide)
    (by decide) (fun τ x h => uAt_setVar h (by decide) x) (fun τ x h => uAt_setVar h (by decide) x)
    (by
      rintro c hc τ' ⟨Hτ, aτ, nτ, -⟩
      obtain ⟨τ'', r'', H'', a'', n'', w'', u''⟩ := hin c (τ'.vars "tw") hc τ' ⟨Hτ, aτ, nτ, rfl⟩
      exact ⟨τ'', r'', H'', a'', n'', w'', u''⟩)
    τ2 ⟨hτ2, by simp [τ2, τ1], by simp [τ2]⟩
  have hrun : Run B uHopC τ τ3 (hopK L s) := by
    unfold uHopC
    refine (Run.seq r1 (Run.seq r2 r3)).mono ?_
    simp only [hopK, Kp, N]
    nlinarith
  obtain ⟨fa, fo, fi⟩ := run_frame hrun uHopC_warrs uHopC_reads uHopC_noWrite
  refine ⟨τ3, hrun, by rw [w3], fun y hy => hrun.frame_var y
    (fun h => hy (uHopC_wvars y h)), fa, fo, fi⟩

end Lax185574Proofs.ResolveRam.Glue
