import Lax185574Proofs.ResolveRam.Glue.PAt0

/-!
The extra tests of the new atoms of an edge, a non-edge and a distance
bound, for the atom words of lem:resolve-lift.

`lkS d y1 y2 r` looks up `[d, y1, y2]` in the atom list and keeps the
answer in `r` (`lkS_run`). `crossT d g` is the extra test of the
candidate `[1, i, j]` (with `d = 2`, `g = 1`) and of `[2, i, j]` (with
`d = 1`, `g = 0`): the sign is `g`, the positions carry `P` and `Q`, and
neither `[0, i, j]` nor `[d, i, j]` is an atom (`crossT_run`). `hopT` is
the extra test `hopW` of the candidate `[4, s, i, j]` (`hopT_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- Look up `[d, y1, y2]` and keep the answer in `r`. -/
def lkS (d : ℕ) (y1 y2 r : String) : Com :=
  .seq (lkG (.lit 3) (.lit d) (.var y1) (.var y2) (.lit 0)) (.assign r (.var "tmb"))

theorem lkG_frame (eL e0 e1 e2 e3 : Expr) {B : ℕ} {σ σ' : Env} {K : ℕ}
    (h : Run B (lkG eL e0 e1 e2 e3) σ σ' K) : σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have := (run_frame h (by simp [lkG, Com.warrs, memScan_warrs])
    (by have := memScan_reads "a"; simp_all [lkG, Com.reads])
    (by have := memScan_noWrite "a"; simp_all [lkG, Com.NoWrite]))
  exact ⟨this.2.1, this.2.2⟩

/-- **A look-up kept in a scalar.** -/
theorem lkS_run {W d : ℕ} {y1 y2 r : String} {A : List (List ℕ)} {Xa rr : List ℕ} {p₁ : ℕ} {τ : Env}
    (ha : τ.arrs "a" = Xa) (hd : Xa.drop p₁ = toWord A ++ rr) (hp : τ.vars "tp1" = p₁)
    (h1 : y1 ∉ mN) (h2 : y2 ∉ mN) (hdW : d ≤ W) (hv1 : τ.vars y1 ≤ W) (hv2 : τ.vars y2 ≤ W)
    (hW : 5 ≤ W) (hB1 : p₁ + (toWord A).length + 2 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1) :
    ∃ τ', Run (W + 1) (lkS d y1 y2 r) τ τ' (70 * A.length + 52) ∧
      τ'.vars r = bv (inW A [d, τ.vars y1, τ.vars y2]) ∧ OFr τ τ' (mN ++ mV ++ [r]) ∧
      τ'.arrs = τ.arrs := by
  obtain ⟨τ1, r1, b1, f1, a1, o1, i1⟩ := lkG_run (B := W + 1) (t := [d, τ.vars y1, τ.vars y2])
    (v3 := 0) ha hd hp (Or.inl rfl) (evS_lit τ (by simp; omega)) (evS_lit τ (by simp; omega))
    (evS_var h1 (by simp) (by simp; omega)) (evS_var h2 (by simp) (by simp; omega)) (evS_lit τ (by omega))
    (fun h => absurd h (by simp)) ⟨rfl, rfl, rfl, rfl, rfl⟩
    (by intro v hv'; simp at hv'; rcases hv' with rfl | rfl | rfl <;> omega) (by omega) hB1 hv
  have hb : bv (inW A [d, τ.vars y1, τ.vars y2]) < W + 1 := by have := bv_le (inW A [d, τ.vars y1, τ.vars y2]); omega
  refine ⟨τ1.setVar r (bv (inW A [d, τ.vars y1, τ.vars y2])), ?_, by simp,
    ((show OFr τ τ1 (mN ++ mV) from ⟨f1, fun b _ => by rw [a1], by rw [a1], o1, i1⟩).trans
      (OFr.setVar τ1 r _)), by simp [a1]⟩
  exact (Run.seq r1 (Run.assign (ev_var b1 hb))).mono (by simp [Expr.size])

/-! ### The edges and the non-edges -/

/-- The extra test of `[1, i, j]` (`d = 2`, `g = 1`) and of `[2, i, j]` (`d = 1`, `g = 0`). -/
def crossT (d g : ℕ) : Com :=
  .seq (lkS 3 "tP" "td1" "tA") (.seq (lkS 3 "tQ" "td1" "tB") (.seq (lkS 3 "tP" "td2" "tC")
    (.seq (lkS 3 "tQ" "td2" "tD") (.seq (lkS 0 "td1" "td2" "tG") (.seq (lkS d "td1" "td2" "tH")
      (.ite (.eq (.var "tsg") (.lit g)) (flagIf pc2 (.eq (.add (.var "tG") (.var "tH")) (.lit 0)) "tF")
        .skip))))))

/-- The scalars that `crossT` writes. -/
def crV : List String := mN ++ mV ++ ["tA", "tB", "tC", "tD", "tG", "tH", "tF"]

theorem crossW_bv (Dw : DW) (A : List (List ℕ)) (i j : ℕ) :
    crossW Dw A i j = (inW A [3, Dw.P, i] && inW A [3, Dw.Q, j] || inW A [3, Dw.Q, i] && inW A [3, Dw.P, j]) :=
  rfl

/-- **The extra test of an edge or a non-edge.** -/
theorem crossT_run {W d g : ℕ} {A : List (List ℕ)} {Xa rr : List ℕ} {p₁ : ℕ} {Dw : DW} {i j : ℕ}
    {τ : Env} (ha : τ.arrs "a" = Xa) (hd : Xa.drop p₁ = toWord A ++ rr) (hp : τ.vars "tp1" = p₁)
    (hP : τ.vars "tP" = Dw.P) (hQ : τ.vars "tQ" = Dw.Q) (hsg : τ.vars "tsg" = bv Dw.sg)
    (hi : τ.vars "td1" = i) (hj : τ.vars "td2" = j) (hF : τ.vars "tF" = 0)
    (hPW : Dw.P ≤ W) (hQW : Dw.Q ≤ W) (hiW : i ≤ W) (hjW : j ≤ W) (hdW : d ≤ W) (hgW : g ≤ W)
    (hW : 5 ≤ W) (hB1 : p₁ + (toWord A).length + 2 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1) :
    ∃ τ', Run (W + 1) (crossT d g) τ τ' (420 * A.length + 400) ∧
      τ'.vars "tF" = bv (decide (bv Dw.sg = g) && crossW Dw A i j && !inW A [0, i, j] &&
        !inW A [d, i, j]) ∧ OFr τ τ' crV ∧ τ'.arrs = τ.arrs := by
  have kp : ∀ (ρ : Env) (Vs : List String), OFr τ ρ Vs → ρ.arrs = τ.arrs →
      (∀ y ∈ ["tp1", "tP", "tQ", "tsg", "td1", "td2", "tF"], y ∉ Vs) →
      ρ.arrs "a" = Xa ∧ ρ.vars "tp1" = p₁ ∧ ρ.vars "tP" = Dw.P ∧ ρ.vars "tQ" = Dw.Q ∧
        ρ.vars "td1" = i ∧ ρ.vars "td2" = j ∧ ρ.vars "tsg" = bv Dw.sg ∧ ρ.vars "tF" = 0 := by
    intro ρ Vs o hA hn
    exact ⟨by rw [hA, ha], by rw [o.vars _ (hn _ (by simp)), hp], by rw [o.vars _ (hn _ (by simp)), hP],
      by rw [o.vars _ (hn _ (by simp)), hQ], by rw [o.vars _ (hn _ (by simp)), hi],
      by rw [o.vars _ (hn _ (by simp)), hj], by rw [o.vars _ (hn _ (by simp)), hsg],
      by rw [o.vars _ (hn _ (by simp)), hF]⟩
  obtain ⟨τ1, r1, b1, o1, a1⟩ := lkS_run (W := W) (d := 3) (y1 := "tP") (y2 := "td1") (r := "tA") ha hd hp
    (by decide) (by decide) (by omega) (by omega) (by omega) hW hB1 hv
  obtain ⟨ha1, hp1, hP1, hQ1, hi1, hj1, hs1, hF1⟩ := kp τ1 _ o1 a1 (by decide)
  obtain ⟨τ2, r2, b2, o2, a2⟩ := lkS_run (W := W) (d := 3) (y1 := "tQ") (y2 := "td1") (r := "tB") ha1 hd hp1
    (by decide) (by decide) (by omega) (by omega) (by omega) hW hB1 hv
  have o12 := o1.trans o2
  obtain ⟨ha2, hp2, hP2, hQ2, hi2, hj2, hs2, hF2⟩ := kp τ2 _ o12 (by rw [a2, a1]) (by decide)
  obtain ⟨τ3, r3, b3, o3, a3⟩ := lkS_run (W := W) (d := 3) (y1 := "tP") (y2 := "td2") (r := "tC") ha2 hd hp2
    (by decide) (by decide) (by omega) (by omega) (by omega) hW hB1 hv
  have o13 := o12.trans o3
  obtain ⟨ha3, hp3, hP3, hQ3, hi3, hj3, hs3, hF3⟩ := kp τ3 _ o13 (by rw [a3, a2, a1]) (by decide)
  obtain ⟨τ4, r4, b4, o4, a4⟩ := lkS_run (W := W) (d := 3) (y1 := "tQ") (y2 := "td2") (r := "tD") ha3 hd hp3
    (by decide) (by decide) (by omega) (by omega) (by omega) hW hB1 hv
  have o14 := o13.trans o4
  obtain ⟨ha4, hp4, hP4, hQ4, hi4, hj4, hs4, hF4⟩ := kp τ4 _ o14 (by rw [a4, a3, a2, a1]) (by decide)
  obtain ⟨τ5, r5, b5, o5, a5⟩ := lkS_run (W := W) (d := 0) (y1 := "td1") (y2 := "td2") (r := "tG") ha4 hd hp4
    (by decide) (by decide) (by omega) (by omega) (by omega) hW hB1 hv
  have o15 := o14.trans o5
  obtain ⟨ha5, hp5, hP5, hQ5, hi5, hj5, hs5, hF5⟩ := kp τ5 _ o15 (by rw [a5, a4, a3, a2, a1]) (by decide)
  obtain ⟨τ6, r6, b6, o6, a6⟩ := lkS_run (W := W) (d := d) (y1 := "td1") (y2 := "td2") (r := "tH") ha5 hd hp5
    (by decide) (by decide) hdW (by omega) (by omega) hW hB1 hv
  have o16 := o15.trans o6
  obtain ⟨-, -, -, -, -, -, hs6, hF6⟩ := kp τ6 _ o16 (by rw [a6, a5, a4, a3, a2, a1]) (by decide)
  -- the values of the look-ups
  set nA := inW A [3, Dw.P, i]
  set nB := inW A [3, Dw.Q, i]
  set nC := inW A [3, Dw.P, j]
  set nD := inW A [3, Dw.Q, j]
  set nG := inW A [0, i, j]
  set nH := inW A [d, i, j]
  have vA : τ6.vars "tA" = bv nA := by
    rw [(((o2.trans o3).trans o4).trans o5 |>.trans o6).vars "tA" (by decide), b1, hP, hi]
  have vB : τ6.vars "tB" = bv nB := by
    rw [((o3.trans o4).trans o5 |>.trans o6).vars "tB" (by decide), b2, hQ1, hi1]
  have vC : τ6.vars "tC" = bv nC := by
    rw [((o4.trans o5).trans o6).vars "tC" (by decide), b3, hP2, hj2]
  have vD : τ6.vars "tD" = bv nD := by rw [(o5.trans o6).vars "tD" (by decide), b4, hQ3, hj3]
  have vG : τ6.vars "tG" = bv nG := by rw [o6.vars "tG" (by decide), b5, hi4, hj4]
  have vH : τ6.vars "tH" = bv nH := by rw [b6, hi5, hj5]
  have bvB : ∀ b : Bool, bv b < W + 1 := fun b => lt_of_le_of_lt (bv_le b) (by omega)
  have hm : ∀ a b : Bool, bv a * bv b ≤ 1 := fun a b => by cases a <;> cases b <;> simp [bv]
  have c1 := evalB_condEq (B := W + 1) (σ := τ6) (ev_var hs6 (bvB Dw.sg)) (evalB_lit (n := g) (by omega))
  have c2 : pc2.evalB (W + 1) τ6 = some (decide (0 < bv nA * bv nD + bv nB * bv nC)) :=
    evalB_condLt (evalB_lit (by omega))
      (ev_add (evalB_bin (ev_var vA (bvB nA)) (ev_var vD (bvB nD)) (lt_of_le_of_lt (hm nA nD) (by omega)))
        (evalB_bin (ev_var vB (bvB nB)) (ev_var vC (bvB nC)) (lt_of_le_of_lt (hm nB nC) (by omega)))
        (lt_of_le_of_lt (Nat.add_le_add (hm nA nD) (hm nB nC)) (by omega)))
  have c3 := evalB_condEq (B := W + 1) (σ := τ6) (ev_add (ev_var vG (bvB nG)) (ev_var vH (bvB nH))
    (by have := bv_le nG; have := bv_le nH; omega)) (evalB_lit (n := 0) (by omega))
  have hval : bv (decide (bv Dw.sg = g) && crossW Dw A i j && !nG && !nH) =
      if ((bv Dw.sg == g) && (decide (0 < bv nA * bv nD + bv nB * bv nC) &&
        (bv nG + bv nH == 0))) = true then 1 else 0 := by
    have key : ∀ (a b c e f h : Bool) (x : ℕ), bv (decide (x = g) && (a && e || b && c) && !f && !h) =
        if ((x == g) && (decide (0 < bv a * bv e + bv b * bv c) && (bv f + bv h == 0))) = true then 1
        else 0 := by
      intro a b c e f h x
      cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> cases h <;>
        by_cases hg : x = g <;> simp [bv, hg]
    rw [crossW_bv]; exact key nA nB nC nD nG nH (bv Dw.sg)
  set τ7 := if ((bv Dw.sg == g) && (decide (0 < bv nA * bv nD + bv nB * bv nC) &&
    (bv nG + bv nH == 0))) = true then τ6.setVar "tF" 1 else τ6
  have r7 : Run (W + 1) (.ite (.eq (.var "tsg") (.lit g))
      (flagIf pc2 (.eq (.add (.var "tG") (.var "tH")) (.lit 0)) "tF") .skip) τ6 τ7 30 := by
    simp only [τ7]
    cases hb1 : (bv Dw.sg == g)
    · rw [hb1] at c1
      exact (Run.ite_false c1 Run.skip).mono (by simp [Cond.size, Expr.size])
    · rw [hb1] at c1
      have := flagIf_run (B := W + 1) (v := "tF") c2 (fun _ => c3) (by omega)
      refine (Run.ite_true c1 this).mono ?_
      simp [pc2, Cond.size, Expr.size]
  refine ⟨τ7, ?_, ?_, ?_, ?_⟩
  · unfold crossT
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono ?_
    omega
  · rw [hval]; simp only [τ7]; split_ifs <;> simp [hF6]
  · have o7 : OFr τ6 τ7 ["tF"] := by
      simp only [τ7]; split_ifs
      · exact OFr.setVar τ6 "tF" 1
      · exact (OFr.refl τ6).mono (by simp)
    exact (o16.trans o7).mono (by decide)
  · simp only [τ7]; split_ifs <;> simp [a6, a5, a4, a3, a2, a1]

/-! ### The distance bounds -/

/-- The extra test of `[4, s, i, j]`. -/
def hopT : Com :=
  .seq (.assign "ts" (.var "td1")) (.seq (.assign "ti1" (.var "td2")) (.seq (.assign "ti2" (.var "td3"))
    (.seq (hop2C "a" "a") (.assign "tF" (.var "tw")))))

/-- The scalars that `hopT` writes. -/
def hoV : List String := ["ts", "ti1", "ti2"] ++ hV ++ ["tF"]

/-- **The extra test of a distance bound.** -/
theorem hopT_run {W : ℕ} {A : List (List ℕ)} {Xa rr : List ℕ} {p₁ : ℕ} {Dw : DW} {s i j : ℕ}
    {τ : Env} (ha : τ.arrs "a" = Xa) (hd : Xa.drop p₁ = toWord A ++ rr) (hp : τ.vars "tp1" = p₁)
    (hp2 : τ.vars "tp2" = p₁) (hP : τ.vars "tP" = Dw.P) (hQ : τ.vars "tQ" = Dw.Q)
    (hcP : τ.vars "tcP" = bv Dw.cP) (hcQ : τ.vars "tcQ" = bv Dw.cQ)
    (hs : τ.vars "td1" = s) (hi : τ.vars "td2" = i) (hj : τ.vars "td3" = j)
    (hPW : Dw.P ≤ W) (hQW : Dw.Q ≤ W) (hiW : i ≤ W) (hjW : j ≤ W) (hsW : 2 * s + 4 ≤ W)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1) :
    ∃ τ', Run (W + 1) hopT τ τ' (hopK (A.length + A.length) s + 10) ∧
      τ'.vars "tF" = bv (hopW Dw A s i j) ∧ OFr τ τ' hoV ∧ τ'.arrs = τ.arrs := by
  set τ1 := ((τ.setVar "ts" s).setVar "ti1" i).setVar "ti2" j
  have hH : HopAt "a" "a" Xa Xa A A p₁ p₁ Dw i j s τ1 :=
    ⟨by simp [τ1, ha], by simp [τ1, ha], by simp [τ1, hp], by simp [τ1, hp2], by simp [τ1, hP],
      by simp [τ1, hQ], by simp [τ1, hcP], by simp [τ1, hcQ], by simp [τ1], by simp [τ1], by simp [τ1]⟩
  obtain ⟨τ2, r2, w2, f2, a2, o2, i2⟩ := hop2C_run (B := W + 1) hH hd hd
    ⟨hB1, hB1, hv, hv, by omega, by omega, by omega, by omega, by omega⟩
  have hb : bv (hop2W Dw A i A j s) < W + 1 := by have := bv_le (hop2W Dw A i A j s); omega
  set τ3 := τ2.setVar "tF" (bv (hop2W Dw A i A j s))
  have r3 : Run (W + 1) (.assign "tF" (.var "tw")) τ2 τ3 2 := Run.assign (ev_var w2 hb)
  refine ⟨τ3, ?_, by simp [τ3, hopW], ?_, by simp [τ3, a2, τ1]⟩
  · unfold hopT
    exact (Run.seq (Run.assign (ev_var hs (by omega))) (Run.seq (Run.assign (ev_var (v := i)
      (by simp [hi]) (by omega))) (Run.seq (Run.assign (ev_var (v := j) (by simp [hj]) (by omega)))
        (Run.seq r2 r3)))).mono (by simp [Expr.size]; omega)
  · refine ⟨fun y hy => ?_, fun b _ => by simp [τ3, a2, τ1], by simp [τ3, a2, τ1], by simp [τ3, o2, τ1],
      by simp [τ3, i2, τ1]⟩
    simp only [hoV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [τ3, vars_setVar, hy.2, if_false]
    rw [f2 y hy.1.2]
    simp [τ1, hy.1.1.1, hy.1.1.2.1, hy.1.1.2.2]

end Lax185574Proofs.ResolveRam.Glue
