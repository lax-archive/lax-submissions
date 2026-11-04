import Lax185574Proofs.MC.Glue.Cmd

/-!
Runs of the glue command of thm:mc on the input of round `0`.

`glue_top`: reading the tag and saturating `dK` into `zk`. `glue0_run`:
on `0 :: |x| :: x ++ [0]` for `x = [n] ++ toWord σ ++ toWord φ`, the command
sets `ovf` when `n = 0`, and otherwise outputs the head and the query of
the first call when `ovf` stays `0`, which it does when the word size
admits the fixed words, the bounds of round `0`, and the checks of the
writer.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees

variable {n : ℕ}

theorem glue_top {W t : ℕ} {σ : Env} {rest : List ℕ} (hinp : σ.inp = t :: rest)
    (hW : σ.vars "W" = W) (hW1 : 1 ≤ W) :
    ∃ τ, Run (W + 1) (.seq (.read "tg") (satLit "zk" dK)) σ τ (30 * dK + 31) ∧ τ.vars "tg" = t ∧
      τ.vars "zk" = min dK W ∧ (∀ y, y ≠ "tg" → y ≠ "zk" → τ.vars y = σ.vars y) ∧
      τ.arrs = σ.arrs ∧ τ.out = σ.out ∧ τ.inp = rest := by
  obtain ⟨τ₁, r₁, hv₁, ha₁, hi₁, ho₁⟩ := read_run (B := W + 1) (x := "tg") (v := t) (rest := rest) hinp
  obtain ⟨τ₂, r₂, hz₂, fv₂, fa₂, fo₂, fi₂⟩ := satLit_run (B := W + 1) (z := "zk") (by decide) (by omega)
    hW1 dK τ₁ (by rw [hv₁]; simp [hW])
  refine ⟨τ₂, (Run.seq r₁ r₂).mono (by omega), by rw [fv₂ _ (by decide), hv₁]; simp, hz₂,
    fun y h1 h2 => by rw [fv₂ y h2, hv₁]; simp [h1], by rw [fa₂, ha₁], by rw [fo₂, ho₁],
    by rw [fi₂, hi₁]⟩

/-- The cost of round `0` with its call. -/
noncomputable def glue0C (eM eR eE d q x L : ℕ) : ℕ :=
  r0C q * (x + 1) + 16 * x + 750 * L + 700 * dK + 60 * (eM + eR + eE + 1) + 30 * 2 ^ d + 30 * dK + 4000

theorem r0_workQ (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n) :
    realQ (ckOf (call0 hn σ.steps)) (cPOf (call0 hn σ.steps)) (cQOf (call0 hn σ.steps))
      (csOf (call0 hn σ.steps)) (gwOf σ.run σ.steps.length (call0 hn σ.steps))
      (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length (call0 hn σ.steps))
      (trOf σ.run (Lax3.FirstOrder.rank φ) (call0 hn σ.steps))
      (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) =
    workQ σ.run (Lax3.FirstOrder.rank φ) φ (call0 hn σ.steps) :=
  realQ_call _ _ _ _ _

theorem round0_noWrite : round0.NoWrite := by
  simp [pushL, afterF, apAll, apJ, apOne, dmRow, dmInit, jbOne, apR, apS, buildInit, copyBack, copyTa, cpCol, cpGW, cpLo, cpSeg, cpTo, cpX, entChk, evEnd, fAnd, fAtom, fBody, fEmit, fEx, fLoop, fNot, fPop, fWalk, fwInit, fwTree, guardChk, guardSel, gwCols, gwInit, gwZeros, hdr1, issue, lastChk, ldL, ldSc, levelBody, locT, mBound, mInit, mxBody, mxSeg, nxF, outEnd, powers, push1, r0Chk2, r0Ev, r0Fields, r0Fill, r0Main, r0Step, rdIn, rdWin, read0, readInto, readOne, round0, roundJ, rpBody, rpTab, satAdd, satInc, satMul, satPow, setIf, sizeChk, skipG, skipL, skipLs, skipPG, skipT, stF, tLoc, tag1, tag2, tagSet, wAtoms, wCDist, wCol, wDist, wEq, wExts, wLevel, wq0, wq1, wq2, wq3, wrAll, wrHd, wrQ, forUp, ldNames, scN, cntE, cdistL, cdistRow, colL, distBlk, distL, distRow, eqL, eqRow, Com.NoWrite]

set_option maxHeartbeats 1000000 in
theorem glue0_run {W eM eR eE d : ℕ} (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hW63 : 63 ≤ W)
    (hent : ∀ e ∈ 0 :: ([n] ++ toWord σ ++ toWord φ).length :: (([n] ++ toWord σ ++ toWord φ) ++ [0]),
      64 * (e + 1) ≤ W + 1) :
    let x := [n] ++ toWord σ ++ toWord φ
    let q := Lax3.FirstOrder.rank φ
    let lw := Lax185574.DistanceLogic.DistFO.code (loc q φ)
    ∃ σ' k, Run (W + 1) (glueCmd eM eR eE d)
        ((initEnv (fun _ => W + 1) (0 :: x.length :: (x ++ [0]))).setVar "W" W) σ' k ∧
      k ≤ glue0C eM eR eE d q x.length (3 * n + 3 + (1 + n * (n + 1)) + (1 + n * (iL q + 3)) +
        lw.length) ∧
      (n = 0 → σ'.vars "ovf" ≠ 0) ∧
      (∀ hn : 0 < n, σ'.vars "ovf" = 0 →
        σ'.out = hdOf σ.run q (n + 3) σ.steps.length lw (call0 hn σ.steps) ++
          callQ σ.run q φ (call0 hn σ.steps) ∧
        maxEntry (hdOf σ.run q (n + 3) σ.steps.length lw (call0 hn σ.steps) ++
          callQ σ.run q φ (call0 hn σ.steps)) < W / 32 / 32 ∧
        min (((workQ σ.run q φ (call0 hn σ.steps)).length +
          maxEntry (workQ σ.run q φ (call0 hn σ.steps)) + 1) ^
            (expOf eM eR eE (ckOf (call0 hn σ.steps)) + 1)) W ≤ W / min (2 ^ d) W) ∧
      (∀ hn : 0 < n, dK < W / 8 → glM q < W / 8 → n * (glM q + 3 + n) < W / 8 →
        dK + (3 * n + 3 + (1 + n * (n + 1))) + (1 + n * (iL q + 3)) + lw.length < W / 8 →
        maxEntry (hdOf σ.run q (n + 3) σ.steps.length lw (call0 hn σ.steps) ++
          callQ σ.run q φ (call0 hn σ.steps)) < W / 32 / 32 →
        min (((workQ σ.run q φ (call0 hn σ.steps)).length +
          maxEntry (workQ σ.run q φ (call0 hn σ.steps)) + 1) ^
            (expOf eM eR eE (ckOf (call0 hn σ.steps)) + 1)) W ≤ W / min (2 ^ d) W →
        σ'.vars "ovf" = 0) := by
  intro x q lw
  have e1 : x.length = ([n] ++ toWord σ ++ toWord φ).length := rfl
  have e2 : r0C q * (x.length + 1) = r0C (Lax3.FirstOrder.rank φ) *
    (([n] ++ toWord σ ++ toWord φ).length + 1) := rfl
  have e3 : lw.length = (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length :=
    rfl
  have e4 : n * (iL q + 3) = n * (iL (Lax3.FirstOrder.rank φ) + 3) := rfl
  set ρ := (initEnv (fun _ => W + 1) (0 :: x.length :: (x ++ [0]))).setVar "W" W with hρ
  have hvρ : ValsLt (W + 1) ρ := valsLt_init _ _ (by omega) (fun v h => by have := hent v h; omega)
  obtain ⟨τ₁, r₁, htg₁, hzk₁, fv₁, fa₁, fo₁, fi₁⟩ := glue_top (W := W) (t := 0) (σ := ρ)
    (rest := x.length :: (x ++ [0])) (by simp [hρ, initEnv]) (by simp [hρ]) (by omega)
  have hv₁ := Run.vals_lt r₁ hvρ
  have hW₁ : τ₁.vars "W" = W := by rw [fv₁ _ (by decide) (by decide)]; simp [hρ]
  have hovf₁ : τ₁.vars "ovf" = 0 := by rw [fv₁ _ (by decide) (by decide)]; simp [hρ, initEnv]
  have hc := condLt_div (B := W + 1) (x := "zk") (d := 8) hzk₁ hW₁ (by omega) (by omega) (by omega)
  have hdK := lens_le_dK
  have hsq : (n + 1) ^ 2 ≤ 3 * n + 3 + (1 + n * (n + 1)) := by nlinarith
  by_cases hz : min dK W < W / 8
  · have hdW : dK < W / 8 := by
      by_contra h; have : min dK W = W ∨ min dK W = dK := by omega
      rcases this with h' | h' <;> omega
    have hc0 := condEq_lit (B := W + 1) (d := 0) htg₁ (by omega) (by omega)
    have hxl : 64 * (x.length + 1) ≤ W + 1 := hent _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hx : ∀ v ∈ x, 64 * (v + 1) ≤ W + 1 := fun v h =>
      hent v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
    obtain ⟨τ₂, r₂, hn0, hO, hT⟩ := round0_run (W := W) (sc := σ) (φ := φ) (rest := [0]) (σ := τ₁)
      (by rw [fi₁]) hW₁ hovf₁ (fun a _ => by rw [fa₁]; simp [hρ, initEnv]) hx hxl
    have hv₂ := Run.vals_lt r₂ hv₁
    have ho₂ : τ₂.out = [] := by
      rw [r₂.out_eq round0_noWrite, fo₁]; simp [hρ, initEnv]
    by_cases hov : τ₂.vars "ovf" = 0
    · have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · exact absurd hov (hn0 h)
        · exact h
      have hR := hO hov
      have hW64 : 64 ≤ W := by omega
      have hlo := hR.lo
      obtain ⟨τ₃, r₃, hS, hC⟩ := r0Call_run (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d)
        (sc := σ) (φ := φ) (τ := τ₂) hn hR hW64 hx hxl
        (by rw [run_length_arrs r₂, fa₁]; simp [hρ, initEnv])
        (fun v h => by
          simp only [List.mem_append] at h
          rcases h with (h | h) | h
          · have := Filled.lt_of_vals hR.GW hv₂ v h; omega
          · have := Filled.lt_of_vals hR.FW hv₂ v h; omega
          · have := Filled.lt_of_vals hR.lo hv₂ v h; omega)
        (by have := hv₂.1 "lp"; rw [hlo.pos] at this; omega)
      rw [r0_workQ σ φ hn] at hS hC
      have hc1 := condEq_lit (B := W + 1) (d := 0) hov (by omega) (by omega)
      refine ⟨τ₃, _, Run.seq r₁ (Run.ite_true (by rw [hc, decide_eq_true hz]) (Run.ite_true
        (by rw [hc0]; rfl) (Run.seq r₂ (Run.ite_true (by rw [hc1]; rfl) r₃)))), ?_,
        fun h => absurd h (by omega), fun _ h => ?_, fun _ _ _ _ h1 h2 h3 => hC h1 h2 h3⟩
      · simp only [Cond.size, Expr.size]
        unfold glue0C
        have := hR.bM
        generalize dK = D at *
        generalize 2 ^ d = T at *
        generalize (n + 1) ^ 2 = S at *
        omega
      · obtain ⟨ho, hE, hG⟩ := hS h
        exact ⟨by rw [ho, ho₂]; rfl, hE, hG⟩
    · refine ⟨τ₂, _, Run.seq r₁ (Run.ite_true (by rw [hc, decide_eq_true hz]) (Run.ite_true
        (by rw [hc0]; rfl) (Run.seq r₂ (Run.ite_false (by
          rw [condEq_lit (B := W + 1) (d := 0) rfl (by have := hv₂.1 "ovf"; omega) (by omega),
            decide_eq_false hov]) Run.skip)))), ?_, fun _ => hov, fun _ h => absurd h hov,
        fun hn h1 h2 h3 _ _ _ => absurd (hT hn h2 h3) hov⟩
      simp only [Cond.size, Expr.size]
      unfold glue0C
      generalize dK = D at *
      generalize 2 ^ d = T at *
      generalize (n + 1) ^ 2 = S at *
      omega
  · refine ⟨τ₁.setVar "ovf" 1, _, Run.seq r₁ (Run.ite_false (by rw [hc, decide_eq_false hz])
      (Run.assign (evalB_lit (by omega)))), ?_, fun _ => by simp, fun _ h => by simp at h,
      fun _ h => absurd (lt_of_le_of_lt (min_le_left _ _) h) hz⟩
    simp only [Cond.size, Expr.size]
    unfold glue0C
    generalize dK = D at *
    generalize 2 ^ d = T at *
    omega


end Lax185574Proofs.MC.Glue
