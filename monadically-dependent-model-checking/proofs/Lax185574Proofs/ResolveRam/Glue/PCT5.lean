import Lax185574Proofs.ResolveRam.Glue.PCT4
import Lax185574Proofs.StpRam.GlueOk

/-!
The piece of the color table (`CTSpec`).

`ctCmd` sets the pointer `tq` to the start of `x` and runs the tape
program `ctIn` through the translation `trC`, with the scalars renamed
by the prefix `tk` and the arrays by the prefix `Tk` (`ctCmd_spec`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574.PartialGraphs Lax185574Proofs.ResolveRam

/-- The renaming of the color table program. -/
def ctRen : Ren := preRen "tk" "Tk"

/-- The scalars of `ctIn`. -/
def ctVs : List String :=
  ["cd", "cx", "cy", "ck", "cv", "cn", "cp", "ok", "v", "gp", "gq", "bx", "nc", "bz", "be", "bv", "bj", "bw",
    "b", "bs", "n", "w", "fd", "u", "lo", "m", "cnt", "c", "dl", "dv", "dx", "du", "dw", "ca", "cb", "cr"]

/-- The arrays of `ctIn`. -/
def ctAs : List String := ["co", "eo", "et", "no", "nt", "cl", "dm", "dn", "ct", "c1", "sy", "su", "dd"]

/-- **The piece of the color table.** -/
def ctCmd : Com := .seq (.assign "tq" (.lit 0)) (trC ctRen ctIn)

/-- The scalars that `ctCmd` writes. -/
def ctCV : List String := "tq" :: "po" :: ctVs.map ctRen.v

theorem ctIn_ok : okC ctVs ctAs ctIn = true := by decide

theorem ctCmd_wvars : ∀ y ∈ ctCmd.wvars, y ∈ ctCV := by decide

theorem ctCmd_warrs : ∀ b ∈ keepA, b ∉ ctCmd.warrs := by decide

theorem ctNames0 : TrP.names ⟨ctRen, ctVs, ctAs, fun _ => [], [], 0, [], 0⟩ = true := by decide

theorem ctNames (pad : String → List ℕ) (X : List ℕ) (L : ℕ) (pre : List ℕ) (N : ℕ) :
    TrP.names ⟨ctRen, ctVs, ctAs, pad, X, L, pre, N⟩ = true := ctNames0

/-- The room for data of size `S`. -/
theorem room0_ge {W S : ℕ} (h : Room W 0 S) : 65536 * (S + 1) ≤ W := by
  unfold Room at h
  have h2 : (S + 1) ≤ (S + 1) ^ 2 := by nlinarith
  calc 65536 * (S + 1) ≤ 2 ^ 16 * (0 + 1) ^ 2 * (S + 1) ^ 2 := by
        rw [show 2 ^ 16 * (0 + 1) ^ 2 * (S + 1) ^ 2 = 65536 * (S + 1) ^ 2 by ring]
        exact Nat.mul_le_mul_left _ h2
    _ ≤ W := h

/-- The prefix of `x`. -/
theorem take_preAt {a : String} {X : List ℕ} {τ : Env} (h : PreAt a X τ) (hl : X.length ≤ (τ.arrs a).length) :
    (τ.arrs a).take X.length = X := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have := h i h2
  rw [List.getElem_take]
  rw [List.getElem?_eq_getElem (by omega)] at this
  exact Option.some.inj this

/-- The lengths of the arrays of `ctIn`. -/
def ctLens (n e f : ℕ) (a : String) : ℕ :=
  if a = "eo" ∨ a = "no" then n + 1 else if a = "et" then e else if a = "nt" then f else
    if a = "dd" then 1 + n * (n + 1) else n

theorem ctTr_cost_le (L : ℕ) : 2 + 8 * (1000 * (L + 1)) ≤ 9000 * (L + 1) := by omega

theorem ctCmd_spec : CTSpec ctCmd ctCV := by
  refine ⟨9000, ?_⟩
  intro W k₀ q₀ n G P Q s τ pre hW hA hx hnx hgn hgP hgQ hF hR
  set x := xIn G k₀ q₀ P Q s with hxdef
  have hroom := room0_ge hR
  have hxl : x.length + maxEntry x + 1 = ySz x := rfl
  have hlen : n + 1 + StpRam.offL G.edge n + StpRam.offL G.nonEdge n + (1 + n * (n + 1)) + 2 ≤ x.length :=
    xIn_len
  -- the pointer
  set τ0 := τ.setVar "tq" 0
  have r0 : Run (W + 1) (.assign "tq" (.lit 0)) τ τ0 2 := (Run.assign (by simp)).mono (by simp)
  have hF0 : Filled "OB" "po" pre τ0 := hF.setVar (by decide) 0
  -- the tape environment
  set lens := ctLens n (StpRam.offL G.edge n) (StpRam.offL G.nonEdge n)
  set σ0 := simEnv ctRen lens (τ0.arrs "x") x.length τ0
  have hs0 := sim_simEnv (r := ctRen) (Vs := ctVs) (As := ctAs) (lens := lens) (L := x.length) hF0
  set p : TrP := ⟨ctRen, ctVs, ctAs, simPad ctRen lens τ0, τ0.arrs "x", x.length, pre,
    (τ0.arrs "OB").length⟩
  have hxa : (τ0.arrs "x").take x.length = x := take_preAt (a := "x") (τ := τ0) hx (by
    simp only [τ0, arrs_setVar]; rw [hA "x"]; omega)
  have hp : p.OK (W + 1) := ⟨ctNames _ _ _ _ _, by simp [p]; omega, fun u hu => by
    simp only [p, hxa] at hu; have := le_maxEntry hu; omega⟩
  have hlenA : ∀ a, (σ0.arrs a).length = lens a := by
    intro a
    simp only [σ0, simEnv, List.length_take, τ0, arrs_setVar]
    rw [hA]
    simp only [lens, ctLens]
    split_ifs <;> omega
  have hinp0 : σ0.inp = x := by
    simp only [σ0, simEnv]
    simp only [τ0, vars_setVar, if_true, List.drop_zero]
    exact hxa
  have hB : 3 * ySz x + 3 < W + 1 := by omega
  obtain ⟨σ1, r1, ho1⟩ := ctIn_run (B := W + 1) G hinp0 (hlenA "co") (hlenA "eo") (hlenA "et") (hlenA "no")
    (hlenA "nt") (hlenA "dd") (hlenA "cl") (hlenA "dm") (hlenA "ct") (hlenA "c1") (hlenA "sy")
    (hlenA "su") hB
  have hctl : (ctW G P Q).length ≤ 3 * n := by
    simp only [ctW, List.length_flatMap, List.length_cons, List.length_nil]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
    have := (colsL_facts G).2.2; omega
  have hout1 : σ1.out = (ctW G P Q).length :: ctW G P Q := by rw [ho1]; simp [σ0, simEnv]
  obtain ⟨τ1, r2, hs1⟩ := trC_run hp ctIn_ok r1 hs0
    (by have hOB : (τ0.arrs "OB").length = W + 1 := hA "OB"
        simp only [p, hout1, List.length_append, List.length_cons, hOB]; omega)
    (by simp only [p, hout1, List.length_append, List.length_cons]; omega)
  have hrun : Run (W + 1) ctCmd τ τ1 (9000 * (x.length + 1)) := by
    unfold ctCmd
    refine (Run.seq r0 r2).mono ?_
    exact ctTr_cost_le _
  refine ⟨τ1, hrun, by simpa [p, hout1] using hs1.outF, ⟨fun y hy => ?_, fun b hb => ?_,
    fun b => run_len_eq hrun b, ?_, ?_⟩⟩
  · exact hrun.frame_var y (fun h => hy (ctCmd_wvars y h))
  · exact hrun.frame_arr b (ctCmd_warrs b hb)
  · exact hrun.out_eq (by simp only [ctCmd, Com.NoWrite]; exact ⟨trivial, trC_noWrite _ _⟩)
  · exact hrun.frame_inp (by simp only [ctCmd, Com.reads]; exact fun h => h.elim id (trC_noRead _ _))

/-- A layout for the piece of the color table. -/
def ctLayout : Lax808846Proofs.Compile.Layout :=
  ⟨ctCV, ctAs.map ctRen.a ++ ["x", "OB"], 6⟩

theorem ctCmd_ok : Lax808846Proofs.Compile.Com.Ok ctLayout ctCmd :=
  StpRam.comOkB_sound _ _ (by decide)

end Lax185574Proofs.ResolveRam.Glue
