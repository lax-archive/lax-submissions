import Lax185574Proofs.ResolveRam.Glue.PH2
import Lax185574Proofs.ResolveRam.Glue.PCT5

/-!
The piece of the resolved graph (`HSpec`).

`hCmd` sets the pointer `tq` to the start of `x` and runs the tape
program `hIn` through the translation `trC`, with the scalars renamed
by the prefix `th` and the arrays by the prefix `Th` (`hCmd_spec`). It
writes the word of the resolved graph and the word of its distance
matrix.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574.PartialGraphs Lax185574Proofs.ResolveRam Lax185574.WordEncoding
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift

/-- The renaming of the program of the resolved graph. -/
def hRen : Ren := preRen "th" "Th"

/-- The scalars of `hIn`. -/
def hVs : List String := ["n", "cx", "c0", "x1", "x", "k", "r", "gp", "gq", "gs", "b", "a", "d", "w", "v",
  "dl", "dv", "dx", "du", "dw", "ca", "cb", "cr", "hp", "hq", "h1", "h2", "h3", "h4"]

/-- The arrays of `hIn`. -/
def hAs : List String := ["co", "E", "N", "Rm", "dd", "dp", "dq"]

/-- **The piece of the resolved graph.** -/
def hCmd : Com := .seq (.assign "tq" (.lit 0)) (trC hRen hIn)

/-- The scalars that `hCmd` writes. -/
def hCV : List String := "tq" :: "po" :: hVs.map hRen.v

set_option maxRecDepth 20000 in
theorem hIn_ok : okC hVs hAs hIn = true := by decide

set_option maxRecDepth 20000 in
theorem hCmd_wvars : ∀ y ∈ hCmd.wvars, y ∈ hCV := by decide

set_option maxRecDepth 20000 in
theorem hCmd_warrs : ∀ b ∈ keepA, b ∉ hCmd.warrs := by decide

set_option maxRecDepth 20000 in
theorem hNames0 : TrP.names ⟨hRen, hVs, hAs, fun _ => [], [], 0, [], 0⟩ = true := by decide

theorem hNames (pad : String → List ℕ) (X : List ℕ) (L : ℕ) (pre : List ℕ) (N : ℕ) :
    TrP.names ⟨hRen, hVs, hAs, pad, X, L, pre, N⟩ = true := hNames0

/-- The lengths of the arrays of `hIn`. -/
def hLens (n : ℕ) (a : String) : ℕ :=
  if a = "co" ∨ a = "dp" ∨ a = "dq" then n else if a = "dd" then 1 + n * (n + 1) else n * n

theorem length_toWord_resolve_le {n : ℕ} (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) :
    (toWord (resolveBy G s P Q)).length ≤ 5 * (n + 1) * (n + 1) := by
  rw [toWord_resolve]
  have h1 := length_graphWord_le n (edgeR G s P Q)
  have h2 := length_graphWord_le n (nonEdgeR G s P Q)
  simp only [List.length_append, List.length_cons, List.length_ofFn]
  nlinarith

theorem hTr_cost_le (L : ℕ) : 2 + 8 * (3000 * (L + 1)) ≤ 30000 * (L + 1) := by omega

open Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix in
theorem length_hWord_le {n : ℕ} (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) :
    (hWord G s P Q).length ≤ 6 * ((n + 1) * (n + 1)) := by
  have h1 := length_toWord_resolve_le G s P Q
  have h2 := length_toWord_distMatrix (resolveBy G s P Q)
  rw [hWord, List.length_append, h2]
  nlinarith

theorem hCmd_spec : HSpec hCmd hCV := by
  refine ⟨30000, ?_⟩
  intro W k₀ q₀ n G P Q s τ pre hW hA hx hnx hgn hgP hgQ hgS hF hR
  set x := xIn G k₀ q₀ P Q s with hxdef
  have hroom := room0_ge hR
  have hxl : x.length + maxEntry x + 1 = ySz x := rfl
  have hlen : n + 1 + StpRam.offL G.edge n + StpRam.offL G.nonEdge n + (1 + n * (n + 1)) + 2 ≤ x.length :=
    xIn_len
  set S := ySz x + pre.length
  have hSq : 65536 * ((S + 1) * (S + 1)) ≤ W := by
    unfold Room at hR; nlinarith
  have hnS : n + 1 ≤ S := by omega
  have hnn : (n + 1) * (n + 1) ≤ (S + 1) * (S + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hyy : ySz x * ySz x ≤ (S + 1) * (S + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hnW : n * n ≤ W := by nlinarith
  have hnW' : n * (n + 1) + 1 ≤ W := by nlinarith
  -- the pointer
  set τ0 := τ.setVar "tq" 0
  have r0 : Run (W + 1) (.assign "tq" (.lit 0)) τ τ0 2 := (Run.assign (by simp)).mono (by simp)
  have hF0 : Filled "OB" "po" pre τ0 := hF.setVar (by decide) 0
  -- the tape environment
  set lens := hLens n
  set σ0 := simEnv hRen lens (τ0.arrs "x") x.length τ0
  have hs0 := sim_simEnv (r := hRen) (Vs := hVs) (As := hAs) (lens := lens) (L := x.length) hF0
  set p : TrP := ⟨hRen, hVs, hAs, simPad hRen lens τ0, τ0.arrs "x", x.length, pre,
    (τ0.arrs "OB").length⟩
  have hxa : (τ0.arrs "x").take x.length = x := take_preAt (a := "x") (τ := τ0) hx (by
    simp only [τ0, arrs_setVar]; rw [hA "x"]; omega)
  have hp : p.OK (W + 1) := ⟨hNames _ _ _ _ _, by simp [p]; omega, fun u hu => by
    simp only [p, hxa] at hu; have := le_maxEntry hu; omega⟩
  have hlenA : ∀ a, (σ0.arrs a).length = lens a := by
    intro a
    simp only [σ0, simEnv, List.length_take, τ0, arrs_setVar]
    rw [hA]
    simp only [lens, hLens]
    split_ifs <;> omega
  have hinp0 : σ0.inp = x := by
    simp only [σ0, simEnv]
    simp only [τ0, vars_setVar, if_true, List.drop_zero]
    exact hxa
  have hB : ySz x * ySz x < W + 1 := by omega
  obtain ⟨σ1, r1, ho1⟩ := hIn_run (B := W + 1) G hinp0 (hlenA "co") (hlenA "E") (hlenA "N") (hlenA "Rm")
    (hlenA "dd") (hlenA "dp") (hlenA "dq") hB
  have hout1 : σ1.out = hWord G s P Q := by
    rw [ho1]; simp [σ0, simEnv, hWord]
  have hHl := length_hWord_le G s P Q
  have hpS : pre.length + 1 ≤ (S + 1) * (S + 1) :=
    Nat.le_trans (by omega : pre.length + 1 ≤ S + 1) (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨τ1, r2, hs1⟩ := trC_run hp hIn_ok r1 hs0
    (by have hOB : (τ0.arrs "OB").length = W + 1 := hA "OB"
        simp only [p, hout1, List.length_append, hOB]; omega)
    (by simp only [p, hout1, List.length_append]; omega)
  have hrun : Run (W + 1) hCmd τ τ1 (30000 * (x.length + 1)) := by
    unfold hCmd
    refine (Run.seq r0 r2).mono ?_
    exact hTr_cost_le _
  refine ⟨τ1, hrun, by simpa [p, hout1] using hs1.outF, ⟨fun y hy => ?_, fun b hb => ?_,
    fun b => run_len_eq hrun b, ?_, ?_⟩⟩
  · exact hrun.frame_var y (fun h => hy (hCmd_wvars y h))
  · exact hrun.frame_arr b (hCmd_warrs b hb)
  · exact hrun.out_eq (by simp only [hCmd, Com.NoWrite]; exact ⟨trivial, trC_noWrite _ _⟩)
  · exact hrun.frame_inp (by simp only [hCmd, Com.reads]; exact fun h => h.elim id (trC_noRead _ _))

/-- A layout for the piece of the resolved graph. -/
def hLayout : Lax808846Proofs.Compile.Layout :=
  ⟨hCV, hAs.map hRen.a ++ ["x", "OB"], 64⟩

theorem hCmd_ok : Lax808846Proofs.Compile.Com.Ok hLayout hCmd :=
  StpRam.comOkB_sound _ _ (by decide)

end Lax185574Proofs.ResolveRam.Glue
