import Lax185574Proofs.ResolveRam.Glue.R0Run
import Lax185574Proofs.ResolveRam.Glue.Wrap

/-!
The glue command of lem:resolve-lift and its first round.

`glueTop K e d rJ` first checks that `W` exceeds the constant `K` (built
from the literals `0` and `1` by saturating arithmetic, so the check runs
at every word length), and sets `ovf` otherwise. Then it reads the tag
and runs the first round (`round0 e d`) or a later round `rJ`.
`top0_run`: on the input of the first round the command has a run that
outputs `gOut0` unless it sets `ovf`, and it sets `ovf` exactly when the
checks `RGood` of the first round fail.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The glue command. -/
noncomputable def glueTop (K e d : ℕ) (rJ : Com) : Com :=
  .seq (satLit "gk" K) (.ite (.lt (.var "gk") (.var "W"))
    (.seq (.read "tg") (.ite (.eq (.var "tg") (.lit 0)) (round0 e d) rJ)) (.assign "ovf" (.lit 1)))

/-- The array lengths of the first round. -/
def ext0 (W xl : ℕ) : String → ℕ := fun a => if a = "OB" then W + 1 else if a = "x" then xl else 0

attribute [local irreducible] s3W k0 mid0

set_option maxHeartbeats 400000 in
/-- **The first round of the glue command.** -/
theorem top0_run {K e d W : ℕ} (rJ : Com) (hW3 : 3 ≤ W) (hK : 4 * k0 + 64 ≤ K)
    (hu : ∀ x ∈ [0, (xIn G k₀ q₀ P Q s).length] ++ xIn G k₀ q₀ P Q s ++ [0], 64 * x < W + 1) :
    ∃ σ' k, Run (W + 1) (glueTop K e d rJ)
        ((initEnv (ext0 W (xIn G k₀ q₀ P Q s).length)
          ([0, (xIn G k₀ q₀ P Q s).length] ++ xIn G k₀ q₀ P Q s ++ [0])).setVar "W" W) σ' k ∧
      (σ'.vars "ovf" = 0 → σ'.out = gOut0 G P Q s k₀ q₀) ∧
      σ'.vars "ovf" = (if RGood W K e d (ySz (xIn G k₀ q₀ P Q s)) (decide (1 ≤ n)) (qF G k₀ q₀ .stp)
        (gOut0 G P Q s k₀ q₀) then 0 else 1) ∧
      k ≤ 30 * K + 200 * ((xIn G k₀ q₀ P Q s).length + 1) + 100 * k0 + 60 * (e + 1) + 30 * 2 ^ d + 5100 := by
  set σ0 := (initEnv (ext0 W (xIn G k₀ q₀ P Q s).length) ([0, (xIn G k₀ q₀ P Q s).length] ++
    xIn G k₀ q₀ P Q s ++ [0])).setVar "W" W
  have hW0 : σ0.vars "W" = W := by simp [σ0]
  obtain ⟨σ1, r1, h1, f1, a1, o1, i1⟩ := satLit_run (B := W + 1) (z := "gk") (by decide) (by omega)
    (by omega) K σ0 hW0
  have hc : (Cond.lt (.var "gk") (.var "W")).evalB (W + 1) σ1 = some (decide (min K W < W)) :=
    evalB_condLt (ev_var (x := "gk") (v := min K W) h1 (by omega)) (ev_var (x := "W") (v := W) (by rw [f1 "W" (by decide), hW0])
      (by omega))
  by_cases hKW : K < W
  · have hc' : (Cond.lt (.var "gk") (.var "W")).evalB (W + 1) σ1 = some true := by
      rw [hc]; simp; omega
    set σ2 : Env := { σ1.setVar "tg" 0 with inp := (xIn G k₀ q₀ P Q s).length :: xIn G k₀ q₀ P Q s ++ [0] }
    have r2 : Run (W + 1) (.read "tg") σ1 σ2 1 := Run.read (by rw [i1]; simp [σ0, initEnv])
    have hc2 : (Cond.eq (.var "tg") (.lit 0)).evalB (W + 1) σ2 = some true := by
      rw [evalB_condEq (ev_var (x := "tg") (v := 0) (by simp [σ2]) (by omega)) (evalB_lit (n := 0) (by omega))]
      rfl
    have hux : ∀ x ∈ xIn G k₀ q₀ P Q s, 64 * x < W + 1 := fun x hx => hu x (by simp [hx])
    have hul : 64 * (xIn G k₀ q₀ P Q s).length < W + 1 := hu _ (by simp)
    have hmx : 64 * maxEntry (xIn G k₀ q₀ P Q s) < W + 1 := by
      have := maxEntry_le (b := W / 64) (x := xIn G k₀ q₀ P Q s) (fun v hv => by have := hux v hv; omega)
      omega
    have hy : 8 * ySz (xIn G k₀ q₀ P Q s) + 2 * k0 ≤ W := by unfold ySz; omega
    obtain ⟨σ3, r3, o3, ov3⟩ := round0_run G P Q s k₀ q₀ (W := W) (e := e) (d := d) (σ := σ2)
      (by simp [σ2]) (by simp [σ2, f1 _ (show ("W" : String) ≠ "gk" by decide), hW0])
      (by simp [σ2, f1 _ (show ("ovf" : String) ≠ "gk" by decide), σ0, initEnv])
      (by simp [σ2, a1, σ0, initEnv, ext0]) (by simp [σ2, a1, σ0, initEnv, ext0]) hy
    refine ⟨σ3, 30 * K + 200 * ((xIn G k₀ q₀ P Q s).length + 1) + 100 * k0 + 60 * (e + 1) + 30 * 2 ^ d + 5100, ?_, fun _ => by rw [o3]; simp [σ2, o1, σ0, initEnv], ?_, le_refl _⟩
    · unfold glueTop
      refine (Run.seq r1 (Run.ite_true hc' (Run.seq r2 (Run.ite_true hc2 r3)))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    · rw [ov3]
      have hiff : ok0 G P Q s k₀ q₀ W e d ↔
          RGood W K e d (ySz (xIn G k₀ q₀ P Q s)) (decide (1 ≤ n)) (qF G k₀ q₀ .stp) (gOut0 G P Q s k₀ q₀) := by
        unfold ok0 RGood gOut0
        by_cases hn : n = 0
        · simp [hn, hKW]
        · simp [hn, hKW, show 1 ≤ n by omega]
      by_cases hg : ok0 G P Q s k₀ q₀ W e d
      · rw [if_pos hg, if_pos (hiff.1 hg)]
      · rw [if_neg hg, if_neg (fun h => hg (hiff.2 h))]
  · have hc' : (Cond.lt (.var "gk") (.var "W")).evalB (W + 1) σ1 = some false := by
      rw [hc]; simp; omega
    refine ⟨σ1.setVar "ovf" 1, 30 * K + 200 * ((xIn G k₀ q₀ P Q s).length + 1) + 100 * k0 + 60 * (e + 1) + 30 * 2 ^ d + 5100, ?_, fun h => by simp at h, ?_, le_refl _⟩
    · unfold glueTop
      refine (Run.seq r1 (Run.ite_false hc' (Run.assign (evalB_lit (by omega))))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    · have hng : ¬ RGood W K e d (ySz (xIn G k₀ q₀ P Q s)) (decide (1 ≤ n)) (qF G k₀ q₀ .stp)
          (gOut0 G P Q s k₀ q₀) := fun h => hKW h.1
      rw [if_neg hng]; simp

end Lax185574Proofs.ResolveRam.Glue
