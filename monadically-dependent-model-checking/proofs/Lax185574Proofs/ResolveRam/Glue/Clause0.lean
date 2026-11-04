import Lax185574Proofs.ResolveRam.Glue.Top0

/-!
The clause of `RGlueAt.rounds` for the first round (`clause0`), for the
guarded program of `glueTop` with any later rounds `rJ`, the input shift
`sI = r + 6` (`r` the guard bits of the layout) and the guard of
exponent `eT + 1` on the query of the scatter type.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The time bound of the first round. -/
noncomputable def t0 (L : Layout) (K e d X : ℕ) : ℕ :=
  L.const * (30 * K + 200 * X + 100 * k0 + 60 * (e + 1) + 30 * 2 ^ d + 5100) + 5

theorem ySz_le_of_sub {a b : List ℕ} (hl : a.length ≤ b.length) (hm : maxEntry a ≤ maxEntry b) :
    ySz a ≤ ySz b := by unfold ySz; omega

/-- **The first round.** -/
theorem clause0 {L : Layout} {K eS eF eC eK eT sQ cG E : ℕ} (rJ : Com)
    (hok : Com.Ok L (glueTop K eT (sQ - guardBits L + eT + 1) rJ)) (hW : "W" ∈ L.scalars)
    (hO : "ovf" ∈ L.scalars) (hK : 4 * k0 + 64 ≤ K) (hrs : guardBits L + 11 ≤ sQ)
    (hcG : 2 * 2 ^ (eT + 1) + K + 1 ≤ cG) (hE : eT + 1 ≤ E) (hd : ℕ → List ℕ)
    (hhd : 1 ≤ n → hd 0 = hdOf G P Q s k₀ q₀ .stp) (v : ℕ) (hv : guardBits L + 6 ≤ v)
    (hu : ∀ e ∈ gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s) 0,
      e < 2 ^ (v - (guardBits L + 6))) :
    (∀ o t, RunsTo v (guardedProgram L (glueTop K eT (sQ - guardBits L + eT + 1) rJ))
        (gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s) 0) o t →
      o = gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s) 0 ∧
      (∀ e ∈ o, e < 2 ^ (v - (guardBits L + 6) - 4)) ∧
      ∀ c, (rcalls G P Q s k₀ q₀)[0]? = some c →
        RGuard G k₀ q₀ eS eF eC eK eT (ySz (xIn G k₀ q₀ P Q s)) v sQ c) ∧
    (cG * (ySz (gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s) 0) +
        ySz (gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s) 0) +
        ySz (xIn G k₀ q₀ P Q s)) ^ E ≤ 2 ^ (v - sQ) →
      ∃ t ≤ t0 L K eT (sQ - guardBits L + eT + 1) ((xIn G k₀ q₀ P Q s).length + 1),
        RunsTo v (guardedProgram L (glueTop K eT (sQ - guardBits L + eT + 1) rJ))
          (gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s) 0)
          (gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s) 0) t) := by
  set r := guardBits L
  set W := Words.guardW L v
  have hW1 : W + 1 = 2 ^ (v - r) := Words.guardW_succ L v
  have hsp : 2 ^ (v - r) = 2 ^ (v - (r + 6)) * 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; omega
  have hgu := gU_zero G P Q s k₀ q₀ (rcalls G P Q s k₀ q₀) hd (zOut G k₀ q₀ P Q s)
  have hgo := gOut_zero G P Q s k₀ q₀ (zOut G k₀ q₀ P Q s) hd (fun hn => by
    subst hn; exact zOut_zero k₀ q₀ G P Q s) hhd
  rw [hgu] at hu ⊢
  rw [hgo]
  have hu64 : ∀ x ∈ [0, (xIn G k₀ q₀ P Q s).length] ++ xIn G k₀ q₀ P Q s ++ [0], 64 * x < W + 1 := by
    intro x hx; have := hu x hx; rw [hW1, hsp]; omega
  have hW64 : 64 ≤ W + 1 := by
    have : 1 ≤ 2 ^ (v - (r + 6)) := Nat.one_le_two_pow
    omega
  have huW : ∀ x ∈ [0, (xIn G k₀ q₀ P Q s).length] ++ xIn G k₀ q₀ P Q s ++ [0], x ≤ W := by
    intro x hx; have := hu64 x hx; omega
  obtain ⟨σ', k, hr, hout, hovf, hk⟩ := top0_run G P Q s k₀ q₀ (K := K) (e := eT)
    (d := sQ - r + eT + 1) rJ (by omega) hK hu64
  have hrun : ∃ (ext : String → ℕ) (σ' : Env) (k : ℕ),
      Run (W + 1) (glueTop K eT (sQ - r + eT + 1) rJ)
        ((initEnv ext ([0, (xIn G k₀ q₀ P Q s).length] ++ xIn G k₀ q₀ P Q s ++ [0])).setVar "W" W) σ' k ∧
      (σ'.vars "ovf" = 0 → σ'.out = gOut0 G P Q s k₀ q₀) ∧
      σ'.vars "ovf" = (if RGood W K eT (sQ - r + eT + 1) (ySz (xIn G k₀ q₀ P Q s)) (decide (1 ≤ n))
        (qF G k₀ q₀ .stp) (gOut0 G P Q s k₀ q₀) then 0 else 1) ∧
      L.const * k + 5 ≤ t0 L K eT (sQ - r + eT + 1) ((xIn G k₀ q₀ P Q s).length + 1) :=
    ⟨_, σ', k, hr, hout, hovf, by unfold t0; have := Nat.mul_le_mul_left L.const hk; omega⟩
  refine ⟨fun o t ht => ?_, fun hcGv => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := round_sound hok hW hO (by omega) (by omega) huW
      (let ⟨ext, σ', k, a, b, c, _⟩ := hrun; ⟨ext, σ', k, a, b, c⟩) o t ht
    refine ⟨h1, by rw [h1]; exact h2, fun c hc => ?_⟩
    have hn : 1 ≤ n := by
      by_contra hn
      simp [rcalls, show n = 0 by omega] at hc
    have hc' : c = .stp := by simp [rcalls, show n ≠ 0 by omega] at hc; exact hc.symm
    subst hc'
    exact h3 (by simp [hn])
  · refine round_halts hok hW hO (by omega) huW hrun (rgood_of hrs ?_ ?_)
    · intro hc
      have hn : 1 ≤ n := by simpa using hc
      have hO0 : gOut0 G P Q s k₀ q₀ = hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp := by
        simp [gOut0, show n ≠ 0 by omega]
      rw [hO0, rQ_stp]
      refine ⟨by simp; omega, maxEntry_le fun v hv => le_maxEntry ?_⟩
      simp [hv]
    · set o := gOut0 G P Q s k₀ q₀
      set u := [0, (xIn G k₀ q₀ P Q s).length] ++ xIn G k₀ q₀ P Q s ++ [0]
      set Y := ySz u + ySz o + ySz (xIn G k₀ q₀ P Q s)
      have hY1 : 1 ≤ Y := by simp only [Y, ySz]; omega
      have hle : o.length + maxEntry o + ySz (xIn G k₀ q₀ P Q s) + 2 ≤ Y := by
        simp only [Y, ySz]; omega
      calc (2 * 2 ^ (eT + 1) + K + 1) * (o.length + maxEntry o + ySz (xIn G k₀ q₀ P Q s) + 2) ^ (eT + 1)
          ≤ cG * Y ^ (eT + 1) := Nat.mul_le_mul hcG (Nat.pow_le_pow_left hle _)
        _ ≤ cG * Y ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 hE)
        _ ≤ 2 ^ (v - sQ) := hcGv

end Lax185574Proofs.ResolveRam.Glue
