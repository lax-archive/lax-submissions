import Lax185574Proofs.ResolveRam.Glue.TailRun

/-!
The output that `tailC` writes is the scripted output of the round.

If the scalars of the head are those of the position `c'` of the next
call, the ranges give the words of the state at `c'` and the real query
is that of the call at `c'`, then the head, the state and the query of
the switch that `tailC` writes are `hdOf c' ++ rQ (callOf c')`
(`out_eq`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam Lax185574.PartialGraphs

/-- The kind of a call: `0` rank shift, `1` far tree, `2` composition, `3` canonical form. -/
def kindOf : RCall → ℕ
  | .shift _ => 0
  | .ftree _ => 1
  | .compose _ _ => 2
  | .canon _ => 3
  | .stp => 4

theorem rQ_kind {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ) (c : RCall) (hc : c ≠ .stp) :
    rQ G k₀ q₀ c = kW (kindOf c) (realQ G k₀ q₀ c) := by
  cases c with
  | stp => exact absurd rfl hc
  | shift τ => rfl
  | ftree τ => rfl
  | compose σ ν => rfl
  | canon ws => rfl

/-- **The output of the round.** -/
theorem out_eq {n : ℕ} {G : PartialGraph (Fin n)} {P Q : ℕ} {s : Bool} {k₀ q₀ : ℕ} {c' : Cur}
    {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {τ : Env}
    (hc : callOf G P Q s k₀ q₀ c' ≠ .stp)
    (ht : τ.vars "Nt" = tagOf G P Q s k₀ q₀ c') (hw : τ.vars "Nw" = winOf G P Q s k₀ q₀ c')
    (hsc : hsV.map τ.vars = scW G P Q s k₀ q₀ c') (hpl : planW L ps = (swAt G P Q s k₀ q₀ c').ws) :
    hdW τ L ps ++ kW (kindOf (callOf G P Q s k₀ q₀ c')) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')) =
      hdOf G P Q s k₀ q₀ c' ++ rQ G k₀ q₀ (callOf G P Q s k₀ q₀ c') := by
  rw [rQ_kind G k₀ q₀ _ hc]
  simp only [hdW, hdOf, stOf, ht, hw, hsc, hpl, List.cons_append, List.length_append]
  congr 2
  simp [scW, curW]
  cases c' <;> simp

end Lax185574Proofs.ResolveRam.Glue

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue

/-- **Soundness of a round**, when the command passes more checks than
those of `RGood`. -/
theorem round_sound' {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) (hW : "W" ∈ L.scalars)
    (hO : "ovf" ∈ L.scalars) {v sQ K e X : ℕ} {call : Bool} {u o q : List ℕ}
    (hrv : guardBits L + 2 ≤ v) (hrs : guardBits L < sQ) (hu : ∀ x ∈ u, x ≤ Words.guardW L v)
    (hrun : ∃ (ext : String → ℕ) (σ' : Env) (k : ℕ),
      Run (Words.guardW L v + 1) cmd ((initEnv ext u).setVar "W" (Words.guardW L v)) σ' k ∧
      (σ'.vars "ovf" = 0 → σ'.out = o ∧
        RGood (Words.guardW L v) K e (sQ - guardBits L + e + 1) X call q o)) :
    ∀ o' t, RunsTo v (guardedProgram L cmd) u o' t → o' = o ∧
      (∀ x ∈ o, x < 2 ^ (v - (guardBits L + 6) - 4)) ∧
      (call = true → (q.length + maxEntry q + 1 + X) ^ (e + 1) ≤ 2 ^ (v - sQ)) := by
  obtain ⟨ext, σ', k, hr, hout⟩ := hrun
  have hs := (guarded_sound hok hW hO hrv hu hr).1
  intro o' t ht
  obtain ⟨h0, hy⟩ := hs o' t ht
  obtain ⟨ho, hK, hgu, hent⟩ := hout h0
  have hW1 := Words.guardW_succ L v
  refine ⟨by rw [hy, ho], fun x hx => ?_, fun hc => guard_sound_X hW1 hrs (by omega) (hgu hc)⟩
  have := ent_sound_arith hW1 (lt_of_le_of_lt (le_maxEntry hx) hent)
  rwa [show v - (guardBits L + 6) - 4 = v - guardBits L - 10 by omega]

/-- **Completeness of a round**, with the checks of the command passed. -/
theorem round_halts' {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) (hW : "W" ∈ L.scalars)
    (hO : "ovf" ∈ L.scalars) {v T : ℕ} {u o : List ℕ}
    (hrv : guardBits L + 2 ≤ v) (hu : ∀ x ∈ u, x ≤ Words.guardW L v)
    (hrun : ∃ (ext : String → ℕ) (σ' : Env) (k : ℕ),
      Run (Words.guardW L v + 1) cmd ((initEnv ext u).setVar "W" (Words.guardW L v)) σ' k ∧
      σ'.out = o ∧ σ'.vars "ovf" = 0 ∧ L.const * k + 5 ≤ T) :
    ∃ t ≤ T, RunsTo v (guardedProgram L cmd) u o t := by
  obtain ⟨ext, σ', k, hr, hout, h0, hT⟩ := hrun
  obtain ⟨t, ht, hrt⟩ := (guarded_sound hok hW hO hrv hu hr).2 h0
  exact ⟨t, by omega, by rwa [hout] at hrt⟩

end Lax185574Proofs.ResolveRam.Glue
