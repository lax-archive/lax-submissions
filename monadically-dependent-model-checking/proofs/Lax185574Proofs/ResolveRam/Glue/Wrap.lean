import Lax185574Proofs.ResolveRam.Glue.Fin
import Lax185574Proofs.Words.GuardedSound

/-!
From a run of the glue command on the input of a round to the clause of
`RGlueAt` for that round.

The command runs at word length `v` with `W = 2^(v-r) - 1`, `r` the
guard bits of the layout. A round outputs `o`, and if it issues a call,
`q` is the query of the working slot and `X` the size of the input of
the composite. The checks of the round (`RGood`): `W` is above a
constant `K` of the program, the guard `guardOK` with factor `2 ^ d`,
`d = sQ - r + e + 1`, and the entries of `o` are below `W / 32 / 32`.
If the command sets `ovf` exactly when a check fails, then every halting
run of the guarded program outputs `o` with small entries and passes the
guard of `RGlueAt` (`round_sound`), and if the checks pass it halts with
`o` (`round_halts`). The checks pass when the sizes are small compared
with `2 ^ (v - sQ)` (`rgood_of`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue

/-- The checks of a round. -/
def RGood (W K e d X : ℕ) (call : Bool) (q o : List ℕ) : Prop :=
  K < W ∧ (call = true → guardOK W e d X q) ∧ maxEntry o < W / 32 / 32

noncomputable instance (W K e d X : ℕ) (call : Bool) (q o : List ℕ) :
    Decidable (RGood W K e d X call q o) := by
  unfold RGood; infer_instance

/-- **The passed guard bounds the query.** -/
theorem guard_sound_X {W v r sQ e X : ℕ} {q : List ℕ} (hW1 : W + 1 = 2 ^ (v - r)) (hrs : r < sQ)
    (hW : 2 ≤ W) (h : guardOK W e (sQ - r + e + 1) X q) :
    (q.length + maxEntry q + 1 + X) ^ (e + 1) ≤ 2 ^ (v - sQ) := by
  set S := q.length + 1 + max (maxEntry q) X + 1
  have h1 : S ^ (e + 1) ≤ 2 ^ (v - (sQ + e + 1)) :=
    guard_sound_arith (sQ := sQ + e + 1) hW1 (by omega) hW
      (by rw [show sQ + e + 1 - r = sQ - r + e + 1 by omega]; exact h)
  have hS2 : 2 ≤ S := by simp only [S]; omega
  have hve : sQ + e + 1 ≤ v := by
    by_contra hh
    rw [show v - (sQ + e + 1) = 0 by omega, pow_zero] at h1
    have : 2 ≤ S ^ (e + 1) := le_trans hS2 (Nat.le_self_pow (by omega) S)
    omega
  have hle : q.length + maxEntry q + 1 + X ≤ 2 * S := by simp only [S]; omega
  calc (q.length + maxEntry q + 1 + X) ^ (e + 1) ≤ (2 * S) ^ (e + 1) := Nat.pow_le_pow_left hle _
    _ = 2 ^ (e + 1) * S ^ (e + 1) := by rw [mul_pow]
    _ ≤ 2 ^ (e + 1) * 2 ^ (v - (sQ + e + 1)) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (v - sQ) := by rw [← pow_add]; congr 1; omega

/-- **A small query passes the guard.** -/
theorem guard_compl_X {W v r sQ e X : ℕ} {q : List ℕ} (hW1 : W + 1 = 2 ^ (v - r)) (hrs : r < sQ)
    (h : 2 * 2 ^ (e + 1) * (q.length + maxEntry q + X + 2) ^ (e + 1) ≤ 2 ^ (v - sQ)) :
    guardOK W e (sQ - r + e + 1) X q := by
  unfold guardOK
  set S := q.length + 1 + max (maxEntry q) X + 1
  have hS : S ≤ q.length + maxEntry q + X + 2 := by simp only [S]; omega
  have hpos : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
  have hv : sQ + e + 1 ≤ v := by
    by_contra hh
    have h2 : 2 ^ (v - sQ) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 ≤ (q.length + maxEntry q + X + 2) ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
    have h4 : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    nlinarith
  have hsplit : 2 ^ (v - sQ) = 2 ^ (e + 1) * 2 ^ (v - (sQ + e + 1)) := by
    rw [← pow_add]; congr 1; omega
  have h' : 2 * S ^ (e + 1) ≤ 2 ^ (v - (sQ + e + 1)) := by
    have h5 : S ^ (e + 1) ≤ (q.length + maxEntry q + X + 2) ^ (e + 1) := Nat.pow_le_pow_left hS _
    rw [hsplit] at h
    have h6 : 2 ^ (e + 1) * (2 * S ^ (e + 1)) ≤ 2 ^ (e + 1) * 2 ^ (v - (sQ + e + 1)) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h6 (by positivity)
  have := guard_compl_arith (sQ := sQ + e + 1) (s := S) (E := e + 1) hW1 (by omega)
    (by simp only [S]; omega) h'
  rwa [show sQ + e + 1 - r = sQ - r + e + 1 by omega] at this

/-- **Soundness of a round.** Every halting run of the guarded program
outputs `o`, with entries below `2 ^ (v - sI - 4)`, and if the round
issues a call, its query passes the guard of `RGlueAt`. -/
theorem round_sound {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) (hW : "W" ∈ L.scalars)
    (hO : "ovf" ∈ L.scalars) {v sQ K e X : ℕ} {call : Bool} {u o q : List ℕ}
    (hrv : guardBits L + 2 ≤ v) (hrs : guardBits L < sQ) (hu : ∀ x ∈ u, x ≤ Words.guardW L v)
    (hrun : ∃ (ext : String → ℕ) (σ' : Env) (k : ℕ),
      Run (Words.guardW L v + 1) cmd ((initEnv ext u).setVar "W" (Words.guardW L v)) σ' k ∧
      (σ'.vars "ovf" = 0 → σ'.out = o) ∧
      σ'.vars "ovf" = (if RGood (Words.guardW L v) K e (sQ - guardBits L + e + 1) X call q o then 0 else 1)) :
    ∀ o' t, RunsTo v (guardedProgram L cmd) u o' t → o' = o ∧
      (∀ x ∈ o, x < 2 ^ (v - (guardBits L + 6) - 4)) ∧
      (call = true → (q.length + maxEntry q + 1 + X) ^ (e + 1) ≤ 2 ^ (v - sQ)) := by
  obtain ⟨ext, σ', k, hr, hout, hovf⟩ := hrun
  have hs := (guarded_sound hok hW hO hrv hu hr).1
  intro o' t ht
  obtain ⟨h0, hy⟩ := hs o' t ht
  have hg : RGood (Words.guardW L v) K e (sQ - guardBits L + e + 1) X call q o := by
    by_contra hh; rw [hovf, if_neg hh] at h0; exact absurd h0 (by decide)
  have hW1 := Words.guardW_succ L v
  obtain ⟨hK, hgu, hent⟩ := hg
  refine ⟨by rw [hy, hout h0], fun x hx => ?_, fun hc => guard_sound_X hW1 hrs (by omega) (hgu hc)⟩
  have := ent_sound_arith hW1 (lt_of_le_of_lt (le_maxEntry hx) hent)
  rwa [show v - (guardBits L + 6) - 4 = v - guardBits L - 10 by omega]

/-- **Completeness of a round.** If the checks pass, the guarded program
halts with `o`. -/
theorem round_halts {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) (hW : "W" ∈ L.scalars)
    (hO : "ovf" ∈ L.scalars) {v sQ K e X T : ℕ} {call : Bool} {u o q : List ℕ}
    (hrv : guardBits L + 2 ≤ v) (hu : ∀ x ∈ u, x ≤ Words.guardW L v)
    (hrun : ∃ (ext : String → ℕ) (σ' : Env) (k : ℕ),
      Run (Words.guardW L v + 1) cmd ((initEnv ext u).setVar "W" (Words.guardW L v)) σ' k ∧
      (σ'.vars "ovf" = 0 → σ'.out = o) ∧
      σ'.vars "ovf" = (if RGood (Words.guardW L v) K e (sQ - guardBits L + e + 1) X call q o then 0 else 1) ∧
      L.const * k + 5 ≤ T)
    (hg : RGood (Words.guardW L v) K e (sQ - guardBits L + e + 1) X call q o) :
    ∃ t ≤ T, RunsTo v (guardedProgram L cmd) u o t := by
  obtain ⟨ext, σ', k, hr, hout, hovf, hT⟩ := hrun
  have h0 : σ'.vars "ovf" = 0 := by rw [hovf, if_pos hg]
  obtain ⟨t, ht, hrt⟩ := (guarded_sound hok hW hO hrv hu hr).2 h0
  exact ⟨t, by omega, by rwa [hout h0] at hrt⟩

/-- **The checks pass for small sizes.** -/
theorem rgood_of {L : Layout} {v sQ K e X : ℕ} {call : Bool} {q o : List ℕ}
    (hrs : guardBits L + 11 ≤ sQ) (hqo : call = true → q.length ≤ o.length ∧ maxEntry q ≤ maxEntry o)
    (h : (2 * 2 ^ (e + 1) + K + 1) * (o.length + maxEntry o + X + 2) ^ (e + 1) ≤ 2 ^ (v - sQ)) :
    RGood (Words.guardW L v) K e (sQ - guardBits L + e + 1) X call q o := by
  have hW1 := Words.guardW_succ L v
  set Y := o.length + maxEntry o + X + 2
  have hY : 2 ≤ Y := by simp only [Y]; omega
  have hY1 : Y ≤ Y ^ (e + 1) := Nat.le_self_pow (by omega) Y
  have hvs : sQ ≤ v := by
    by_contra hh
    rw [show v - sQ = 0 by omega, pow_zero] at h
    have : 1 * 2 ≤ (2 * 2 ^ (e + 1) + K + 1) * Y ^ (e + 1) := Nat.mul_le_mul (by omega) (le_trans hY hY1)
    omega
  have hsplit : 2 ^ (v - guardBits L) = 2 ^ (v - sQ) * 2 ^ (sQ - guardBits L) := by
    rw [← pow_add]; congr 1; omega
  have h11 : 2 ^ 11 ≤ 2 ^ (sQ - guardBits L) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : (K + 1) * Y ^ (e + 1) ≤ 2 ^ (v - sQ) := le_trans (Nat.mul_le_mul_right _ (by omega)) h
  have hYv : Y ≤ 2 ^ (v - sQ) := le_trans hY1 (le_trans (Nat.le_mul_of_pos_left _ (by omega)) hbig)
  have hKv : K + 1 ≤ 2 ^ (v - sQ) := by
    have : 1 ≤ Y ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  refine ⟨?_, fun hc => guard_compl_X hW1 (by omega) ?_, ?_⟩
  · have : 2 ^ (v - sQ) * 2 ≤ Words.guardW L v + 1 := by rw [hW1, hsplit]; nlinarith
    omega
  · have hqo' := hqo hc
    have h2 : q.length + maxEntry q + X + 2 ≤ Y := by simp only [Y]; omega
    have h3 := Nat.pow_le_pow_left h2 (e + 1)
    have : 2 * 2 ^ (e + 1) * Y ^ (e + 1) ≤ 2 ^ (v - sQ) :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) h
    exact le_trans (Nat.mul_le_mul_left _ h3) this
  · have hme : maxEntry o + 1 ≤ 2 ^ (v - sQ) := by simp only [Y] at hYv; omega
    have h4 : 2 ^ (v - sQ) * 2048 ≤ Words.guardW L v + 1 := by rw [hW1, hsplit]; nlinarith
    rw [Nat.div_div_eq_div_mul]
    rw [Nat.lt_div_iff_mul_lt (by norm_num)]
    omega

end Lax185574Proofs.ResolveRam.Glue
