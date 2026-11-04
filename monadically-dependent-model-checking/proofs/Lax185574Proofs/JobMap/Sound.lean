import Lax185574Proofs.JobMap.Round
import Lax185574Proofs.RamCapped

/-!
Soundness of the composite that runs a program on every job.

The composite is the loop driver with the guarded glue program and the
callee `capped p sI`, which runs `p` at `sI + 2` levels below the word
length of its region and caps its output. At a word length at which the
input word `x` is admissible for a large constant and the exponent
`e + 3`, every region of the driver up to the last round has room for
the constants and for `x`, and the jobs are admissible for `p` there.
The invariant of round `j` is that the input of the round has entries
below `2^(v - sI)` at the word length `v` of the round. The checks of the
glue program and the capped output of the callee carry it from round
to round, since the word length drops by at most four from one round to
the next.
-/

namespace Lax185574Proofs.JobMap

open Lax808846.Ram Lax185574.Computing Lax185574.WordEncoding Lax185574Proofs.Words
open Lax185574Proofs.RamSim Lax185574Proofs.RamExec Lax185574Proofs.Simulate Lax185574Proofs.RamCat

/-- The specification of the callee `capped p D` with constant `K`. -/
def CapSpec (P p : Program) (K D : ℕ) : Prop :=
  ∀ (w : ℕ) (x : List ℕ), K ≤ 2 ^ (w - 2 - D) → x.length < 2 ^ (w - 2 - D) → D + 7 ≤ w →
    (∀ y t, RunsTo (w - 2 - D) p x y t → y.length ≤ catLim (w - 2) (D + 2) →
      ∃ t' ≤ K * (t + y.length + 1), RunsTo w P x y t') ∧
    (∀ o T, RunsTo w P x o T →
      ∃ t ≤ T, RunsTo (w - 2 - D) p x o t ∧ o.length ≤ catLim (w - 2) (D + 2))

/-- The specification of the loop driver `pJ` of `G` and `P` with constant `K`. -/
def LoopSpec (pJ G P : Program) (K : ℕ) : Prop :=
  ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
    (∀ z T, LoopTrace w G P x 0 (lpA0 x) [] z T →
      ∃ t ≤ K * (T + z.length + 1), RunsTo w pJ x z t) ∧
    (∀ z t, RunsTo w pJ x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)

/-- The size measure of the input word: its length plus its largest entry plus one. -/
def xSz (x : List ℕ) : ℕ := x.length + maxEntry x + 1

theorem two_pow_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- The threshold of the checks is below `2^(v - sI - 4)`. -/
theorem thr_lt {v : ℕ} (hv : sI + 5 ≤ v) : guardW glueLay v / 64 < 2 ^ (v - sI - 4) := by
  have h1 := guardW_succ glueLay v
  have h2 : 2 ^ (v - guardBits glueLay) = 64 * 2 ^ (v - sI - 4) := by
    rw [sI_eq, show v - guardBits glueLay = (v - (guardBits glueLay + 2) - 4) + 6 by
      rw [sI_eq] at hv; omega, pow_add]
    ring
  have := Nat.div_mul_le_self (guardW glueLay v) 64
  omega

theorem le_mul_pow {X k : ℕ} (hX : 1 ≤ X) (n : ℕ) : X ^ n ≤ X ^ (n + k) :=
  Nat.pow_le_pow_right hX (by omega)

/-- **Soundness.** -/
theorem jm_sound {p P pJ : Program} {e c a KP KL : ℕ} (hP : CapSpec P p KP sI)
    (hL : LoopSpec pJ gProg P KL) (js : List (List ℕ)) (f : List ℕ → List ℕ)
    (hjob : ∀ u ∈ js, JobOK p e c a f u) {w : ℕ}
    (hadm : 2 ^ (2 * sI + 20) * (KP + c + 1) * xSz (toWord js) ^ (e + 3) ≤ 2 ^ w) :
    ∀ y t, RunsTo w pJ (toWord js) y t → y = toWord (js.map f) := by
  set x := toWord js with hx
  set X := xSz x with hX
  set J := js.length with hJ
  have hJx : J < x.length := jobs_length_lt js
  have hxl : (toWord js).length = x.length := rfl
  have hxm : maxEntry (toWord js) = maxEntry x := rfl
  have hX1 : x.length + maxEntry x + 1 = X := rfl
  have hXpos : 1 ≤ X := by omega
  set S := KP + c * X ^ e + X with hS
  set N := 2 ^ (2 * sI + 10) * S with hN
  have hS1 : 1 ≤ S := by omega
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hreg : 8 * (2 * J + 3) ^ 2 * N ≤ 2 ^ w := by
    have h1 : (2 * J + 3) ^ 2 ≤ 9 * X ^ 2 := by
      have : 2 * J + 3 ≤ 3 * X := by omega
      calc (2 * J + 3) ^ 2 ≤ (3 * X) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 9 * X ^ 2 := by ring
    have h2 : X ^ 2 * S ≤ (KP + c + 1) * X ^ (e + 3) := by
      have e1 : KP * X ^ 2 ≤ KP * X ^ (e + 3) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hXpos (by omega))
      have e2 : X ^ 2 * X ^ e ≤ X ^ (e + 3) := by rw [← pow_add]; exact Nat.pow_le_pow_right hXpos (by omega)
      have e3 : X ^ 2 * X ≤ X ^ (e + 3) := by rw [← pow_succ]; exact Nat.pow_le_pow_right hXpos (by omega)
      have e4 : c * (X ^ 2 * X ^ e) ≤ c * X ^ (e + 3) := Nat.mul_le_mul_left _ e2
      calc X ^ 2 * S = KP * X ^ 2 + c * (X ^ 2 * X ^ e) + X ^ 2 * X := by rw [hS]; ring
        _ ≤ KP * X ^ (e + 3) + c * X ^ (e + 3) + X ^ (e + 3) := by omega
        _ = (KP + c + 1) * X ^ (e + 3) := by ring
    have h3 : 2 ^ (2 * sI + 20) = 2 ^ (2 * sI + 10) * 1024 := by
      rw [show 2 * sI + 20 = (2 * sI + 10) + 10 by ring, pow_add]; norm_num
    calc 8 * (2 * J + 3) ^ 2 * N ≤ 8 * (9 * X ^ 2) * N := by gcongr
      _ = 72 * 2 ^ (2 * sI + 10) * (X ^ 2 * S) := by rw [hN]; ring
      _ ≤ 72 * 2 ^ (2 * sI + 10) * ((KP + c + 1) * X ^ (e + 3)) := by gcongr
      _ ≤ 2 ^ (2 * sI + 10) * 1024 * (KP + c + 1) * X ^ (e + 3) := by
          have : 72 * 2 ^ (2 * sI + 10) * ((KP + c + 1) * X ^ (e + 3)) =
            72 * (2 ^ (2 * sI + 10) * (KP + c + 1) * X ^ (e + 3)) := by ring
          rw [this]
          have : 2 ^ (2 * sI + 10) * 1024 * (KP + c + 1) * X ^ (e + 3) =
            1024 * (2 ^ (2 * sI + 10) * (KP + c + 1) * X ^ (e + 3)) := by ring
          rw [this]; omega
      _ ≤ 2 ^ w := by rw [← h3]; exact hadm
  obtain ⟨hw3, hR⟩ := regions hN1 hreg
  -- what a region gives
  have hpart : ∀ i ≤ 2 * J + 2, ∀ B k, B * 2 ^ k ≤ N → 1 ≤ B → k ≤ lpV w i ∧ B ≤ 2 ^ (lpV w i - k) :=
    fun i hi B k h hB => le_pow_sub' (le_trans h (hR i hi).2) hB
  have hsplit : ∀ T k, T ≤ S → k ≤ 2 * sI + 10 → T * 2 ^ k ≤ N := by
    intro T k hT hk
    rw [hN, mul_comm]
    exact Nat.mul_le_mul (two_pow_le hk) hT
  have hR1 : ∀ i ≤ 2 * J + 2, sI + 7 ≤ lpV w i ∧ X ≤ 2 ^ (lpV w i - (sI + 2)) := fun i hi =>
    ⟨(hpart i hi 1 (sI + 7) (hsplit 1 _ hS1 (by omega)) le_rfl).1,
      (hpart i hi X (sI + 2) (hsplit X _ (by omega) (by omega)) hXpos).2⟩
  have hw8 : 8 ≤ w := by
    have := (hR1 0 (by omega)).1
    have : lpV w 0 ≤ w := by simp only [lpV]; omega
    rw [sI_eq] at *; omega
  have hxw : x.length < 2 ^ (w - 1) := by
    have h1 := (hR1 0 (by omega)).2
    have h2 : 2 ^ (lpV w 0 - (sI + 2)) ≤ 2 ^ (w - 1) := two_pow_le (by simp only [lpV]; omega)
    omega
  -- the script
  refine inv_script_sound (fun w x hw hx => (hL w x hw hx).2) hw8 hxw (A := gA js f) (B := gB js f)
    (I := fun j => ∀ y ∈ gIn js f j, y < 2 ^ (lpV w (2 * j) - sI)) (R := J)
    (z := toWord (js.map f)) rfl rfl ?_ ?_ ?_
  · -- the first round
    intro y hy
    have h1 := (hR1 0 (by omega)).2
    have h2 : 2 ^ (lpV w 0 - (sI + 2)) ≤ 2 ^ (lpV w 0 - sI) := two_pow_le (by omega)
    show y < 2 ^ (lpV w 0 - sI)
    simp only [gIn, if_true] at hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_append.mp h with h | h
      · simp at h; omega
      · have := le_maxEntry h; omega
    · simp at h; omega
  · -- the calls
    intro j hj hI o t ho
    rw [lpU_gA hj.le] at ho
    have hv := hR1 (2 * j) (by omega)
    obtain ⟨e1, hck⟩ := glue_sound_at js f hj.le (by omega) hI o t ho
    refine ⟨e1, (gA_head hj).2, fun r t' hr => ?_⟩
    have hlpQ : lpQ o = js[j] := by rw [e1]; exact lpQ_gA hj
    rw [hlpQ] at hr
    have hjx : js[j].length < x.length := length_job_lt (List.getElem_mem hj)
    obtain ⟨hk1, hKP⟩ := hpart (2 * j + 1) (by omega) (KP + 1) (sI + 2)
      (hsplit _ _ (by omega) (by omega)) (by omega)
    obtain ⟨-, hXc⟩ := hR1 (2 * j + 1) (by omega)
    have hvc7 := (hR1 (2 * j + 1) (by omega)).1
    obtain ⟨-, hc⟩ := hpart (2 * j + 1) (by omega) (c * X ^ e + 1) (sI + 2)
      (hsplit _ _ (by omega) (by omega)) (by omega)
    have hv1 := lpV_succ_ge w (2 * j)
    have hv2 := lpV_succ_ge w (2 * j + 1)
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring] at hv2
    generalize lpV w (2 * j + 1) = vc at *
    have hsub : vc - 2 - sI = vc - (sI + 2) := by omega
    obtain ⟨t1, -, hp1, hlen⟩ := (hP vc js[j] (by rw [hsub]; omega) (by rw [hsub]; omega)
      (by omega)).2 r t' hr
    -- the job is admissible for `p`
    have hadmj : WordAdmissible e c (vc - 2 - sI) js[j] := by
      intro y hy
      have hy' : y ≤ maxEntry x := le_maxEntry (mem_job hj hy)
      rw [hsub]
      calc c * (js[j].length + y + 1) ^ e ≤ c * X ^ e :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ ≤ _ := by omega
    have hr' : r = f js[j] := ((hjob js[j] (List.getElem_mem hj)) _ hadmj).1 r t1 hp1
    refine ⟨by rw [hr', gB_succ hj], ?_⟩
    -- the invariant of the next round
    generalize lpV w (2 * j) = v at *
    generalize lpV w (2 * (j + 1)) = v' at *
    have hv2' : vc - 2 ≤ v' := hv2
    have hthr := thr_lt (v := v) (by omega)
    have hT : 2 ^ (v - sI - 4) ≤ 2 ^ (v' - sI) := two_pow_le (by omega)
    obtain ⟨c1, c2, c3, c4⟩ := hck
    have hrl : r.length < 2 ^ (v' - sI) := by
      rw [catLim_eq (by omega)] at hlen
      have : 2 ^ (vc - 2 - (sI + 2)) ≤ 2 ^ (v' - sI) := two_pow_le (by omega)
      have : 0 < 2 ^ (vc - 2 - (sI + 2)) := by positivity
      omega
    have hre : ∀ y ∈ r, y < 2 ^ (v' - sI) := fun y hy =>
      lt_of_lt_of_le (runsTo_out_lt hp1 y hy) (two_pow_le (by omega))
    rw [hr'] at hrl hre
    intro y hy
    rw [gIn_succ hj] at hy
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hy
    rcases hy with ((((h | h) | h) | h | h) | h) | h | h
    · omega
    · omega
    · have := c3 y h; omega
    · have : 0 < 2 ^ (v' - sI) := by positivity
      omega
    · omega
    · have := c4 y h; omega
    · omega
    · exact hre y h
  · -- the last round
    intro hI o t ho
    rw [lpU_gA le_rfl] at ho
    have hv := hR1 (2 * J) (by omega)
    rw [(glue_sound_at js f le_rfl (by omega) hI o t ho).1, gOut_last]

end Lax185574Proofs.JobMap
