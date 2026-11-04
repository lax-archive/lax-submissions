import Lax185574Proofs.JobMap.Time

/-!
# Running a program on every job

`jobMap`: for every program `p` there is a program `pJ` that runs `p` on
every job of a list of jobs and outputs the list of the answers. The
jobs and the answers are lists of words, and `pJ` reads and writes them
as the word `toWord`, that is, the number of jobs followed by the
frames of the jobs. If `p` computes `f u` from every job `u` within the
time `c (|u| + 1)^a` at every word length at which `u` is admissible for
the constant `c` and the exponent `e`, then `pJ` computes the list of
the answers within the time `cJ (J + 1)² (maxLen + 1)^aJ`, where `J` is
the number of jobs and `maxLen` the length of the longest job.

The constants come from the soundness and running-time theorems of the
composite and from two estimates of products, `time_arith` and
`room_arith`.
-/

namespace Lax185574Proofs.JobMap

open Lax808846.Ram Lax185574.Computing Lax185574.WordEncoding Lax185574Proofs.Words
open Lax185574Proofs.Words.Fast
open Lax185574Proofs.RamSim Lax185574Proofs.RamExec Lax185574Proofs.Simulate Lax185574Proofs.RamCat

/-- The estimate of the running time. -/
theorem time_arith {KL K0 KP J L Pa P1 PJ x FJ Y cJ : ℕ} (hK0 : 1 ≤ K0) (hKP : KP ≤ K0)
    (hPa : 1 ≤ Pa) (hP1 : P1 = (L + 1) * Pa) (hPJ : P1 ≤ PJ) (hx : x ≤ (J + 1) * (L + 1))
    (hF : FJ ≤ J * (Y + 1)) (hY : Y + 1 ≤ K0 * Pa) (hc : KL * 6012 * K0 ^ 2 ≤ cJ) :
    KL * ((J + 1) * (1000 * (x + FJ) + 4007 + KP * (2 * Y + 1)) + FJ + 2) ≤
      cJ * (J + 1) ^ 2 * PJ := by
  set G := (J + 1) * K0 * P1 with hG
  have hKPa : 1 ≤ K0 * Pa := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hG' : G = K0 * Pa * ((J + 1) * (L + 1)) := by rw [hG, hP1]; ring
  have hJL : 1 ≤ (J + 1) * (L + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hKPaG : K0 * Pa ≤ G := by rw [hG']; exact Nat.le_mul_of_pos_right _ hJL
  have hG1 : 1 ≤ G := le_trans hKPa hKPaG
  have hGK : G ≤ K0 * G := Nat.le_mul_of_pos_left _ hK0
  have h1 : x ≤ G := by
    rw [hG']; exact le_trans hx (Nat.le_mul_of_pos_left _ hKPa)
  have h2 : FJ ≤ G := by
    have e1 : J * (Y + 1) ≤ (J + 1) * (K0 * Pa) := Nat.mul_le_mul (by omega) hY
    have e2 : (J + 1) * (K0 * Pa) ≤ G := by
      rw [hG']
      calc (J + 1) * (K0 * Pa) ≤ (J + 1) * (K0 * Pa) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
        _ = K0 * Pa * ((J + 1) * (L + 1)) := by ring
    omega
  have h3 : KP * (2 * Y + 1) ≤ 2 * (K0 * G) := by
    calc KP * (2 * Y + 1) ≤ K0 * (2 * (K0 * Pa)) := Nat.mul_le_mul hKP (by omega)
      _ ≤ K0 * (2 * G) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (K0 * G) := by ring
  have h4 : 1000 * (x + FJ) + 4007 + KP * (2 * Y + 1) ≤ 6009 * (K0 * G) := by omega
  have h5 : (J + 1) * (1000 * (x + FJ) + 4007 + KP * (2 * Y + 1)) ≤
      6009 * ((J + 1) * (K0 * G)) := by
    calc _ ≤ (J + 1) * (6009 * (K0 * G)) := Nat.mul_le_mul_left _ h4
      _ = _ := by ring
  have h6 : K0 * G ≤ (J + 1) * (K0 * G) := Nat.le_mul_of_pos_left _ (by omega)
  have h7 : (J + 1) * (1000 * (x + FJ) + 4007 + KP * (2 * Y + 1)) + FJ + 2 ≤
      6012 * ((J + 1) * (K0 * G)) := by omega
  calc _ ≤ KL * (6012 * ((J + 1) * (K0 * G))) := Nat.mul_le_mul_left _ h7
    _ = KL * 6012 * K0 ^ 2 * (J + 1) ^ 2 * P1 := by rw [hG]; ring
    _ ≤ cJ * (J + 1) ^ 2 * PJ := by gcongr

/-- The estimate of the room in the regions. -/
theorem room_arith {J X K0 KP c e Pa PJ FJ Y B cJ W : ℕ} (hJX : J + 1 ≤ X) (hK0 : 1 ≤ K0)
    (hKP : KP ≤ K0) (hc : c ≤ K0) (hF : FJ ≤ J * (Y + 1)) (hY : Y + 1 ≤ K0 * Pa)
    (hPJ : Pa * Pa ≤ PJ) (hcJ : 1728 * B * K0 ≤ cJ) (h1 : cJ * X ^ (e + 4) ≤ W)
    (h2 : cJ * (J + 1) ^ 2 * PJ ≤ W) :
    8 * (2 * J + 3) ^ 2 * (B * (KP + c * X ^ e + (X + FJ + Y + (2 * c * X ^ e + 2 * Y) + 4))) ≤
      W := by
  have hX : 1 ≤ X := by omega
  set E := X ^ e with hE
  set X1 := X ^ (e + 1) with hX1
  set X4 := X ^ (e + 4) with hX4
  have hEX : E ≤ X1 := Nat.pow_le_pow_right hX (by omega)
  have hXX : X ≤ X1 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X1 := Nat.pow_le_pow_right hX (by omega)
  have hX11 : 1 ≤ X1 := le_trans hX hXX
  have hKX : X1 ≤ K0 * X1 := Nat.le_mul_of_pos_left _ hK0
  have hcE : c * E ≤ K0 * X1 := Nat.mul_le_mul hc hEX
  have hA : KP + 3 * (c * E) + X + 4 ≤ 9 * (K0 * X1) := by
    have : K0 ≤ K0 * X1 := Nat.le_mul_of_pos_right _ hX11
    omega
  have hsplit : KP + c * E + (X + FJ + Y + (2 * (c * E) + 2 * Y) + 4) =
      (KP + 3 * (c * E) + X + 4) + (FJ + 3 * Y) := by ring
  have hsqX : (2 * J + 3) ^ 2 ≤ 9 * X ^ 2 := by
    calc (2 * J + 3) ^ 2 ≤ (3 * X) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 9 * X ^ 2 := by ring
  have hsqJ : (2 * J + 3) ^ 2 ≤ 9 * (J + 1) ^ 2 := by
    calc (2 * J + 3) ^ 2 ≤ (3 * (J + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 9 * (J + 1) ^ 2 := by ring
  -- the first part
  have hPA : (2 * J + 3) ^ 2 * (KP + 3 * (c * E) + X + 4) ≤ 81 * (K0 * X4) := by
    have e1 : X ^ 2 * X1 ≤ X4 := by
      rw [hX1, hX4, ← pow_add]; exact Nat.pow_le_pow_right hX (by omega)
    calc _ ≤ 9 * X ^ 2 * (9 * (K0 * X1)) := Nat.mul_le_mul hsqX hA
      _ = 81 * (K0 * (X ^ 2 * X1)) := by ring
      _ ≤ 81 * (K0 * X4) := by gcongr
  -- the second part
  have hB : FJ + 3 * Y ≤ 3 * ((J + 1) * (K0 * Pa)) := by
    have e1 : J * (Y + 1) + 3 * (Y + 1) = (J + 3) * (Y + 1) := by ring
    have e2 : (J + 3) * (Y + 1) ≤ (3 * (J + 1)) * (K0 * Pa) := Nat.mul_le_mul (by omega) hY
    have e3 : (3 * (J + 1)) * (K0 * Pa) = 3 * ((J + 1) * (K0 * Pa)) := by ring
    omega
  have hPB : (2 * J + 3) ^ 2 * (FJ + 3 * Y) ≤ 27 * (K0 * X4) + 27 * (K0 * ((J + 1) ^ 2 * PJ)) := by
    have e1 : (2 * J + 3) ^ 2 * (FJ + 3 * Y) ≤ 27 * (K0 * ((J + 1) ^ 2 * ((J + 1) * Pa))) :=
      calc _ ≤ 9 * (J + 1) ^ 2 * (3 * ((J + 1) * (K0 * Pa))) := Nat.mul_le_mul hsqJ hB
        _ = _ := by ring
    rcases le_or_gt Pa (J + 1) with h | h
    · have e2 : (J + 1) ^ 2 * ((J + 1) * Pa) ≤ X4 :=
        calc _ ≤ (J + 1) ^ 2 * ((J + 1) * (J + 1)) := by gcongr
          _ = (J + 1) ^ 4 := by ring
          _ ≤ X ^ 4 := Nat.pow_le_pow_left hJX 4
          _ ≤ X4 := Nat.pow_le_pow_right hX (by omega)
      have : 27 * (K0 * ((J + 1) ^ 2 * ((J + 1) * Pa))) ≤ 27 * (K0 * X4) := by gcongr
      omega
    · have e2 : (J + 1) ^ 2 * ((J + 1) * Pa) ≤ (J + 1) ^ 2 * PJ :=
        Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_right _ h.le) hPJ)
      have : 27 * (K0 * ((J + 1) ^ 2 * ((J + 1) * Pa))) ≤ 27 * (K0 * ((J + 1) ^ 2 * PJ)) := by
        gcongr
      omega
  -- together
  have h2cE : 2 * c * E = 2 * (c * E) := by ring
  rw [h2cE, hsplit]
  have hsum : (2 * J + 3) ^ 2 * ((KP + 3 * (c * E) + X + 4) + (FJ + 3 * Y)) ≤
      108 * (K0 * X4) + 27 * (K0 * ((J + 1) ^ 2 * PJ)) := by
    rw [Nat.mul_add]; omega
  have hc1 : 1728 * (B * K0 * X4) ≤ W := by
    calc _ = 1728 * B * K0 * X4 := by ring
      _ ≤ W := le_trans (Nat.mul_le_mul_right _ hcJ) h1
  have hc2 : 1728 * (B * K0 * ((J + 1) ^ 2 * PJ)) ≤ W := by
    calc _ = 1728 * B * K0 * ((J + 1) ^ 2 * PJ) := by ring
      _ ≤ cJ * ((J + 1) ^ 2 * PJ) := Nat.mul_le_mul_right _ hcJ
      _ = cJ * (J + 1) ^ 2 * PJ := by ring
      _ ≤ W := h2
  calc 8 * (2 * J + 3) ^ 2 * (B * ((KP + 3 * (c * E) + X + 4) + (FJ + 3 * Y)))
        = 8 * B * ((2 * J + 3) ^ 2 * ((KP + 3 * (c * E) + X + 4) + (FJ + 3 * Y))) := by ring
    _ ≤ 8 * B * (108 * (K0 * X4) + 27 * (K0 * ((J + 1) ^ 2 * PJ))) := Nat.mul_le_mul_left _ hsum
    _ = 864 * (B * K0 * X4) + 216 * (B * K0 * ((J + 1) ^ 2 * PJ)) := by ring
    _ ≤ W := by omega

/-- **Running a program on every job.** -/
theorem jobMap {p : Program} {e : ℕ} :
    ∃ (pJ : Program) (eJ : ℕ), ∀ c a : ℕ, ∃ cJ aJ : ℕ,
      ∀ (js : List (List ℕ)) (f : List ℕ → List ℕ),
        (∀ j ∈ js, ∀ w, WordAdmissible e c w j → (∀ y t, RunsTo w p j y t → y = f j) ∧
          (c * (j.length + 1) ^ a ≤ 2 ^ w → ∃ t ≤ c * (j.length + 1) ^ a, RunsTo w p j (f j) t)) →
        ∀ w, WordAdmissible eJ cJ w (toWord js) →
          (∀ y t, RunsTo w pJ (toWord js) y t → y = toWord (js.map f)) ∧
          (cJ * (js.length + 1) ^ 2 * (maxLen js + 1) ^ aJ ≤ 2 ^ w →
            ∃ t ≤ cJ * (js.length + 1) ^ 2 * (maxLen js + 1) ^ aJ,
              RunsTo w pJ (toWord js) (toWord (js.map f)) t) := by
  obtain ⟨P, KP, hP⟩ := capped p sI
  obtain ⟨pJ, KL, hL⟩ := loop_sound gProg P
  refine ⟨pJ, e + 4, fun c a => ?_⟩
  set K0 := KP + c + 1 with hK0
  set cJ := 2 ^ (2 * sI + 30) * (KL + 1) * K0 ^ 2 with hcJ
  refine ⟨cJ, 2 * a + 1, fun js f hjob w hadm => ?_⟩
  have hjob' : ∀ u ∈ js, JobOK p e c a f u := hjob
  have hKpos : 1 ≤ K0 := by omega
  have hK2 : K0 ≤ K0 ^ 2 := by nlinarith
  have hp2 : 2 ^ (2 * sI + 30) = 2 ^ (2 * sI + 10) * 2 ^ 20 := by rw [← pow_add]
  have hXadm : cJ * xSz (toWord js) ^ (e + 4) ≤ 2 ^ w :=
    hadm (maxEntry (toWord js)) (maxEntry_mem (toWord_jobs_ne js))
  have hXpos : 1 ≤ xSz (toWord js) := by simp only [xSz]; omega
  refine ⟨?_, fun htime => ?_⟩
  · refine jm_sound hP hL js f hjob' (le_trans ?_ hXadm)
    have e1 : 2 ^ (2 * sI + 20) * (KP + c + 1) ≤ cJ := by
      rw [hcJ, show 2 ^ (2 * sI + 30) = 2 ^ (2 * sI + 20) * 2 ^ 10 by rw [← pow_add]]
      have h10 : K0 ≤ 2 ^ 10 * (KL + 1) * K0 := Nat.le_mul_of_pos_left _ (by positivity)
      show 2 ^ (2 * sI + 20) * K0 ≤ _
      calc 2 ^ (2 * sI + 20) * K0 ≤ 2 ^ (2 * sI + 20) * (2 ^ 10 * (KL + 1) * K0) :=
            Nat.mul_le_mul_left _ h10
        _ = 2 ^ (2 * sI + 20) * 2 ^ 10 * (KL + 1) * K0 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hK2
    exact Nat.mul_le_mul e1 (Nat.pow_le_pow_right hXpos (by omega))
  -- the running time
  set J := js.length with hJ
  set L := maxLen js with hL'
  set Y := yB c a js with hY
  set FJ := (fr js f J).length with hFJ
  set Pa := (L + 1) ^ a with hPa
  have hPa1 : 1 ≤ Pa := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hYK : Y + 1 ≤ K0 * Pa := by
    have : Y = c * Pa := rfl
    rw [this, hK0]; nlinarith
  have hxlen : (toWord js).length ≤ (J + 1) * (L + 1) := by
    rw [length_toWord_jobs]
    have := List.sum_le_card_nsmul (js.map List.length) L (fun n hn => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hn; exact length_le_maxLen hu)
    simp only [List.length_map, smul_eq_mul, ← hJ] at this
    have e1 : (J + 1) * (L + 1) = 1 + J + J * L + L := by ring
    omega
  have hFJb : FJ ≤ J * (Y + 1) := by
    rw [hFJ, length_fr_last, ← hJ]
    have := List.sum_le_card_nsmul ((js.map f).map List.length) Y (fun n hn => by
      simp only [List.map_map, List.mem_map, Function.comp] at hn
      obtain ⟨u, hu, rfl⟩ := hn; exact (answer_le hjob' hu).1)
    simp only [List.length_map, smul_eq_mul, ← hJ] at this
    have e1 : J * (Y + 1) = J + J * Y := by ring
    omega
  have hcJt : KL * 6012 * K0 ^ 2 ≤ cJ := by
    rw [hcJ]
    have : 6012 ≤ 2 ^ (2 * sI + 30) := le_trans (by norm_num) (Nat.pow_le_pow_right
      (by norm_num) (show 13 ≤ 2 * sI + 30 by omega))
    calc KL * 6012 * K0 ^ 2 ≤ 2 ^ (2 * sI + 30) * (KL + 1) * K0 ^ 2 := by
          apply Nat.mul_le_mul_right; nlinarith
      _ = _ := rfl
  have hroom := room_arith (J := J) (X := xSz (toWord js)) (KP := KP) (c := c) (e := e) (Pa := Pa)
    (PJ := (L + 1) ^ (2 * a + 1)) (FJ := FJ) (Y := Y) (B := 2 ^ (2 * sI + 10)) (cJ := cJ)
    (W := 2 ^ w) (by have := jobs_length_lt js; simp only [xSz]; omega) hKpos (by omega)
    (by omega) hFJb hYK (by rw [hPa, ← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega))
    (by
      rw [hcJ, hp2]
      have : 1728 ≤ 2 ^ 20 := by norm_num
      calc 1728 * 2 ^ (2 * sI + 10) * K0 ≤ 2 ^ 20 * 2 ^ (2 * sI + 10) * K0 := by gcongr
        _ = 2 ^ (2 * sI + 10) * 2 ^ 20 * 1 * K0 := by ring
        _ ≤ 2 ^ (2 * sI + 10) * 2 ^ 20 * (KL + 1) * K0 ^ 2 := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hK2)
    hXadm htime
  obtain ⟨t, ht, hr⟩ := jm_time hP hL js f hjob' (w := w) (by
    simp only [vB, eB]; exact hroom)
  refine ⟨t, le_trans ht ?_, hr⟩
  exact time_arith (P1 := (L + 1) ^ (a + 1)) hKpos (by omega) hPa1 (by rw [hPa, pow_succ]; ring)
    (Nat.pow_le_pow_right (by omega) (by omega)) hxlen hFJb hYK hcJt

end Lax185574Proofs.JobMap
