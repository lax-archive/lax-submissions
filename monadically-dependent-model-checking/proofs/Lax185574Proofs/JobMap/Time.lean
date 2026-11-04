import Lax185574Proofs.JobMap.Sound

/-!
The running time of the composite that runs a program on every job.

If every region of the loop driver up to the last round has room for
the constants, for the size measure `X` of the input, and for the bound
`V` on the lengths and entries of all words of the script, then the
composite halts with `toWord (js.map f)`. The glue program checks pass
and each round takes time linear in the lengths of the input and of the
frames of the answers. The callee halts within the time bound of `p` on
the job. The bounds on the answers come from `answer_bound`.
-/

namespace Lax185574Proofs.JobMap

open Lax808846.Ram Lax185574.Computing Lax185574.WordEncoding Lax185574Proofs.Words
open Lax185574Proofs.Words.Fast
open Lax185574Proofs.RamSim Lax185574Proofs.RamExec Lax185574Proofs.Simulate Lax185574Proofs.RamCat

/-- The time bound of the callee on the longest job. -/
def yB (c a : ℕ) (js : List (List ℕ)) : ℕ := c * (maxLen js + 1) ^ a

/-- The bound on the entries of the answers. -/
def eB (e c a : ℕ) (js : List (List ℕ)) : ℕ :=
  2 * c * xSz (toWord js) ^ e + 2 * yB c a js

/-- The bound on all lengths and entries of the script. -/
def vB (e c a : ℕ) (js : List (List ℕ)) (f : List ℕ → List ℕ) : ℕ :=
  xSz (toWord js) + (fr js f js.length).length + yB c a js + eB e c a js + 4

theorem maxEntry_le' {x : List ℕ} {b : ℕ} (h : ∀ v ∈ x, v ≤ b) : maxEntry x ≤ b := by
  induction x with
  | nil => exact Nat.zero_le _
  | cons z x ih =>
    show max z (maxEntry x) ≤ b
    exact max_le (h z (by simp)) (ih fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem answer_le {p : Program} {e c a : ℕ} {js : List (List ℕ)} {f : List ℕ → List ℕ}
    (hjob : ∀ u ∈ js, JobOK p e c a f u) {u : List ℕ} (hu : u ∈ js) :
    (f u).length ≤ yB c a js ∧ ∀ y ∈ f u, y ≤ eB e c a js := by
  obtain ⟨h1, h2⟩ := answer_bound (hjob u hu)
  have hl := length_le_maxLen hu
  have hlx := length_job_lt hu
  have hm : maxEntry u ≤ maxEntry (toWord js) := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
    exact maxEntry_le' fun y hy => le_maxEntry (mem_job hj hy)
  have hY : c * (u.length + 1) ^ a ≤ yB c a js :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hE : c * (u.length + maxEntry u + 1) ^ e ≤ c * xSz (toWord js) ^ e :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simp only [xSz]; omega) _)
  refine ⟨le_trans h1 hY, fun y hy => ?_⟩
  have := h2 y hy
  simp only [eB]
  have e1 : 2 * c * (u.length + maxEntry u + 1) ^ e = 2 * (c * (u.length + maxEntry u + 1) ^ e) := by
    ring
  have e2 : 2 * c * (u.length + 1) ^ a = 2 * (c * (u.length + 1) ^ a) := by ring
  have e3 : 2 * c * xSz (toWord js) ^ e = 2 * (c * xSz (toWord js) ^ e) := by ring
  omega

theorem fr_entry_le {p : Program} {e c a : ℕ} {js : List (List ℕ)} {f : List ℕ → List ℕ}
    (hjob : ∀ u ∈ js, JobOK p e c a f u) {j y : ℕ} (hy : y ∈ fr js f j) :
    y ≤ yB c a js + eB e c a js := by
  obtain ⟨u, hu, h | h⟩ := mem_fr hy
  · have := (answer_le hjob hu).1; omega
  · have := (answer_le hjob hu).2 y h; omega

/-- **Running time.** -/
theorem jm_time {p P pJ : Program} {e c a KP KL : ℕ} (hP : CapSpec P p KP sI)
    (hL : LoopSpec pJ gProg P KL) (js : List (List ℕ)) (f : List ℕ → List ℕ)
    (hjob : ∀ u ∈ js, JobOK p e c a f u) {w : ℕ}
    (hroom : 8 * (2 * js.length + 3) ^ 2 *
      (2 ^ (2 * sI + 10) * (KP + c * xSz (toWord js) ^ e + vB e c a js f)) ≤ 2 ^ w) :
    ∃ t ≤ KL * ((js.length + 1) * (1000 * ((toWord js).length + (fr js f js.length).length) + 4007 +
        KP * (2 * yB c a js + 1)) + (fr js f js.length).length + 2),
      RunsTo w pJ (toWord js) (toWord (js.map f)) t := by
  set x := toWord js with hx
  set X := xSz x with hX
  set J := js.length with hJ
  set V := vB e c a js f with hV
  set Y := yB c a js with hY
  set FJ := (fr js f J).length with hFJ
  have hxl : (toWord js).length = x.length := rfl
  have hxm : maxEntry (toWord js) = maxEntry x := rfl
  have hX1 : x.length + maxEntry x + 1 = X := rfl
  have hXr : xSz (toWord js) = X := rfl
  have hYr : yB c a js = Y := rfl
  have hFr : (fr js f js.length).length = FJ := rfl
  have hJx : J < x.length := jobs_length_lt js
  have hVe : V = X + FJ + Y + eB e c a js + 4 := by simp only [hV, vB, hXr, hYr, hFr]
  have hXV : X ≤ V := by omega
  have hYV : Y + 1 ≤ V := by omega
  have hFV : FJ + 2 ≤ V := by omega
  have hEV : Y + eB e c a js ≤ V := by omega
  have hxX : x.length + 1 ≤ X := by simp only [hX, xSz]; omega
  have hmX : maxEntry x < X := by simp only [hX, xSz]; omega
  set S := KP + c * X ^ e + V with hS
  set N := 2 ^ (2 * sI + 10) * S with hN
  have hS1 : 1 ≤ S := by omega
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨hw3, hR⟩ := regions hN1 hroom
  have hpart : ∀ i ≤ 2 * J + 2, ∀ B k, B * 2 ^ k ≤ N → 1 ≤ B → k ≤ lpV w i ∧ B ≤ 2 ^ (lpV w i - k) :=
    fun i hi B k h hB => le_pow_sub' (le_trans h (hR i hi).2) hB
  have hsplit : ∀ T k, T ≤ S → k ≤ 2 * sI + 10 → T * 2 ^ k ≤ N := by
    intro T k hT hk
    rw [hN, mul_comm]
    exact Nat.mul_le_mul (two_pow_le hk) hT
  have hR1 : ∀ i ≤ 2 * J + 2, sI + 7 ≤ lpV w i ∧ V ≤ 2 ^ (lpV w i - (sI + 5)) := fun i hi =>
    ⟨(hpart i hi 1 (sI + 7) (hsplit 1 _ hS1 (by omega)) le_rfl).1,
      (hpart i hi V (sI + 5) (hsplit V _ (by omega) (by omega)) (by omega)).2⟩
  have hcap : ∀ i ≤ 2 * J + 2, ∀ n ≤ 2 * V, n ≤ lpCap w := by
    intro i hi n hn
    have h1 := (hR1 i hi).2
    have h2 : 2 ^ (lpV w i - (sI + 5)) * 2 ≤ 2 ^ lpV w i := by
      rw [← pow_succ]; exact two_pow_le (by have := (hR1 i hi).1; omega)
    have := lpV_le_cap w i
    omega
  have hw8 : 8 ≤ w := by
    have := (hR1 0 (by omega)).1
    have : lpV w 0 ≤ w := by simp only [lpV]; omega
    rw [sI_eq] at *; omega
  have hxw : x.length < 2 ^ (w - 1) := by
    have h1 := (hR1 0 (by omega)).2
    have h2 : 2 ^ (lpV w 0 - (sI + 5)) ≤ 2 ^ (w - 1) := two_pow_le (by simp only [lpV]; omega)
    omega
  -- the glue rounds
  have hG : ∀ j, ∃ tg, j ≤ J → tg ≤ 1000 * (x.length + FJ) + 4005 ∧
      RunsTo (lpV w (2 * j)) gProg (lpU x (gA js f j) (gB js f j)) (gA js f (j + 1)) tg ∧
      ∀ o t, RunsTo (lpV w (2 * j)) gProg (lpU x (gA js f j) (gB js f j)) o t → o = gA js f (j + 1) := by
    intro j
    by_cases hj : j ≤ J
    · obtain ⟨h7, hVv⟩ := hR1 (2 * j) (by omega)
      generalize lpV w (2 * j) = v at h7 hVv
      have hW1 := guardW_succ glueLay v
      have hv' : guardBits glueLay + 7 ≤ v := by rw [sI_eq] at h7; omega
      have h2 : 2 ^ (v - guardBits glueLay) = 2 ^ (v - (sI + 5)) * 128 := by
        rw [sI_eq, show v - guardBits glueLay = (v - (guardBits glueLay + 2 + 5)) + 7 by omega,
          pow_add]; norm_num
      have hT : V ≤ guardW glueLay v / 64 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
      have hfl : (fr js f j).length ≤ FJ := length_fr_le js f j
      obtain ⟨⟨t, ht, hr⟩, hu⟩ := glue_time_at js f hj (v := v) (by omega) (by omega)
        ⟨by omega, by omega, fun y hy => by have := le_maxEntry hy; omega,
          fun y hy => by have := fr_entry_le hjob hy; omega⟩
      refine ⟨t, fun _ => ⟨by omega, ?_, ?_⟩⟩
      · rw [lpU_gA hj]; exact hr
      · intro o t' h; rw [lpU_gA hj] at h; exact hu o t' h
    · exact ⟨0, fun h => absurd h hj⟩
  choose tG htG using hG
  -- the calls
  have hPc : ∀ j, ∃ tp, j < J → lpSize w (2 * j + 1) ≠ 0 ∧ tp ≤ KP * (2 * Y + 1) ∧
      RunsTo (lpV w (2 * j + 1)) P (lpQ (gA js f (j + 1))) (gB js f (j + 1)) tp ∧
      ∀ r t, RunsTo (lpV w (2 * j + 1)) P (lpQ (gA js f (j + 1))) r t → r = gB js f (j + 1) := by
    intro j
    by_cases hj : j < J
    · have hsz := (hR (2 * j + 1) (by omega)).1
      have hmem := List.getElem_mem hj
      have hjx : js[j].length < x.length := length_job_lt hmem
      obtain ⟨hk1, hKP⟩ := hpart (2 * j + 1) (by omega) (KP + 1) (sI + 2)
        (hsplit _ _ (by omega) (by omega)) (by omega)
      obtain ⟨-, hXc⟩ := hpart (2 * j + 1) (by omega) (X + 1) (sI + 2)
        (hsplit _ _ (by omega) (by omega)) (by omega)
      obtain ⟨-, hc⟩ := hpart (2 * j + 1) (by omega) (c * X ^ e + 1) (sI + 2)
        (hsplit _ _ (by omega) (by omega)) (by omega)
      obtain ⟨-, hYc⟩ := hpart (2 * j + 1) (by omega) (Y + 1) (sI + 4)
        (hsplit _ _ (by omega) (by omega)) (by omega)
      have hvc7 := (hR1 (2 * j + 1) (by omega)).1
      rw [lpQ_gA hj, gB_succ hj]
      generalize lpV w (2 * j + 1) = vc at *
      have hsub : vc - 2 - sI = vc - (sI + 2) := by omega
      have hadmj : WordAdmissible e c (vc - 2 - sI) js[j] := by
        intro y hy
        have hy' : y ≤ maxEntry x := le_maxEntry (mem_job hj hy)
        rw [hsub]
        calc c * (js[j].length + y + 1) ^ e ≤ c * X ^ e :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
          _ ≤ _ := by omega
      have hYj : c * (js[j].length + 1) ^ a ≤ Y := by
        have hl := length_le_maxLen hmem
        have : (js[j].length + 1) ^ a ≤ (maxLen js + 1) ^ a := Nat.pow_le_pow_left (by omega) _
        exact Nat.mul_le_mul_left c this
      obtain ⟨hsnd, htm⟩ := (hjob js[j] hmem) _ hadmj
      have h24 : 2 ^ (vc - (sI + 4)) ≤ 2 ^ (vc - (sI + 2)) := two_pow_le (by omega)
      obtain ⟨t, ht, hp⟩ := htm (by rw [hsub]; omega)
      have hcl : (f js[j]).length ≤ catLim (vc - 2) (sI + 2) := by
        rw [catLim_eq (by omega)]
        have := (answer_le hjob hmem).1
        rw [show vc - 2 - (sI + 2) = vc - (sI + 4) by omega]; omega
      obtain ⟨hf, hb⟩ := hP vc js[j] (by rw [hsub]; omega) (by rw [hsub]; omega) (by omega)
      obtain ⟨t', ht', hr⟩ := hf _ t hp hcl
      refine ⟨t', fun _ => ⟨hsz, le_trans ht' ?_, hr, fun r t2 h2 => ?_⟩⟩
      · have := (answer_le hjob hmem).1
        exact Nat.mul_le_mul_left _ (by omega)
      · obtain ⟨t3, -, h3, -⟩ := hb r t2 h2
        exact hsnd r t3 h3
    · exact ⟨0, fun h => absurd h hj⟩
  choose tP htP using hPc
  have hCO : ∀ j < J, CallOK w gProg P x (gA js f) (gB js f) tG tP j := by
    intro j hj
    obtain ⟨hg1, hg2, hg3⟩ := htG j hj.le
    obtain ⟨hp0, hp1, hp2, hp3⟩ := htP j hj
    have hlo : (gA js f (j + 1)).length ≤ 2 * V := by
      simp only [gA, gOut_lt hj, List.length_append, List.length_cons, List.length_nil]
      have := length_fr_le js f j
      have := length_job_lt (List.getElem_mem hj)
      omega
    refine ⟨(hR (2 * j) (by omega)).1, hg2, hg3, (gA_head hj).1, (gA_head hj).2,
      hcap (2 * j) (by omega) _ hlo, hp0, hp2, hp3, ?_⟩
    rw [gB_succ hj]
    exact hcap 0 (by omega) _ (by have := (answer_le hjob (List.getElem_mem hj)).1; omega)
  have hlast : gA js f (J + 1) = 0 :: toWord (js.map f) := by simp [gA, gOut_last, hJ]
  have hzl : (toWord (js.map f)).length = FJ + 1 := by rw [toWord_map]; simp [hFJ, hJ]
  have hDO : DoneOK w gProg x (gA js f) (gB js f) tG J (toWord (js.map f)) := by
    obtain ⟨hg1, hg2, hg3⟩ := htG J le_rfl
    refine ⟨(hR (2 * J) (by omega)).1, by rw [← hlast]; exact hg2, by rw [← hlast]; exact hg3, ?_⟩
    exact hcap 0 (by omega) _ (by simp only [List.length_cons, hzl]; omega)
  obtain ⟨t, ht, hrun⟩ := loop_script_run (fun w x hw hx => (hL w x hw hx).1) hw8 hxw
    (A := gA js f) (B := gB js f) (tG := tG) (tP := tP) (R := J) rfl rfl hCO hDO
  refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ ?_), hrun⟩
  -- the sum of the rounds
  set TG := 1000 * (x.length + FJ) + 4005 with hTG
  set TP := KP * (2 * Y + 1) with hTP
  have hsum : scriptTime tG tP J 0 ≤ (J + 1) * (TG + TP + 2) := by
    simp only [scriptTime]
    have h1 : ∑ i ∈ Finset.Ico 0 J, (tG i + tP i + 2) ≤ ∑ _i ∈ Finset.Ico 0 J, (TG + TP + 2) :=
      Finset.sum_le_sum fun i hi => by
        have hi' := (Finset.mem_Ico.mp hi).2
        have := (htG i hi'.le).1; have := (htP i hi').2.1; omega
    rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at h1
    have h2 := (htG J le_rfl).1
    have : (J + 1) * (TG + TP + 2) = (J - 0) * (TG + TP + 2) + (TG + TP + 2) := by
      rw [Nat.sub_zero]; ring
    omega
  have e1 : TG + TP + 2 = 1000 * (x.length + FJ) + 4007 + TP := by
    rw [hTG]; ring
  rw [e1] at hsum
  omega

end Lax185574Proofs.JobMap
