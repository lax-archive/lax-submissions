import Lax185574Proofs.StpRam.Room
import Lax185574.ComputeScatterType
import Lax185574Proofs.Interface.Shim.RankShift
import Lax185574Proofs.Interface.Poly

/-!
Computing the scatter type on the word RAM (lem:compute-stp), as a
composite of the program of the rank shift (lem:shift) with the loop
driver.
-/

namespace Lax185574Proofs.ComputeScatterType

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.PartialGraphEncoding Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim Lax185574Proofs.StpRam Lax185574.DistanceMatrix

theorem head_Ao {n : ℕ} (G : PartialGraph (Fin n)) (k q j : ℕ) :
    (Ao G k q (j + 1)).head? ≠ some 0 := by
  simp only [Ao, tagS]; split_ifs <;> simp

theorem ne_Ao {n : ℕ} (G : PartialGraph (Fin n)) (k q j : ℕ) : Ao G k q (j + 1) ≠ [] := by
  simp [Ao]

theorem lpQ_Ao {n : ℕ} (G : PartialGraph (Fin n)) (k q j : ℕ) :
    lpQ (Ao G k q (j + 1)) = qryS G k q j := by
  simp only [Ao]; exact lpQ_round _ _ _ _

theorem idxS_lt {Q j : ℕ} (hQ : 1 ≤ Q) : idxS Q j < Q := by
  unfold idxS; split_ifs <;> omega

theorem vB_ge {n : ℕ} {G : PartialGraph (Fin n)} {k q X : ℕ}
    (hX : X = (xIn G k q).length + maxEntry (xIn G k q) + 1) :
    64 * (rK k q + 1) * X ^ 3 = vB G k q := by rw [vB, ← hX]

theorem length_Ao_le {n : ℕ} {G : PartialGraph (Fin n)} {k q X : ℕ} (hs : Sizes G k q X)
    (hX : X = (xIn G k q).length + maxEntry (xIn G k q) + 1) {j : ℕ} (hj : j ≤ q * n) :
    (Ao G k q (j + 1)).length ≤ vB G k q := by
  obtain ⟨h1, -⟩ := stS_bound hs hj
  obtain ⟨h2, -⟩ := qryS_bound hs j
  have hL := hs.LX
  obtain ⟨hX3, -, -⟩ := X_pow hs
  have h4 : 64 * X ^ 3 ≤ 64 * (rK k q + 1) * X ^ 3 := by
    rw [Nat.mul_assoc 64]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  rw [← vB_ge hX]
  simp only [Ao, List.length_append, List.length_cons, List.length_nil]
  omega

theorem length_Bo_le {n : ℕ} {G : PartialGraph (Fin n)} {k q X : ℕ} (hs : Sizes G k q X)
    (hX : X = (xIn G k q).length + maxEntry (xIn G k q) + 1) (j : ℕ) :
    (Bo G k q (j + 1)).length ≤ vB G k q := by
  obtain ⟨h1, -⟩ := ansS_bound hs j
  have hL := hs.LX
  obtain ⟨hX3, -, -⟩ := X_pow hs
  have h4 : 64 * X ^ 3 ≤ 64 * (rK k q + 1) * X ^ 3 := by
    rw [Nat.mul_assoc 64]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  rw [← vB_ge hX]
  simp only [Bo]
  omega

theorem length_out_le {n : ℕ} {G : PartialGraph (Fin n)} {k q X : ℕ} (hs : Sizes G k q X)
    (hX : X = (xIn G k q).length + maxEntry (xIn G k q) + 1) :
    (0 :: toWord (stp G k q)).length ≤ vB G k q := by
  have hz := length_toWord_stp_le G k q (maxTreeSize G k q) hs.ansL
  have hL := hs.LX
  have hQ := hs.QX
  obtain ⟨hX3, -, -⟩ := X_pow hs
  have hR : radius k q 1 ≤ rK k q := by unfold rK; omega
  have h1 : radius k q 1 * (q * n) * (maxTreeSize G k q + 3) ≤ rK k q * X ^ 2 * (4 * X) :=
    Nat.mul_le_mul (Nat.mul_le_mul hR hQ) (by omega)
  have h2 : rK k q * X ^ 2 * (4 * X) = 4 * (rK k q * X ^ 3) := by ring
  have h3 : 64 * (rK k q + 1) * X ^ 3 = 64 * (rK k q * X ^ 3) + 64 * X ^ 3 := by ring
  rw [← vB_ge hX, List.length_cons]
  omega

set_option maxHeartbeats 8000000 in
/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_stp_old :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)), 1 ≤ k → 1 ≤ n →
        Computes p e c (G, k, q, distMatrix G, family G k q) (stp G k q)
          (fun _ => c * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a) := by
  obtain ⟨pS, eS, hS⟩ := Lax185574Proofs.Shim.RankShift.exists_program_shift
  choose cS aS hcS using hS
  obtain ⟨p, KL, hL⟩ := loop_sound gProg pS
  refine ⟨p, eS + 8, fun k q => ?_⟩
  set cM := cSum cS k q with hcM
  set aM := cSum aS k q with haM
  set R1 := radius k q 1 with hR1
  set C0 := (rK k q + 1) * (cM * 4 ^ eS + 1) *
    ((KL + 1) * tK k q R1 cM + 32 * (q + 1) ^ 2 * (cM + 1)) with hC0
  have hC0a : rK k q + 1 ≤ C0 := by
    rw [hC0, Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (Nat.add_pos_right _ (by positivity)))
  have hC0b : cM * 4 ^ eS + 1 ≤ C0 := by
    rw [hC0, Nat.mul_comm (rK k q + 1), Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (Nat.add_pos_right _ (by positivity)))
  have hC0c : (KL + 1) * tK k q R1 cM + 32 * (q + 1) ^ 2 * (cM + 1) ≤ C0 := by
    rw [hC0]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  refine ⟨2 ^ 22 * C0, aM + 1, fun n G hk hn => ?_⟩
  intro w hadm
  have hxe : toWord (G, k, q, distMatrix G, family G k q) = xIn G k q := rfl
  rw [hxe] at hadm ⊢
  have hs := sizes G k q
  have hx0 : xIn G k q ≠ [] := by rw [xIn_eq]; simp
  generalize hXd : (xIn G k q).length + maxEntry (xIn G k q) + 1 = X at hs
  have hadm' : 2 ^ 22 * C0 * X ^ (eS + 8) ≤ 2 ^ w := by
    have := hadm _ (maxEntry_mem hx0); rw [hXd] at this; exact this
  have hX1 := hs.one
  have hRG := fun j (hj : j ≤ q * n + 1) => room_glue hs hXd.symm (by omega) hC0a hadm' hj
  have hRP := fun j (hj : j ≤ q * n) => room_shift (cM := cM) hs rfl hC0b hadm' hj
  obtain ⟨-, -, hcap, hw8⟩ := hRG 0 (by omega)
  have hxw : (xIn G k q).length < 2 ^ (w - 1) := by
    have h1 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 : 2 * X ≤ 2 ^ 22 * C0 * X ^ (eS + 8) := by
      have : X ≤ X ^ (eS + 8) := le_self_pow₀ hX1 (by omega)
      have : 2 ≤ 2 ^ 22 * C0 := by
        have : 1 ≤ C0 := by omega
        calc 2 ≤ 2 ^ 22 * 1 := by norm_num
          _ ≤ 2 ^ 22 * C0 := Nat.mul_le_mul_left _ this
      nlinarith
    omega
  have hLA := hL w (xIn G k q) hw8 hxw
  -- the answers of the rank shift
  have hCal : ∀ j ≤ q * n, 1 ≤ q * n →
      (∀ r t, RunsTo (lpV w (2 * j + 1)) pS (lpQ (Ao G k q (j + 1))) r t → r = Bo G k q (j + 1)) ∧
      (cM * ((qryS G k q j).length + 1) ^ aM ≤ 2 ^ lpV w (2 * j + 1) →
        ∃ t ≤ cM * ((qryS G k q j).length + 1) ^ aM,
          RunsTo (lpV w (2 * j + 1)) pS (lpQ (Ao G k q (j + 1))) (Bo G k q (j + 1)) t) := by
    intro j hj hQ
    rw [lpQ_Ao]
    obtain ⟨-, hroom⟩ := hRP j hj
    obtain ⟨hql, hqv⟩ := qryS_bound hs j
    have hLX := hs.LX
    exact callee_facts hcS G hk (idxS_lt hQ) _ (fun y hy => by
      have h1 : (qryS G k q j).length + y + 1 ≤ 4 * X := by have := hqv y hy; omega
      have h2 := Nat.mul_le_mul_left cM (Nat.pow_le_pow_left h1 eS)
      exact le_trans h2 (by omega))
  -- the time
  set L := maxTreeSize G k q with hLd
  set P := (n + 1) * (n + 1) * (L + 1) with hPd
  set Lp := (L + 1) ^ aM with hLpd
  have hLp : 1 ≤ Lp := Nat.one_le_pow _ _ (by omega)
  have hPLp : P * Lp = (n + 1) ^ 2 * (L + 1) ^ (aM + 1) := by rw [hPd, hLpd, pow_succ]; ring
  have hKT : KL * (tK k q R1 cM * (P * Lp)) ≤ 2 ^ 22 * C0 * (n + 1) ^ 2 * (L + 1) ^ (aM + 1) := by
    have h1 : KL * tK k q R1 cM ≤ C0 := by
      have : KL * tK k q R1 cM ≤ (KL + 1) * tK k q R1 cM := Nat.mul_le_mul_right _ (by omega)
      omega
    calc KL * (tK k q R1 cM * (P * Lp)) = KL * tK k q R1 cM * (P * Lp) := by ring
      _ ≤ C0 * (P * Lp) := Nat.mul_le_mul_right _ h1
      _ ≤ 2 ^ 22 * C0 * (P * Lp) := by
          rw [Nat.mul_assoc (2 ^ 22)]; exact Nat.le_mul_of_pos_left _ (by positivity)
      _ = 2 ^ 22 * C0 * (n + 1) ^ 2 * (L + 1) ^ (aM + 1) := by rw [hPLp]; ring
  have hfl := length_toWord_family_le G k q
  have hzl := length_toWord_stp_le G k q L hs.ansL
  have hcapG := hcap
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · -- no rounds with calls
    subst hq0
    obtain ⟨⟨tm0, htm0, hr0⟩, hu0⟩ := script_r0_zero (G := G) (k := k) hn le_rfl (hRG 0 (by omega)).2.1
    have hz0 : (0 :: toWord (stp G k 0)).length ≤ lpCap w :=
      le_trans (length_out_le hs hXd.symm) (le_trans (Nat.le_mul_of_pos_left _ (by rw [gsz_eq]; omega)) hcapG)
    refine ⟨fun y t' h => ?_, fun hT => ?_⟩
    · exact loop_script_sound (fun w x hw hx => (hL w x hw hx).2) hw8 hxw (A := Ao G k 0) (B := Bo G k 0)
        (R := 0) rfl rfl (fun j hj => absurd hj (by omega)) hu0 y t' h
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨tz, htz, hrun⟩ := loop_script_run (fun w x hw hx => (hL w x hw hx).1) hw8 hxw
        (A := Ao G k 0) (B := Bo G k 0) (tG := fun _ => tm0) (tP := fun _ => 0) (R := 0) rfl rfl
        (fun j hj => absurd hj (by omega)) ⟨(hRG 0 (by omega)).1, hr0, hu0, hz0⟩
      refine ⟨tz, le_trans htz (le_trans ?_ hKT), hrun⟩
      have hst : scriptTime (fun _ => tm0) (fun _ => 0) 0 0 = tm0 + 1 := by simp [scriptTime]
      rw [hst]
      have := time_arith k 0 R1 cM n L 0
        (toWord (family G k 0)).length 0 (toWord (stp G k 0)).length P tm0 0 0 0 Lp hfl
        (by omega) (by omega) hzl hLp htm0 (by omega) (by omega) (by omega) rfl
      simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_zero, Nat.add_zero] at this
      apply Nat.mul_le_mul_left
      try simp only [List.length_cons]
      omega
  -- the rounds with calls
  have hQ1 : 1 ≤ q * n := Nat.mul_pos hq1 hn
  have hr0 := script_r0 (G := G) (k := k) (q := q) hn hq1 le_rfl (hRG 0 (by omega)).2.1
  have hmid := fun t (ht : t < q * n) =>
    script_mid (G := G) (k := k) (q := q) (t := t) hn ht le_rfl (hRG (t + 1) (by omega)).2.1
  have hfin := script_fin (G := G) (k := k) (q := q) hq1 le_rfl (hRG (q * n + 1) le_rfl).2.1
  have huG : ∀ j < q * n + 1, ∀ o t, RunsTo (lpV w (2 * j)) gProg
      (lpU (xIn G k q) (Ao G k q j) (Bo G k q j)) o t → o = Ao G k q (j + 1) := by
    intro j hj
    rcases j with _ | t
    · exact hr0.2
    · exact (hmid t (by omega)).2
  refine ⟨fun y t' h => ?_, fun hT => ?_⟩
  · exact loop_script_sound (fun w x hw hx => (hL w x hw hx).2) hw8 hxw (A := Ao G k q) (B := Bo G k q)
      (R := q * n + 1) rfl rfl
      (fun j hj => ⟨huG j hj, head_Ao G k q j, (hCal j (by omega) hQ1).1⟩) hfin.2 y t' h
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  simp only at hT
  -- the runs of the glue program
  set a0 := 10 * (winCost n + 9 * (n * (n + 1)) + n * (48 * L + 110) +
    100 * ((toWord (family G k q)).length + n) + 1030) + 1
    with ha0
  set sl := 6 + ((toWord (family G k q)).length + n) + (toWord (answers G k q)).length with hsl
  have hstS : ∀ j, (stS G k q j).length ≤ sl := by
    intro j
    rw [stS, length_stState, length_toWord_famF]
    have := length_toWord_take_le (answers G k q) j
    omega
  set cf := 10 * (readCost n L n (toWord (answers G k q)).length +
    finalCost n k q L (q * n) (radius k q 1) + 20) + 1 with hcf
  have hG : ∀ j, ∃ tm, (j = 0 → tm ≤ a0 ∧ RunsTo (lpV w (2 * 0)) gProg
        (lpU (xIn G k q) (Ao G k q 0) (Bo G k q 0)) (Ao G k q 1) tm) ∧
      (∀ t, j = t + 1 → t < q * n → tm ≤ 10 * (100 * sl + 420) + 1 ∧ RunsTo (lpV w (2 * (t + 1))) gProg
        (lpU (xIn G k q) (Ao G k q (t + 1)) (Bo G k q (t + 1))) (Ao G k q (t + 2)) tm) ∧
      (j = q * n + 1 → tm ≤ cf ∧ RunsTo (lpV w (2 * (q * n + 1))) gProg
        (lpU (xIn G k q) (Ao G k q (q * n + 1)) (Bo G k q (q * n + 1))) (0 :: toWord (stp G k q)) tm) := by
    intro j
    rcases j with _ | t
    · obtain ⟨tm, htm, hr⟩ := hr0.1
      exact ⟨tm, fun _ => ⟨htm, hr⟩, fun t h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · by_cases ht : t < q * n
      · obtain ⟨tm, htm, hr⟩ := (hmid t ht).1
        refine ⟨tm, fun h => absurd h (by omega), fun t' h _ => ?_, fun h => absurd h (by omega)⟩
        obtain rfl : t = t' := by omega
        exact ⟨le_trans htm (by have := hstS (t + 1); omega), hr⟩
      · by_cases htq : t = q * n
        · subst htq
          obtain ⟨tm, htm, hr⟩ := hfin.1
          exact ⟨tm, fun h => absurd h (by omega), fun t' h h' => absurd h' (by omega), fun _ => ⟨htm, hr⟩⟩
        · exact ⟨0, fun h => absurd h (by omega), fun t' h h' => absurd h' (by omega),
            fun h => absurd h (by omega)⟩
  choose tG htG using hG
  -- the runs of the rank shift
  have hroomT : ∀ j ≤ q * n, lpSize w (2 * j + 1) ≠ 0 ∧ cM * Lp + 1 ≤ 2 ^ lpV w (2 * j + 1) := by
    intro j hj
    refine lp_room (by omega) ?_
    have hw' := lpCap_eq (w := w) (by omega)
    have h1 : (2 * j + 1 + 1) ^ 2 ≤ 4 * (q + 1) ^ 2 * ((n + 1) * (n + 1)) := by
      have : 2 * j + 1 + 1 ≤ 2 * ((q + 1) * (n + 1)) := by nlinarith
      calc (2 * j + 1 + 1) ^ 2 ≤ (2 * ((q + 1) * (n + 1))) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 4 * (q + 1) ^ 2 * ((n + 1) * (n + 1)) := by ring
    have h2 : cM * Lp + 1 ≤ (cM + 1) * Lp := by nlinarith
    have h3 : 8 * (4 * (q + 1) ^ 2 * ((n + 1) * (n + 1)) * ((cM + 1) * Lp)) ≤
        2 ^ 22 * C0 * (n + 1) ^ 2 * (L + 1) ^ (aM + 1) := by
      have h4 : 32 * (q + 1) ^ 2 * (cM + 1) ≤ 2 ^ 22 * C0 := by
        have : 32 * (q + 1) ^ 2 * (cM + 1) ≤ C0 := by omega
        have : C0 ≤ 2 ^ 22 * C0 := Nat.le_mul_of_pos_left _ (by positivity)
        omega
      have h5 : Lp ≤ (L + 1) ^ (aM + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc 8 * (4 * (q + 1) ^ 2 * ((n + 1) * (n + 1)) * ((cM + 1) * Lp)) =
          32 * (q + 1) ^ 2 * (cM + 1) * ((n + 1) * (n + 1)) * Lp := by ring
        _ ≤ 2 ^ 22 * C0 * ((n + 1) * (n + 1)) * (L + 1) ^ (aM + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ h4) h5
        _ = 2 ^ 22 * C0 * (n + 1) ^ 2 * (L + 1) ^ (aM + 1) := by ring
    calc (2 * j + 1 + 1) ^ 2 * (cM * Lp + 1) ≤ 4 * (q + 1) ^ 2 * ((n + 1) * (n + 1)) * ((cM + 1) * Lp) :=
          Nat.mul_le_mul h1 h2
      _ ≤ lpCap w := by omega
  have hPr : ∀ j, ∃ tm, j ≤ q * n → tm ≤ cM * Lp ∧
      RunsTo (lpV w (2 * j + 1)) pS (lpQ (Ao G k q (j + 1))) (Bo G k q (j + 1)) tm := by
    intro j
    by_cases hj : j ≤ q * n
    · have hql := (qryS_bound hs j).1
      have hb : cM * ((qryS G k q j).length + 1) ^ aM ≤ cM * Lp :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      obtain ⟨tm, htm, hr⟩ := (hCal j hj hQ1).2 (le_trans hb (by have := (hroomT j hj).2; omega))
      exact ⟨tm, fun _ => ⟨le_trans htm hb, hr⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose tP htP using hPr
  -- the script
  have hcapv : vB G k q ≤ lpCap w :=
    le_trans (Nat.le_mul_of_pos_left _ (by rw [gsz_eq]; omega)) hcapG
  obtain ⟨tz, htz, hrun⟩ := loop_script_run (fun w x hw hx => (hL w x hw hx).1) hw8 hxw
    (A := Ao G k q) (B := Bo G k q) (tG := tG) (tP := tP) (R := q * n + 1) rfl rfl
    (fun j hj => by
      have hrG : RunsTo (lpV w (2 * j)) gProg (lpU (xIn G k q) (Ao G k q j) (Bo G k q j)) (Ao G k q (j + 1))
          (tG j) := by
        rcases j with _ | t
        · exact ((htG 0).1 rfl).2
        · exact ((htG (t + 1)).2.1 t rfl (by omega)).2
      exact ⟨(hRG j (by omega)).1, hrG, huG j hj, ne_Ao G k q j, head_Ao G k q j,
        le_trans (length_Ao_le hs hXd.symm (by omega)) hcapv, (hroomT j (by omega)).1,
        ((htP j (by omega)).2), (hCal j (by omega) hQ1).1,
        le_trans (length_Bo_le hs hXd.symm j) hcapv⟩)
    ⟨(hRG (q * n + 1) le_rfl).1, ((htG (q * n + 1)).2.2 rfl).2, hfin.2,
      le_trans (length_out_le hs hXd.symm) hcapv⟩
  refine ⟨tz, le_trans htz (le_trans ?_ hKT), hrun⟩
  apply Nat.mul_le_mul_left
  have hst := scriptTime_le tG tP (q * n) a0 (10 * (100 * sl + 420) + 1) cf (cM * Lp)
    ((htG 0).1 rfl).1
    (fun j h1 h2 => by
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      exact ((htG (t + 1)).2.1 t rfl (by omega)).1)
    ((htG (q * n + 1)).2.2 rfl).1 (fun j hj => (htP j hj).1)
  have htw := length_toWord_answers_le G k q hs.ansL
  have := time_arith k q R1 cM n L (toWord (answers G k q)).length
    (toWord (family G k q)).length sl (toWord (stp G k q)).length P a0 (10 * (100 * sl + 420) + 1) cf
    (cM * Lp) Lp hfl htw le_rfl hzl hLp le_rfl le_rfl le_rfl le_rfl rfl
  try simp only [List.length_cons]
  omega

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.ComputeScatterType.exists_program_stp
---
The program runs the glue program `StpRam.glue` and the program of the
rank shift lemma in the loop driver `loop_sound`, as in the proof of the lemma on computing scatter types. The first round
reads the graph, `k` and `q`, skips the distance matrix `D_G` and reads
the family of type trees. For `q = 0` it outputs the empty scatter type.
Otherwise the rounds ask for the shifts of the entries of the list of
the family trees followed by the answers, one by one, so that the
answers are the trees `tree_{k+i,q−i}(v)` for `1 ≤ i ≤ q` and all
vertices `v`, in this order. After a dummy call the final round reads
the graph, `D_G` and the answers and computes the scatter type
(`StpRam.finalRound_run`). Its greedy scans test whether a vertex is
within distance `r` of a chosen vertex by one entry of the row of `D_G`
of the chosen vertex, in place of a breadth-first search. The script has
`q · n + 1` calls. Every run inside the driver is right at an admissible
word length: the runs of the glue program because their values are below
a constant in `k, q` times the cube of `|x| + max x + 1`, the runs of
the rank shift because their queries are admissible at the word lengths
of their regions. The time is that of the first round, `O_{k,q}(n² + n ·
L)`, and of the final round, `O_{k,q}(n² · (L + 1))`, plus `q · n`
middle rounds of time `O_{k,q}(n · L)` and `q · n + 1` calls of time
`O_{k,q}((L + 1)^a)`.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_stp :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)), 1 ≤ k → 1 ≤ n →
        A.Computes c (G, k, q, distMatrix G, family G k q) (stp G k q)
          (n ^ 2 * (maxTreeSize G k q + 1) ^ a) := by
  obtain ⟨p, e, h⟩ := exists_program_stp_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  refine ⟨4 * c, a, fun n G hk hn => ?_⟩
  refine computes_of_old_nat (n ^ 2 * (maxTreeSize G k q + 1) ^ a) (by push_cast; rfl)
    (by omega) ?_ (h n G hk hn)
  show c * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a ≤ _
  refine le_trans ?_ (Nat.le_add_right _ _)
  have h4 : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
  calc c * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a
      ≤ c * (4 * n ^ 2) * (maxTreeSize G k q + 1) ^ a := by gcongr
    _ = 4 * c * (n ^ 2 * (maxTreeSize G k q + 1) ^ a) := by ring

end Lax185574Proofs.ComputeScatterType
