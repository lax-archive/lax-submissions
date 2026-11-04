import Lax185574Proofs.FarRam.Top
import Lax185574Proofs.Interface.Shim.Restriction
import Lax185574Proofs.Interface.Poly


/-!
The far tree on the word RAM (lem:to-ftree), as a composite of the
restriction program (lem:restrict) with the loop driver.
-/

namespace Lax185574Proofs.ToFarTree

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574Proofs.TreeAlgo Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax185574Proofs.FarRam Lax185574Proofs.RestrictionRam
open Lax3.DistFO (rhoMinus)

theorem dvd_le {a c : ℕ} (h : a ∣ c) (hc : 0 < c) : a ≤ c := Nat.le_of_dvd hc h

/-- The room of a region for a number `N`, from the admissibility of the input. -/
theorem room_of {w i N Y c e : ℕ} (hY : 1 ≤ Y) (hi : i + 1 ≤ 3 * Y) (hN : 1 ≤ N) (h8 : 8 ≤ w)
    (hcN : 72 * N ≤ c * Y ^ (e - 2)) (he : 2 ≤ e) (hadm : c * Y ^ e ≤ 2 ^ w) :
    lpSize w i ≠ 0 ∧ N ≤ 2 ^ lpV w i := by
  refine lp_room hN ?_
  obtain ⟨-, hcap⟩ := lpCap_bounds h8
  have h1 : (i + 1) ^ 2 ≤ 9 * Y ^ 2 := by nlinarith
  have h2 : Y ^ e = Y ^ (e - 2) * Y ^ 2 := by rw [← pow_add]; congr 1; omega
  have h3 : 8 * ((i + 1) ^ 2 * N) ≤ c * Y ^ e := by
    rw [h2]
    calc 8 * ((i + 1) ^ 2 * N) ≤ 8 * (9 * Y ^ 2 * N) := by gcongr
      _ = 72 * N * Y ^ 2 := by ring
      _ ≤ c * Y ^ (e - 2) * Y ^ 2 := Nat.mul_le_mul_right _ hcN
      _ = c * (Y ^ (e - 2) * Y ^ 2) := by ring
  omega

/-- The room of the regions of the glue program. -/
theorem glue_room_arith {Y D e : ℕ} (hY : 1 ≤ Y) (he : 4 ≤ e) :
    72 * (91 * (1764 * Y ^ 4 + D)) ≤ 2 ^ 20 * (1764 + D) * Y ^ e := by
  have h1 : Y ^ 4 ≤ Y ^ e := Nat.pow_le_pow_right hY he
  have h2 : 1 ≤ Y ^ e := Nat.one_le_pow _ _ hY
  have hDZ : D ≤ D * Y ^ e := Nat.le_mul_of_pos_right _ h2
  have e1 : 2 ^ 20 * (1764 + D) * Y ^ e = 1849688064 * Y ^ e + 1048576 * (D * Y ^ e) := by ring
  rw [e1]; omega

/-- The time of the script of the far tree, from the bounds `bG` and `bP`
of the runs of the glue program and of the restriction program. -/
theorem ftree_time_arith {tG tP : ℕ → ℕ} {R P Nσ Z bG bP F cR aR KL K0 c zl : ℕ}
    (htG : ∀ i, tG i ≤ bG) (htP : ∀ i, tP i ≤ bP) (hRP : R ≤ P) (hP4 : 4 ≤ P)
    (hzl : zl ≤ Nσ) (hZd : Z = (Nσ + 1) * P ^ (aR + 3))
    (hbG : bG = 10 * (F * (Nσ + 1) * P ^ 2) + 1) (hbP : bP = cR * (2 * P) ^ aR)
    (hK : 20 * F + cR * 2 ^ aR + 6 ≤ 2 * K0) (hcC : 2 * ((KL + 1) * K0) ≤ c) :
    KL * (scriptTime tG tP R 0 + zl + 1) ≤ c * Z := by
  have hsum : ∑ i ∈ Finset.Ico 0 R, (tG i + tP i + 2) ≤ R * (bG + bP + 2) := by
    have := Finset.sum_le_card_nsmul (Finset.Ico 0 R) (fun i => tG i + tP i + 2) (bG + bP + 2)
      (fun i _ => by have := htG i; have := htP i; omega)
    simpa using this
  have hst : scriptTime tG tP R 0 ≤ R * (bG + bP + 2) + bG + 1 := by
    unfold scriptTime; have := htG R; omega
  have hz1 : (Nσ + 1) * P ^ 2 * P ≤ Z := by
    rw [hZd, mul_assoc, ← pow_succ]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hz2 : P ^ aR * P ≤ Z := by
    rw [hZd, ← pow_succ]
    exact le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.le_mul_of_pos_left _ (by omega))
  have hz3 : (Nσ + 1) * P ^ 2 ≤ Z := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hz1
  have hz4 : Nσ + 1 ≤ Z :=
    le_trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) 2)) hz3
  have hz5 : P ≤ Z := le_trans (le_trans (Nat.le_self_pow (by norm_num) P)
    (Nat.le_mul_of_pos_left _ (by omega))) hz3
  have e1 : P * bG = 10 * F * ((Nσ + 1) * P ^ 2 * P) + P := by rw [hbG]; ring
  have e2 : P * bP = cR * 2 ^ aR * (P ^ aR * P) := by rw [hbP, mul_pow]; ring
  have e3 : bG = 10 * F * ((Nσ + 1) * P ^ 2) + 1 := by rw [hbG]; ring
  have t1 : 10 * F * ((Nσ + 1) * P ^ 2 * P) ≤ 10 * F * Z := Nat.mul_le_mul_left _ hz1
  have t2 : cR * 2 ^ aR * (P ^ aR * P) ≤ cR * 2 ^ aR * Z := Nat.mul_le_mul_left _ hz2
  have t3 : 10 * F * ((Nσ + 1) * P ^ 2) ≤ 10 * F * Z := Nat.mul_le_mul_left _ hz3
  have hRb : R * (bG + bP + 2) ≤ P * bG + P * bP + 2 * P := by
    calc R * (bG + bP + 2) ≤ P * (bG + bP + 2) := Nat.mul_le_mul_right _ hRP
      _ = P * bG + P * bP + 2 * P := by ring
  obtain ⟨A, hAd⟩ : ∃ A, A = 20 * F + cR * 2 ^ aR + 6 := ⟨_, rfl⟩
  have hAZ : A * Z = 2 * (10 * F * Z) + cR * 2 ^ aR * Z + 6 * Z := by rw [hAd]; ring
  have htot : scriptTime tG tP R 0 + zl + 1 ≤ A * Z := by
    rw [hAZ]; omega
  have hKA : KL * A ≤ c := le_trans (Nat.mul_le_mul (Nat.le_add_right KL 1) (show A ≤ 2 * K0 by omega)) (by
    rw [show (KL + 1) * (2 * K0) = 2 * ((KL + 1) * K0) by ring]; exact hcC)
  calc KL * (scriptTime tG tP R 0 + zl + 1) ≤ KL * (A * Z) := Nat.mul_le_mul_left _ htot
    _ = (KL * A) * Z := by ring
    _ ≤ c * Z := Nat.mul_le_mul_right _ hKA

/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_ftree_old :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
        1 ≤ ℓ → ℓ ≤ k →
        Computes p e c (tree G k (q + 1) u, stp G k (q + 1)) (ftree G k (q + 1) u)
          (fun _ => c * (wordLength (stp G k (q + 1)) + 1) *
            (wordLength (tree G k (q + 1) u) + 1) ^ a) := by
  obtain ⟨pR, eR, hR⟩ := Lax185574Proofs.Shim.Restriction.exists_program_restrict
  obtain ⟨p, KL, hL⟩ := loop_sound glueProg pR
  refine ⟨p, eR + 6, fun k q => ?_⟩
  obtain ⟨cR, aR, hRk⟩ := hR (k + 1) q
  obtain ⟨D, hD⟩ : ∃ D, D = finK k q + 4 * (9 ^ k * rhoMinus (k + 1) q) + 2 * rhoMinus (k + 1) q +
    (k + (q + 1) + 1) * q + 20 := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ : ∃ K0, K0 = 8011 + cR * 2 ^ aR + 10 * finK k q := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 2 ^ 20 * (1764 + D) * (cR + 1) * 7 ^ eR * 2 ^ aR * (KL + 1) * K0 := ⟨_, rfl⟩
  have hK0p : 0 < K0 := by omega
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcA : 2 ^ 20 * (1764 + D) ≤ c := dvd_le ⟨(cR + 1) * 7 ^ eR * 2 ^ aR * (KL + 1) * K0, by rw [hc]; ring⟩ hcpos
  have hcB : 72 * (cR + 1) * 7 ^ eR ≤ c := le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (show 72 ≤ 2 ^ 20 * (1764 + D) from
      Nat.le_trans (by norm_num : 72 ≤ 2 ^ 20) (Nat.le_mul_of_pos_right _ (by omega))))) (dvd_le
      ⟨2 ^ aR * (KL + 1) * K0, by rw [hc]; ring⟩ hcpos)
  have hcC : 2 * ((KL + 1) * K0) ≤ c :=
    dvd_le ⟨2 ^ 19 * (1764 + D) * (cR + 1) * 7 ^ eR * 2 ^ aR, by rw [hc]; ring⟩ hcpos
  have hcD : 64 * ((cR + 1) * 2 ^ aR) ≤ c := le_trans (Nat.mul_le_mul_right _
    (show 64 ≤ 2 ^ 20 * (1764 + D) * 7 ^ eR from
      Nat.le_trans (Nat.le_trans (by norm_num : 64 ≤ 2 ^ 20) (Nat.le_mul_of_pos_right _ (by omega)))
        (Nat.le_mul_of_pos_right _ (by positivity)))) (dvd_le
        ⟨(KL + 1) * K0, by rw [hc]; ring⟩ hcpos)
  refine ⟨c, aR + 3, fun n G ℓ u hℓ hℓk => ?_⟩
  intro w hadm
  have hxw : toWord (tree G k (q + 1) u, stp G k (q + 1)) =
      [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u) ++ toWord (stp G k (q + 1)).words := rfl
  rw [hxw] at hadm ⊢
  set t := node G k (q + 1) u with ht
  set S := (stp G k (q + 1)).words with hS
  set x := [k, q + 1, ℓ] ++ toWord t ++ toWord S with hx
  set R := (Node.exts t).words.length with hRdef
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = ySz x := ⟨_, rfl⟩
  have hYx : Y = x.length + maxEntry x + 1 := hYd
  have hY1 : 1 ≤ Y := by omega
  have hadmY : c * Y ^ (eR + 6) ≤ 2 ^ w := by
    have := hadm (maxEntry x) (maxEntry_mem (by simp [hx])); rw [hYx]; exact this
  have hYe : Y ≤ Y ^ (eR + 6) := Nat.le_self_pow (by omega) _
  have hw8 : 8 ≤ w := by
    by_contra hlt
    have h1 : 2 ^ w ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 20 ≤ c := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hcA
    have h3 : c ≤ c * Y ^ (eR + 6) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  obtain ⟨hcap32, hcap⟩ := lpCap_bounds hw8
  have hxN : x.length < 2 ^ (w - 1) := by
    have h1 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 : 2 ^ 20 ≤ c := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hcA
    have h3 : 2 ^ 20 * Y ≤ c * Y ^ (eR + 6) := Nat.mul_le_mul h2 hYe
    omega
  have htx : (toWord t).length + 3 + (toWord S).length = x.length := by simp [hx]; omega
  have hRt : R ≤ (toWord t).length := by
    have := length_toWord_words (Node.exts t).words
    rw [toWord_node_succ, List.length_append]; omega
  have hR1 : 1 ≤ R := exts_pos G k q u hℓ
  obtain ⟨Bv, hBvd⟩ : ∃ Bv, Bv = 1764 * Y ^ 4 + D := ⟨_, rfl⟩
  have hBv : 1764 * ySz x ^ 4 ≤ Bv := by rw [← hYd, hBvd]; omega
  -- room for the glue program
  have hGroom : ∀ j ≤ R, lpSize w (2 * j) ≠ 0 ∧ lsz * Bv ≤ 2 ^ lpV w (2 * j) := by
    intro j hj
    refine room_of (Y := Y) (c := c) (e := eR + 6) hY1 (by omega)
      (Nat.one_le_iff_ne_zero.mpr (by rw [lsz_eq, hBvd]; positivity)) hw8
      ?_ (by omega) hadmY
    rw [lsz_eq, hBvd, show eR + 6 - 2 = eR + 4 by omega]
    exact le_trans (glue_room_arith hY1 (by omega)) (Nat.mul_le_mul_right _ hcA)
  have hD' : 4 * (9 ^ (ℓ - 1) * rhoMinus (k + 1) q) + 2 * rhoMinus (k + 1) q + (k + (q + 1) + 1) * q + 20 ≤ Bv := by
    have : 9 ^ (ℓ - 1) * rhoMinus (k + 1) q ≤ 9 ^ k * rhoMinus (k + 1) q :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [hBvd, hD]; omega
  -- the queries
  have hqry : ∀ j < R, ∃ b : Fin n, queryW k t j = toWord (tree G (k + 1) q (Fin.snoc u b), [Fin.last ℓ]) ∧
      ansW k t j = toWord (tree G (k + 1) q (fun i => (Fin.snoc u b : Fin (ℓ + 1) → Fin n) ([Fin.last ℓ].get i))) ∧
      (queryW k t j).length ≤ (toWord t).length + 5 ∧ ∀ v ∈ queryW k t j, v ≤ maxEntry x + 1 := by
    intro j hj
    obtain ⟨b, h1, h2, h3⟩ := ans_query G k q u j hj
    have hc : childW t j = toWord (node G (k + 1) q (Fin.snoc u b)) := by
      have := h1; rw [queryW, toWord_tree_pair, toWord_listFin] at this
      simp [tree] at this; exact this
    refine ⟨b, h1, h2, ?_, fun v hv => ?_⟩
    · rw [queryW, hc]; have := h3.length_le; simp; omega
    · rw [queryW, hc] at hv
      have hk' : k ≤ maxEntry x := le_maxEntry (by simp [hx])
      have hq' : q + 1 ≤ maxEntry x := le_maxEntry (by simp [hx])
      have hl' : ℓ ≤ maxEntry x := le_maxEntry (by simp [hx])
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with ((h | h | h) | h) | (h | h)
      · omega
      · omega
      · omega
      · have := le_maxEntry (x := x) (v := v)
          (by rw [hx]; exact List.mem_append_left _ (List.mem_append_right _ (h3.subset h)))
        omega
      · omega
      · omega
  have hPadm : ∀ j < R, WordAdmissible eR cR (lpV w (2 * j + 1)) (queryW k t j) := by
    intro j hj v hv
    obtain ⟨-, -, -, hl, hvb⟩ := hqry j hj
    have hv' := hvb v hv
    have h7 : (queryW k t j).length + v + 1 ≤ 7 * Y := by omega
    have hcN : 72 * (cR * (7 * Y) ^ eR + 1) ≤ c * Y ^ (eR + 6 - 2) := by
      rw [show eR + 6 - 2 = eR + 4 by omega, mul_pow]
      have h1 : Y ^ eR ≤ Y ^ (eR + 4) := Nat.pow_le_pow_right hY1 (by omega)
      have h2 : 1 ≤ Y ^ eR := Nat.one_le_pow _ _ hY1
      calc 72 * (cR * (7 ^ eR * Y ^ eR) + 1) ≤ 72 * (cR + 1) * 7 ^ eR * Y ^ eR := by
            have : 1 ≤ 7 ^ eR * Y ^ eR := Nat.one_le_iff_ne_zero.mpr (by positivity)
            have e : 72 * (cR + 1) * 7 ^ eR * Y ^ eR = 72 * (cR * (7 ^ eR * Y ^ eR)) + 72 * (7 ^ eR * Y ^ eR) := by
              ring
            omega
        _ ≤ c * Y ^ (eR + 4) := Nat.mul_le_mul hcB h1
    obtain ⟨-, hroom⟩ := room_of (w := w) (i := 2 * j + 1) (N := cR * (7 * Y) ^ eR + 1) (Y := Y) (c := c)
      (e := eR + 6) hY1 (by omega) (by omega) hw8 hcN (by omega) hadmY
    have := Nat.mul_le_mul_left cR (Nat.pow_le_pow_left h7 eR); omega
  -- the rounds
  have hM : ∀ v ∈ [k, q + 1, ℓ] ++ toWord t, v ≤ maxEntry x :=
    fun v hv => le_maxEntry (by rw [hx]; exact List.mem_append_left _ hv)
  set z := toWord (ftree G k (q + 1) u) with hz
  have hWlR : (wl k t S R).length = S.length + R := (wl_bound G k q u (maxEntry x) hM S R).2
  have hfin := fun (tg sl : ℕ) (hdr rin : List ℕ) (hb : GBnd tg sl k t hdr (wl k t S R) rin S.length R Bv) =>
    g_final (v := lpV w (2 * R)) t k (wl k t S R) S.length tg sl hdr rin hb hWlR
      (wd_wl_three G k q u S (entries_three _) R) hD' (hGroom R le_rfl).2
  have hfz : toWord (farList (toWord t) ((wl k t S R).drop S.length) k q ℓ ((wl k t S R).take S.length)) = z :=
    far_answer G k q u hℓ hℓk
  have hDu : ∀ o tm, RunsTo (lpV w (2 * R)) glueProg (lpU x (scA k t x S R) (scB k t R)) o tm → o = 0 :: z := by
    intro o tm h
    obtain ⟨tg, sl, hdr, rin, hin, hb⟩ := round_in G k q u S x hx Bv hBv R le_rfl
    rw [hin] at h
    rw [(hfin tg sl hdr rin hb).2 o tm h, hfz]
  have hCu : ∀ j < R, CallUniq w glueProg pR x (scA k t x S) (scB k t) j := by
    intro j hj
    refine ⟨fun o tm h => ?_, by simp [scA, callOut], fun r tm h => ?_⟩
    · obtain ⟨tg, sl, hdr, rin, hin, hb⟩ := round_in G k q u S x hx Bv hBv j hj.le
      rw [hin] at h
      exact (g_call t k (wl k t S j) S.length j tg sl hdr rin hb hj (hGroom j hj.le).2).2 o tm h
    · obtain ⟨b, hq, ha, -, -⟩ := hqry j hj
      rw [show scA k t x S (j + 1) = callOut k t S j from rfl, lpQ_callOut, hq] at h
      have := (hRk n G (ℓ + 1) (Fin.snoc u b) [Fin.last ℓ] (by omega) (List.nodup_singleton _)
        (lpV w (2 * j + 1)) (by rw [← hq]; exact hPadm j hj)).1 r tm h
      rw [this, ← ha]; rfl
  refine ⟨fun y tm hrun => ?_, fun hT => ?_⟩
  · exact loop_script_sound (fun w x hw hx => (hL w x hw hx).2) hw8 hxN (A := scA k t x S) (B := scB k t)
      (R := R) (z := z) rfl rfl hCu hDu y tm hrun
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simp only [wordLength]
    have hTd : (toWord (stp G k (q + 1))).length = (toWord S).length := rfl
    have hTt : (toWord (tree G k (q + 1) u)).length = (toWord t).length + 3 := by
      have : toWord (tree G k (q + 1) u) = [k, q + 1, ℓ] ++ toWord t := rfl
      rw [this]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    simp only [wordLength] at hT
    rw [hTd, hTt] at hT ⊢
    obtain ⟨P, hPd⟩ : ∃ P, P = (toWord t).length + 4 := ⟨_, rfl⟩
    obtain ⟨Nσ, hNσ⟩ : ∃ Nσ, Nσ = (toWord S).length := ⟨_, rfl⟩
    rw [show (toWord t).length + 3 + 1 = P by omega, ← hNσ] at hT ⊢
    have hP4 : 4 ≤ P := by omega
    obtain ⟨Z, hZd⟩ : ∃ Z, Z = (Nσ + 1) * P ^ (aR + 3) := ⟨_, rfl⟩
    have hTZ : c * (Nσ + 1) * P ^ (aR + 3) = c * Z := by rw [hZd]; ring
    rw [hTZ] at hT ⊢
    have hSl := length_toWord_words S
    -- the bounds of the runs
    have hconst : FarRam.layout.const = 10 := rfl
    obtain ⟨bG, hbG⟩ : ∃ bG, bG = 10 * ((finK k q + 800) * (Nσ + 1) * P ^ 2) + 1 := ⟨_, rfl⟩
    obtain ⟨bP, hbP⟩ : ∃ bP, bP = cR * (2 * P) ^ aR := ⟨_, rfl⟩
    have hWb : ∀ j ≤ R, (wl k t S j).length + total (wl k t S j) ≤ Nσ + j * ((toWord t).length + 4) := by
      intro j hj
      obtain ⟨h1, h2⟩ := wl_bound G k q u (maxEntry x) hM S j
      rw [← ht] at h1 h2
      have : j * ((toWord t).length + 4) = j * ((toWord t).length + 3) + j := by ring
      omega
    have hcallG : ∀ j < R, ∃ tm ≤ bG, RunsTo (lpV w (2 * j)) glueProg (lpU x (scA k t x S j) (scB k t j))
        (scA k t x S (j + 1)) tm := by
      intro j hj
      obtain ⟨tg, sl, hdr, rin, hin, hb⟩ := round_in G k q u S x hx Bv hBv j hj.le
      rw [hin]
      obtain ⟨tm, htm, hrun⟩ := (g_call t k (wl k t S j) S.length j tg sl hdr rin hb hj (hGroom j hj.le).2).1
      have hcr := callRound_le t (wl k t S j) j Nσ (hWb j hj.le) (by omega)
      refine ⟨tm, le_trans htm ?_, hrun⟩
      rw [hbG, hconst]; rw [← hPd] at hcr
      have : 800 * (Nσ + 1) * P ^ 2 ≤ (finK k q + 800) * (Nσ + 1) * P ^ 2 := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 (le_trans hcr this)) 1
    have hfinG : ∃ tm ≤ bG, RunsTo (lpV w (2 * R)) glueProg (lpU x (scA k t x S R) (scB k t R)) (0 :: z) tm := by
      obtain ⟨tg, sl, hdr, rin, hin, hb⟩ := round_in G k q u S x hx Bv hBv R le_rfl
      rw [hin]
      obtain ⟨tm, htm, hrun⟩ := (hfin tg sl hdr rin hb).1
      rw [hfz] at hrun
      have htk : (wl k t S R).take S.length = S := by simp [wl]
      have hfr := finalRound_le t k (wl k t S R) S.length Nσ hℓk (by omega) (by rw [htk]; omega)
        (by omega) (le_trans (hWb R le_rfl) (by
          have := Nat.mul_le_mul_right ((toWord t).length + 4) hRt; omega)) hRt
      refine ⟨tm, le_trans htm ?_, hrun⟩
      rw [hbG, hconst]; rw [← hPd] at hfr
      have : finK k q * (Nσ + 1) * P ^ 2 ≤ (finK k q + 800) * (Nσ + 1) * P ^ 2 := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 (le_trans hfr this)) 1
    -- the runs of the restriction program
    have hPZ : P ^ (aR + 2) ≤ Z := by
      rw [hZd]
      calc P ^ (aR + 2) ≤ P ^ (aR + 3) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ (Nσ + 1) * P ^ (aR + 3) := Nat.le_mul_of_pos_left _ (by omega)
    have hcallP : ∀ j < R, lpSize w (2 * j + 1) ≠ 0 ∧ ∃ tm ≤ bP,
        RunsTo (lpV w (2 * j + 1)) pR (lpQ (scA k t x S (j + 1))) (scB k t (j + 1)) tm := by
      intro j hj
      obtain ⟨b, hq, ha, hql, -⟩ := hqry j hj
      have hbP1 : 1 ≤ bP + 1 := by omega
      obtain ⟨hs, hroom⟩ := lp_room (w := w) (i := 2 * j + 1) hbP1 (by
        have h1 : (2 * j + 1 + 1) ^ 2 ≤ 4 * P ^ 2 := by
          have : 2 * j + 1 + 1 ≤ 2 * P := by omega
          calc (2 * j + 1 + 1) ^ 2 ≤ (2 * P) ^ 2 := Nat.pow_le_pow_left this 2
            _ = 4 * P ^ 2 := by ring
        obtain ⟨W0, hW0⟩ : ∃ W0, W0 = (cR + 1) * 2 ^ aR * P ^ (aR + 2) := ⟨_, rfl⟩
        have h2 : 4 * P ^ 2 * (bP + 1) ≤ 8 * W0 := by
          rw [hbP, mul_pow, hW0]
          have hA : 1 ≤ 2 ^ aR * P ^ aR := Nat.one_le_iff_ne_zero.mpr (by positivity)
          have hA3 : P ^ 2 ≤ 2 ^ aR * P ^ aR * P ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
          have e1 : 4 * P ^ 2 * (cR * (2 ^ aR * P ^ aR) + 1) =
              4 * (cR * (2 ^ aR * P ^ aR * P ^ 2)) + 4 * P ^ 2 := by ring
          have e2 : 8 * ((cR + 1) * 2 ^ aR * P ^ (aR + 2)) =
              8 * (cR * (2 ^ aR * P ^ aR * P ^ 2)) + 8 * (2 ^ aR * P ^ aR * P ^ 2) := by
            rw [pow_add]; ring
          rw [e1, e2]; omega
        have h3 : 64 * W0 ≤ c * Z := by
          rw [hW0]
          calc 64 * ((cR + 1) * 2 ^ aR * P ^ (aR + 2)) = 64 * ((cR + 1) * 2 ^ aR) * P ^ (aR + 2) := by ring
            _ ≤ c * Z := Nat.mul_le_mul hcD hPZ
        calc (2 * j + 1 + 1) ^ 2 * (bP + 1) ≤ 4 * P ^ 2 * (bP + 1) := Nat.mul_le_mul_right _ h1
          _ ≤ lpCap w := by omega)
      refine ⟨hs, ?_⟩
      have hwl : wordLength (tree G (k + 1) q (Fin.snoc u b), [Fin.last ℓ]) + 1 ≤ 2 * P := by
        simp only [wordLength]; rw [← hq]; omega
      have hTP : cR * (wordLength (tree G (k + 1) q (Fin.snoc u b), [Fin.last ℓ]) + 1) ^ aR ≤
          2 ^ lpV w (2 * j + 1) := by
        have := Nat.mul_le_mul_left cR (Nat.pow_le_pow_left hwl aR); rw [hbP] at hroom; omega
      obtain ⟨tm, htm, hrun⟩ := (hRk n G (ℓ + 1) (Fin.snoc u b) [Fin.last ℓ] (by omega)
        (List.nodup_singleton _) (lpV w (2 * j + 1)) (by rw [← hq]; exact hPadm j hj)).2 hTP _ rfl
      refine ⟨tm, le_trans htm ?_, ?_⟩
      · rw [hbP]; exact Nat.mul_le_mul_left cR (Nat.pow_le_pow_left hwl aR)
      · rw [show scA k t x S (j + 1) = callOut k t S j from rfl, lpQ_callOut, hq,
          show scB k t (j + 1) = ansW k t j from rfl, ha]
        exact hrun
    -- the script
    have hG' : ∀ j, ∃ tm, tm ≤ bG ∧ (j < R → RunsTo (lpV w (2 * j)) glueProg
        (lpU x (scA k t x S j) (scB k t j)) (scA k t x S (j + 1)) tm) ∧
        (j = R → RunsTo (lpV w (2 * j)) glueProg (lpU x (scA k t x S j) (scB k t j)) (0 :: z) tm) := by
      intro j
      rcases lt_trichotomy j R with h | h | h
      · obtain ⟨tm, htm, hr⟩ := hcallG j h
        exact ⟨tm, htm, fun _ => hr, fun h' => absurd h' (by omega)⟩
      · subst h
        obtain ⟨tm, htm, hr⟩ := hfinG
        exact ⟨tm, htm, fun h' => absurd h' (by omega), fun _ => hr⟩
      · exact ⟨0, Nat.zero_le _, fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩
    choose tG htG using hG'
    have hP' : ∀ j, ∃ tm, tm ≤ bP ∧ (j < R → RunsTo (lpV w (2 * j + 1)) pR (lpQ (scA k t x S (j + 1)))
        (scB k t (j + 1)) tm) := by
      intro j
      by_cases h : j < R
      · obtain ⟨-, tm, htm, hr⟩ := hcallP j h
        exact ⟨tm, htm, fun _ => hr⟩
      · exact ⟨0, Nat.zero_le _, fun h' => absurd h' h⟩
    choose tP htP using hP'
    have hcapY : ∀ m, m ≤ 16 * Y ^ 2 → m ≤ lpCap w := by
      intro m hm
      have h1 : Y ^ 2 ≤ Y ^ (eR + 6) := Nat.pow_le_pow_right hY1 (by omega)
      have h2 : 2 ^ 20 ≤ c := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hcA
      have h3 : 2 ^ 20 * Y ^ 2 ≤ c * Y ^ (eR + 6) := Nat.mul_le_mul h2 h1
      omega
    have htY : (toWord t).length + 4 ≤ Y := by omega
    have hσY : (toWord S).length ≤ Y := by omega
    have hYY : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
    have hzS : z.length ≤ (toWord S).length := by
      rw [← hfz]
      have htk : (wl k t S R).take S.length = S := by simp [wl]
      unfold farList
      exact le_trans (toWord_filter_map_le _ _) (le_of_eq (by rw [htk]))
    have hcapA : ∀ j < R, (scA k t x S (j + 1)).length ≤ lpCap w := by
      intro j hj
      apply hcapY
      obtain ⟨b, -, -, hql, -⟩ := hqry j hj
      have hwb := hWb j hj.le
      have hfl := length_frames (wl k t S j)
      simp only [scA, callOut, List.length_append, List.length_cons, List.length_nil]
      have : j * ((toWord t).length + 4) ≤ Y * Y := Nat.mul_le_mul (by omega) htY
      have e2 : Y ^ 2 = Y * Y := sq Y
      omega
    have hcapB : ∀ j < R, (scB k t (j + 1)).length ≤ lpCap w := by
      intro j hj
      apply hcapY
      have := (ansW_bound G k q u (maxEntry x) hM j).1
      simp only [scB]; rw [← ht] at this; omega
    obtain ⟨tz, htz, hrun⟩ := loop_script_run (fun w x hw hx => (hL w x hw hx).1) hw8 hxN
      (A := scA k t x S) (B := scB k t) (tG := tG) (tP := tP) (R := R) (z := z) rfl rfl
      (fun j hj => ⟨(hGroom j hj.le).1, (htG j).2.1 hj, (hCu j hj).uniqG, by simp [scA, callOut],
        (hCu j hj).head, hcapA j hj, (hcallP j hj).1, (htP j).2 hj, (hCu j hj).uniqP, hcapB j hj⟩)
      ⟨(hGroom R le_rfl).1, (htG R).2.2 rfl, hDu, hcapY _ (by simp; omega)⟩
    refine ⟨tz, le_trans htz ?_, hrun⟩
    -- the time of the script
    exact ftree_time_arith (fun i => (htG i).1) (fun i => (htP i).1) (by omega) hP4
      (by rw [hNσ]; exact hzS) hZd (by rw [hbG]) hbP (by rw [hK0]; omega) hcC

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.ToFarTree.exists_program_ftree
---
The program runs the glue program `FarRam.glue` and the restriction
program of the restriction lemma in the loop driver `loop_sound`. Round
`j` of the glue program reads the tree, the scatter type and the answers
so far, and asks for the restriction `μ ↾ (ℓ+1)` of the child of
extension `j` to its last position, one call per extension. The last
round reads the radius and the blocks off the root, the met and far bits
off the roots of the children, scans the scatter type and writes the
selected trees, as in the proof of the far tree lemma. Its output is the
far tree by `farTree_tree`, which applies the clustering lemma. Every
run inside the driver is right at an admissible word length: the runs of
the glue program because their values are polynomial in the input with a
factor depending on the rank, the runs of the restriction program
because their queries are admissible at the word lengths of their
regions.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_ftree :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
        A.Computes c (tree G k (q + 1) u, stp G k (q + 1)) (ftree G k (q + 1) u)
          (((encode (stp G k (q + 1))).length + 1) *
            ((encode (tree G k (q + 1) u)).length + 1) ^ a) := by
  obtain ⟨p, e, h⟩ := exists_program_ftree_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  refine ⟨c, a, fun n G ℓ u h₁ h₂ => ?_⟩
  refine computes_of_old_nat (((encode (stp G k (q + 1))).length + 1) *
      ((encode (tree G k (q + 1) u)).length + 1) ^ a) (by push_cast; rfl) le_rfl ?_
    (h n G ℓ u h₁ h₂)
  show c * ((encode (stp G k (q + 1))).length + 1) *
    ((encode (tree G k (q + 1) u)).length + 1) ^ a ≤ _
  rw [mul_assoc]
  exact Nat.le_add_right _ _

end Lax185574Proofs.ToFarTree
