import Lax185574Proofs.ResolveRam.TimeAdm

/-!
**Halting within the time bound.** At every word length at which the
input of lem:resolve-lift is admissible for `eRes` and `cRes` and the
bound `rBound` with `cRes` and `aRes` fits into a word, the composite
halts with the output within that bound. This is the second clause of
`Computes` for the composite.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

theorem final_time {KL Ks cG C rb S R Z L W Y aG A a dF : ℕ} (hY : 1 ≤ Y) (hW : 1 ≤ W)
    (ha : aG + A ≤ a) (hrB : rb = cG * W * Y ^ aG) (hS : S ≤ L) (hR : R ≤ C * W * Y ^ A)
    (hZ : Z ≤ L) (hL : L = C * W * Y ^ A) :
    KL * (rb + Ks * (2 * S + (8 * dF + 1) * R) + 2 * R + 1 + Z + 1) ≤
      KL * (cG + Ks * (8 * dF + 3) * C + 3 * C + 2) * (W * Y ^ a) := by
  set U := W * Y ^ a with hU
  have hYa : Y ^ aG ≤ Y ^ a := Nat.pow_le_pow_right hY (by omega)
  have hYA : Y ^ A ≤ Y ^ a := Nat.pow_le_pow_right hY (by omega)
  have h1 : rb ≤ cG * U := by
    rw [hrB, hU, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hYa)
  have hCU : C * W * Y ^ A ≤ C * U := by
    rw [hU, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hYA)
  have hU1 : 1 ≤ U := Nat.mul_pos hW (Nat.one_le_pow _ _ hY)
  have h2 : 2 * S + (8 * dF + 1) * R ≤ (8 * dF + 3) * (C * U) := by
    have : (8 * dF + 1) * R ≤ (8 * dF + 1) * (C * U) := Nat.mul_le_mul_left _ (by omega)
    have e : (8 * dF + 3) * (C * U) = 2 * (C * U) + (8 * dF + 1) * (C * U) := by ring
    omega
  have h3 : Ks * (2 * S + (8 * dF + 1) * R) ≤ Ks * (8 * dF + 3) * C * U := by
    calc _ ≤ Ks * ((8 * dF + 3) * (C * U)) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have h4 : rb + Ks * (2 * S + (8 * dF + 1) * R) + 2 * R + 1 + Z + 1 ≤
      (cG + Ks * (8 * dF + 3) * C + 3 * C + 2) * U := by
    have e : (cG + Ks * (8 * dF + 3) * C + 3 * C + 2) * U =
        cG * U + Ks * (8 * dF + 3) * C * U + 3 * (C * U) + 2 * U := by ring
    omega
  calc _ ≤ KL * ((cG + Ks * (8 * dF + 3) * C + 3 * C + 2) * U) := Nat.mul_le_mul_left _ h4
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **Halting within the time bound.** -/
theorem resolve_time {Gp sw P0 : Program} {sI D Ks KL cG aG C A : ℕ}
    (hsw : Sw5Spec sw Ks D pSh pFt pCo pCa pSt) (hP0 : LoopSpec P0 Gp sw KL) (hD : sI + 4 ≤ D)
    {P Q : ℕ} {s : Bool} (hk : 1 ≤ k₀)
    (hgl : RGlueAt G k₀ q₀ Gp sI (2 * D + 20) eSh eFt eCo eCa eSt cG aG P Q s)
    (hcb : CallBounds G k₀ q₀ P Q s C A) {w : ℕ}
    (hadm : WordAdmissible eRes (cRes k₀ q₀ Ks KL D C cG) w (xIn G k₀ q₀ P Q s))
    (hT : rBound G k₀ q₀ P Q s (cRes k₀ q₀ Ks KL D C cG) (aRes A aG) ≤ 2 ^ w) :
    ∃ t ≤ rBound G k₀ q₀ P Q s (cRes k₀ q₀ Ks KL D C cG) (aRes A aG),
      RunsTo w P0 (xIn G k₀ q₀ P Q s) (zOut G k₀ q₀ P Q s) t := by
  obtain ⟨hcalls, htime, hlen, hzlen, hent, hzent⟩ := hcb
  set x := xIn G k₀ q₀ P Q s with hxd
  set z := zOut G k₀ q₀ P Q s with hzd
  set cs := rcalls G P Q s k₀ q₀ with hcsd
  set R := cs.length with hRd
  set X := ySz x with hXd
  set H := resolveBy G s P Q with hHd
  set T := treeCount G H k₀ q₀ with hTd
  set M := maxTreeSize G k₀ q₀ with hMd
  set Y := M + T + 1 with hYd
  set L := polyB G k₀ q₀ P Q s C A with hLd
  set c := cRes k₀ q₀ Ks KL D C cG with hcd
  have hX1 : 1 ≤ X := by simp only [hXd, ySz]; omega
  have hY1 : 1 ≤ Y := by omega
  have hN : n + 1 ≤ X := n_lt_ySz G k₀ q₀ P Q s
  have hHs : n + 1 ≤ X ^ 2 := le_trans hN (Nat.le_self_pow (by norm_num) _)
  have hL : L = C * ((n + 1) * (n + 1)) * Y ^ A := by
    simp only [hLd, polyB]; ring
  -- the polynomial bounds
  set P1 := X ^ 3 * Y ^ (A + aG) with hP1
  have hP1p : 1 ≤ P1 := Nat.mul_pos (Nat.one_le_pow _ _ hX1) (Nat.one_le_pow _ _ hY1)
  have hX3 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) _
  have hYA : Y ^ A ≤ Y ^ (A + aG) := Nat.pow_le_pow_right hY1 (by omega)
  have hYa : Y ^ aG ≤ Y ^ (A + aG) := Nat.pow_le_pow_right hY1 (by omega)
  have hXP : X ≤ P1 := le_trans hX3 (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hY1))
  have hLP : L ≤ C * P1 := by
    rw [hL, hP1, mul_assoc]
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ hYA)
    calc (n + 1) * (n + 1) ≤ X ^ 2 * X := Nat.mul_le_mul hHs hN
      _ = X ^ 3 := by ring
  set Qb := (C + 1) * (L + X) + 2 with hQb
  have pQ : Qb ≤ ((C + 1) ^ 2 + 2) * P1 := by
    have h1 : (C + 1) * (L + X) ≤ (C + 1) * ((C + 1) * P1) :=
      Nat.mul_le_mul_left _ (by rw [add_mul, one_mul]; omega)
    have e : ((C + 1) ^ 2 + 2) * P1 = (C + 1) * ((C + 1) * P1) + 2 * P1 := by ring
    omega
  set Hb := cG * (X + (n + 1) * Y ^ aG) with hHb
  have pH : Hb ≤ 2 * cG * P1 := by
    have a2 : (n + 1) * Y ^ aG ≤ P1 := Nat.mul_le_mul (le_trans hN hX3) hYa
    calc Hb ≤ cG * (2 * P1) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  set S := 8 * (Hb + Qb) + 16 with hS
  have pS : S ≤ kS C cG * P1 := by
    have e : kS C cG * P1 = 8 * (2 * cG * P1 + ((C + 1) ^ 2 + 2) * P1) + 16 * P1 := by
      unfold kS; ring
    omega
  set Bnd := cG * S ^ eGl + S + 2 * L + 11 * dFix + 2 + bigAll k₀ q₀ Ks with hBnd
  have pB : Bnd ≤ kB k₀ q₀ Ks C cG * P1 ^ (eGl + 1) := by
    have hPP : P1 ≤ P1 ^ (eGl + 1) := Nat.le_self_pow (by omega) _
    have hPe : P1 ^ eGl ≤ P1 ^ (eGl + 1) := Nat.pow_le_pow_right hP1p (by omega)
    have h1P : 1 ≤ P1 ^ (eGl + 1) := Nat.one_le_pow _ _ hP1p
    have q1 : cG * S ^ eGl ≤ cG * kS C cG ^ eGl * P1 ^ (eGl + 1) := by
      calc cG * S ^ eGl ≤ cG * (kS C cG * P1) ^ eGl := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pS _)
        _ = cG * kS C cG ^ eGl * P1 ^ eGl := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hPe
    have q2 : S ≤ kS C cG * P1 ^ (eGl + 1) := le_trans pS (Nat.mul_le_mul_left _ hPP)
    have q3 : 2 * L ≤ 2 * C * P1 ^ (eGl + 1) := by
      calc 2 * L ≤ 2 * (C * P1) := by omega
        _ ≤ 2 * (C * P1 ^ (eGl + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hPP)
        _ = _ := by ring
    have q4 : 11 * dFix + 2 + bigAll k₀ q₀ Ks ≤ (11 * dFix + 2 + bigAll k₀ q₀ Ks) * P1 ^ (eGl + 1) :=
      Nat.le_mul_of_pos_right _ h1P
    have e : kB k₀ q₀ Ks C cG * P1 ^ (eGl + 1) = cG * kS C cG ^ eGl * P1 ^ (eGl + 1) +
        kS C cG * P1 ^ (eGl + 1) + 2 * C * P1 ^ (eGl + 1) +
        (11 * dFix + 2 + bigAll k₀ q₀ Ks) * P1 ^ (eGl + 1) := by unfold kB; ring
    omega
  have hR : R ≤ C * X * Y ^ A := by
    have h := hcalls
    have : (T + 1) ^ A ≤ Y ^ A := Nat.pow_le_pow_left (by omega) _
    calc R ≤ C * (n + 1) * (T + 1) ^ A := h
      _ ≤ C * X * Y ^ A := by gcongr
  have pR : 2 * R + 3 ≤ (2 * C + 3) * P1 := by
    have h1 : C * X * Y ^ A ≤ C * P1 := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hX3 hYA)
    have e : (2 * C + 3) * P1 = 2 * (C * P1) + 3 * P1 := by ring
    omega
  set Z := Bnd * 2 ^ (2 * D + 20) * (2 * R + 3) ^ 2 * 8 with hZ
  have pZ : PB X Y (kZ k₀ q₀ Ks D C cG) (3 * (eGl + 3)) (bZ A aG) Z := by
    unfold PB
    have e1 : X ^ (3 * (eGl + 3)) * Y ^ bZ A aG = P1 ^ (eGl + 3) := by
      rw [hP1, mul_pow, ← pow_mul, ← pow_mul]; unfold bZ; ring_nf
    rw [mul_assoc, e1]
    calc Z ≤ (kB k₀ q₀ Ks C cG * P1 ^ (eGl + 1)) * 2 ^ (2 * D + 20) * ((2 * C + 3) * P1) ^ 2 * 8 := by
          rw [hZ]; gcongr
      _ = kZ k₀ q₀ Ks D C cG * P1 ^ (eGl + 3) := by
          unfold kZ
          rw [show 2 ^ (2 * D + 23) = 2 ^ (2 * D + 20) * 8 by
            rw [show 2 * D + 23 = (2 * D + 20) + 3 by omega, pow_add]; norm_num]
          ring
  -- the room
  have hcZ : kZ k₀ q₀ Ks D C cG ≤ c := by simp only [hcd, cRes]; omega
  have hTb : rBound G k₀ q₀ P Q s c (aRes A aG) = c * ((n + 1) * (n + 1) * Y ^ aRes A aG) := by
    simp only [rBound]; ring
  have hZw : Z ≤ 2 ^ w := by
    refine le_of_sq_le pZ hcZ ?_ ?_
    · have := adm_X G k₀ q₀ hadm
      rwa [show 2 * (3 * (eGl + 3)) = eRes by unfold eRes; ring]
    · refine le_trans ?_ hT
      rw [hTb]
      refine Nat.mul_le_mul_left _ ?_
      have : Y ^ (2 * bZ A aG) ≤ Y ^ aRes A aG := Nat.pow_le_pow_right hY1 (by unfold aRes; omega)
      exact le_trans this (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
  have hBnd1 : 1 ≤ Bnd := by omega
  obtain ⟨hreg, hsz, hw, hBw⟩ := regions_of hBnd1 hZw
  have hxw : x.length < 2 ^ (w - 1) := by
    have h1 := length_lt_ySz x
    have h2 : 2 ^ (w - 3) ≤ 2 ^ (w - 1) := two_pow_mono (by omega)
    have h3 : Bnd ≤ Bnd * 2 ^ (2 * D + 20) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have h4 : X ≤ Qb := by
      have : L + X ≤ (C + 1) * (L + X) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  -- the bounds of the rounds
  have hQ : ∀ c' ∈ cs, ySz (rQ G k₀ q₀ c') + ySz (rY G k₀ q₀ c') ≤ Qb := by
    intro c' hc'
    have h1 := hlen c' hc'
    have h2 := hent c' hc'
    have h3 : C * ((rQ G k₀ q₀ c').length + (rY G k₀ q₀ c').length + X) ≤ C * (L + X) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (C + 1) * (L + X) = C * (L + X) + (L + X) := by ring
    unfold ySz; omega
  have hz : ySz z ≤ Qb := by
    have h1 := hzlen
    have h2 := hzent
    have h3 : C * (z.length + X) ≤ C * (L + X) := Nat.mul_le_mul_left _ (by omega)
    have h4 : (C + 1) * (L + X) = C * (L + X) + (L + X) := by ring
    unfold ySz; omega
  have hx : X ≤ Qb := by
    have : L + X ≤ (C + 1) * (L + X) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hB2 : ∀ c' ∈ cs, 2 * realT G k₀ q₀ c' + 10 * dFix + 2 ≤ Bnd := by
    intro c' hc'
    have h1 : realT G k₀ q₀ c' ≤ (cs.map (realT G k₀ q₀)).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hc')
    have h2 := htime
    omega
  obtain ⟨t, ht, hr⟩ := resolve_run G k₀ q₀ hsw hP0 hD hk hgl hQ hz hx (Bnd := Bnd)
    (show cG * S ^ eGl + S ≤ Bnd by omega) hB2 (show bigAll k₀ q₀ Ks + dFix ≤ Bnd by omega)
    hreg hw hxw hsz
  refine ⟨t, le_trans ht ?_, hr⟩
  rw [sum_swT, hTb]
  have hfin := final_time (KL := KL) (Ks := Ks) (cG := cG) (C := C) (dF := dFix)
    (rb := rBound G k₀ q₀ P Q s cG aG) (S := (cs.map (realT G k₀ q₀)).sum) (R := R) (Z := z.length)
    (L := L) (W := (n + 1) * (n + 1)) (Y := Y) (aG := aG) (A := A) (a := aRes A aG) hY1
    (Nat.mul_pos (by omega) (by omega)) (by unfold aRes; omega)
    (by simp only [rBound, hYd, hTd, hMd, hHd]; ring) htime (le_trans hcalls ?_) hzlen hL
  · refine le_trans hfin ?_
    calc _ = (KL * (cG + Ks * (8 * dFix + 3) * C + 3 * C + 2)) *
          ((n + 1) * (n + 1) * Y ^ aRes A aG) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by simp only [hcd, cRes]; omega)
  · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega)))
      (Nat.pow_le_pow_left (by omega) _)

end Lax185574Proofs.ResolveRam
