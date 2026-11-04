import Lax185574Proofs.ResolveRam.Glue.CFERound

/-!
The clause of `RGlueAt.rounds` for the last round.

Round `j + 1 = R` reads the answer of the last call at `cur j` and
writes `0` followed by the output of lem:resolve-lift. If the case of
the round only sets the new phase to `3` (`BodyFin`), then the guarded
glue program with the end command `fECmd` meets the clause of round `R`
(`clauseFin`), within the time `tFin`. The library of the round is the
state at `cur j`, so it is at most `72` times the size of the input of
the round (`fe_sbig`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam

/-- The size of the room checks of a round whose library is its state. -/
theorem fe_sbig (t : ℕ) (sc wx b : List ℕ) (ws : List (List ℕ)) (nx : ℕ) :
    sBig ws b nx (maxEntry wx) ≤
      72 * (ySz ([t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++ (b.length :: b)) + nx) := by
  set u := [t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++ (b.length :: b)
  have hl := length_toWord_words ws
  have hul : (toWord ws).length + b.length ≤ u.length := by simp [u]; omega
  have hm1 : maxEntry wx ≤ maxEntry u := maxEntry_le fun v hv => le_maxEntry (by simp [u, hv])
  have hm2 : maxEntry b ≤ maxEntry u := maxEntry_le fun v hv => le_maxEntry (by simp [u, hv])
  have hm3 : maxEntry ws.flatten ≤ maxEntry u := maxEntry_le fun v hv => le_maxEntry (by
    obtain ⟨w, hw, hvw⟩ := List.mem_flatten.1 hv
    have : v ∈ toWord ws := by
      rw [toWord_words]
      exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨w.length :: w, List.mem_map.2 ⟨w, hw, rfl⟩,
        List.mem_cons_of_mem _ hvw⟩)
    simp [u, this])
  unfold sBig sOf ySz
  have : max (max (maxEntry wx) (maxEntry ws.flatten)) (maxEntry b) ≤ maxEntry u := by omega
  omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The time bound of the last round. -/
noncomputable def tFin (Lay : Layout) (K KB : ℕ) (wx st b : List ℕ) (k₀ q₀ : ℕ) (ws : List (List ℕ))
    (KF : ℕ) : ℕ :=
  Lay.const * (30 * K + 50 + preK wx st b k₀ q₀ 0 ws + KB + KF + 30) + 5

set_option maxHeartbeats 1600000 in
/-- **The clause of the last round.** -/
theorem clauseFin {Lay : Layout} {eS eF eC eK eT sQ K cG E KB j : ℕ} (body : Com)
    (hok : Com.Ok Lay (glueTop K eT (sQ - guardBits Lay + eT + 1) (roundJ body fECmd eS eF eC eK
      (sQ - guardBits Lay + eS + 1) (sQ - guardBits Lay + eF + 1) (sQ - guardBits Lay + eC + 1)
      (sQ - guardBits Lay + eK + 1))))
    (hW : "W" ∈ Lay.scalars) (hO : "ovf" ∈ Lay.scalars) (hK : kq0 ≤ K) (hrs : guardBits Lay + 11 ≤ sQ)
    (hk : 1 ≤ k₀) (hn : 1 ≤ n) (hj : j + 1 = (rcalls G P Q s k₀ q₀).length)
    (hbody : ∀ W, BodyFin body W (Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2)
      (scW G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) KB)
    (hcG1 : K + 5 ≤ cG) (hcG2 : 2 ^ 24 * (Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * 72 ^ 2 ≤ cG)
    (hE2 : 2 ≤ E) :
    ClauseAt G P Q s k₀ q₀ (guardedProgram Lay (glueTop K eT (sQ - guardBits Lay + eT + 1)
      (roundJ body fECmd eS eF eC eK (sQ - guardBits Lay + eS + 1) (sQ - guardBits Lay + eF + 1)
        (sQ - guardBits Lay + eC + 1) (sQ - guardBits Lay + eK + 1))))
      (guardBits Lay + 6) sQ eS eF eC eK eT cG E
      (tFin Lay K KB ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        k₀ q₀ (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
        (feK n (xIn G k₀ q₀ P Q s).length (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) (0 :: zOut G k₀ q₀ P Q s)))
      (j + 1) := by
  intro v hv hu
  set r := guardBits Lay with hr
  set W := Words.guardW Lay v
  set c := cur G P Q s k₀ q₀ j
  set x := xIn G k₀ q₀ P Q s
  have hW1 : W + 1 = 2 ^ (v - r) := Words.guardW_succ Lay v
  have hsp : 2 ^ (v - r) = 2 ^ (v - (r + 6)) * 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; omega
  have hW63 : 63 ≤ W := by
    have : 1 ≤ 2 ^ (v - (r + 6)) := Nat.one_le_two_pow
    omega
  obtain ⟨-, -, hc⟩ := fe_cur G P Q s k₀ q₀ hn hj
  have hnone : (rcalls G P Q s k₀ q₀)[j + 1]? = none := List.getElem?_eq_none (by omega)
  have hgu := gU_succ G P Q s k₀ q₀ (zOut G k₀ q₀ P Q s) hc
  have hgo : gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) (j + 1) =
      0 :: zOut G k₀ q₀ P Q s := by simp [gOut, hnone]
  rw [hgu] at hu ⊢
  rw [hgo]
  have hst : stOf G P Q s k₀ q₀ c = scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws := rfl
  rw [hst] at hu ⊢
  have hu64 : ∀ e ∈ [tagOf G P Q s k₀ q₀ c, (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws).length] ++
      x.take (winOf G P Q s k₀ q₀ c) ++ (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws) ++
      ((rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)).length :: rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)), 64 * e < W + 1 := by
    intro e he; have := hu e he; rw [hW1, hsp]; omega
  have h7 : (scW G P Q s k₀ q₀ c).getD 7 0 = k₀ := by simp [scW]
  have h8 : (scW G P Q s k₀ q₀ c).getD 8 0 = q₀ := by simp [scW]
  have h2 : (scW G P Q s k₀ q₀ c).getD 2 0 = x.length := by simp [scW, x]
  have hwl : (x.take (winOf G P Q s k₀ q₀ c)).length = tagOf G P Q s k₀ q₀ c - 1 := by
    rw [List.length_take, min_eq_left (winOf_le G P Q s k₀ q₀ c)]; simp [tagOf]
  set o := 0 :: zOut G k₀ q₀ P Q s
  obtain ⟨σ', k', r', hk', hsnd, hcmp⟩ := roundJ_fin (K := K) (e := eT) (d := sQ - r + eT + 1) (W := W)
    (R := Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2) (o := o)
    (eS := eS) (eF := eF) (eC := eC) (eK := eK) (dS := sQ - r + eS + 1) (dF := sQ - r + eF + 1)
    (dC := sQ - r + eC + 1) (dK := sQ - r + eK + 1) body fECmd (by simp [tagOf]) hwl
    (length_scW G P Q s k₀ q₀ c) (by simp [SW.ws]) (by simp [scW]) hK
    (by rw [h7, h8]) hu64 (hbody W)
    (fun τ P0 hov => fECmd_run G P Q s k₀ q₀ hk hn hj (preR_nph P0 (by omega)) (by simp [hov]) (by omega))
  rw [h2] at hcmp
  set u := [tagOf G P Q s k₀ q₀ c, (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws).length] ++
      x.take (winOf G P Q s k₀ q₀ c) ++ (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws) ++
      ((rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)).length :: rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) with hu_def
  have huW : ∀ e ∈ u, e ≤ W := fun e he => by have := hu64 e he; omega
  refine ⟨fun o' t ht => ?_, fun hY => ?_⟩
  · have := round_sound' (L := Lay) (cmd := glueTop K eT (sQ - r + eT + 1) (roundJ body fECmd eS eF eC eK
        (sQ - r + eS + 1) (sQ - r + eF + 1) (sQ - r + eC + 1) (sQ - r + eK + 1))) (v := v) (sQ := sQ)
      (K := K) (e := 0) (X := ySz x) (call := false) (o := o) (q := [])
      hok hW hO (by rw [← hr]; omega) (by rw [← hr]; omega) huW ⟨extJ W, σ', k', r', fun h0 => by
        obtain ⟨ho, hKW, he⟩ := hsnd h0
        exact ⟨ho, hKW, fun h => absurd h (by decide), he⟩⟩ o' t ht
    obtain ⟨h1, h2', -⟩ := this
    refine ⟨h1, by rw [h1]; exact h2', fun c0 hc0 => ?_⟩
    rw [hnone] at hc0; cases hc0
  · set Y := ySz u + ySz o + ySz x
    have hY1 : 1 ≤ Y := by show 1 ≤ ySz u + ySz o + ySz x; unfold ySz; omega
    have hle : o.length + maxEntry o + ySz x + 2 ≤ Y := by
      show _ ≤ ySz u + ySz o + ySz x; unfold ySz; omega
    have hY' : cG * Y ^ E ≤ 2 ^ (v - sQ) := hY
    have hYE : Y ≤ Y ^ E := Nat.le_self_pow (by omega) Y
    have hgood := rgood_of (L := Lay) (v := v) (K := K) (e := 0) (X := ySz x) (call := false)
      (q := []) (o := o) hrs (fun h => absurd h (by decide))
      (calc (2 * 2 ^ (0 + 1) + K + 1) * (o.length + maxEntry o + ySz x + 2) ^ (0 + 1)
          ≤ cG * Y := by simp only [Nat.zero_add, pow_one]; exact Nat.mul_le_mul (by omega) hle
        _ ≤ cG * Y ^ E := Nat.mul_le_mul_left _ hYE
        _ ≤ 2 ^ (v - sQ) := hY')
    obtain ⟨hKW, -, he⟩ := hgood
    have hvsq : sQ ≤ v := by
      by_contra hh
      have h1 : 2 ^ (v - sQ) = 1 := by rw [show v - sQ = 0 by omega]; rfl
      have h2 : 1 ≤ Y ^ E := Nat.one_le_pow _ _ hY1
      have := Nat.mul_le_mul hcG1 h2
      omega
    have hvs : 2 ^ (v - sQ) * 2 ^ 11 ≤ W + 1 := by
      rw [hW1, ← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have hbig : BigRoom W (Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2) (swAt G P Q s k₀ q₀ c).ws
        (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) x.length (maxEntry (x.take (winOf G P Q s k₀ q₀ c))) := by
      unfold BigRoom
      set S := sBig (swAt G P Q s k₀ q₀ c).ws (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) x.length
        (maxEntry (x.take (winOf G P Q s k₀ q₀ c)))
      set R := Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2
      have hS : S ≤ 72 * Y := by
        have hsb := fe_sbig (tagOf G P Q s k₀ q₀ c) (scW G P Q s k₀ q₀ c) (x.take (winOf G P Q s k₀ q₀ c))
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) (swAt G P Q s k₀ q₀ c).ws x.length
        rw [← hu_def] at hsb
        have hx : x.length ≤ ySz x := by unfold ySz; omega
        have : ySz u + x.length ≤ Y := by show _ ≤ ySz u + ySz o + ySz x; omega
        omega
      have h1 : 2 ^ 24 * R * R * R * R * S * S ≤ cG * Y ^ 2 := by
        calc 2 ^ 24 * R * R * R * R * S * S = 2 ^ 24 * R ^ 4 * (S * S) := by ring
          _ ≤ 2 ^ 24 * R ^ 4 * ((72 * Y) * (72 * Y)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hS hS)
          _ = (2 ^ 24 * R ^ 4 * 72 ^ 2) * Y ^ 2 := by ring
          _ ≤ cG * Y ^ 2 := Nat.mul_le_mul_right _ hcG2
      have h2 : cG * Y ^ 2 ≤ cG * Y ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 hE2)
      have h3 : 2 ^ (v - sQ) < W := by
        have : 1 ≤ 2 ^ (v - sQ) := Nat.one_le_two_pow
        omega
      omega
    have h0 := hcmp hKW hbig he
    obtain ⟨ho, -, -⟩ := hsnd h0
    refine round_halts' hok hW hO (by omega) huW ⟨extJ W, σ', k', r', ho, h0, ?_⟩
    refine le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left Lay.const hk') 5) (le_of_eq ?_)
    rw [h7, h8]; rfl

end Lax185574Proofs.ResolveRam.Glue
