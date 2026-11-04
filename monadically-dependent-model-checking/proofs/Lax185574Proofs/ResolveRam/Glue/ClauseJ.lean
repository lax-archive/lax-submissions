import Lax185574Proofs.ResolveRam.Glue.RoundJ
import Lax185574Proofs.ResolveRam.Glue.Clause0

/-!
The clause of `RGlueAt.rounds` for a later round that issues a call.

Round `j + 1` reads the answer of call `j` at the position `c = cur j`
and issues the call at `c' = next c`. If the case of the round meets
`BodyCall` for the library `L` and the plan `ps` whose ranges are the
state at `c'`, and the library is at most a constant `cS` times the
sizes of the input and the output of the round, then the guarded glue
program meets the clause of round `j + 1` (`clauseJ_call`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The clause of `RGlueAt.rounds` at round `j`, with time `tj`. -/
def ClauseAt (Gp : Program) (sI sQ eS eF eC eK eT cG E tj j : ℕ) : Prop :=
  ∀ v, sI ≤ v →
    (∀ e ∈ gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) j,
      e < 2 ^ (v - sI)) →
    (∀ o t, RunsTo v Gp (gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀)
        (zOut G k₀ q₀ P Q s) j) o t →
      o = gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) j ∧
      (∀ e ∈ o, e < 2 ^ (v - sI - 4)) ∧
      ∀ c, (rcalls G P Q s k₀ q₀)[j]? = some c →
        RGuard G k₀ q₀ eS eF eC eK eT (ySz (xIn G k₀ q₀ P Q s)) v sQ c) ∧
    (cG * (ySz (gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀)
        (zOut G k₀ q₀ P Q s) j) +
      ySz (gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) j) +
      ySz (xIn G k₀ q₀ P Q s)) ^ E ≤ 2 ^ (v - sQ) →
      ∃ t ≤ tj, RunsTo v Gp (gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀)
        (zOut G k₀ q₀ P Q s) j)
        (gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) j) t)

theorem hdC_eq {c' : Cur} {L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hc : callOf G P Q s k₀ q₀ c' ≠ .stp) (hpl : planW L ps = (swAt G P Q s k₀ q₀ c').ws) :
    hdC (tagOf G P Q s k₀ q₀ c') (winOf G P Q s k₀ q₀ c') (scW G P Q s k₀ q₀ c') L ps ++
        kW (kindOf (callOf G P Q s k₀ q₀ c')) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')) =
      hdOf G P Q s k₀ q₀ c' ++ rQ G k₀ q₀ (callOf G P Q s k₀ q₀ c') := by
  rw [rQ_kind G k₀ q₀ _ hc]
  simp only [hdC, hdOf, stOf, hpl, List.cons_append, List.length_append]
  congr 2
  simp [scW, curW]
  cases c' <;> simp

theorem kE_kind {eS eF eC eK eT : ℕ} {c : RCall} (hc : c ≠ .stp) :
    kE eS eF eC eK (kindOf c) = eOf eS eF eC eK eT c := by
  cases c <;> first | exact absurd rfl hc | rfl

theorem kD_kind {eS eF eC eK eT a : ℕ} {c : RCall} (hc : c ≠ .stp) :
    kD (a + eS + 1) (a + eF + 1) (a + eC + 1) (a + eK + 1) (kindOf c) = a + eOf eS eF eC eK eT c + 1 := by
  cases c <;> first | exact absurd rfl hc | rfl

theorem next_ne_stp (c : Cur) : next G P Q s k₀ q₀ c ≠ .stp := by
  cases c <;> simp only [next] <;> (try split_ifs) <;> simp

theorem cur_succ_ne_stp (j : ℕ) : cur G P Q s k₀ q₀ (j + 1) ≠ .stp := by
  rw [cur_succ]; exact next_ne_stp G P Q s k₀ q₀ _

theorem callOf_ne_stp {c : Cur} (hv : Valid G P Q s k₀ q₀ c) (hc : c ≠ .stp) :
    callOf G P Q s k₀ q₀ c ≠ .stp := by
  cases c with
  | stp => exact absurd rfl hc
  | fin => exact hv.elim
  | dn d i m =>
    obtain ⟨-, hi, hm⟩ := hv
    rw [callOf_dn' hi hm]; split_ifs <;> simp
  | up d i m =>
    obtain ⟨-, hi, hm⟩ := hv
    rw [callOf_up' hi hm]; split_ifs <;> simp

theorem scW_ph {c : Cur} (h : c ≠ .fin) : (scW G P Q s k₀ q₀ c).getD 9 0 ≠ 3 := by
  cases c <;> simp [scW, curW] at h ⊢

theorem kindOf_le {c : RCall} (h : c ≠ .stp) : kindOf c ≤ 3 := by
  cases c <;> simp [kindOf] at h ⊢

theorem length_scW (c : Cur) : (scW G P Q s k₀ q₀ c).length = 17 := by
  cases c <;> simp [scW, curW]

theorem winOf_le (c : Cur) : winOf G P Q s k₀ q₀ c ≤ (xIn G k₀ q₀ P Q s).length := by
  unfold winOf; split_ifs <;> omega

/-- The time bound of a later round with a call. -/
noncomputable def tJ (Lay : Layout) (K KB : ℕ) (wx st b : List ℕ) (k₀ q₀ : ℕ) (ws L : List (List ℕ))
    (ps : List (ℕ × ℕ)) (o : List ℕ) (e d : ℕ) : ℕ :=
  Lay.const * (30 * K + 50 + preK wx st b k₀ q₀ 0 ws + 4 + KB + 4 + 10 + tailK L ps o b e d) + 5

/-- **The time bound of a later round with a call is linear in the word
lengths.** The constant term depends only on `K`, the exponents and the
rank `(k₀, q₀)`. -/
theorem tJ_le (Lay : Layout) (K KB : ℕ) (wx st b : List ℕ) (k₀ q₀ : ℕ) (ws L : List (List ℕ))
    (ps : List (ℕ × ℕ)) (o : List ℕ) (e d : ℕ) (hps : ps.length ≤ 12) :
    tJ Lay K KB wx st b k₀ q₀ ws L ps o e d ≤
      Lay.const * (1000 * (wx.length + st.length + b.length + total ws + total L + L.length + o.length +
        KB + 1) + (30 * K + 23 * ((k₀ + q₀ + 1) * (q₀ + 1)) + 60 * (e + 1) + 30 * 2 ^ d +
        1000 * qLen + 20000)) + 5 := by
  unfold tJ
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 5
  unfold preK tailK
  omega

set_option maxHeartbeats 1600000 in
/-- **The clause of a later round with a call.** -/
theorem clauseJ_call {Lay : Layout} {eS eF eC eK eT sQ K cG E cS KB j : ℕ} (body fE : Com)
    {L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hok : Com.Ok Lay (glueTop K eT (sQ - guardBits Lay + eT + 1) (roundJ body fE eS eF eC eK
      (sQ - guardBits Lay + eS + 1) (sQ - guardBits Lay + eF + 1) (sQ - guardBits Lay + eC + 1)
      (sQ - guardBits Lay + eK + 1))))
    (hW : "W" ∈ Lay.scalars) (hO : "ovf" ∈ Lay.scalars) (hK : kq0 ≤ K) (hrs : guardBits Lay + 11 ≤ sQ)
    (hn : 1 ≤ n) (hj : j + 1 < (rcalls G P Q s k₀ q₀).length)
    (hbody : ∀ W, BodyCall body W (Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s))
      (scW G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) L ps
      (kindOf (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))))
      (tagOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))) (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1)))
      (scW G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))) KB)
    (hpl : planW L ps = (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))).ws)
    (hsub : (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws.Sublist L)
    (hsz : sBig L (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) (xIn G k₀ q₀ P Q s).length
        (maxEntry ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))) ≤
      cS * (ySz (gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀)
        (zOut G k₀ q₀ P Q s) (j + 1)) +
        ySz (gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) (j + 1)) +
        ySz (xIn G k₀ q₀ P Q s)))
    (hcG1 : 2 * 2 ^ (eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))) + 1) + K + 1 ≤ cG)
    (hcG2 : 2 ^ 24 * (Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * cS ^ 2 ≤ cG)
    (hE1 : eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))) + 1 ≤ E) (hE2 : 2 ≤ E) :
    ClauseAt G P Q s k₀ q₀ (guardedProgram Lay (glueTop K eT (sQ - guardBits Lay + eT + 1)
      (roundJ body fE eS eF eC eK (sQ - guardBits Lay + eS + 1) (sQ - guardBits Lay + eF + 1)
        (sQ - guardBits Lay + eC + 1) (sQ - guardBits Lay + eK + 1))))
      (guardBits Lay + 6) sQ eS eF eC eK eT cG E
      (tJ Lay K KB ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        k₀ q₀ (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws L ps
        (hdOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1)) ++
          rQ G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))))
        (eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))))
        (sQ - guardBits Lay + eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))) + 1))
      (j + 1) := by
  intro v hv hu
  set r := guardBits Lay with hr
  set W := Words.guardW Lay v
  set c := cur G P Q s k₀ q₀ j
  set c' := cur G P Q s k₀ q₀ (j + 1)
  set x := xIn G k₀ q₀ P Q s
  set cl' := callOf G P Q s k₀ q₀ c'
  set e' := eOf eS eF eC eK eT cl'
  have hW1 : W + 1 = 2 ^ (v - r) := Words.guardW_succ Lay v
  have hsp : 2 ^ (v - r) = 2 ^ (v - (r + 6)) * 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; omega
  have hc := (rcalls_get G P Q s k₀ q₀ hn (j := j) (by omega)).2
  obtain ⟨hv', hc'⟩ := rcalls_get G P Q s k₀ q₀ hn (j := j + 1) hj
  have hne : cl' ≠ .stp := callOf_ne_stp G P Q s k₀ q₀ hv' (cur_succ_ne_stp G P Q s k₀ q₀ j)
  have hgu := gU_succ G P Q s k₀ q₀ (zOut G k₀ q₀ P Q s) hc
  have hgo : gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) (j + 1) =
      hdOf G P Q s k₀ q₀ c' ++ rQ G k₀ q₀ cl' := by simp [gOut, hc', hdJ, c', cl']
  rw [hgu] at hu ⊢
  rw [hgo] at hsz ⊢
  rw [hgu] at hsz
  have hst : stOf G P Q s k₀ q₀ c = scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws := rfl
  rw [hst] at hu hsz ⊢
  have hu64 : ∀ e ∈ [tagOf G P Q s k₀ q₀ c, (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws).length] ++
      x.take (winOf G P Q s k₀ q₀ c) ++ (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws) ++
      ((rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)).length :: rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)), 64 * e < W + 1 := by
    intro e he; have := hu e he; rw [hW1, hsp]; omega
  have h7 : (scW G P Q s k₀ q₀ c).getD 7 0 = k₀ := by simp [scW]
  have h8 : (scW G P Q s k₀ q₀ c).getD 8 0 = q₀ := by simp [scW]
  have h2 : (scW G P Q s k₀ q₀ c).getD 2 0 = x.length := by simp [scW, x]
  have hwl : (x.take (winOf G P Q s k₀ q₀ c)).length = tagOf G P Q s k₀ q₀ c - 1 := by
    rw [List.length_take, min_eq_left (winOf_le G P Q s k₀ q₀ c)]; simp [tagOf]
  obtain ⟨σ', k', r', hk', hsnd, hcmp⟩ := roundJ_run (K := K) (e := eT) (d := sQ - r + eT + 1) (W := W)
    (eS := eS) (eF := eF) (eC := eC) (eK := eK) (dS := sQ - r + eS + 1) (dF := sQ - r + eF + 1)
    (dC := sQ - r + eC + 1) (dK := sQ - r + eK + 1) body fE (by simp [tagOf]) hwl
    (length_scW G P Q s k₀ q₀ c) (by simp [SW.ws]) (by simp [scW]) hK
    (by rw [h7, h8]) hu64 (hbody W) (scW_ph G P Q s k₀ q₀ (fun h => by
      have := hv'; rw [show cur G P Q s k₀ q₀ (j + 1) = c' from rfl, h] at this; exact this)) hsub
  rw [hdC_eq G P Q s k₀ q₀ hne hpl, kE_kind (eT := eT) hne, kD_kind (eT := eT) hne] at hk' hsnd hcmp
  rw [h2] at hcmp
  have he' : eOf eS eF eC eK eT cl' = e' := rfl
  rw [he'] at hk' hsnd hcmp
  set u := [tagOf G P Q s k₀ q₀ c, (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws).length] ++
      x.take (winOf G P Q s k₀ q₀ c) ++ (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws) ++
      ((rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)).length :: rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) with hu_def
  set o := hdOf G P Q s k₀ q₀ c' ++ rQ G k₀ q₀ cl'
  have huW : ∀ e ∈ u, e ≤ W := fun e he => by have := hu64 e he; omega
  -- the real query is a segment of the output
  have hqo : (realQ G k₀ q₀ cl').length ≤ o.length ∧ maxEntry (realQ G k₀ q₀ cl') ≤ maxEntry o := by
    obtain ⟨pre, post, hsp', -, -⟩ := kW_split (kindOf cl') (realQ G k₀ q₀ cl') (kindOf_le hne)
    have ho : o = (hdOf G P Q s k₀ q₀ c' ++ pre) ++ realQ G k₀ q₀ cl' ++ post := by
      simp only [o]; rw [rQ_kind G k₀ q₀ _ hne, hsp']; simp
    rw [ho]
    exact ⟨by simp only [List.length_append]; omega, maxEntry_le fun v hv => le_maxEntry (by simp [hv])⟩
  refine ⟨fun o' t ht => ?_, fun hY => ?_⟩
  · have := round_sound' (L := Lay) (cmd := glueTop K eT (sQ - r + eT + 1) (roundJ body fE eS eF eC eK
        (sQ - r + eS + 1) (sQ - r + eF + 1) (sQ - r + eC + 1) (sQ - r + eK + 1))) (v := v) (sQ := sQ) (K := K) (e := e') (X := ySz x) (call := true) (o := o) (q := realQ G k₀ q₀ cl')
      hok hW hO (by rw [← hr]; omega) (by rw [← hr]; omega) huW ⟨extJ W, σ', k', r', fun h0 => by
        obtain ⟨ho, hKW, hg, he⟩ := hsnd h0
        exact ⟨ho, hKW, fun _ => hg, he⟩⟩ o' t ht
    obtain ⟨h1, h2', h3⟩ := this
    refine ⟨h1, by rw [h1]; exact h2', fun c0 hc0 => ?_⟩
    rw [hc'] at hc0; cases hc0
    exact h3 rfl
  · set Y := ySz u + ySz o + ySz x
    have hY1 : 1 ≤ Y := by show 1 ≤ ySz u + ySz o + ySz x; unfold ySz; omega
    have hle : o.length + maxEntry o + ySz x + 2 ≤ Y := by
      show _ ≤ ySz u + ySz o + ySz x; unfold ySz; omega
    have hvsq : sQ ≤ v := by
      by_contra hh
      have h1 : 2 ^ (v - sQ) = 1 := by rw [show v - sQ = 0 by omega]; rfl
      have h2 : 1 ≤ Y ^ E := Nat.one_le_pow _ _ hY1
      have := Nat.mul_le_mul hcG1 h2
      have := Nat.one_le_two_pow (n := e' + 1)
      have hY' : cG * Y ^ E ≤ 2 ^ (v - sQ) := hY
      omega
    have hvs : 2 ^ (v - sQ) * 2 ^ 11 ≤ W + 1 := by
      rw [hW1, ← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have hgood := rgood_of (L := Lay) (v := v) (K := K) (e := e') (X := ySz x) (call := true)
      (q := realQ G k₀ q₀ cl') (o := o) hrs (fun _ => hqo)
      (calc (2 * 2 ^ (e' + 1) + K + 1) * (o.length + maxEntry o + ySz x + 2) ^ (e' + 1)
          ≤ cG * Y ^ (e' + 1) := Nat.mul_le_mul hcG1 (Nat.pow_le_pow_left hle _)
        _ ≤ cG * Y ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 hE1)
        _ ≤ 2 ^ (v - sQ) := hY)
    obtain ⟨hKW, hg, he⟩ := hgood
    have hbig : BigRoom W (Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2) L (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c))
        x.length (maxEntry (x.take (winOf G P Q s k₀ q₀ c))) := by
      unfold BigRoom
      set S := sBig L (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) x.length (maxEntry (x.take (winOf G P Q s k₀ q₀ c)))
      set R := Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2
      have hS : S ≤ cS * Y := hsz
      have h1 : 2 ^ 24 * R * R * R * R * S * S ≤ cG * Y ^ 2 := by
        calc 2 ^ 24 * R * R * R * R * S * S = 2 ^ 24 * R ^ 4 * (S * S) := by ring
          _ ≤ 2 ^ 24 * R ^ 4 * ((cS * Y) * (cS * Y)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hS hS)
          _ = (2 ^ 24 * R ^ 4 * cS ^ 2) * Y ^ 2 := by ring
          _ ≤ cG * Y ^ 2 := Nat.mul_le_mul_right _ hcG2
      have h2 : cG * Y ^ 2 ≤ cG * Y ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 hE2)
      have h3 : 2 ^ (v - sQ) < W := by
        have : 1 ≤ 2 ^ (v - sQ) := Nat.one_le_two_pow
        omega
      omega
    have h0 := hcmp hKW hbig (hg rfl) he
    obtain ⟨ho, -, -, -⟩ := hsnd h0
    refine round_halts' hok hW hO (by omega) huW ⟨extJ W, σ', k', r', ho, h0, ?_⟩
    unfold tJ
    have : preK (x.take (winOf G P Q s k₀ q₀ c)) (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws)
        (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) k₀ q₀ W (swAt G P Q s k₀ q₀ c).ws =
      preK (x.take (winOf G P Q s k₀ q₀ c)) (scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws)
        (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) k₀ q₀ 0 (swAt G P Q s k₀ q₀ c).ws := rfl
    rw [h7, h8, this] at hk'
    have := Nat.mul_le_mul_left Lay.const hk'
    omega

end Lax185574Proofs.ResolveRam.Glue
