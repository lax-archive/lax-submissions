import Lax185574Proofs.ResolveRam.Glue.DispCall
import Lax185574Proofs.ResolveRam.Glue.OkDisp
import Lax185574Proofs.ResolveRam.Glue.CFECost
import Lax185574Proofs.ResolveRam.Glue.Clause0

/-!
The clauses of the rounds of the glue program with their times: the
first round (`round_zero`), a round in the middle (`round_mid`) and the
last round (`round_fin`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TypeTreeSizes Lax3.DistFO Lax808846Proofs.Compile Lax808846.Ram


/-- The glue program. -/
noncomputable def rgProg (K eS eF eC eK eT sQ : ℕ) : Program :=
  guardedProgram glueLay (glueTop K eT (sQ - guardBits glueLay + eT + 1)
    (roundJ (disp atCmd (bR1 atCmd)) fECmd eS eF eC eK (sQ - guardBits glueLay + eS + 1)
      (sQ - guardBits glueLay + eF + 1) (sQ - guardBits glueLay + eC + 1) (sQ - guardBits glueLay + eK + 1)))

theorem eOf_le_eSum (eS eF eC eK eT : ℕ) (c : RCall) : eOf eS eF eC eK eT c ≤ eS + eF + eC + eK + eT := by
  cases c <;> simp [eOf] <;> omega

/-- The constant part of the time of a round in the middle. -/
noncomputable def cstJ (K eSum sQ k₀ q₀ : ℕ) : ℕ :=
  30 * K + 23 * ((k₀ + q₀ + 1) * (q₀ + 1)) + 60 * (eSum + 1) + 30 * 2 ^ (sQ + eSum + 1) + 1000 * qLen + 20000

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- **The first round.** -/
theorem round_zero {K eS eF eC eK eT sQ cG E : ℕ} (hK : 4 * k0 + 64 ≤ K) (hrs : guardBits glueLay + 11 ≤ sQ)
    (hcG : 2 * 2 ^ (eT + 1) + K + 1 ≤ cG) (hE : eT + 1 ≤ E) :
    ClauseAt G P Q s k₀ q₀ (rgProg K eS eF eC eK eT sQ) (guardBits glueLay + 6) sQ eS eF eC eK eT cG E
      (t0 glueLay K eT (sQ - guardBits glueLay + eT + 1) ((xIn G k₀ q₀ P Q s).length + 1)) 0 :=
  fun v hv hu => clause0 G P Q s k₀ q₀ _ (glue_ok _ _ _ _ _ _ _ _ _ _ _) glueLay_W glueLay_ovf hK hrs hcG hE
    (hdJ G P Q s k₀ q₀) (fun _ => rfl) v hv hu

/-- **The last round.** -/
theorem round_fin {K eS eF eC eK eT sQ cG E j : ℕ} (hk : 1 ≤ k₀) (hKq : kq0 ≤ K)
    (hrs : guardBits glueLay + 11 ≤ sQ) (hn : 1 ≤ n) (hj : j + 1 = (rcalls G P Q s k₀ q₀).length)
    (hcG1 : K + 5 ≤ cG) (hcG2 : 2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * 72 ^ 2 ≤ cG) (hE2 : 2 ≤ E) :
    ClauseAt G P Q s k₀ q₀ (rgProg K eS eF eC eK eT sQ) (guardBits glueLay + 6) sQ eS eF eC eK eT cG E
      (tFin glueLay K 100 ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        k₀ q₀ (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
        (feK n (xIn G k₀ q₀ P Q s).length (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) (0 :: zOut G k₀ q₀ P Q s)))
      (j + 1) := by
  refine clauseFin G P Q s k₀ q₀ (Lay := glueLay) (disp atCmd (bR1 atCmd)) (glue_ok _ _ _ _ _ _ _ _ _ _ _)
    glueLay_W glueLay_ovf hKq hrs hk hn hj (fun W => ?_) hcG1 hcG2 hE2
  intro τ P0 hov hkq
  obtain ⟨hv, hf, -⟩ := fe_cur G P Q s k₀ q₀ hn hj
  obtain ⟨i, m, hcm, hi, hm⟩ := fe_last G P Q s k₀ q₀ hv hf
  rw [hcm] at P0
  obtain ⟨τ', K', r, hK', h3, hvv, ha, ho, hi'⟩ :=
    disp_end G P Q s k₀ q₀ (atC := atCmd) (bR1 := bR1 atCmd) hi hm P0 hkq
  rw [env_nph h3 hvv ha ho hi'] at r
  exact ⟨K', hK', r⟩

/-- **A round in the middle.** -/
theorem round_mid {C A : ℕ} (hK : SzKit G P Q s k₀ q₀ C A) (hk : 1 ≤ k₀)
    {K eS eF eC eK eT sQ cG E j : ℕ} (hKq : kq0 ≤ K)
    (hrs : guardBits glueLay + 11 ≤ sQ) (hn : 1 ≤ n) (hj1 : 1 ≤ j) (hj : j + 1 < (rcalls G P Q s k₀ q₀).length)
    (hcG1 : 2 * 2 ^ (eS + eF + eC + eK + eT + 1) + K + 1 ≤ cG)
    (hcG2 : 2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * 100 ^ 2 ≤ cG) (hE : E = eS + eF + eC + eK + eT + 2) :
    ∃ t, ClauseAt G P Q s k₀ q₀ (rgProg K eS eF eC eK eT sQ) (guardBits glueLay + 6) sQ eS eF eC eK eT cG E t
      (j + 1) ∧
      t ≤ glueLay.const * (1000 * (9000 * vU G P Q s k₀ q₀ atCmd_spec atKeep_atV C A) +
        cstJ K (eS + eF + eC + eK + eT) sQ k₀ q₀) + 5 := by
  set c := cur G P Q s k₀ q₀ j with hcdef
  obtain ⟨hv, hcj⟩ := rcalls_get G P Q s k₀ q₀ hn (j := j) (by omega)
  obtain ⟨hv1, hc1⟩ := rcalls_get G P Q s k₀ q₀ hn (j := j + 1) hj
  have ecs := cur_succ G P Q s k₀ q₀ j
  rw [← hcdef] at ecs
  have hc : c ≠ .stp := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact cur_succ_ne_stp G P Q s k₀ q₀ j'
  have hnf : next G P Q s k₀ q₀ c ≠ .fin := by
    intro h
    rw [← ecs] at h
    have := (cur_succ_fin G P Q s k₀ q₀ hn (j := j) (by omega)).1 h
    omega
  have hne := callOf_ne_stp G P Q s k₀ q₀ hv hc
  have hne1 := callOf_ne_stp G P Q s k₀ q₀ hv1 (cur_succ_ne_stp G P Q s k₀ q₀ j)
  set Y := yQ G P Q s k₀ q₀
  set Z := C * ((n + 1) * Y ^ A)
  have eZ : C * (n + 1) * Y ^ A = Z := by simp only [Z]; ring
  have hcall0 := hK.call _ (List.mem_iff_getElem?.2 ⟨_, hcj⟩) hne
  have hcall1 := hK.call _ (List.mem_iff_getElem?.2 ⟨_, hc1⟩) hne1
  have hst0 := hK.st c (Or.inr (Or.inr hv))
  have hst1 := hK.st _ (Or.inr (Or.inr hv1))
  rw [eZ] at hcall0 hcall1 hst0 hst1
  rw [ecs] at hcall1 hst1
  try rw [← hcdef] at hcall0
  try rw [← hcdef] at hcall1
  try rw [← hcdef] at hst1
  have hsl0 : (stOf G P Q s k₀ q₀ c).length = (scW G P Q s k₀ q₀ c).length + 1 +
      tot (swAt G P Q s k₀ q₀ c).ws := by
    simp only [stOf, List.length_append, length_toWord_ws]; omega
  have hsl1 : (stOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)).length =
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)).length + 1 + tot (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)).ws := by
    simp only [stOf, List.length_append, length_toWord_ws]; omega
  have hA : Atoms G P Q s k₀ q₀ c Z := ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨L, ps, KB, hD, hP, hLib, hKB⟩ :=
    disp_call G P Q s k₀ q₀ atCmd_spec atKeep_atV hK hk (bR1 := bR1 atCmd) hv hc hnf hA
  unfold DPlan at hP
  obtain ⟨hpl, hsub, hps⟩ := hP
  set eSum := eS + eF + eC + eK + eT
  have he := eOf_le_eSum eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1)))
  have hgo : gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) (j + 1) =
      oOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c) := by
    simp only [gOut, hc1, hdJ, oOf, ecs]
  have hgu := gU_succ G P Q s k₀ q₀ (zOut G k₀ q₀ P Q s) hcj
  have hsz := sBig_le (x := xIn G k₀ q₀ P Q s) (t := tagOf G P Q s k₀ q₀ c) (sc := scW G P Q s k₀ q₀ c)
    (k := winOf G P Q s k₀ q₀ c) hLib
  refine ⟨_, clauseJ_call G P Q s k₀ q₀ (Lay := glueLay) (cS := 100) (disp atCmd (bR1 atCmd)) fECmd
    (glue_ok _ _ _ _ _ _ _ _ _ _ _) glueLay_W glueLay_ovf hKq hrs hn hj (fun W => by rw [ecs]; exact hD W)
    (by rw [ecs]; exact hpl) hsub (by rw [hgu, hgo]; exact hsz)
    (le_trans (by
      have := Nat.pow_le_pow_right (n := 2) (by omega) (Nat.succ_le_succ he)
      have e2 : 2 ^ eSum = 2 ^ (eS + eF + eC + eK + eT) := rfl
      omega) hcG1)
    hcG2 (by omega) (by omega), ?_⟩
  -- the time
  have hw0 : winOf G P Q s k₀ q₀ c = 0 := by unfold winOf; simp [hc, hnf]
  have hT := tJ_le glueLay K KB ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ c)) (stOf G P Q s k₀ q₀ c)
    (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) k₀ q₀ (swAt G P Q s k₀ q₀ c).ws L ps
    (hdOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1)) ++ rQ G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))))
    (eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))))
    (sQ - guardBits glueLay + eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))) + 1) hps
  refine le_trans hT (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 5)
  set V := vU G P Q s k₀ q₀ atCmd_spec atKeep_atV C A
  have hZV : Z ≤ V := le_vU G P Q s k₀ q₀ atCmd_spec atKeep_atV C A le_rfl
  have hV := one_le_vU G P Q s k₀ q₀ atCmd_spec atKeep_atV C A
  have hlen := hLib.len
  try rw [← hcdef] at hlen
  have t1 := total_le_tot (swAt G P Q s k₀ q₀ c).ws
  have t2 := length_le_tot (swAt G P Q s k₀ q₀ c).ws
  have ho : (hdOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1)) ++
      rQ G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1)))).length ≤ 3 + 2 * Z := by
    simp only [hdOf, List.length_append, List.length_cons, ecs]
    omega
  have hol : (oOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)).length ≤ 3 + 2 * Z := by
    simp only [oOf, hdOf, List.length_append, List.length_cons]; omega
  have hd2 : 2 ^ (sQ - guardBits glueLay + eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ (j + 1))) + 1)
      ≤ 2 ^ (sQ + eSum + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [hw0, List.take_zero, List.length_nil]
  unfold cstJ
  omega

end Lax185574Proofs.ResolveRam.Glue
