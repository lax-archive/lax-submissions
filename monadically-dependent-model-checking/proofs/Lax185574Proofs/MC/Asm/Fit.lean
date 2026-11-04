import Lax185574Proofs.MC.Asm.Run
import Lax185574Proofs.LoopScript

/-!
The pipeline halts if all rounds fit.

`pipe_run`: let `Bnd` bound, for every round of the glue program, the
guard quantity of its time clause (with constant `cG + 1`), the time
bound `realT` of the callee of its call, and the constants of the
callees and of the switch. If every region of the loop driver up to
round `R` has room for `Bnd · 2 ^ (D + 20)`, then the pipeline halts
with the final answer `finAns`, within the constant of the driver times
the sum of the time bounds of the rounds: `bG j` for the glue program
and `bP j` for the callee.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Words Lax185574Proofs.RamSim Lax185574Proofs.Simulate
open Lax185574Proofs.RamCat Lax808846Proofs.Machine
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences

theorem le_catLim {B w E : ℕ} (hE : E ≤ w) (h : B + 1 ≤ 2 ^ (w - E)) : B ≤ catLim w E := by
  unfold catLim
  rw [Nat.le_div_iff_mul_le (by positivity)]
  have e : 2 ^ w = 2 ^ (w - E) * 2 ^ E := by rw [← pow_add]; congr 1; omega
  have h2 : (B + 1) * 2 ^ E ≤ 2 ^ (w - E) * 2 ^ E := Nat.mul_le_mul_right _ h
  have : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  rw [add_mul, one_mul] at h2
  omega

theorem lpSize_ne {w i : ℕ} (h : (i + 1) ^ 2 ≤ lpCap w) : lpSize w i ≠ 0 := by
  have h1 := lpSize_ge w i
  have : 1 ≤ lpCap w / (i + 1) ^ 2 := (Nat.one_le_div_iff (by positivity)).2 h
  omega

theorem pow_lpV_le (w i : ℕ) : 2 ^ lpV w i ≤ lpCap w := two_pow_mono (by unfold lpV; omega)

/-- The time bound of round `j` of the glue program. -/
noncomputable def bG {n : ℕ} (x : List ℕ) (s : List (PartialGraph (Fin n))) (q : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (cs : List (PCall n)) (hd : ℕ → List ℕ) (ans : List ℕ) (cG j : ℕ) :
    ℕ :=
  cG * ((pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length + 1)

/-- The time bound of the callee in round `j`. -/
noncomputable def bP {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (cs : List (PCall n)) (k : CCst) (Ks j : ℕ) : ℕ :=
  match cs[j]? with
  | some c => Ks * (realT s q φ k c + 3 * k.d + (callY s q φ c).length + 1)
  | none => 0

theorem mul_pow_le {c b E B : ℕ} (hE : 1 ≤ E) (h : (c + 1) * b ^ E ≤ B) :
    b < B + 1 ∧ c * b ^ E ≤ B ∧ b ^ E ≤ B := by
  have h1 : b ≤ b ^ E := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Nat.zero_le _
    · exact Nat.le_self_pow (by omega) _
  have h2 : b ^ E ≤ (c + 1) * b ^ E := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : c * b ^ E ≤ (c + 1) * b ^ E := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The pipeline halts if all rounds fit.** -/
theorem pipe_run {pM pR pE G sw P0 : Program} {eM eR eE q Ks KL D sI cG Bnd : ℕ} {k : CCst}
    (hC : CalleeRun pM pR pE eM eR eE q k) (hsw : SwSpec sw Ks D pM pR pE)
    (hP0 : LoopSpec P0 G sw KL) (hD : sI + 4 ≤ D) {φ : Lax3.FirstOrder.FO 0}
    (hq : Lax3.FirstOrder.rank φ = q) {n : ℕ} {s : List (PartialGraph (Fin n))} {x : List ℕ}
    {steps : List Step} {hd : ℕ → List ℕ}
    (hhd : ∀ j < (pcalls n steps).length,
      hd j ≠ [] ∧ (hd j).head? ≠ some 0 ∧ (hd j).getD 1 0 + 3 = (hd j).length)
    (hrd : ∀ j ≤ (pcalls n steps).length, ∀ v, sI ≤ v →
      (∀ e ∈ pU x s q φ (pcalls n steps) hd (finAns s q φ) j, e < 2 ^ (v - sI)) →
      (∀ o t, RunsTo v G (pU x s q φ (pcalls n steps) hd (finAns s q φ) j) o t →
        o = glueOut s q φ (pcalls n steps) hd (finAns s q φ) j ∧ (∀ e ∈ o, e < 2 ^ (v - sI - 4)) ∧
        ∀ c, (pcalls n steps)[j]? = some c → GuardOK s q φ eM eR eE v (D + 16) c) ∧
      (cG * (((pU x s q φ (pcalls n steps) hd (finAns s q φ) j).length +
          (glueOut s q φ (pcalls n steps) hd (finAns s q φ) j).length +
          maxEntry (pU x s q φ (pcalls n steps) hd (finAns s q φ) j ++
            glueOut s q φ (pcalls n steps) hd (finAns s q φ) j) + 1) ^
          (eM + eR + eE + 1)) ≤ 2 ^ (v - (D + 16)) →
        ∃ t ≤ cG * ((pU x s q φ (pcalls n steps) hd (finAns s q φ) j).length +
            (glueOut s q φ (pcalls n steps) hd (finAns s q φ) j).length + 1),
          RunsTo v G (pU x s q φ (pcalls n steps) hd (finAns s q φ) j)
            (glueOut s q φ (pcalls n steps) hd (finAns s q φ) j) t))
    (hB1 : ∀ j ≤ (pcalls n steps).length,
      (cG + 1) * ((pU x s q φ (pcalls n steps) hd (finAns s q φ) j).length +
          (glueOut s q φ (pcalls n steps) hd (finAns s q φ) j).length +
          maxEntry (pU x s q φ (pcalls n steps) hd (finAns s q φ) j ++
            glueOut s q φ (pcalls n steps) hd (finAns s q φ) j) + 1) ^ (eM + eR + eE + 1) ≤ Bnd)
    (hB2 : ∀ (j : ℕ) (c : PCall n), (pcalls n steps)[j]? = some c → realT s q φ k c ≤ Bnd)
    (hB3 : Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1 ≤ Bnd)
    {w : ℕ} (hreg : ∀ i ≤ 2 * (pcalls n steps).length + 2, Bnd * 2 ^ (D + 20) ≤ 2 ^ lpV w i)
    (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1))
    (hsz : (2 * (pcalls n steps).length + 3) ^ 2 ≤ lpCap w) :
    ∃ t ≤ KL * ((∑ j ∈ Finset.range (pcalls n steps).length,
        (bG x s q φ (pcalls n steps) hd (finAns s q φ) cG j + bP s q φ (pcalls n steps) k Ks j + 2)) +
        (bG x s q φ (pcalls n steps) hd (finAns s q φ) cG (pcalls n steps).length + 1) +
        (finAns s q φ).length + 1),
      RunsTo w P0 x (finAns s q φ) t := by
  set cs := pcalls n steps with hcs
  set R := cs.length with hR
  set ans := finAns s q φ with hans
  have hBnd : 1 ≤ Bnd := by omega
  have hreg' : ∀ i ≤ 2 * R + 2, D + 20 ≤ lpV w i ∧ Bnd ≤ 2 ^ (lpV w i - (D + 20)) :=
    fun i hi => le_pow_sub (hreg i hi) hBnd
  have hsize : ∀ i ≤ 2 * R + 2, lpSize w i ≠ 0 := fun i hi =>
    lpSize_ne (le_trans (Nat.pow_le_pow_left (by omega) 2) hsz)
  -- the runs of the glue program
  have hG : ∀ j, ∃ t, j ≤ R → t ≤ bG x s q φ cs hd ans cG j ∧
      RunsTo (lpV w (2 * j)) G (pU x s q φ cs hd ans j) (glueOut s q φ cs hd ans j) t := by
    intro j
    by_cases hj : j ≤ R
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    obtain ⟨hv, hBv⟩ := hreg' (2 * j) (by omega)
    obtain ⟨l1, l2, -⟩ := mul_pow_le (by omega) (hB1 j hj)
    have p1 : 2 ^ (lpV w (2 * j) - (D + 20)) ≤ 2 ^ (lpV w (2 * j) - sI) := two_pow_mono (by omega)
    have p2 : 2 ^ (lpV w (2 * j) - (D + 20)) ≤ 2 ^ (lpV w (2 * j) - (D + 16)) :=
      two_pow_mono (by omega)
    have hent : ∀ e ∈ pU x s q φ cs hd ans j, e < 2 ^ (lpV w (2 * j) - sI) := by
      intro e he
      have := le_maxEntry (List.mem_append_left (glueOut s q φ cs hd ans j) he)
      omega
    obtain ⟨t, ht, hr⟩ := (hrd j hj _ (by omega) hent).2 (by omega)
    exact ⟨t, fun _ => ⟨ht, hr⟩⟩
  choose tG htG using hG
  -- the runs of the callee
  have hP : ∀ j, ∃ t, j < R → t ≤ bP s q φ cs k Ks j ∧
      RunsTo (lpV w (2 * j + 1)) sw (lpQ (pA x s q φ cs hd ans (j + 1)))
        (pB s q φ cs (j + 1)) t ∧ (pB s q φ cs (j + 1)).length ≤ lpCap w := by
    intro j
    by_cases hj : j < R
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hj⟩
    have hgo : glueOut s q φ cs hd ans j = hd j ++ callQ s q φ c := by simp only [glueOut, hc]
    have hA : pA x s q φ cs hd ans (j + 1) = hd j ++ callQ s q φ c := by simp only [pA, hgo]
    have hB' : pB s q φ cs (j + 1) = callY s q φ c := by simp only [pB, hc]
    obtain ⟨-, -, hlen⟩ := hhd j hj
    rw [hA, lpQ_append hlen, hB']
    obtain ⟨hv, hBv⟩ := hreg' (2 * j + 1) (by omega)
    set v' := lpV w (2 * j + 1)
    obtain ⟨-, -, l3⟩ := mul_pow_le (by omega) (hB1 j hj.le)
    rw [hgo] at l3
    have hT := hB2 j c hc
    -- the query is small
    have hsub : ∀ e ∈ callQ s q φ c, e ∈ pU x s q φ cs hd ans j ++ (hd j ++ callQ s q φ c) :=
      fun e he => List.mem_append_right _ (List.mem_append_right _ he)
    have hql : (callQ s q φ c).length ≤ (hd j ++ callQ s q φ c).length := by simp
    have hg : ((callQ s q φ c).length + maxEntry (callQ s q φ c) + 1) ^ (eM + eR + eE + 1) ≤
        Bnd := by
      refine le_trans (Nat.pow_le_pow_left ?_ _) l3
      have := maxEntry_le_of_sub hsub
      omega
    have q8 : 2 ^ (v' - (D + 20)) * 2 ^ 12 = 2 ^ (v' - 8 - D) := by
      rw [← pow_add]; congr 1; omega
    have q10 : 2 ^ (v' - (D + 20)) * 2 ^ 10 = 2 ^ (v' - 10 - D) := by
      rw [← pow_add]; congr 1; omega
    have q6 : 2 ^ (v' - (D + 20)) * 2 ^ 14 = 2 ^ (v' - 6 - D) := by
      rw [← pow_add]; congr 1; omega
    have q4 : 2 ^ (v' - (D + 20)) * 2 ^ 16 = 2 ^ (v' - 4 - D) := by
      rw [← pow_add]; congr 1; omega
    obtain ⟨y, z, u, tA, tB, tC, rr1, rr2, rr3, hyzu, htt⟩ :=
      callee_run hC (s := s) hq c (vA := v' - 4 - D) (vB := v' - 6 - D) (vC := v' - 8 - D)
        (by omega) (by omega) (by omega) (by omega)
    have oy := runsTo_out_length rr1
    have oz := runsTo_out_length rr2
    have ou := runsTo_out_length rr3
    have cy : y.length ≤ catLim (v' - 4) (D + 2) :=
      le_catLim (by omega) (by rw [show v' - 4 - (D + 2) = v' - 6 - D by omega]; omega)
    have cz : z.length ≤ catLim (v' - 6) (D + 2) :=
      le_catLim (by omega) (by rw [show v' - 6 - (D + 2) = v' - 8 - D by omega]; omega)
    have cu : u.length ≤ catLim (v' - 8) (D + 2) :=
      le_catLim (by omega) (by rw [show v' - 8 - (D + 2) = v' - 10 - D by omega]; omega)
    have hswl : (swIn (callQM s q c) (callQR s q c) (callQE s q φ c)).length <
        2 ^ (v' - 10 - D) := by
      have := le_self_pow₀ (M₀ := ℕ) (a := (callQ s q φ c).length + maxEntry (callQ s q φ c) + 1)
        (by omega) (show eM + eR + eE + 1 ≠ 0 by omega)
      rw [callQ] at this hg
      omega
    obtain ⟨t, ht, hr⟩ := (hsw v' _ _ _ (by omega) hswl (by omega)).1 y z u tA tB tC rr1 rr2 rr3
      cy cz cu
    rw [hyzu] at hr
    refine ⟨t, fun _ => ⟨?_, by rw [callQ]; exact hr, ?_⟩⟩
    · have hyl : y.length + z.length + u.length = (callY s q φ c).length := by
        rw [← hyzu]; simp only [List.length_append]
      simp only [bP, hc]
      refine le_trans ht (Nat.mul_le_mul_left _ ?_)
      omega
    · have : (callY s q φ c).length ≤ 2 ^ v' := by
        rw [← hyzu]; simp only [List.length_append]
        have : 2 ^ (v' - 8 - D) ≤ 2 ^ v' := two_pow_mono (by omega)
        omega
      exact le_trans this (pow_lpV_le w _)
  choose tP htP using hP
  -- the calls of the script
  have hcall : ∀ j < R, CallOK w G sw x (pA x s q φ cs hd ans) (pB s q φ cs) tG tP j := by
    intro j hj
    obtain ⟨hne, hh0, -⟩ := hhd j hj
    obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hj⟩
    have hgo : glueOut s q φ cs hd ans j = hd j ++ callQ s q φ c := by simp only [glueOut, hc]
    have hA : pA x s q φ cs hd ans (j + 1) = glueOut s q φ cs hd ans j := rfl
    obtain ⟨-, hrG⟩ := htG j hj.le
    obtain ⟨-, hrP, hcap⟩ := htP j hj
    obtain ⟨hv, hBv⟩ := hreg' (2 * j) (by omega)
    obtain ⟨-, -, l3⟩ := mul_pow_le (by omega) (hB1 j hj.le)
    have hol : (glueOut s q φ cs hd ans j).length ≤ lpCap w := by
      have : (glueOut s q φ cs hd ans j).length ≤
          ((pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length +
            maxEntry (pU x s q φ cs hd ans j ++ glueOut s q φ cs hd ans j) + 1) ^
            (eM + eR + eE + 1) :=
        le_trans (by omega) (le_self_pow₀ (by omega) (by omega))
      have h1 : 2 ^ (lpV w (2 * j) - (D + 20)) ≤ 2 ^ lpV w (2 * j) := two_pow_mono (by omega)
      exact le_trans (by omega) (pow_lpV_le w (2 * j))
    refine ⟨hsize _ (by omega), hrG, fun o t h => (runsTo_unique h hrG).1, ?_, ?_, ?_,
      hsize _ (by omega), hrP, fun r t h => (runsTo_unique h hrP).1, hcap⟩
    · rw [hA, hgo]; simp [hne]
    · rw [hA, hgo]
      rcases hhj : hd j with _ | ⟨a, l⟩
      · exact absurd hhj hne
      · rw [hhj] at hh0; simpa using hh0
    · rw [hA]; exact hol
  -- the last round
  have hdone : DoneOK w G x (pA x s q φ cs hd ans) (pB s q φ cs) tG R ans := by
    have hgo : glueOut s q φ cs hd ans R = 0 :: ans := by
      simp only [glueOut, List.getElem?_eq_none (le_refl R)]
    obtain ⟨-, hrG⟩ := htG R le_rfl
    rw [hgo] at hrG
    obtain ⟨hv, hBv⟩ := hreg' (2 * R) (by omega)
    obtain ⟨-, -, l3⟩ := mul_pow_le (by omega) (hB1 R le_rfl)
    rw [hgo] at l3
    have hol : (0 :: ans).length ≤ lpCap w := by
      have : (0 :: ans).length ≤
          ((pU x s q φ cs hd ans R).length + (0 :: ans).length +
            maxEntry (pU x s q φ cs hd ans R ++ 0 :: ans) + 1) ^ (eM + eR + eE + 1) :=
        le_trans (by omega) (le_self_pow₀ (by omega) (by omega))
      have h1 : 2 ^ (lpV w (2 * R) - (D + 20)) ≤ 2 ^ lpV w (2 * R) := two_pow_mono (by omega)
      exact le_trans (by omega) (pow_lpV_le w (2 * R))
    exact ⟨hsize _ (by omega), hrG, fun o t h => (runsTo_unique h hrG).1, hol⟩
  obtain ⟨t, ht, hr⟩ := loop_script_run (fun w x hw hx => (hP0 w x hw hx).1) hw hx
    (A := pA x s q φ cs hd ans) (B := pB s q φ cs) rfl rfl hcall hdone
  refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ ?_), hr⟩
  have hsum : scriptTime tG tP R 0 ≤ (∑ j ∈ Finset.range R,
      (bG x s q φ cs hd ans cG j + bP s q φ cs k Ks j + 2)) + (bG x s q φ cs hd ans cG R + 1) := by
    unfold scriptTime
    rw [← Finset.range_eq_Ico]
    have h1 : ∑ i ∈ Finset.range R, (tG i + tP i + 2) ≤
        ∑ j ∈ Finset.range R, (bG x s q φ cs hd ans cG j + bP s q φ cs k Ks j + 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have := (htG i hi'.le).1
      have := (htP i hi').1
      omega
    have := (htG R le_rfl).1
    omega
  omega

end Lax185574Proofs.MC
