import Lax185574Proofs.MC.Asm.Poly
import Lax185574Proofs.MC.Asm.Skip
import Lax185574Proofs.Interface.Shim.Evaluation
import Lax185574Proofs.Interface.Shim.ResolveLift

/-!
The pipeline thread of thm:mc.

From a glue program as in `GlueHyp`, the three cited callees, the switch
and the loop driver, `thread_spec` builds one program `Ps`, the skip of
the graph word in front of the pipeline. Its word-length exponent `eP`
comes before the sentence. For each sentence there are a constant `cP`
and a degree `A` such that, on the input `g ++ toWord σ ++ toWord φ` of
thm:mc at a word length with `cP X ^ eP ≤ 2 ^ w`, every halting run of
`Ps` outputs `1 :: mcAns`, and if `n ≥ 1` and `(K + 1) ^ A ≤ |x| + 1`
then `Ps` halts within `cP (m + 1) (n + 1)² (K + 1) ^ A` steps. In the
other case the brute force is fast enough.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Words Lax185574Proofs.RamSim Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.TypeTrees Lax185574.Width
open Lax271696.GraphEncoding
open Lax3.DistFO (rhoMinus rhoPlus)

theorem le_half {Z w : ℕ} (h : 2 * Z ≤ 2 ^ w) (hZ : 1 ≤ Z) : Z ≤ 2 ^ (w - 1) := by
  cases w with
  | zero => simp at h; omega
  | succ w => rw [pow_succ] at h; simp only [Nat.add_sub_cancel]; omega

theorem len_arith (n m L : ℕ) : n + 3 * m + 3 + L ≤ (m + 1) * (n + 1) * (L + 6) := by ring_nf; omega

theorem pow_mono_le {X a b : ℕ} (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right hX h

set_option maxHeartbeats 1000000 in
/-- **The pipeline thread.** -/
theorem thread_spec (hG : GlueHyp) : ∃ (Ps : Program) (eP : ℕ), ∀ φ : Lax3.FirstOrder.FO 0,
    ∃ cP A : ℕ, ∀ (n : ℕ) (Gr : SimpleGraph (Fin n)) (g : List ℕ) (σ : Script n) (K w : ℕ),
      EncodesGraph g n Gr → IsConstructionSequence Gr σ.run →
      width (rhoPlus 1 (Lax3.FirstOrder.rank φ))
        (rhoPlus 1 (Lax3.FirstOrder.rank φ) + 1 + Lax3.FirstOrder.rank φ) σ.run ≤ K →
      cP * ((g ++ (toWord σ ++ toWord φ)).length + maxEntry (g ++ (toWord σ ++ toWord φ)) + 1) ^ eP ≤
        2 ^ w →
      (∀ z t, RunsTo w Ps (g ++ (toWord σ ++ toWord φ)) z t → z = 1 :: mcAns Gr φ) ∧
      (1 ≤ n → (K + 1) ^ A ≤ (g ++ (toWord σ ++ toWord φ)).length + 1 →
        ∃ t ≤ cP * (σ.steps.length + 1) * (n + 1) ^ 2 * (K + 1) ^ A,
          RunsTo w Ps (g ++ (toWord σ ++ toWord φ)) (1 :: mcAns Gr φ) t) := by
  obtain ⟨pM, eM, hM⟩ := mergeJobs
  obtain ⟨pR, eR, hR⟩ := Lax185574Proofs.Shim.ResolveLift.exists_program_resolveLift
  have hR' : RLSpec pR eR := hR
  obtain ⟨pE, eE, hE⟩ := Lax185574Proofs.Shim.Evaluation.exists_program_eval
  obtain ⟨sI, hGl⟩ := hG
  obtain ⟨Gp, hGp⟩ := hGl eM eR eE (sI + 4) le_rfl
  obtain ⟨sw, Ks, hsw⟩ := Lax185574Proofs.Simulate.switch pM pR pE (sI + 4) (by omega)
  obtain ⟨P0, KL, hP0⟩ := Lax185574Proofs.Simulate.loop_sound Gp sw
  obtain ⟨Ps, Kk, hKk, hskip⟩ := skip P0
  set D := sI + 4 with hDd
  set E := eM + eR + eE + 1 with hEd
  refine ⟨Ps, 2 * E + 9, fun φ => ?_⟩
  set q := Lax3.FirstOrder.rank φ with hq
  obtain ⟨cG, hcG⟩ := hGp φ
  obtain ⟨k, hk⟩ := calleeRun_of hM hR' hE q
  obtain ⟨cM, cR, cE, dM, dR, dE, hS⟩ := calleeSound_of hM hR' hE q
  obtain ⟨cT, aT, hT⟩ := treeMax_le q
  set γ := pγ k with hγ
  set A := aT * E + (aT + 1) * γ with hAd
  obtain ⟨C0, hC0⟩ : ∃ c, c = cT + (toWord (loc q φ)).length + (q + 1) * (1 + q) + 3 := ⟨_, rfl⟩
  obtain ⟨SB, hSB⟩ : ∃ c, c = soundBig eM eR eE cM cR cE dM dR dE Ks := ⟨_, rfl⟩
  obtain ⟨Cb, hCb⟩ : ∃ c, c = (cG + 1) * (pC1 cG q φ * (cT + 1)) ^ E + (k.cM + k.cE + k.cR) * C0 ^ γ +
    (Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1) := ⟨_, rfl⟩
  obtain ⟨Cpoly, hCpoly⟩ : ∃ c, c = 2 * cG * ((toWord φ).length + 6) + 2 * pC cG Ks q φ k + 4
    := ⟨_, rfl⟩
  obtain ⟨Ct, hCt⟩ : ∃ c, c = Kk * (KL * Cpoly * C0 ^ γ + 1) := ⟨_, rfl⟩
  obtain ⟨cP, hcP⟩ : ∃ c, c = 2 ^ (D + 31 + sI) * (Cb + SB) + 2 * Kk + Ct + 1 := ⟨_, rfl⟩
  refine ⟨cP, A, fun n Gr g σ K w hg hcs hK hadm => ?_⟩
  set y := toWord σ ++ toWord φ with hy
  set x := g ++ y with hx
  set x' := [n] ++ toWord σ ++ toWord φ with hx'
  have hxa : [n] ++ y = x' := by simp [y, x']
  set X := x.length + maxEntry x + 1 with hXd
  set X' := x'.length + maxEntry x' + 1 with hX'd
  have hgl := hg.length_eq
  have hng : n ∈ g := by
    have h0 := hg.vertexCount_eq
    simp only [vertexCount] at h0
    rw [← h0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hX'X : X' ≤ X := by
    have h1 : x'.length + 2 ≤ x.length := by simp [x', x, y]; omega
    have h2 : maxEntry x' ≤ maxEntry x := maxEntry_le_of_sub fun e he => by
      simp only [x', List.mem_append, List.mem_singleton] at he
      simp only [x, y, List.mem_append]
      rcases he with (rfl | he) | he
      · exact Or.inl hng
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr he)
    omega
  have hX1 : 1 ≤ X := by omega
  have hXe : 1 ≤ X ^ (2 * E + 9) := Nat.one_le_pow _ _ hX1
  have hx'e : X' ^ 5 ≤ X ^ (2 * E + 9) :=
    le_trans (Nat.pow_le_pow_left hX'X 5) (pow_mono_le hX1 (by omega))
  -- word-length facts
  have hcPX : cP ≤ cP * X ^ (2 * E + 9) := Nat.le_mul_of_pos_right _ hXe
  have hcP1 : 2 * Kk + 1 ≤ cP := by rw [hcP]; omega
  have hcP2 : 2 ^ (D + 31 + sI) * (Cb + SB) ≤ cP := by rw [hcP]; omega
  have hcP3 : Ct ≤ cP := by rw [hcP]; omega
  have hKw : Kk ≤ 2 ^ (w - 1) := le_half (by omega) hKk
  have hxw : x.length < 2 ^ w := by
    have : X ≤ X ^ (2 * E + 9) := by
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (2 * E + 9) := pow_mono_le hX1 (by omega)
    have : X ≤ cP * X ^ (2 * E + 9) := le_trans this (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hbig : ∀ Z, Z ≤ (Cb + SB) * X ^ (2 * E + 4) →
      2 ^ (D + 30 + sI) * Z * X' ^ 5 ≤ 2 ^ (w - 1) := by
    intro Z hZ
    by_cases hZ0 : Z = 0
    · subst hZ0; simp
    refine le_half ?_ (Nat.one_le_iff_ne_zero.2 (by positivity))
    have e : 2 * (2 ^ (D + 30 + sI) * Z * X' ^ 5) = 2 ^ (D + 31 + sI) * Z * X' ^ 5 := by
      rw [show 2 ^ (D + 31 + sI) = 2 * 2 ^ (D + 30 + sI) by
        rw [← pow_succ']; congr 1; omega]
      ring
    have h5 : X' ^ 5 ≤ X ^ 5 := Nat.pow_le_pow_left hX'X 5
    have e2 : 2 ^ (D + 31 + sI) * ((Cb + SB) * X ^ (2 * E + 4)) * X ^ 5 =
        2 ^ (D + 31 + sI) * (Cb + SB) * X ^ (2 * E + 9) := by
      rw [show X ^ (2 * E + 9) = X ^ (2 * E + 4) * X ^ 5 by
        rw [← pow_add]]
      ring
    rw [e]
    calc 2 ^ (D + 31 + sI) * Z * X' ^ 5
        ≤ 2 ^ (D + 31 + sI) * ((Cb + SB) * X ^ (2 * E + 4)) * X ^ 5 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hZ) h5
      _ = 2 ^ (D + 31 + sI) * (Cb + SB) * X ^ (2 * E + 9) := e2
      _ ≤ cP * X ^ (2 * E + 9) := Nat.mul_le_mul_right _ hcP2
      _ ≤ 2 ^ w := hadm
  have hP1 : 1 ≤ X ^ (2 * E + 4) := Nat.one_le_pow _ _ hX1
  obtain ⟨hsf, hsb⟩ := hskip w n Gr g y hg hKw hxw
  rw [hxa] at hsf hsb
  have hglue := hcG n σ
  refine ⟨fun z t hrun => ?_, fun hn hYA => ?_⟩
  · -- soundness
    obtain ⟨t', -, h'⟩ := hsb z t hrun
    have hSB' : SB ≤ (Cb + SB) * X ^ (2 * E + 4) :=
      le_trans (by omega) (Nat.le_mul_of_pos_right _ hP1)
    have hb := hbig SB hSB'
    rw [hSB] at hb
    exact pipe_sound_adm hS hsw hP0 le_rfl rfl hcs hglue hb z t' h'
  · -- the run in the pipe case
    set T := treeMax σ.run q with hTd
    set Y := K + 1 with hYd
    have hY1 : 1 ≤ Y := by omega
    have hTb : T ≤ cT * Y ^ aT := hT n Gr σ.run K hcs hK
    have hYa : 1 ≤ Y ^ aT := Nat.one_le_pow _ _ hY1
    have hYAX : Y ^ A ≤ X := le_trans hYA (Nat.add_le_add_right (Nat.le_add_right _ _) 1)
    have hYle : ∀ j ≤ A, Y ^ j ≤ X := fun j hj => le_trans (pow_mono_le hY1 hj) hYAX
    have h0 : pM0 T q K φ ≤ C0 * Y ^ (aT + 1) := by
      rw [hC0]; exact pM0_le (T := T) (q := q) (K := K) (cT := cT) (aT := aT) φ hTb
    have hM0 : pM0 T q K φ ^ γ ≤ C0 ^ γ * Y ^ ((aT + 1) * γ) :=
      le_trans (Nat.pow_le_pow_left h0 γ) (le_of_eq (by rw [mul_pow, ← pow_mul]))
    have hn3 : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by
      have := le_maxEntry (show n ∈ x by simp [x, hng]); omega) 2
    -- the bound of the rounds
    obtain ⟨P, hPd⟩ : ∃ P, P = X ^ (2 * E + 4) := ⟨_, rfl⟩
    have hXP : ∀ j ≤ 2 * E + 4, X ^ j ≤ P := fun j hj => hPd ▸ pow_mono_le hX1 hj
    have hP1' : 1 ≤ P := hPd ▸ hP1
    have hB : pBnd eM eR eE cG Ks n T q K X' φ k ≤ Cb * P := by
      have s1 : pC1 cG q φ * (X' ^ 2 * (T + 1)) ≤ (pC1 cG q φ * (cT + 1)) * (X ^ 2 * Y ^ aT) := by
        have a1 : X' ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hX'X 2
        have a2 : T + 1 ≤ (cT + 1) * Y ^ aT := by nlinarith
        calc pC1 cG q φ * (X' ^ 2 * (T + 1)) ≤ pC1 cG q φ * (X ^ 2 * ((cT + 1) * Y ^ aT)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul a1 a2)
          _ = (pC1 cG q φ * (cT + 1)) * (X ^ 2 * Y ^ aT) := by ring
      have s2 : (pC1 cG q φ * (X' ^ 2 * (T + 1))) ^ E ≤ (pC1 cG q φ * (cT + 1)) ^ E * P := by
        have b1 : (X ^ 2 * Y ^ aT) ^ E = X ^ (2 * E) * Y ^ (aT * E) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
        have b2 : X ^ (2 * E) * Y ^ (aT * E) ≤ P := by
          calc X ^ (2 * E) * Y ^ (aT * E) ≤ X ^ (2 * E) * X :=
                Nat.mul_le_mul_left _ (hYle _ (by simp only [A]; omega))
            _ = X ^ (2 * E + 1) := (pow_succ _ _).symm
            _ ≤ P := hXP _ (by omega)
        calc (pC1 cG q φ * (X' ^ 2 * (T + 1))) ^ E
            ≤ ((pC1 cG q φ * (cT + 1)) * (X ^ 2 * Y ^ aT)) ^ E := Nat.pow_le_pow_left s1 _
          _ = (pC1 cG q φ * (cT + 1)) ^ E * (X ^ 2 * Y ^ aT) ^ E := mul_pow _ _ _
          _ ≤ (pC1 cG q φ * (cT + 1)) ^ E * P := by rw [b1]; exact Nat.mul_le_mul_left _ b2
      have s3 : realB n T q K φ k ≤ ((k.cM + k.cE + k.cR) * C0 ^ γ) * P := by
        have c1 := (mcR_le cG Ks n T q K φ k).2
        have c2 : (n + 1) ^ 2 * pM0 T q K φ ^ pγ k ≤ C0 ^ γ * P := by
          calc (n + 1) ^ 2 * pM0 T q K φ ^ pγ k ≤ X ^ 2 * (C0 ^ γ * Y ^ ((aT + 1) * γ)) :=
                Nat.mul_le_mul hn3 hM0
            _ ≤ X ^ 2 * (C0 ^ γ * X) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hYle _ (by simp only [A]; omega)))
            _ = C0 ^ γ * X ^ 3 := by ring
            _ ≤ C0 ^ γ * P := Nat.mul_le_mul_left _ (hXP 3 (by omega))
        calc realB n T q K φ k ≤ (k.cM + k.cE + k.cR) * ((n + 1) ^ 2 * pM0 T q K φ ^ pγ k) := c1
          _ ≤ (k.cM + k.cE + k.cR) * (C0 ^ γ * P) := Nat.mul_le_mul_left _ c2
          _ = ((k.cM + k.cE + k.cR) * C0 ^ γ) * P := by ring
      have s4 := Nat.mul_le_mul_left (cG + 1) s2
      have s5 : Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1 ≤
          (Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1) * P :=
        Nat.le_mul_of_pos_right _ hP1'
      have e : Cb * P = (cG + 1) * ((pC1 cG q φ * (cT + 1)) ^ E * P) +
          ((k.cM + k.cE + k.cR) * C0 ^ γ) * P +
          (Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1) * P := by
        rw [hCb]; ring
      show (cG + 1) * (pC1 cG q φ * (X' ^ 2 * (T + 1))) ^ E + realB n T q K φ k +
          (Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1) ≤ Cb * P
      omega
    have hB' : pBnd eM eR eE cG Ks n T q K X' φ k ≤ (Cb + SB) * X ^ (2 * E + 4) :=
      le_trans hB (by rw [hPd]; exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    obtain ⟨t, ht, hrun⟩ := pipe_time hk hsw hP0 le_rfl hn hcs hK hglue (hbig _ hB')
    obtain ⟨t', ht', hrun'⟩ := hsf _ t hrun
    refine ⟨t', le_trans ht' ?_, hrun'⟩
    -- the time
    set m := σ.steps.length with hm
    have hL : x'.length ≤ (m + 1) * (n + 1) * ((toWord φ).length + 6) := by
      have e : x'.length = n + 3 * m + 3 + (toWord φ).length := by
        simp only [x', List.length_append, List.length_singleton, script_length σ]; omega
      rw [e]; exact len_arith n m _
    have hpp := pipe_poly KL cG Ks n T q K m x'.length ((toWord φ).length + 6) φ k hL
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = (m + 1) * (n + 1) ^ 2 * Y ^ A := ⟨_, rfl⟩
    have hZ1 : 1 ≤ Z := by
      rw [hZ]; exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos m) (Nat.pow_pos (Nat.succ_pos n))) (Nat.pow_pos hY1)
    have hW : (m + 1) * ((n + 1) ^ 2 * pM0 T q K φ ^ pγ k) ≤ C0 ^ γ * Z := by
      calc (m + 1) * ((n + 1) ^ 2 * pM0 T q K φ ^ pγ k)
          ≤ (m + 1) * ((n + 1) ^ 2 * (C0 ^ γ * Y ^ A)) := by
            refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_trans hM0 ?_))
            exact Nat.mul_le_mul_left _ (pow_mono_le hY1 (by simp only [A]; omega))
        _ = C0 ^ γ * Z := by rw [hZ]; ring
    have ht2 : t ≤ KL * Cpoly * C0 ^ γ * Z := by
      calc t ≤ _ := ht
        _ ≤ KL * Cpoly * ((m + 1) * ((n + 1) ^ 2 * pM0 T q K φ ^ pγ k)) := by rw [hCpoly]; exact hpp
        _ ≤ KL * Cpoly * (C0 ^ γ * Z) := Nat.mul_le_mul_left _ hW
        _ = KL * Cpoly * C0 ^ γ * Z := by ring
    have ht3 : Kk * (t + 1) ≤ Ct * Z := by
      calc Kk * (t + 1) ≤ Kk * (KL * Cpoly * C0 ^ γ * Z + Z) := Nat.mul_le_mul_left _ (by omega)
        _ = Ct * Z := by rw [hCt]; ring
    calc Kk * (t + 1) ≤ Ct * Z := ht3
      _ ≤ cP * Z := Nat.mul_le_mul_right _ hcP3
      _ = cP * (m + 1) * (n + 1) ^ 2 * Y ^ A := by rw [hZ]; ring

end Lax185574Proofs.MC
