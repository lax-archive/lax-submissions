import Lax185574Proofs.MainRam.Sound

/-!
Completeness of a thread. If the unpairing program, the program of
thm:skel-few-types and the model-checking program behave as their
specifications say at the word lengths where the thread runs them,
then the thread accepts with the right answer, and its time is bounded
by the sum of their times.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim
open Lax3.FirstOrder Lax271696.GraphEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionSequences Lax185574.PartialGraphs Lax185574.InstanceEncoding

/-- The time constant of a thread. -/
def thK (cC cV cW : ℕ) : ℕ :=
  pipeK ρid ρQ * (15 * pipeK ρid ρU + shK * (3 * cC + cV + cW + 21) + 12)

/-- **Completeness of a thread.** -/
theorem thread_complete {U FT Cl V M Wr : Program} {cU cC cV cW : ℕ} {φ : FO 0} {c₂ e₂ : ℕ}
    (hU : UnpairSpec U cU) (hCl : ClipSpec Cl cC) (hV : ValidSpec V cV) (hWr : WrapSpec Wr cW)
    {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G)
    (i wQ : ℕ) (hw : 12 ≤ wQ) (y : List ℕ) (tF : ℕ)
    (hF : RunsTo (wQ - 4) FT (triWord i ++ g) y tF)
    (s : List (PartialGraph (Fin n))) (hs : EncodesSequence y s) (hcs : IsConstructionSequence G s)
    (hye : ∀ v ∈ y, v ≤ y.length + n) (tMb : ℕ)
    (hMT : ∀ w : ℕ, (∀ a ∈ mcIn n G φ g y, c₂ * ((mcIn n G φ g y).length + a + 1) ^ e₂ ≤ 2 ^ w) →
      tMb ≤ 2 ^ w → ∃ t ≤ tMb, RunsTo w M (mcIn n G φ g y) (ansW G φ) t)
    (hfitM : tMb ≤ 2 ^ (wQ - 8))
    (hUadm : ∀ v ∈ i :: (g ++ toWord φ), cU * (i + v + 2) ^ 2 ≤ 2 ^ (wQ - 4))
    (hbig : thC cV * (y.length + (g ++ toWord φ).length + 10) ^ 2 ≤ 2 ^ (wQ - 8))
    (hpU : pipeK ρid ρU ≤ 2 ^ (wQ - 8))
    (hmc : c₂ * (2 * (y.length + (g ++ toWord φ).length) + 12) ^ e₂ ≤ 2 ^ (wQ - 8)) :
    ∃ t ≤ thK cC cV cW * (cU * (i + 2) ^ 2 + tF + (y.length + 1) * (n + 1) ^ 2 +
        (g ++ toWord φ).length + tMb + 1),
      RunsTo wQ (threadProg U FT Cl V M Wr) (i :: (g ++ toWord φ)) [1, ansB G φ] t := by
  set x := g ++ toWord φ with hx
  have hxl : x.length = g.length + (toWord φ).length := by simp [hx]
  have hng : n ≤ g.length := vertexCount_le hg
  obtain ⟨V8, hV8⟩ : ∃ V8, V8 = 2 ^ (wQ - 8) := ⟨_, rfl⟩
  have e4 : 2 ^ (wQ - 4) = 16 * V8 := by
    rw [hV8, two_pow_sub_mul (show 4 ≤ 8 by omega) (by omega)]; norm_num
  have e2 : 2 ^ (wQ - 2) = 64 * V8 := by
    rw [hV8, two_pow_sub_mul (show 2 ≤ 8 by omega) (by omega)]; norm_num
  have e0 : 2 ^ wQ = 256 * V8 := by
    rw [hV8, show 2 ^ wQ = 2 ^ (wQ - 0) by simp, two_pow_sub_mul (show 0 ≤ 8 by omega) (by omega)]
    norm_num
  rw [← hV8] at hbig hmc hpU
  set S := y.length + x.length + 10 with hS
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) S
  have hthC : 64 ≤ thC cV := by simp only [thC, shC]; omega
  have hSV : 64 * S ≤ V8 := le_trans (Nat.mul_le_mul hthC hSS) hbig
  have hKQ : pipeK ρid ρQ ≤ V8 := by
    have : pipeK ρid ρQ ≤ thC cV := by simp only [thC]; omega
    have : thC cV ≤ thC cV * S ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  -- the first half
  obtain ⟨tU, htU, hrU⟩ := hU (wQ - 4) i x hUadm
  have e42 : wQ - 2 - 2 = wQ - 4 := by omega
  have htw : (triWord i).length = 5 := rfl
  obtain ⟨t₁, ht₁, hr₁⟩ := pipe_fwd U FT ρid ρU (wQ - 2) (i :: x) (triWord i) y tU tF
    (by rw [e42, e4]; omega) (by rw [e42, e4, htw]; omega)
    (ρid_fits (by rw [e2]; simp; omega))
    (ρU_fits hg (by omega) (by rw [e2, htw]; omega) (by rw [e2]; omega) (by rw [e2, htw]; omega))
    (by rw [e42, ρid_apply]; exact hrU)
    (by rw [e42, ρU_apply hg]; exact hF)
  rw [ρid_cost, ρU_cost] at ht₁
  -- the second half
  set L := y.length + x.length + 2 with hL
  have hclip : clipY (wQ - 2 - 2) L y = y := by
    apply clipY_of_le
    intro a ha
    have := hye a ha
    exact ⟨by rw [e42, e4]; omega, by omega⟩
  have hval : ValidScript n G y := by
    obtain ⟨σ, hσ, rfl⟩ := hs
    exact ⟨σ, hσ, hcs⟩
  have hent := mcIn_entries_le hg φ (L := L) (fun a ha => by have := hye a ha; omega)
    (by rw [← hx]; omega)
  have hlen := mcIn_length_le n G φ g y
  obtain ⟨tM, htM, hrM⟩ := hMT (wQ - 8) (fun a ha => by
    rw [← hV8]
    refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) hmc
    have := hent a ha
    omega) hfitM
  rw [ansW_eq] at hrM
  have e86 : wQ - 2 - 6 = wQ - 8 := by omega
  have hbig' : shC cV * (y.length + x.length + 8) ^ 2 ≤ 2 ^ (wQ - 2 - 6) := by
    rw [e86, ← hV8]
    have h1 : (y.length + x.length + 8) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : shC cV ≤ thC cV := by simp only [thC]; omega
    exact le_trans (Nat.mul_le_mul h2 h1) hbig
  obtain ⟨tS, htS, hrS⟩ := secondHalf_run hCl hV hWr hg φ y (wQ - 2) (by omega) hbig'
    (ansB_le G φ) (by rw [e86, hclip]; exact hrM)
  rw [hclip] at hrS
  have hf : vFlag n G y = 1 := by unfold vFlag; rw [if_pos hval]
  rw [hf] at hrS
  -- the thread
  obtain ⟨T, hT, hrT⟩ := pipe_fwd (firstHalf U FT) (secondHalf Cl V M Wr) ρid ρQ wQ (i :: x) y
    [1, ansB G φ] t₁ tS (by rw [e2]; omega) (by rw [e2]; omega)
    (ρid_fits (by rw [e0]; simp; omega)) (ρQ_fits (by omega) (by rw [e0]; omega))
    (by rw [ρid_apply]; exact hr₁)
    (by rw [ρQ_apply]; exact hrS)
  rw [ρid_cost, ρQ_cost] at hT
  refine ⟨T, ?_, hrT⟩
  -- the time
  set W := cU * (i + 2) ^ 2 + tF + (y.length + 1) * (n + 1) ^ 2 + x.length + tMb + 1 with hW
  have hy1 : y.length ≤ (y.length + 1) * (n + 1) ^ 2 :=
    le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ (by positivity))
  have hW1 : 1 ≤ W := by omega
  have h1 : t₁ ≤ pipeK ρid ρU * (15 * W) :=
    le_trans ht₁ (Nat.mul_le_mul_left _ (by omega))
  have hZ : cC * (y.length + x.length + 3) + cV * ((y.length + 1) * (n + 1) ^ 2 + x.length + 1) +
      tM + cW + 20 ≤ (3 * cC + cV + cW + 21) * W := by
    have a1 : cC * (y.length + x.length + 3) ≤ 3 * cC * W := by
      have : y.length + x.length + 3 ≤ 3 * W := by omega
      calc cC * (y.length + x.length + 3) ≤ cC * (3 * W) := Nat.mul_le_mul_left _ this
        _ = 3 * cC * W := by ring
    have a2 : cV * ((y.length + 1) * (n + 1) ^ 2 + x.length + 1) ≤ cV * W :=
      Nat.mul_le_mul_left _ (by omega)
    have a3 : cW + 20 ≤ (cW + 20) * W := Nat.le_mul_of_pos_right _ hW1
    have a4 : (3 * cC + cV + cW + 21) * W = 3 * cC * W + cV * W + (cW + 20) * W + W := by ring
    omega
  have h2 : tS ≤ shK * ((3 * cC + cV + cW + 21) * W) :=
    le_trans htS (Nat.mul_le_mul_left _ hZ)
  have h3 : t₁ + tS + 3 + 9 ≤ (15 * pipeK ρid ρU + shK * (3 * cC + cV + cW + 21) + 12) * W := by
    have b1 : pipeK ρid ρU * (15 * W) = 15 * pipeK ρid ρU * W := by ring
    have b2 : shK * ((3 * cC + cV + cW + 21) * W) = shK * (3 * cC + cV + cW + 21) * W := by ring
    have b3 : (15 * pipeK ρid ρU + shK * (3 * cC + cV + cW + 21) + 12) * W =
      15 * pipeK ρid ρU * W + shK * (3 * cC + cV + cW + 21) * W + 12 * W := by ring
    omega
  calc T ≤ pipeK ρid ρQ * (t₁ + tS + 3 + 9) := hT
    _ ≤ pipeK ρid ρQ * ((15 * pipeK ρid ρU + shK * (3 * cC + cV + cW + 21) + 12) * W) :=
        Nat.mul_le_mul_left _ h3
    _ = thK cC cV cW * W := by simp only [thK]; ring

end Lax185574Proofs.MainRam
