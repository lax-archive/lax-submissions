import Lax185574Proofs.ResolveRam.Glue.Rounds
import Lax185574Proofs.ResolveRam.Glue.TimeSum
import Lax185574Proofs.ResolveRam.Glue.Round1
import Lax185574Proofs.ResolveRam.SizeGlue.Ent
import Lax185574Proofs.ResolveRam.Assembly

/-!
The glue program of lem:resolve-lift meets `RGlueHyp`.

The time of a round is at most `a (n + 1) Y^b` in the middle and
`a (n + 1)² Y^b` at the rounds `0`, `1` and `R`, with `Y = M + T + 1`
(`round_le`). The sum is then at most `rBound` (`time_sum`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TypeTreeSizes Lax3.DistFO Lax808846Proofs.Compile Lax808846.Ram

/-- A bound `L (c₁ X + c₀) + 5` is a bound `a W` when `X ≤ W` and `1 ≤ W`. -/
theorem lin_bound {t L c1 X c0 W a : ℕ} (hX : X ≤ W) (hW : 1 ≤ W) (h : t ≤ L * (c1 * X + c0) + 5)
    (ha : L * c1 + L * c0 + 5 ≤ a) : t ≤ a * W := by
  have h1 : L * (c1 * X + c0) + 5 ≤ (L * c1 + L * c0 + 5) * W := by
    have e1 : L * (c1 * X + c0) = L * c1 * X + L * c0 := by ring
    have e2 : (L * c1 + L * c0 + 5) * W = L * c1 * W + L * c0 * W + 5 * W := by ring
    rw [e1, e2]
    have := Nat.mul_le_mul_left (L * c1) hX
    have := Nat.mul_le_mul_left (L * c0) hW
    omega
  exact le_trans h (le_trans h1 (Nat.mul_le_mul_right _ ha))

/-- The constant part of the special rounds. -/
noncomputable def cstS (K eSum sQ k₀ q₀ : ℕ) : ℕ :=
  cstJ K eSum sQ k₀ q₀ + 100 * (K + 2 ^ (sQ + eSum + 1)) + 100 * k0 + 10000

/-- The constant of the times of the rounds. -/
noncomputable def aOf (kq Cs Cf K eSum sQ k₀ q₀ : ℕ) : ℕ :=
  glueLay.const * (9000000 * kq + Cs + Cf + 2400 + cstS K eSum sQ k₀ q₀) + 5

/-- A constant `K` for the glue program. -/
theorem exists_kG : ∃ K, kq0 ≤ K ∧ 4 * k0 + 64 ≤ K :=
  ⟨kq0 + 4 * k0 + 64, le_trans (Nat.le_add_right kq0 (4 * k0)) (Nat.le_add_right _ 64), by
    rw [Nat.add_assoc kq0]; exact Nat.le_add_left _ _⟩

theorem a_ge {kq Cs Cf K eSum sQ k₀ q₀ c1 c0 : ℕ} (h1 : c1 ≤ 9000000 * kq + Cs + Cf + 2400)
    (h0 : c0 ≤ cstS K eSum sQ k₀ q₀) :
    glueLay.const * c1 + glueLay.const * c0 + 5 ≤ aOf kq Cs Cf K eSum sQ k₀ q₀ := by
  unfold aOf
  rw [Nat.mul_add]
  have := Nat.mul_le_mul_left glueLay.const h1
  have := Nat.mul_le_mul_left glueLay.const h0
  omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem one_le_W (A : ℕ) : 1 ≤ (n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ A := by
  have := Nat.one_le_pow A _ (one_le_yQ G P Q s k₀ q₀)
  have : 1 ≤ (n + 1) * (n + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

theorem W_mono {A B : ℕ} (h : A ≤ B) : (n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ A ≤
    (n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ B :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_yQ G P Q s k₀ q₀) h)

theorem U_mono {A B : ℕ} (h : A ≤ B) : (n + 1) * yQ G P Q s k₀ q₀ ^ A ≤ (n + 1) * yQ G P Q s k₀ q₀ ^ B :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_yQ G P Q s k₀ q₀) h)

theorem U_le_W (A : ℕ) : (n + 1) * yQ G P Q s k₀ q₀ ^ A ≤
    (n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ A := by
  rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)

/-- **The rounds with their times.** -/
theorem round_le (hk : 1 ≤ k₀) {C A Cs As cS Cf Af : ℕ}
    (hKit : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), SzKit G P Q s k₀ q₀ C A)
    (hR1 : ∀ (K eS eF eC eK eT sQ cG E : ℕ) (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool),
      kq0 ≤ K → guardBits glueLay + 11 ≤ sQ → 1 ≤ n →
      2 * 2 ^ (eS + eF + eC + eK + eT + 1) + K + 1 ≤ cG →
      2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * cS ^ 2 ≤ cG →
      E = eS + eF + eC + eK + eT + 2 →
      ∃ t, ClauseAt G P Q s k₀ q₀ (rgProg K eS eF eC eK eT sQ) (guardBits glueLay + 6) sQ eS eF eC eK eT cG E t 1 ∧
      t ≤ glueLay.const * (Cs * (n + 1) * (n + 1) *
        (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ As +
        100 * (K + 2 ^ (sQ + eS + eF + eC + eK + eT + 1))) + 5)
    (hFin : ∀ (Lay : Layout) (K KB : ℕ) (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (j : ℕ), 1 ≤ n →
      j + 1 = (rcalls G P Q s k₀ q₀).length →
      tFin Lay K KB ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
          (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
          k₀ q₀ (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
          (feK n (xIn G k₀ q₀ P Q s).length (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
            (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) (0 :: zOut G k₀ q₀ P Q s)) ≤
        Lay.const * (Cf * (n + 1) * (n + 1) *
            (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ Af +
          KB + 30 * K + 23 * ((k₀ + q₀ + 1) * (q₀ + 1))) + 5)
    {kG : ℕ} (hKq : kq0 ≤ kG) (hk0 : 4 * k0 + 64 ≤ kG)
    {eS eF eC eK eT sQ cG : ℕ} (hrs : guardBits glueLay + 11 ≤ sQ)
    (hcG1 : 2 * 2 ^ (eS + eF + eC + eK + eT + 1) + kG + 5 ≤ cG)
    (hcG2 : 2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * (cS ^ 2 + 100 ^ 2 + 72 ^ 2) ≤ cG)
    {j : ℕ} (hj : j ≤ (rcalls G P Q s k₀ q₀).length) :
    ∃ t, ClauseAt G P Q s k₀ q₀ (rgProg kG eS eF eC eK eT sQ) (guardBits glueLay + 6) sQ eS eF eC eK eT cG
        (eS + eF + eC + eK + eT + 2) t j ∧
      t ≤ (if j ≤ 1 ∨ j = (rcalls G P Q s k₀ q₀).length then
          aOf (kqOf atCmd_spec atKeep_atV C k₀ q₀) Cs Cf kG (eS + eF + eC + eK + eT) sQ k₀ q₀ *
            (n + 1) * (n + 1) *
            yQ G P Q s k₀ q₀ ^ (2 * A * (aPc atCmd_spec atKeep_atV + 1) + As + Af + 1) else 0) +
        aOf (kqOf atCmd_spec atKeep_atV C k₀ q₀) Cs Cf kG (eS + eF + eC + eK + eT) sQ k₀ q₀ * (n + 1) *
          yQ G P Q s k₀ q₀ ^ (2 * A * (aPc atCmd_spec atKeep_atV + 1) + As + Af + 1) := by
  set kq := kqOf atCmd_spec atKeep_atV C k₀ q₀
  set a := aOf kq Cs Cf kG (eS + eF + eC + eK + eT) sQ k₀ q₀
  set B := 2 * A * (aPc atCmd_spec atKeep_atV + 1) with hB
  set b := B + As + Af + 1 with hb
  have eW : a * ((n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ b) =
      a * (n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ b := by ring
  have eU : a * ((n + 1) * yQ G P Q s k₀ q₀ ^ b) = a * (n + 1) * yQ G P Q s k₀ q₀ ^ b := by ring
  have hP0 : 2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * cS ^ 2 ≤
      2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * (cS ^ 2 + 100 ^ 2 + 72 ^ 2) :=
    Nat.mul_le_mul_left _ (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hcS := le_trans hP0 hcG2
  have hP1 : 2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * 100 ^ 2 ≤
      2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * (cS ^ 2 + 100 ^ 2 + 72 ^ 2) :=
    Nat.mul_le_mul_left _ (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  have hc100 := le_trans hP1 hcG2
  have hP2 : 2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * 72 ^ 2 ≤
      2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * (cS ^ 2 + 100 ^ 2 + 72 ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have hc72 := le_trans hP2 hcG2
  have hcst : cstJ kG (eS + eF + eC + eK + eT) sQ k₀ q₀ ≤ cstS kG (eS + eF + eC + eK + eT) sQ k₀ q₀ := by
    unfold cstS; omega
  have hW1 := one_le_W G P Q s k₀ q₀ b
  have hUW := U_le_W G P Q s k₀ q₀ b
  have h2e : 2 * 2 ^ (eT + 1) ≤ 2 * 2 ^ ((eS + eF + eC + eK + eT) + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- round 0
    refine ⟨_, round_zero G P Q s k₀ q₀ hk0 hrs (by omega) (by omega), ?_⟩
    rw [if_pos (Or.inl (by omega))]
    have hx := xIn_len_le' k₀ q₀ G P Q s
    have hM : maxTreeSize G k₀ q₀ + 1 ≤ yQ G P Q s k₀ q₀ := by unfold yQ; omega
    have hX : (xIn G k₀ q₀ P Q s).length + 1 ≤ 12 * ((n + 1) * (n + 1) *
        yQ G P Q s k₀ q₀ ^ 1) := by
      have h2 : (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) ≤
          (n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ 1 := by
        rw [pow_one]; exact Nat.mul_le_mul_left _ hM
      have e3 : 11 * (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) =
          11 * ((n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1)) := by ring
      have := one_le_W G P Q s k₀ q₀ 1
      omega
    have hd : 2 ^ (sQ - guardBits glueLay + eT + 1) ≤ 2 ^ (sQ + (eS + eF + eC + eK + eT) + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have ht : t0 glueLay kG eT (sQ - guardBits glueLay + eT + 1) ((xIn G k₀ q₀ P Q s).length + 1) ≤
        glueLay.const * (2400 * ((n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ 1) +
          cstS kG (eS + eF + eC + eK + eT) sQ k₀ q₀) + 5 := by
      unfold t0 cstS cstJ
      refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 5
      omega
    have := lin_bound (W_mono G P Q s k₀ q₀ (show 1 ≤ b by omega)) hW1 ht (a := a) (a_ge (by omega) (by omega))
    omega
  have hn : 1 ≤ n := by
    by_contra h
    have : (rcalls G P Q s k₀ q₀) = [] := by simp [rcalls, show n = 0 by omega]
    rw [this] at hj; simp at hj; omega
  -- 2 ≤ R
  have hR2 : 2 ≤ (rcalls G P Q s k₀ q₀).length := by
    have h1 : 0 < (rcalls G P Q s k₀ q₀).length := by simp [rcalls, show n ≠ 0 by omega]
    by_contra h
    have h1' : (rcalls G P Q s k₀ q₀).length = 1 := by omega
    have := (cur_succ_fin G P Q s k₀ q₀ hn (j := 0) (by omega)).2 (by omega)
    rw [cur_succ] at this
    simp only [cur, Function.iterate_zero, id, next] at this
    split_ifs at this
  rcases (show j = 1 ∨ (2 ≤ j ∧ j < (rcalls G P Q s k₀ q₀).length) ∨ j = (rcalls G P Q s k₀ q₀).length by omega)
    with rfl | ⟨hj2, hjR⟩ | rfl
  · -- round 1
    obtain ⟨t, hC, ht⟩ := hR1 kG eS eF eC eK eT sQ cG _ n G P Q s hKq hrs hn (by omega) hcS rfl
    refine ⟨t, hC, ?_⟩
    rw [if_pos (Or.inl le_rfl)]
    have ht' : t ≤ glueLay.const * (Cs * ((n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ As) +
        cstS kG (eS + eF + eC + eK + eT) sQ k₀ q₀) + 5 := by
      refine le_trans ht (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 5)
      have e : Cs * (n + 1) * (n + 1) *
          (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ As =
          Cs * ((n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ As) := by
        unfold yQ; ring
      rw [e, show sQ + eS + eF + eC + eK + eT + 1 = sQ + (eS + eF + eC + eK + eT) + 1 by omega]
      unfold cstS; omega
    have := lin_bound (W_mono G P Q s k₀ q₀ (show As ≤ b by omega)) hW1 ht' (a := a) (a_ge (by omega) (by omega))
    omega
  · -- a round in the middle
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨t, hC, ht⟩ := round_mid G P Q s k₀ q₀ (hKit n G P Q s) hk (eS := eS) (eF := eF) (eC := eC)
      (eK := eK) (eT := eT) (cG := cG) (E := (eS + eF + eC + eK + eT) + 2) hKq hrs hn (by omega) hjR (by omega) hc100 rfl
    refine ⟨t, hC, ?_⟩
    rw [if_neg (by omega), zero_add]
    have ht' : t ≤ glueLay.const * ((9000000 * kq) * ((n + 1) * yQ G P Q s k₀ q₀ ^ B) +
        cstJ kG (eS + eF + eC + eK + eT) sQ k₀ q₀) + 5 := by
      refine le_trans ht (le_of_eq ?_)
      unfold vU; ring
    have := lin_bound (U_mono G P Q s k₀ q₀ (show B ≤ b by omega)) (one_le_U (by omega) (one_le_yQ G P Q s k₀ q₀))
      ht' (a := a) (a_ge (by omega) hcst)
    omega
  · -- the last round
    obtain ⟨j', hj'⟩ : ∃ j', (rcalls G P Q s k₀ q₀).length = j' + 1 :=
      ⟨(rcalls G P Q s k₀ q₀).length - 1, by omega⟩
    rw [hj']
    refine ⟨_, round_fin G P Q s k₀ q₀ (E := (eS + eF + eC + eK + eT) + 2) hk hKq hrs hn hj'.symm (by omega) hc72
      (by omega), ?_⟩
    rw [if_pos (Or.inr rfl)]
    have ht := hFin glueLay kG 100 n G P Q s j' hn hj'.symm
    have ht' : tFin glueLay kG 100 ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j')))
          (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j')) (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j')))
          k₀ q₀ (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j')).ws
          (feK n (xIn G k₀ q₀ P Q s).length (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j')).ws
            (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j'))) (0 :: zOut G k₀ q₀ P Q s)) ≤
        glueLay.const * (Cf * ((n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ Af) +
          cstS kG (eS + eF + eC + eK + eT) sQ k₀ q₀) + 5 := by
      refine le_trans ht (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 5)
      have e : Cf * (n + 1) * (n + 1) *
          (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ Af =
          Cf * ((n + 1) * (n + 1) * yQ G P Q s k₀ q₀ ^ Af) := by
        unfold yQ; ring
      rw [e]; unfold cstS cstJ; omega
    have := lin_bound (W_mono G P Q s k₀ q₀ (show Af ≤ b by omega)) hW1 ht' (a := a) (a_ge (by omega) (by omega))
    omega

end Lax185574Proofs.ResolveRam.Glue

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ResolveLift Lax3.DistFO
open Lax185574Proofs.ResolveRam.Glue Lax808846Proofs.Compile Lax185574Proofs.Words

/-- **The glue program meets `RGlueAt`** at every rank. -/
theorem rglueAt_of {kG : ℕ} (hKq : kq0 ≤ kG) (hk0 : 4 * k0 + 64 ≤ kG) (eS eF eC eK eT D : ℕ)
    (hD : guardBits glueLay + 6 + 4 ≤ D) (k q : ℕ) :
    ∃ cG aG : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
      RGlueAt G k q (rgProg kG eS eF eC eK eT (2 * D + 20)) (guardBits glueLay + 6) (2 * D + 20)
        eS eF eC eK eT cG aG P Q s := by
  by_cases hk : 1 ≤ k
  swap
  · exact ⟨0, 0, fun _ _ _ _ _ h => absurd h hk⟩
  obtain ⟨C, A, hKit⟩ := szKit k q hk
  obtain ⟨Cs, As, cS, hR1⟩ := round1 k q hk
  obtain ⟨Cf, Af, hFin⟩ := tFin_le k q hk
  obtain ⟨Cc, Ac, hSum⟩ := time_sum k q hk
  obtain ⟨Ch, Ah, hHead⟩ := heads_clause k q hk
  set sQ := 2 * D + 20 with hsQ
  set a := aOf (kqOf atCmd_spec atKeep_atV C k q) Cs Cf kG (eS + eF + eC + eK + eT) sQ k q
  set b := 2 * A * (aPc atCmd_spec atKeep_atV + 1) + As + Af + 1
  set cG := a * (Cc + 3) + Ch + 2 * 2 ^ ((eS + eF + eC + eK + eT) + 1) + kG + 5 +
    2 ^ 24 * (rhoPlus (k + 1) q + 2) ^ 4 * (cS ^ 2 + 100 ^ 2 + 72 ^ 2) with hcG
  refine ⟨cG, b + Ac + Ah, fun n G P Q s _ => ⟨?_⟩⟩
  have hrs : guardBits glueLay + 11 ≤ sQ := by omega
  have hround : ∀ j, ∃ t, (j ≤ (rcalls G P Q s k q).length →
      ClauseAt G P Q s k q (rgProg kG eS eF eC eK eT sQ) (guardBits glueLay + 6) sQ eS eF eC eK eT cG
        ((eS + eF + eC + eK + eT) + 2) t j ∧
      t ≤ (if j ≤ 1 ∨ j = (rcalls G P Q s k q).length then
          a * (n + 1) * (n + 1) * yQ G P Q s k q ^ b else 0) +
        a * (n + 1) * yQ G P Q s k q ^ b) := by
    intro j
    by_cases hj : j ≤ (rcalls G P Q s k q).length
    · obtain ⟨t, h1, h2⟩ := round_le G P Q s k q hk hKit
        (fun K eS eF eC eK eT sQ cG E n G P Q s => hR1 K eS eF eC eK eT sQ cG E n G P Q s) hFin
        hKq hk0 (eS := eS) (eF := eF) (eC := eC) (eK := eK) (eT := eT) (cG := cG) hrs (by omega) (by omega) hj
      exact ⟨t, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose tG htG using hround
  refine ⟨hdJ G P Q s k q, tG, fun j _ => hdJ_shape G P Q s k q j, ?_, fun j hj => ?_, fun j hj => (htG j hj).1⟩
  · refine le_trans (hSum n G P Q s tG a b fun j hj => ?_) (rBound_mono G k q P Q s (by omega) (by omega))
    have := (htG j hj).2
    simpa [yQ] using this
  · refine le_trans (hHead n G P Q s j hj) (Nat.mul_le_mul (by omega) (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))) _))

/-- **The hypothesis on the glue program holds.** -/
theorem rglueHyp : RGlueHyp := by
  obtain ⟨kG, hKq, hk0⟩ := exists_kG
  exact ⟨guardBits glueLay + 6, fun eS eF eC eK eT D hD =>
    ⟨rgProg kG eS eF eC eK eT (2 * D + 20), fun k q => rglueAt_of hKq hk0 eS eF eC eK eT D hD k q⟩⟩

end Lax185574Proofs.ResolveRam
