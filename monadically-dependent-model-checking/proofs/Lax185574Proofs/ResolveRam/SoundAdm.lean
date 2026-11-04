import Lax185574Proofs.ResolveRam.Sound
import Lax185574Proofs.ResolveRam.Count

/-!
Soundness of the composite at every word length at which the input is
admissible for the constant `sCst`.

If the input is at least `bigAll`, the guards give room. Otherwise
`|G| ≤ bigAll`, so the number of calls is at most
`callMax k₀ q₀ bigAll`, and every region up to the last round has room
for the constants by `lpV_pow`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim

/-- The constant of soundness. -/
noncomputable def sCst (k₀ q₀ Ks D : ℕ) : ℕ :=
  2 ^ (2 * D + 33) * bigAll k₀ q₀ Ks * (2 * callMax k₀ q₀ (bigAll k₀ q₀ Ks) + 3) ^ 2

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

theorem mem_xIn (P Q : ℕ) (s : Bool) : n ∈ xIn G k₀ q₀ P Q s := by
  simp [xIn, word_simps]

theorem div_room {N A B V : ℕ} (hp : A ≤ V * B) (hB : 0 < B) (hN : N * B ≤ A) : N ≤ V :=
  Nat.le_of_mul_le_mul_right (le_trans hN hp) hB

set_option maxHeartbeats 1000000 in
/-- **Soundness at admissible word lengths.** -/
theorem resolve_sound_adm {Gp sw P0 : Program} {sI D Ks KL cG aG : ℕ}
    (hsw : Sw5Spec sw Ks D pSh pFt pCo pCa pSt) (hP0 : LoopSpec P0 Gp sw KL) (hD : sI + 4 ≤ D)
    {P Q : ℕ} {s : Bool} (hk : 1 ≤ k₀)
    (hgl : RGlueAt G k₀ q₀ Gp sI (2 * D + 20) eSh eFt eCo eCa eSt cG aG P Q s)
    {w : ℕ} (hadm : sCst k₀ q₀ Ks D * ySz (xIn G k₀ q₀ P Q s) ≤ 2 ^ w) :
    ∀ z t, RunsTo w P0 (xIn G k₀ q₀ P Q s) z t → z = zOut G k₀ q₀ P Q s := by
  set x := xIn G k₀ q₀ P Q s with hxd
  set X := ySz x with hXd
  set Bg := bigAll k₀ q₀ Ks with hBg
  set Rb := callMax k₀ q₀ Bg with hRb
  have hX1 : 1 ≤ X := by simp only [hXd, ySz]; omega
  have hBg1 : 1 ≤ Bg := by simp only [hBg, bigAll]; omega
  have hS : 2 ^ 3 * (2 ^ (2 * D + 30) * Bg * (2 * Rb + 3) ^ 2 * X) ≤ 2 ^ w := by
    refine le_trans (le_of_eq ?_) hadm
    simp only [sCst, ← hBg, ← hRb]
    rw [show 2 * D + 33 = 3 + (2 * D + 30) by omega, pow_add]; ring
  have hpos : 1 ≤ 2 ^ (2 * D + 30) * Bg * (2 * Rb + 3) ^ 2 * X :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h3w, hw3⟩ := le_pow_sub (by rw [mul_comm] at hS; exact hS) hpos
  have hR9 : 9 ≤ (2 * Rb + 3) ^ 2 := by nlinarith
  have hbig : X * 2 ^ (2 * D + 30) * 9 ≤ 2 ^ (w - 3) := by
    refine le_trans ?_ hw3
    calc X * 2 ^ (2 * D + 30) * 9 ≤ X * 2 ^ (2 * D + 30) * (Bg * (2 * Rb + 3) ^ 2) :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have hw : 2 * D + 33 ≤ w := by
    have : 2 ^ (2 * D + 30) ≤ 2 ^ (w - 3) := by nlinarith
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
    omega
  have hx : x.length < 2 ^ (w - 1) := by
    have h1 : x.length < X := by simp only [hXd, ySz]; omega
    have h2 : X ≤ 2 ^ (w - 3) := by nlinarith [Nat.one_le_two_pow (n := 2 * D + 30)]
    exact lt_of_lt_of_le h1 (le_trans h2 (two_pow_mono (by omega)))
  have h0 : X * 2 ^ (2 * D + 20) ≤ 2 ^ lpV w 0 := by
    have := lpV_pow w 0
    simp only [zero_add, one_pow, mul_one] at this
    refine le_trans ?_ this
    refine le_trans (Nat.mul_le_mul_left _ (two_pow_mono (show 2 * D + 20 ≤ 2 * D + 30 by omega))) ?_
    omega
  refine resolve_sound G k₀ q₀ hsw hP0 hD hk hgl (by omega) hx h0 ?_
  rcases le_or_gt Bg X with h | h
  · exact Or.inl h
  · right
    have hn : n ≤ Bg := by
      have h1 : n ≤ maxEntry x := le_maxEntry (mem_xIn G k₀ q₀ P Q s)
      have h2 : maxEntry x < X := by simp only [hXd, ySz]; omega
      omega
    have hR := le_trans (length_rcalls_le G P Q s k₀ q₀ hk) (callMax_mono k₀ q₀ hn)
    generalize (rcalls G P Q s k₀ q₀).length = R at hR ⊢
    intro i hi
    have hp := lpV_pow w i
    have hi2 : (i + 1) ^ 2 ≤ (2 * Rb + 3) ^ 2 := Nat.pow_le_pow_left (by rw [← hRb] at hR; omega) 2
    have hipos : 0 < (i + 1) ^ 2 := pow_pos (Nat.succ_pos i) 2
    have key : ∀ N, N * (2 * Rb + 3) ^ 2 ≤ 2 ^ (w - 3) → N ≤ 2 ^ lpV w i := fun N hN =>
      div_room hp hipos (le_trans (Nat.mul_le_mul_left N hi2) hN)
    refine ⟨key (Bg * 2 ^ (2 * D + 30)) ?_, key (X * 2 ^ (2 * D + 20)) ?_⟩
    · refine le_trans ?_ hw3
      calc Bg * 2 ^ (2 * D + 30) * (2 * Rb + 3) ^ 2 ≤
            Bg * 2 ^ (2 * D + 30) * (2 * Rb + 3) ^ 2 * X := Nat.le_mul_of_pos_right _ hX1
        _ = _ := by ring
    · refine le_trans ?_ hw3
      calc X * 2 ^ (2 * D + 20) * (2 * Rb + 3) ^ 2 ≤
            Bg * 2 ^ (2 * D + 30) * (2 * Rb + 3) ^ 2 * X := by
            have e1 : 2 ^ (2 * D + 20) ≤ 2 ^ (2 * D + 30) := two_pow_mono (by omega)
            have e2 : 2 ^ (2 * D + 20) ≤ Bg * 2 ^ (2 * D + 30) :=
              le_trans e1 (Nat.le_mul_of_pos_left _ hBg1)
            calc X * 2 ^ (2 * D + 20) * (2 * Rb + 3) ^ 2
                ≤ X * (Bg * 2 ^ (2 * D + 30)) * (2 * Rb + 3) ^ 2 :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ e2)
              _ = Bg * 2 ^ (2 * D + 30) * (2 * Rb + 3) ^ 2 * X := by ring
        _ = _ := by ring

end Lax185574Proofs.ResolveRam
