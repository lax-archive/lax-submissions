import Lax185574Proofs.ResolveRam.Run
import Lax185574Proofs.ResolveRam.SizeSpec
import Lax185574Proofs.ResolveRam.SoundAdm

/-!
Halting of the composite of lem:resolve-lift within its time bound, the
second clause of `Computes`.

Write `X` for the size of the input and `Y = M + T + 1`. Every quantity
that the rounds need room for is at most a constant times `X ^ α` times
`Y ^ β` (`PB`), where `α` depends only on the literal exponents and `β`
may depend on the rank. Admissibility gives `c X ^ e ≤ 2 ^ w` and the
time bound gives `c Y ^ a ≤ 2 ^ w`, so their product bounds the square
of the room that the regions need once `e ≥ 2 α` and `a ≥ 2 β`. Then
`resolve_run` applies, and its time is at most the bound of
lem:resolve-lift.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim

/-! ### Polynomial bounds in two variables -/

/-- `u ≤ K X ^ α Y ^ β`. -/
def PB (X Y K α β u : ℕ) : Prop := u ≤ K * X ^ α * Y ^ β

section PB

variable {X Y : ℕ}

theorem PB.mono {K α β u v : ℕ} (h : PB X Y K α β v) (huv : u ≤ v) : PB X Y K α β u :=
  le_trans huv h

theorem PB.le (hX : 1 ≤ X) (hY : 1 ≤ Y) {K α β K' α' β' u : ℕ} (h : PB X Y K α β u) (hK : K ≤ K')
    (ha : α ≤ α') (hb : β ≤ β') : PB X Y K' α' β' u := by
  unfold PB at *
  refine le_trans h ?_
  have h1 : X ^ α ≤ X ^ α' := Nat.pow_le_pow_right hX ha
  have h2 : Y ^ β ≤ Y ^ β' := Nat.pow_le_pow_right hY hb
  calc K * X ^ α * Y ^ β ≤ K' * X ^ α' * Y ^ β' := by gcongr

theorem PB.add {K₁ K₂ α β u v : ℕ} (h₁ : PB X Y K₁ α β u) (h₂ : PB X Y K₂ α β v) :
    PB X Y (K₁ + K₂) α β (u + v) := by
  unfold PB at *
  calc u + v ≤ K₁ * X ^ α * Y ^ β + K₂ * X ^ α * Y ^ β := Nat.add_le_add h₁ h₂
    _ = (K₁ + K₂) * X ^ α * Y ^ β := by ring

theorem PB.mul {K₁ K₂ α₁ β₁ α₂ β₂ u v : ℕ} (h₁ : PB X Y K₁ α₁ β₁ u) (h₂ : PB X Y K₂ α₂ β₂ v) :
    PB X Y (K₁ * K₂) (α₁ + α₂) (β₁ + β₂) (u * v) := by
  unfold PB at *
  calc u * v ≤ (K₁ * X ^ α₁ * Y ^ β₁) * (K₂ * X ^ α₂ * Y ^ β₂) := Nat.mul_le_mul h₁ h₂
    _ = (K₁ * K₂) * X ^ (α₁ + α₂) * Y ^ (β₁ + β₂) := by ring

theorem PB.pow {K α β u : ℕ} (h : PB X Y K α β u) (m : ℕ) :
    PB X Y (K ^ m) (α * m) (β * m) (u ^ m) := by
  unfold PB at *
  calc u ^ m ≤ (K * X ^ α * Y ^ β) ^ m := Nat.pow_le_pow_left h m
    _ = K ^ m * X ^ (α * m) * Y ^ (β * m) := by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]

theorem PB.const {K : ℕ} : PB X Y K 0 0 K := by unfold PB; simp

theorem PB.x : PB X Y 1 1 0 X := by unfold PB; simp

theorem PB.y : PB X Y 1 0 1 Y := by unfold PB; simp

end PB

/-! ### Facts about the input -/

theorem maxEntry_mem {x : List ℕ} (hx : x ≠ []) : maxEntry x ∈ x := by
  induction x with
  | nil => exact absurd rfl hx
  | cons a l ih =>
    show max a (maxEntry l) ∈ a :: l
    rcases l with _ | ⟨b, l⟩
    · simp [maxEntry]
    · rcases le_total a (maxEntry (b :: l)) with h | h
      · rw [max_eq_right h]; exact List.mem_cons_of_mem _ (ih (by simp))
      · rw [max_eq_left h]; exact List.mem_cons_self

theorem size_le_sq {n : ℕ} (G : PartialGraph (Fin n)) : G.size ≤ n + n ^ 2 := by
  classical
  unfold PartialGraph.size
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.resolved)
  rw [Fintype.card_fin, Nat.choose_two_right] at h1
  have h2 : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
  have h3 : n * (n - 1) ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

theorem n_lt_ySz (P Q : ℕ) (s : Bool) : n + 1 ≤ ySz (xIn G k₀ q₀ P Q s) := by
  have := le_maxEntry (mem_xIn G k₀ q₀ P Q s)
  unfold ySz; omega

theorem adm_X {e c w : ℕ} {P Q : ℕ} {s : Bool}
    (h : WordAdmissible e c w (xIn G k₀ q₀ P Q s)) : c * ySz (xIn G k₀ q₀ P Q s) ^ e ≤ 2 ^ w := by
  have hne : xIn G k₀ q₀ P Q s ≠ [] := List.ne_nil_of_mem (mem_xIn G k₀ q₀ P Q s)
  exact h _ (maxEntry_mem hne)

theorem sum_map_swT {Ks : ℕ} (cs : List RCall) :
    (cs.map fun c => Ks * (2 * realT G k₀ q₀ c + 8 * dFix + 1)).sum =
      Ks * (2 * (cs.map (realT G k₀ q₀)).sum + (8 * dFix + 1) * cs.length) := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem sum_swT (Ks : ℕ) (cs : List RCall) :
    ∑ j ∈ Finset.range cs.length, swT G k₀ q₀ Ks cs j =
      Ks * (2 * (cs.map (realT G k₀ q₀)).sum + (8 * dFix + 1) * cs.length) := by
  rw [← sum_map_swT, ← sum_range_calls (fun c => Ks * (2 * realT G k₀ q₀ c + 8 * dFix + 1)) cs]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold swT
  rcases cs[j]? with _ | c <;> rfl

theorem le_of_sq_le {Z KZ c X Y α β w : ℕ} (hZ : PB X Y KZ α β Z) (hc : KZ ≤ c)
    (h1 : c * X ^ (2 * α) ≤ 2 ^ w) (h2 : c * Y ^ (2 * β) ≤ 2 ^ w) : Z ≤ 2 ^ w := by
  unfold PB at hZ
  have hsq : Z ^ 2 ≤ (2 ^ w) ^ 2 := by
    calc Z ^ 2 ≤ (KZ * X ^ α * Y ^ β) ^ 2 := Nat.pow_le_pow_left hZ 2
      _ = (KZ * X ^ (2 * α)) * (KZ * Y ^ (2 * β)) := by ring
      _ ≤ (c * X ^ (2 * α)) * (c * Y ^ (2 * β)) := by gcongr
      _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul h1 h2
      _ = (2 ^ w) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq

theorem regions_of {Bnd D R w : ℕ} (hB : 1 ≤ Bnd)
    (h : Bnd * 2 ^ (2 * D + 20) * (2 * R + 3) ^ 2 * 8 ≤ 2 ^ w) :
    (∀ i ≤ 2 * R + 2, Bnd * 2 ^ (2 * D + 20) ≤ 2 ^ lpV w i) ∧ (2 * R + 3) ^ 2 ≤ lpCap w ∧
      8 ≤ w ∧ Bnd * 2 ^ (2 * D + 20) ≤ 2 ^ (w - 3) := by
  have hpos : 1 ≤ Bnd * 2 ^ (2 * D + 20) * (2 * R + 3) ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h3, hw3⟩ := le_pow_sub (B := Bnd * 2 ^ (2 * D + 20) * (2 * R + 3) ^ 2) (k := 3) (v := w)
    (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact h) hpos
  have hR9 : 9 ≤ (2 * R + 3) ^ 2 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left (show 3 ≤ 2 * R + 3 by omega) 2)
  have hB2 : 2 ^ (2 * D + 20) ≤ Bnd * 2 ^ (2 * D + 20) := Nat.le_mul_of_pos_left _ hB
  have hw : 8 ≤ w := by
    have h20 : 2 ^ 20 ≤ 2 ^ (w - 3) := by
      have : 2 ^ 20 ≤ 2 ^ (2 * D + 20) := two_pow_mono (by omega)
      nlinarith
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h20
    omega
  refine ⟨fun i hi => ?_, ?_, hw, ?_⟩
  · have hp := lpV_pow w i
    have hi2 : (i + 1) ^ 2 ≤ (2 * R + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact div_room hp (pow_pos (Nat.succ_pos i) 2)
      (le_trans (Nat.mul_le_mul_left _ hi2) hw3)
  · unfold lpCap
    refine le_trans ?_ hw3
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (Nat.two_pow_pos _))
  · refine le_trans ?_ hw3
    exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) 2)

/-- The exponent of the composite. -/
noncomputable def eRes : ℕ := 6 * eGl + 18

/-- The constant of the room of the rounds. -/
noncomputable def kS (C cG : ℕ) : ℕ := 8 * (2 * cG + ((C + 1) ^ 2 + 2)) + 16

noncomputable def kB (k₀ q₀ Ks C cG : ℕ) : ℕ :=
  cG * kS C cG ^ eGl + kS C cG + 2 * C + 11 * dFix + 2 + bigAll k₀ q₀ Ks

noncomputable def kZ (k₀ q₀ Ks D C cG : ℕ) : ℕ := kB k₀ q₀ Ks C cG * 2 ^ (2 * D + 23) * (2 * C + 3) ^ 2

/-- The degree of the room of the rounds in `Y`. -/
noncomputable def bZ (A aG : ℕ) : ℕ := (A + aG) * (eGl + 3)

/-- The constant of lem:resolve-lift. -/
noncomputable def cRes (k₀ q₀ Ks KL D C cG : ℕ) : ℕ :=
  kZ k₀ q₀ Ks D C cG + KL * (cG + Ks * (8 * dFix + 3) * C + 3 * C + 2) + sCst k₀ q₀ Ks D

/-- The degree of lem:resolve-lift. -/
noncomputable def aRes (A aG : ℕ) : ℕ := 2 * bZ A aG + aG + A

end Lax185574Proofs.ResolveRam
