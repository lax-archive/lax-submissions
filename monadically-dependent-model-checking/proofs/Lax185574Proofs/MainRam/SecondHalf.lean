import Lax185574Proofs.MainRam.Instances

/-!
The second half of a thread, forwards. Given any word `y` written by
the first half, the second half clips it, validates it, and runs the
model-checking program on the instance written by the validation. If
that program halts with an answer `b ≤ 1`, the second half halts with
the flag of the validation and `b`.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim
open Lax3.FirstOrder Lax271696.GraphEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionSequences Lax185574.PartialGraphs Lax185574.InstanceEncoding

/-- The size constant of the second half. -/
def shC (cV : ℕ) : ℕ := cV + pipeK ρid ρout + pipeK ρdrop ρW + 64

/-- The time constant of the second half. -/
def shK : ℕ := 4 * pipeK ρid ρout ^ 2 * pipeK ρdrop ρW

theorem two_pow_sub_mul {w a b : ℕ} (hab : a ≤ b) (hb : b ≤ w) :
    2 ^ (w - a) = 2 ^ (b - a) * 2 ^ (w - b) := by
  rw [← pow_add]; congr 1; omega

theorem pipeK_pos (ρ : Rewrite 1) (ρ' : Rewrite 2) : 1 ≤ pipeK ρ ρ' := by
  simp only [pipeK]; omega

/-- **The second half forwards.** -/
theorem secondHalf_run {Cl V M Wr : Program} {cC cV cW : ℕ}
    (hCl : ClipSpec Cl cC) (hV : ValidSpec V cV) (hWr : WrapSpec Wr cW)
    {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G) (φ : FO 0)
    (y : List ℕ) (w : ℕ) (hw : 10 ≤ w)
    (hbig : shC cV * (y.length + (g ++ toWord φ).length + 8) ^ 2 ≤ 2 ^ (w - 6))
    {b tM : ℕ} (hb : b ≤ 1)
    (hM : RunsTo (w - 6) M
      (mcIn n G φ g (clipY (w - 2) (y.length + (g ++ toWord φ).length + 2) y)) [b] tM) :
    ∃ t ≤ shK * (cC * (y.length + (g ++ toWord φ).length + 3) +
        cV * ((y.length + 1) * (n + 1) ^ 2 + (g ++ toWord φ).length + 1) + tM + cW + 20),
      RunsTo w (secondHalf Cl V M Wr)
        (y.length :: ((g ++ toWord φ).length + 1) :: (y ++ (g ++ toWord φ)))
        [vFlag n G (clipY (w - 2) (y.length + (g ++ toWord φ).length + 2) y), b] t := by
  set x := g ++ toWord φ with hx
  set L := y.length + x.length + 2 with hL
  set y' := clipY (w - 2) L y with hy'
  set u := y.length :: (x.length + 1) :: (y ++ x) with hu
  set u' := y.length :: (x.length + 1) :: (y' ++ x) with hu'
  set f := vFlag n G y' with hf
  have hy'l : y'.length = y.length := clipY_length _ _ _
  have hxl : x.length = g.length + (toWord φ).length := by simp [hx]
  have hul : u.length = L := by simp [hu, hL] <;> omega
  have hu'l : u'.length = L := by simp [hu', hL, hy'l] <;> omega
  set S := y.length + x.length + 8 with hS
  obtain ⟨V6, hV6⟩ : ∃ V6, V6 = 2 ^ (w - 6) := ⟨_, rfl⟩
  have e4 : 2 ^ (w - 4) = 4 * V6 := by
    rw [hV6, two_pow_sub_mul (show 4 ≤ 6 by omega) (by omega)]; norm_num
  have e2 : 2 ^ (w - 2) = 16 * V6 := by
    rw [hV6, two_pow_sub_mul (show 2 ≤ 6 by omega) (by omega)]; norm_num
  have e0 : 2 ^ w = 64 * V6 := by
    rw [hV6, show 2 ^ w = 2 ^ (w - 0) by simp, two_pow_sub_mul (show 0 ≤ 6 by omega) (by omega)]
    norm_num
  rw [← hV6] at hbig
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) S
  have hK1 := pipeK_pos ρid ρout
  have hK2 := pipeK_pos ρdrop ρW
  have hcS : shC cV * S ≤ V6 := le_trans (Nat.mul_le_mul_left _ hSS) hbig
  have hshC : 64 ≤ shC cV := by simp only [shC]; omega
  have hSV : 64 * S ≤ V6 := le_trans (Nat.mul_le_mul_right _ hshC) hcS
  have hKV1 : pipeK ρid ρout ≤ V6 := by
    have : pipeK ρid ρout ≤ shC cV := by simp only [shC]; omega
    have : shC cV ≤ shC cV * S := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hKV2 : pipeK ρdrop ρW ≤ V6 := by
    have : pipeK ρdrop ρW ≤ shC cV := by simp only [shC]; omega
    have : shC cV ≤ shC cV * S := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hxe := instance_entries_le hg φ
  -- clipping
  obtain ⟨tC, htC, hrC⟩ := hCl (w - 2) u (by omega) (by rw [hul, e2]; omega)
  have hclip : clipList (w - 2) u = u' := by
    rw [hu, clipList_input (v := w - 2) (y := y) (x := x) (by rw [e2]; omega) (by rw [e2]; omega)
      hxe]
    rfl
  rw [hclip] at hrC
  -- validation
  have hvB : cV * (y'.length + x.length + 2) ^ 2 ≤ 2 ^ (w - 4) := by
    rw [hy'l, e4]
    have h1 : (y.length + x.length + 2) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : cV ≤ shC cV := by simp only [shC]; omega
    calc cV * (y.length + x.length + 2) ^ 2 ≤ shC cV * S ^ 2 := Nat.mul_le_mul h2 h1
      _ ≤ V6 := hbig
      _ ≤ 4 * V6 := by omega
  obtain ⟨tV, htV, hrV⟩ := hV (w - 4) n G φ g y' hg (fun a ha => by
    have := clipY_le a ha; rw [hy'l]; omega) hvB
  rw [hy'l, ← hu'] at hrV
  rw [vOut_eq] at hrV
  -- the last quarter
  have hml := mcIn_length_le n G φ g y'
  rw [hy'l] at hml
  obtain ⟨tW, htW, hrW⟩ := hWr (w - 6) f b (by omega) (vFlag_le _ _ _) hb
  have e64 : w - 4 - 2 = w - 6 := by omega
  have hLQ := pipe_fwd M Wr ρdrop ρW (w - 4) (f :: mcIn n G φ g y') [b] [f, b] tM tW
    (by rw [e64, ← hV6]; exact hKV2) (by rw [e64, ← hV6]; simp; omega)
    (ρdrop_fits (by omega) (by rw [e4]; simp; omega))
    (ρW_fits (by omega) (by rw [e4]; simp; omega) (by rw [e4]; omega))
    (by rw [e64, ρdrop_apply]; exact hM)
    (by rw [e64, ρW_apply]; exact hrW)
  obtain ⟨tL, htL, hrL⟩ := hLQ
  rw [ρdrop_cost, ρW_cost] at htL
  -- the second quarter
  have e42 : w - 2 - 2 = w - 4 := by omega
  obtain ⟨tQ, htQ, hrQ⟩ := pipe_fwd V (lastQuarter M Wr) ρid ρout (w - 2) u'
    (f :: mcIn n G φ g y') [f, b] tV tL
    (by rw [e42, e4]; omega) (by rw [e42, e4]; simp; omega)
    (ρid_fits (by rw [hu'l, e2]; omega))
    (ρout_fits (by rw [e2]; simp; omega) (by rw [hu'l, e2]; omega))
    (by rw [e42, ρid_apply]; exact hrV)
    (by rw [e42, ρout_apply]; exact hrL)
  rw [ρid_cost, ρout_cost] at htQ
  -- the second half
  obtain ⟨t, ht, hr⟩ := pipe_fwd Cl (secondQuarter V M Wr) ρid ρout w u u' [f, b] tC tQ
    (by rw [e2]; omega) (by rw [hu'l, e2]; omega)
    (ρid_fits (by rw [hul, e0]; omega))
    (ρout_fits (by rw [hu'l, e0]; omega) (by rw [hul, e0]; omega))
    (by rw [ρid_apply]; exact hrC)
    (by rw [ρout_apply]; exact hrQ)
  rw [ρid_cost, ρout_cost] at ht
  refine ⟨t, ?_, hr⟩
  -- the time
  rw [hul] at htC
  set A := pipeK ρid ρout
  set A' := pipeK ρdrop ρW
  set Z := cC * (y.length + x.length + 3) +
    cV * ((y.length + 1) * (n + 1) ^ 2 + x.length + 1) + tM + cW + 20
  have hZ1 : tC + 6 ≤ Z := by
    have : cC * (L + 1) = cC * (y.length + x.length + 3) := by rw [hL]
    omega
  have hZ2 : tV ≤ Z := by rw [hy'l, ← hx] at htV; omega
  have hZ3 : tM + tW + 8 ≤ Z := by omega
  have hL' : tL ≤ A' * Z := le_trans htL (Nat.mul_le_mul_left _ (by omega))
  have hQ' : tQ ≤ A * (Z + A' * Z + 6) := le_trans htQ (Nat.mul_le_mul_left _ (by omega))
  have hZ6 : 6 ≤ Z := by omega
  have hAZ : Z ≤ A' * Z := Nat.le_mul_of_pos_left _ (by omega)
  have h1 : A * (Z + A' * Z + 6) ≤ A * (3 * A' * Z) := by
    apply Nat.mul_le_mul_left
    have : 3 * A' * Z = A' * Z + A' * Z + A' * Z := by ring
    omega
  have h2 : t ≤ A * (tC + tQ + 6) := ht
  show t ≤ (4 * A ^ 2 * A') * Z
  have h3 : A * (tC + tQ + 6) ≤ A * (Z + A * (3 * A' * Z)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : A * Z ≤ A ^ 2 * A' * Z := by
    have : A ≤ A ^ 2 * A' := by
      rw [pow_two]
      calc A = A * 1 * 1 := by ring
        _ ≤ A * A * A' := Nat.mul_le_mul (Nat.mul_le_mul_left _ hK1) hK2
    exact Nat.mul_le_mul_right _ this
  have h5 : A * (Z + A * (3 * A' * Z)) = A * Z + 3 * (A ^ 2 * A' * Z) := by ring
  have h6 : 4 * A ^ 2 * A' * Z = 4 * (A ^ 2 * A' * Z) := by ring
  omega

end Lax185574Proofs.MainRam
