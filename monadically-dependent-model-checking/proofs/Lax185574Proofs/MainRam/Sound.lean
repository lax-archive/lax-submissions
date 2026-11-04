import Lax185574Proofs.MainRam.SecondHalf

/-!
Soundness of a thread. Whatever its first half did, a thread that
halts with an output starting with `1` has written the right answer,
provided that its word length is large compared with its running time
and the input. The first half is opaque: only the fact that it halted
is used, through `pipe_back`. The second half also halted, and so did
the model-checking program inside it, whose output is then the answer.
With this run, the rest is our own code, so it is known forwards.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim
open Lax3.FirstOrder Lax271696.GraphEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionSequences Lax185574.PartialGraphs Lax185574.InstanceEncoding

open Classical in
/-- The answer for `G` and `φ`. -/
noncomputable def ansW {n : ℕ} (G : SimpleGraph (Fin n)) (φ : FO 0) : List ℕ :=
  if Sat G Fin.elim0 φ then [1] else [0]

open Classical in
/-- The answer as a number. -/
noncomputable def ansB {n : ℕ} (G : SimpleGraph (Fin n)) (φ : FO 0) : ℕ :=
  if Sat G Fin.elim0 φ then 1 else 0

theorem ansW_eq {n : ℕ} (G : SimpleGraph (Fin n)) (φ : FO 0) : ansW G φ = [ansB G φ] := by
  unfold ansW ansB; split_ifs <;> rfl

theorem ansB_le {n : ℕ} (G : SimpleGraph (Fin n)) (φ : FO 0) : ansB G φ ≤ 1 := by
  unfold ansB; split_ifs <;> omega

/-- Every halting run of the model-checking program on an instance on a
construction sequence outputs the answer, at every word length where the
instance is admissible for `c`. -/
def MCSound (M : Program) (φ : FO 0) (c e : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : List (PartialGraph (Fin n))) (z : List ℕ) (w : ℕ),
    IsConstructionSequence G s → Lax185574.ConstructionModelChecking.EncodesInput z n G s φ →
    (∀ a ∈ z, c * (z.length + a + 1) ^ e ≤ 2 ^ w) →
      ∀ z' t, RunsTo w M z z' t → z' = ansW G φ

/-- A halting run of the model-checking program on the instance written
by the validation outputs an answer at most one. -/
theorem mc_on_mcIn {M : Program} {φ : FO 0} {c e : ℕ} (hM : MCSound M φ c e)
    {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G) (y : List ℕ)
    (w L : ℕ) (hy : ∀ a ∈ y, a ≤ L) (hL : (g ++ toWord φ).length ≤ L)
    (hadm : c * (g.length + y.length + (toWord φ).length + 5 + L + 1) ^ e ≤ 2 ^ w)
    {zM : List ℕ} {tM : ℕ} (hrun : RunsTo w M (mcIn n G φ g y) zM tM) :
    ∃ b, b ≤ 1 ∧ RunsTo w M (mcIn n G φ g y) [b] tM ∧
      (ValidScript n G y → b = ansB G φ) := by
  have hent := mcIn_entries_le hg φ hy hL
  have hlen := mcIn_length_le n G φ g y
  have hadm' : ∀ a ∈ mcIn n G φ g y, c * ((mcIn n G φ g y).length + a + 1) ^ e ≤ 2 ^ w := by
    intro a ha
    refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) hadm
    have := hent a ha
    omega
  by_cases hv : ValidScript n G y
  · obtain ⟨s, hs, hcs, -⟩ := mcIn_valid hg φ y hv
    have hz := hM n G s _ w hcs hs hadm' zM tM hrun
    rw [ansW_eq] at hz
    subst hz
    exact ⟨_, ansB_le G φ, hrun, fun _ => rfl⟩
  · have hz := mcIn_invalid φ g y hv
    have hz' := hM 0 emptyGraph [emptyPartial] _ w dummy_isConstruction
      (by rw [hz]; exact dummy_encodes φ) hadm' zM tM hrun
    rw [ansW_eq] at hz'
    subst hz'
    exact ⟨_, ansB_le _ φ, hrun, fun h => absurd h hv⟩

/-- **The second half backwards.** A halting run of the second half
contains a halting run of the model-checking program on the instance
written by the validation. -/
theorem secondHalf_back {Cl V M Wr : Program} {cC cV : ℕ}
    (hCl : ClipSpec Cl cC) (hV : ValidSpec V cV)
    {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G) (φ : FO 0)
    (y : List ℕ) (w : ℕ) (hw : 10 ≤ w)
    (hbig : shC cV * (y.length + (g ++ toWord φ).length + 8) ^ 2 ≤ 2 ^ (w - 6))
    {z : List ℕ} {tS : ℕ}
    (hS : RunsTo w (secondHalf Cl V M Wr)
      (y.length :: ((g ++ toWord φ).length + 1) :: (y ++ (g ++ toWord φ))) z tS) :
    ∃ zM tM, RunsTo (w - 6) M
      (mcIn n G φ g (clipY (w - 2) (y.length + (g ++ toWord φ).length + 2) y)) zM tM := by
  set x := g ++ toWord φ with hx
  set L := y.length + x.length + 2 with hL
  set y' := clipY (w - 2) L y with hy'
  set u := y.length :: (x.length + 1) :: (y ++ x) with hu
  set u' := y.length :: (x.length + 1) :: (y' ++ x) with hu'
  set f := vFlag n G y' with hf
  have hy'l : y'.length = y.length := clipY_length _ _ _
  have hxl : x.length = g.length + (toWord φ).length := by simp [hx]
  have hul : u.length = L := by simp [hu, hL]
  have hu'l : u'.length = L := by simp [hu', hL, hy'l]
  set S := y.length + x.length + 8 with hSd
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
  have hB1 := pipeBase_le_pipeK ρid ρout
  have hB2 := pipeBase_le_pipeK ρdrop ρW
  have hxe := instance_entries_le hg φ
  -- clipping
  obtain ⟨tC, -, hrC⟩ := hCl (w - 2) u (by omega) (by rw [hul, e2]; omega)
  have hclip : clipList (w - 2) u = u' := by
    rw [hu, clipList_input (v := w - 2) (y := y) (x := x) (by rw [e2]; omega) (by rw [e2]; omega)
      hxe]
    rfl
  rw [hclip] at hrC
  obtain ⟨y₁, t₁, -, -, hr₁, hb₁⟩ := pipe_back Cl (secondQuarter V M Wr) ρid ρout w u z tS
    (by rw [e2]; omega) (ρid_fits (by rw [hul, e0]; omega)) hS
  rw [ρid_apply] at hr₁
  obtain ⟨rfl, -⟩ := runsTo_unique hr₁ hrC
  obtain ⟨tQ, -, hrQ⟩ := hb₁ (ρout_fits (by rw [hu'l, e0]; omega) (by rw [hul, e0]; omega))
  rw [ρout_apply] at hrQ
  -- validation
  have hvB : cV * (y'.length + x.length + 2) ^ 2 ≤ 2 ^ (w - 4) := by
    rw [hy'l, e4]
    have h1 : (y.length + x.length + 2) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : cV ≤ shC cV := by simp only [shC]; omega
    calc cV * (y.length + x.length + 2) ^ 2 ≤ shC cV * S ^ 2 := Nat.mul_le_mul h2 h1
      _ ≤ V6 := hbig
      _ ≤ 4 * V6 := by omega
  obtain ⟨tV, -, hrV⟩ := hV (w - 4) n G φ g y' hg (fun a ha => by
    have := clipY_le a ha; rw [hy'l]; omega) hvB
  rw [hy'l, ← hu'] at hrV
  rw [vOut_eq] at hrV
  have hml := mcIn_length_le n G φ g y'
  rw [hy'l] at hml
  have e42 : w - 2 - 2 = w - 4 := by omega
  obtain ⟨y₂, t₂, -, -, hr₂, hb₂⟩ := pipe_back V (lastQuarter M Wr) ρid ρout (w - 2) u' z tQ
    (by rw [e42, e4]; omega) (ρid_fits (by rw [hu'l, e2]; omega)) hrQ
  rw [ρid_apply, e42] at hr₂
  obtain ⟨rfl, -⟩ := runsTo_unique hr₂ hrV
  obtain ⟨tL, -, hrL⟩ := hb₂ (ρout_fits (by rw [e2]; simp; omega) (by rw [hu'l, e2]; omega))
  rw [ρout_apply, e42] at hrL
  -- the model-checking program
  have e64 : w - 4 - 2 = w - 6 := by omega
  obtain ⟨zM, tM, -, -, hrM, -⟩ := pipe_back M Wr ρdrop ρW (w - 4) (f :: mcIn n G φ g y') z tL
    (by rw [e64, ← hV6]; omega) (ρdrop_fits (by omega) (by rw [e4]; simp; omega)) hrL
  rw [ρdrop_apply, e64] at hrM
  exact ⟨zM, tM, hrM⟩

/-- The size constant of a thread. -/
def thC (cV : ℕ) : ℕ := shC cV + pipeK ρid ρQ

/-- **Soundness of a thread.** -/
theorem thread_sound {U FT Cl V M Wr : Program} {cC cV cW : ℕ} {φ : FO 0} {c₂ e₂ : ℕ}
    (hCl : ClipSpec Cl cC) (hV : ValidSpec V cV) (hWr : WrapSpec Wr cW) (hM : MCSound M φ c₂ e₂)
    {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G)
    (i wQ t' : ℕ) (y' : List ℕ) (hw : 12 ≤ wQ)
    (hbig : thC cV * (t' + (g ++ toWord φ).length + 10) ^ 2 ≤ 2 ^ (wQ - 8))
    (hmc : c₂ * (2 * (t' + (g ++ toWord φ).length) + 12) ^ e₂ ≤ 2 ^ (wQ - 8))
    (hR : RunsTo wQ (threadProg U FT Cl V M Wr) (i :: (g ++ toWord φ)) (1 :: y') t') :
    y' = [ansB G φ] := by
  set x := g ++ toWord φ with hx
  have hxl : x.length = g.length + (toWord φ).length := by simp [hx]
  obtain ⟨V8, hV8⟩ : ∃ V8, V8 = 2 ^ (wQ - 8) := ⟨_, rfl⟩
  have e2 : 2 ^ (wQ - 2) = 64 * V8 := by
    rw [hV8, two_pow_sub_mul (show 2 ≤ 8 by omega) (by omega)]; norm_num
  have e0 : 2 ^ wQ = 256 * V8 := by
    rw [hV8, show 2 ^ wQ = 2 ^ (wQ - 0) by simp, two_pow_sub_mul (show 0 ≤ 8 by omega) (by omega)]
    norm_num
  rw [← hV8] at hbig hmc
  set S := t' + x.length + 10 with hS
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) S
  have hthC : 64 ≤ thC cV := by simp only [thC, shC]; omega
  have hSV : 64 * S ≤ V8 := le_trans (Nat.mul_le_mul hthC hSS) hbig
  have hKQ : pipeK ρid ρQ ≤ V8 := by
    have : pipeK ρid ρQ ≤ thC cV := by simp only [thC]; omega
    have : thC cV ≤ thC cV * S ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  -- the first half halted
  obtain ⟨y, t₁, ht₁, -, hr₁, hb₁⟩ := pipe_back (firstHalf U FT) (secondHalf Cl V M Wr) ρid ρQ wQ
    (i :: x) (1 :: y') t' (by rw [e2]; have := pipeBase_le_pipeK ρid ρQ; omega)
    (ρid_fits (by rw [e0]; simp; omega)) hR
  rw [ρid_apply] at hr₁
  have hyl : y.length ≤ t' + 2 := le_trans (runsTo_out_length hr₁) (by omega)
  -- the model-checking program on the validated instance
  set v := wQ - 2 with hv
  set L := y.length + x.length + 2 with hL
  set y'' := clipY (v - 2) L y with hy''
  have hy''l : y''.length = y.length := clipY_length _ _ _
  have ev : v - 6 = wQ - 8 := by omega
  have hbig' : shC cV * (y.length + x.length + 8) ^ 2 ≤ 2 ^ (v - 6) := by
    rw [ev, ← hV8]
    have h1 : (y.length + x.length + 8) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : shC cV ≤ thC cV := by simp only [thC]; omega
    exact le_trans (Nat.mul_le_mul h2 h1) hbig
  -- the second half halted, and with it the model-checking program
  obtain ⟨tS', -, hrS'⟩ := hb₁ (ρQ_fits (by omega) (by rw [e0]; omega))
  rw [ρQ_apply] at hrS'
  obtain ⟨zM, tM, hrM'⟩ := secondHalf_back hCl hV hg φ y v (by omega) hbig' hrS'
  obtain ⟨b, hb, hrM, hbv⟩ := mc_on_mcIn hM hg y'' (v - 6) L clipY_le
      (by rw [← hx]; omega) (by
    rw [ev, ← hV8, hy''l]
    refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) hmc
    omega) hrM'
  -- the second half forwards
  obtain ⟨tS, -, hrS⟩ := secondHalf_run hCl hV hWr hg φ y v (by omega) hbig' hb hrM
  -- the thread runs to the flag and the answer
  have e22 : wQ - 2 = v := rfl
  obtain ⟨T, -, hrT⟩ := pipe_fwd (firstHalf U FT) (secondHalf Cl V M Wr) ρid ρQ wQ (i :: x) y
    [vFlag n G y'', b] t₁ tS (by rw [e2]; omega) (by rw [e2]; omega)
    (ρid_fits (by rw [e0]; simp; omega)) (ρQ_fits (by omega) (by rw [e0]; omega))
    (by rw [ρid_apply]; exact hr₁)
    (by rw [ρQ_apply]; exact hrS)
  obtain ⟨heq, -⟩ := runsTo_unique hR hrT
  simp only [List.cons.injEq] at heq
  obtain ⟨hf, rfl⟩ := heq
  have hval : ValidScript n G y'' := by
    by_contra h
    unfold vFlag at hf
    rw [if_neg h] at hf
    omega
  rw [hbv hval]

end Lax185574Proofs.MainRam
