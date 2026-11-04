import Lax185574Proofs.MC.Asm.Sound

/-!
The regions of the loop driver are large at admissible word lengths.

`regions_big`: if `2 ^ (D + 30 + sI) · B · (|x| + max x + 1) ^ 5 ≤ 2 ^ w`
and the number of calls is at most `(|x| + 1) ^ 2`, then every region
that a run of the pipeline uses has room for `B · 2 ^ (D + 20)` and for
`(|x| + max x + 1) · 2 ^ sI`, which is what `pipe_sound` needs.
`script_length`: the word of a script with `m` steps on `n` vertices
has length `n + 3 m + 2`, so the number of calls is at most
`(|x| + 1) ^ 2`.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences

theorem regions_big {B D sI w R : ℕ} {x : List ℕ} (hB : 1 ≤ B) (hR : R ≤ (x.length + 1) ^ 2)
    (h : 2 ^ (D + 30 + sI) * B * (x.length + maxEntry x + 1) ^ 5 ≤ 2 ^ w) :
    8 ≤ w ∧ x.length < 2 ^ (w - 1) ∧ ∀ i ≤ 2 * R + 2,
      B * 2 ^ (D + 20) ≤ 2 ^ lpV w i ∧ (x.length + maxEntry x + 1) * 2 ^ sI ≤ 2 ^ lpV w i := by
  have hP : 2 ^ (D + 30 + sI) = 2 ^ (D + 20) * 2 ^ sI * 1024 := by
    rw [show D + 30 + sI = (D + 20) + sI + 10 by omega, pow_add, pow_add]; norm_num
  rw [hP] at h
  have hR' : R ≤ (x.length + maxEntry x + 1) ^ 2 :=
    le_trans hR (Nat.pow_le_pow_left (by omega) _)
  have hxX : x.length + 1 ≤ (x.length + maxEntry x + 1) ^ 5 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have ha : 1 ≤ 2 ^ (D + 20) := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ sI := Nat.one_le_two_pow
  have hX1 : 1 ≤ x.length + maxEntry x + 1 := by omega
  generalize 2 ^ (D + 20) = a at h ha ⊢
  generalize 2 ^ sI = b at h hb ⊢
  generalize x.length + maxEntry x + 1 = X at h hR' hxX hX1 ⊢
  have hX2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX1
  have hab : 1 ≤ a * b * B := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hA : 1024 * X ^ 5 ≤ 2 ^ w :=
    le_trans (by nlinarith [Nat.zero_le (X ^ 5)]) h
  have hw : 10 ≤ w := by
    have : 2 ^ 10 ≤ 2 ^ w := le_trans (by nlinarith [Nat.one_le_pow 5 X hX1]) hA
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have h2w : 2 ^ w = 8 * 2 ^ (w - 3) := by
    rw [show w = (w - 3) + 3 by omega, pow_add]; simp; ring
  have h2w' : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [show w = (w - 1) + 1 by omega, pow_add]; simp; ring
  refine ⟨by omega, by omega, fun i hi => ?_⟩
  have hi1 : i + 1 ≤ 5 * X ^ 2 := by omega
  have hi2 : (i + 1) ^ 2 ≤ 25 * X ^ 4 := by
    calc (i + 1) ^ 2 ≤ (5 * X ^ 2) ^ 2 := Nat.pow_le_pow_left hi1 2
      _ = 25 * X ^ 4 := by ring
  have hN : B * a + X * b ≤ 2 * (a * b * B) * X := by
    have hbX : 1 ≤ b * X := Nat.one_le_iff_ne_zero.2 (by positivity)
    have haB : 1 ≤ a * B := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e1 : B * a ≤ (a * B) * (b * X) := by
      calc B * a = (a * B) * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hbX
    have e2 : X * b ≤ (b * X) * (a * B) := by
      calc X * b = (b * X) * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ haB
    have e3 : (a * B) * (b * X) = a * b * B * X := by ring
    have e4 : (b * X) * (a * B) = a * b * B * X := by ring
    have e5 : 2 * (a * b * B) * X = 2 * (a * b * B * X) := by ring
    omega
  have hV := lpV_pow w i
  have key : (B * a + X * b) * (i + 1) ^ 2 ≤ 2 ^ (w - 3) := by
    calc (B * a + X * b) * (i + 1) ^ 2 ≤ (2 * (a * b * B) * X) * (25 * X ^ 4) :=
          Nat.mul_le_mul hN hi2
      _ = 50 * (a * b * B * X ^ 5) := by ring
      _ ≤ 2 ^ (w - 3) := by
        have e : a * b * 1024 * B * X ^ 5 = 1024 * (a * b * B * X ^ 5) := by ring
        omega
  have : B * a + X * b ≤ 2 ^ lpV w i :=
    Nat.le_of_mul_le_mul_right (le_trans key hV) (by positivity)
  constructor <;> nlinarith

/-- The length of the word of a script. -/
theorem script_length {n : ℕ} (σ : Script n) :
    (toWord σ).length = n + 3 * σ.steps.length + 2 := by
  have h1 : (toWord σ.colors).length = n + 1 := by
    show ((List.ofFn σ.colors).map (toWord : ℕ → List ℕ)).flatten.length + 1 = n + 1
    have : ∀ l : List ℕ, ((l.map (toWord : ℕ → List ℕ)).flatten).length = l.length := by
      intro l; induction l <;> simp_all [word_simps]
    rw [this, List.length_ofFn]
  have h2 : ∀ l : List Step, (toWord l).length = 3 * l.length + 1 := by
    intro l
    show ((l.map toWord).flatten).length + 1 = _
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
      have : (toWord a).length = 3 := by cases a <;> rfl
      omega
  show (toWord σ.colors ++ toWord σ.steps).length = _
  rw [List.length_append, h1, h2]; ring

theorem calls_le_input {n : ℕ} (g : List ℕ) (σ : Script n) (y : List ℕ) :
    (pcalls n σ.steps).length ≤ ((g ++ toWord σ ++ y).length + 1) ^ 2 := by
  have h1 := length_pcalls_le n σ.steps
  have h2 := script_length σ
  have h3 : (toWord σ).length ≤ (g ++ toWord σ ++ y).length := by simp; omega
  have : (n + 1) * σ.steps.length + 1 ≤ ((toWord σ).length + 1) ^ 2 := by rw [h2]; nlinarith
  exact le_trans h1 (le_trans this (Nat.pow_le_pow_left (by omega) 2))

/-- **Soundness of the pipeline thread at an admissible word length.** -/
theorem pipe_sound_adm {pM pR pE G sw P0 : Program}
    {eM eR eE q cM cR cE dM dR dE Ks KL D sI cG : ℕ}
    (hS : CalleeSound pM pR pE eM eR eE q cM cR cE dM dR dE) (hsw : SwSpec sw Ks D pM pR pE)
    (hP0 : LoopSpec P0 G sw KL) (hD : sI + 4 ≤ D) {φ : Lax3.FirstOrder.FO 0}
    (hq : Lax3.FirstOrder.rank φ = q) {n : ℕ} {Gr : SimpleGraph (Fin n)} {g : List ℕ}
    {σ : Script n} (hcs : IsConstructionSequence Gr σ.run)
    (hgl : GlueAt G sI (D + 16) eM eR eE cG φ (g ++ toWord σ ++ toWord φ) σ.run σ.steps) {w : ℕ}
    (h : 2 ^ (D + 30 + sI) * soundBig eM eR eE cM cR cE dM dR dE Ks *
      ((g ++ toWord σ ++ toWord φ).length + maxEntry (g ++ toWord σ ++ toWord φ) + 1) ^ 5 ≤
        2 ^ w) :
    ∀ z t, RunsTo w P0 (g ++ toWord σ ++ toWord φ) z t → z = 1 :: mcAns Gr φ := by
  obtain ⟨hw, hx, hreg⟩ := regions_big (by simp only [soundBig]; omega)
    (calls_le_input g σ (toWord φ)) h
  exact pipe_sound hS hsw hP0 hD hq hcs hgl hw hx hreg

end Lax185574Proofs.MC
