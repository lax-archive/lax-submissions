import Lax185574Proofs.MC.Asm.Script

/-!
Soundness of a conditional script with an invariant, and a lower bound
on the word lengths of the regions of the loop driver.

`inv_script_sound` is `cond_script_sound` with a predicate `I` on the
rounds. Round `j` needs to behave as scripted only if `I j` holds, and
then it establishes `I (j + 1)`. In the use for thm:mc the invariant
says that the input of a round has small entries, which the guarded
bridge needs, and which follows from the output bounds of the previous
round.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.RamSim Lax185574Proofs.Simulate

/-- What soundness needs of round `j < R` under the invariant `I`. -/
def InvCall (w : ℕ) (G P : Program) (x : List ℕ) (A B : ℕ → List ℕ) (I : ℕ → Prop) (j : ℕ) :
    Prop :=
  I j → ∀ o t, RunsTo (lpV w (2 * j)) G (lpU x (A j) (B j)) o t →
    o = A (j + 1) ∧ (A (j + 1)).head? ≠ some 0 ∧
      ∀ r t', RunsTo (lpV w (2 * j + 1)) P (lpQ o) r t' → r = B (j + 1) ∧ I (j + 1)

theorem inv_script_back {w : ℕ} {G P : Program} {x : List ℕ} {A B : ℕ → List ℕ}
    {I : ℕ → Prop} {R : ℕ} {z : List ℕ} (hC : ∀ j < R, InvCall w G P x A B I j)
    (hD : I R → ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) {i : ℕ}
    {a b z' : List ℕ} {T : ℕ} (h : LoopTrace w G P x i a b z' T) :
    ∀ j ≤ R, i = 2 * j → a = A j → b = B j → I j → z' = z := by
  induction h with
  | done hs hG ho =>
    intro j hj hi ha hb hI
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e1, h0, -⟩ := hC j hlt hI _ _ hG
      rw [← e1] at h0; simp at h0
    · exact (List.cons.inj (hD hI _ _ hG)).2
  | call hs hG hne h0 ho hs' hP hr _ ih =>
    intro j hj hi ha hb hI
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e1, -, hPu⟩ := hC j hlt hI _ _ hG
      obtain ⟨e2, hI'⟩ := hPu _ _ hP
      subst e1 e2
      exact ih (j + 1) (by omega) (by ring) rfl rfl hI'
    · have := hD hI _ _ hG
      rw [this] at h0; simp at h0

/-- **Soundness of a script with an invariant.** -/
theorem inv_script_sound {G P p : Program}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)
    {w : ℕ} {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1)) {A B : ℕ → List ℕ}
    {I : ℕ → Prop} {R : ℕ} {z : List ℕ} (hA0 : A 0 = lpA0 x) (hB0 : B 0 = []) (hI0 : I 0)
    (hC : ∀ j < R, InvCall w G P x A B I j)
    (hD : I R → ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) :
    ∀ z' t, RunsTo w p x z' t → z' = z := by
  intro z' t h
  obtain ⟨T, hT⟩ := hp w x hw hx z' t h
  exact inv_script_back hC hD hT 0 (Nat.zero_le _) rfl hA0.symm hB0.symm hI0

/-- The word length of region `i` is at least `w - 3 - 2 log₂ (i + 1)`. -/
theorem lpV_pow (w i : ℕ) : 2 ^ (w - 3) ≤ 2 ^ lpV w i * (i + 1) ^ 2 := by
  obtain ⟨-, h2, -, h4, -⟩ := lpAlloc_inv (lpCap w) i
  have hb : 2 ^ (lpAlloc (lpCap w) i).bat ≤ i + 1 := by omega
  have hb2 : 4 ^ (lpAlloc (lpCap w) i).bat ≤ (i + 1) ^ 2 := by
    rw [show (4 : ℕ) ^ (lpAlloc (lpCap w) i).bat = (2 ^ (lpAlloc (lpCap w) i).bat) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    exact Nat.pow_le_pow_left hb 2
  simp only [lpV]
  generalize (lpAlloc (lpCap w) i).bat = b at hb2
  rw [show (4 : ℕ) ^ b = 2 ^ (2 * b) by rw [pow_mul]; norm_num] at hb2
  by_cases h : 2 * b ≤ w - 3
  · calc 2 ^ (w - 3) = 2 ^ (w - 3 - 2 * b) * 2 ^ (2 * b) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_left _ hb2
  · calc 2 ^ (w - 3) ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (i + 1) ^ 2 := hb2
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)

end Lax185574Proofs.MC
