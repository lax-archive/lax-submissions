import Lax185574Proofs.LoopScript
import Lax185574Proofs.RamOut
import Lax185574Proofs.RamCat

/-!
Tools for scripts of the loop driver whose glue program is guarded, as
in the assembly of thm:mc (`MC/Asm/InvScript`, `MC/Asm/Sound`), copied
here so that the two assemblies do not depend on each other.

`inv_script_sound`: round `j` needs to behave as scripted only if an
invariant `I j` holds, and then it establishes `I (j + 1)`. `lpV_pow`
bounds the word lengths of the regions from below.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574Proofs.RamSim Lax185574Proofs.Simulate Lax185574Proofs.RamCat

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

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem le_pow_sub {B k v : ℕ} (h : B * 2 ^ k ≤ 2 ^ v) (hB : 1 ≤ B) : k ≤ v ∧ B ≤ 2 ^ (v - k) := by
  have hk : k ≤ v := by
    have : 2 ^ k ≤ 2 ^ v := le_trans (Nat.le_mul_of_pos_left _ hB) h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  refine ⟨hk, ?_⟩
  rw [show 2 ^ v = 2 ^ (v - k) * 2 ^ k by rw [← pow_add]; congr 1; omega] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem catLim_le (w E : ℕ) : catLim w E ≤ 2 ^ (w - E) := by
  unfold catLim
  rcases le_total E w with h | h
  · calc (2 ^ w - 1) / 2 ^ E ≤ 2 ^ w / 2 ^ E := Nat.div_le_div_right (Nat.sub_le _ _)
      _ = 2 ^ (w - E) := by rw [Nat.pow_div h (by norm_num)]
  · calc (2 ^ w - 1) / 2 ^ E ≤ 2 ^ w / 2 ^ E := Nat.div_le_div_right (Nat.sub_le _ _)
      _ ≤ 1 := by
        rcases Nat.lt_or_ge (2 ^ w) (2 ^ E) with h' | h'
        · rw [Nat.div_eq_of_lt h']; omega
        · have : 2 ^ w = 2 ^ E := le_antisymm (two_pow_mono h) h'
          rw [this, Nat.div_self (by positivity)]
      _ ≤ _ := Nat.one_le_two_pow

theorem lpU_lt {x a b : List ℕ} {N : ℕ} (hN : 0 < N) (hx : ∀ e ∈ x, e < N)
    (ha : ∀ e ∈ a, e < N) (hb : ∀ e ∈ b, e < N) (hbl : b.length < N) :
    ∀ e ∈ lpU x a b, e < N := by
  have hg : ∀ i, a.getD i 0 < N := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    rcases h : a[i]? with _ | e
    · simpa using hN
    · exact ha e (List.mem_of_getElem? h)
  intro e he
  simp only [lpU, List.mem_append, List.mem_cons, List.mem_singleton] at he
  rcases he with ((((rfl | rfl | he) | he) | he) | rfl | he)
  · exact hg 0
  · exact hg 1
  · simp at he
  · exact hx e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  · exact ha e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  · exact hbl
  · exact hb e he

theorem lpQ_append {h u : List ℕ} (hh : h.getD 1 0 + 3 = h.length) : lpQ (h ++ u) = u := by
  have h1 : 1 < h.length := by omega
  have : (h ++ u).getD 1 0 = h.getD 1 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  simp only [lpQ, this]
  rw [show 3 + h.getD 1 0 = h.length by omega, List.drop_left]

/-- The specification of the loop driver `p` of `G` and `P` with
constant `K`. -/
def LoopSpec (p G P : Program) (K : ℕ) : Prop :=
  ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
    (∀ z T, LoopTrace w G P x 0 (lpA0 x) [] z T →
      ∃ t ≤ K * (T + z.length + 1), RunsTo w p x z t) ∧
    (∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)

end Lax185574Proofs.ResolveRam
