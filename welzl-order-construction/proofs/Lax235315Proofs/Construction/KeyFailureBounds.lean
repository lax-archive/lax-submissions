import Lax235315Proofs.Construction.KeySamplingBounds
import Mathlib.Tactic

/-! Per-round failure bounds for unconditioned finite random keys. -/

namespace Lax235315Proofs.Construction.KeyFailureBounds

open Finset
open Lax235315Proofs.Construction.FiniteRandomKeys
open Lax235315Proofs.Construction.KeySampling
open Lax235315Proofs.Construction.KeySamplingBounds
open Lax235315Proofs.Construction.Sampling

/-- Forget that a key assignment is injective. -/
def injectionEmbedding (α : Type*) [Fintype α] [DecidableEq α] (M : ℕ) :
    KeyInjection α M ↪ (α → Fin M) :=
  ⟨fun f => f.1, fun _ _ h => Subtype.ext h⟩

/-- Collision-free assignments whose induced sample lies in `bad`, viewed
inside the full, unconditioned assignment space. -/
def badInjectionAssignments {α : Type*} [Fintype α] [DecidableEq α]
    (M s : ℕ) (bad : Finset (Finset α)) : Finset (α → Fin M) :=
  (badInjections M s bad).map (injectionEmbedding α M)

@[simp] lemma card_badInjectionAssignments {α : Type*} [Fintype α]
    [DecidableEq α] (M s : ℕ) (bad : Finset (Finset α)) :
    (badInjectionAssignments M s bad).card =
      (badInjections M s bad).card := by
  simp [badInjectionAssignments]

/-- A round fails if the keys collide, or if they are collision-free but
their bottom sample belongs to the bad family. -/
def failingAssignments {α : Type*} [Fintype α] [DecidableEq α]
    (M s : ℕ) (bad : Finset (Finset α)) : Finset (α → Fin M) :=
  collisions α M ∪ badInjectionAssignments M s bad

lemma card_keyInjections_le_assignments (α : Type*) [Fintype α]
    [DecidableEq α] (M : ℕ) :
    Fintype.card (KeyInjection α M) ≤ M ^ Fintype.card α := by
  calc
    Fintype.card (KeyInjection α M) ≤ Fintype.card (α → Fin M) :=
      Fintype.card_subtype_le _
    _ = M ^ Fintype.card α := by simp

/-- Conditioning on collision-free keys cannot make the absolute frequency
of a bad fixed-size sample exceed its uniform-subset frequency. -/
lemma badInjectionAssignments_fraction_le {α : Type*} [Fintype α]
    [DecidableEq α] {M s : ℕ} (hM : 0 < M)
    (hs : s ≤ Fintype.card α) {bad : Finset (Finset α)}
    (hbad : bad ⊆ samples (Finset.univ : Finset α) s) :
    ((badInjectionAssignments M s bad).card : ℝ) /
        (allAssignments α M).card ≤
      (bad.card : ℝ) / (samples (Finset.univ : Finset α) s).card := by
  have hcross := card_badInjections_mul_samples (M := M) hs hbad
  have hall : (allAssignments α M).card = M ^ Fintype.card α :=
    card_allAssignments α M
  have hinj := card_keyInjections_le_assignments α M
  have hsposNat : 0 < (samples (Finset.univ : Finset α) s).card := by
    rw [card_samples]
    exact Nat.choose_pos hs
  have hallposNat : 0 < (allAssignments α M).card := by
    rw [hall]
    positivity
  have hspos : (0 : ℝ) < (samples (Finset.univ : Finset α) s).card := by
    exact_mod_cast hsposNat
  have hallpos : (0 : ℝ) < (allAssignments α M).card := by
    exact_mod_cast hallposNat
  rw [div_le_div_iff₀ hallpos hspos]
  rw [card_badInjectionAssignments]
  have hcrossR :
      ((badInjections M s bad).card : ℝ) *
          (samples (Finset.univ : Finset α) s).card =
        (bad.card : ℝ) * Fintype.card (KeyInjection α M) := by
    exact_mod_cast hcross
  rw [hcrossR]
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast (hinj.trans_eq hall.symm)) (by positivity)

/-- The unconditioned failure probability is at most the collision union
bound plus the uniform bad-sample probability. -/
lemma failingAssignments_fraction_le {α : Type*} [Fintype α]
    [DecidableEq α] {M s : ℕ} (hM : 0 < M)
    (hs : s ≤ Fintype.card α) {bad : Finset (Finset α)}
    (hbad : bad ⊆ samples (Finset.univ : Finset α) s) :
    ((failingAssignments M s bad).card : ℝ) /
        (allAssignments α M).card ≤
      (Fintype.card α : ℝ) ^ 2 / M +
        (bad.card : ℝ) / (samples (Finset.univ : Finset α) s).card := by
  have hallpos : (0 : ℝ) ≤ (allAssignments α M).card := by positivity
  calc
    ((failingAssignments M s bad).card : ℝ) /
        (allAssignments α M).card ≤
      (((collisions α M).card : ℝ) +
        (badInjectionAssignments M s bad).card) /
          (allAssignments α M).card := by
        apply div_le_div_of_nonneg_right _ hallpos
        exact_mod_cast Finset.card_union_le (collisions α M)
          (badInjectionAssignments M s bad)
    _ = ((collisions α M).card : ℝ) / (allAssignments α M).card +
        ((badInjectionAssignments M s bad).card : ℝ) /
          (allAssignments α M).card := by ring
    _ ≤ (Fintype.card α : ℝ) ^ 2 / M +
        (bad.card : ℝ) / (samples (Finset.univ : Finset α) s).card :=
      add_le_add (collision_fraction_le α hM)
        (badInjectionAssignments_fraction_le hM hs hbad)

lemma collision_term_le_one_div_pow_six {a N q : ℕ}
    (hN : 0 < N) (haN : a ≤ N) (hNq : N ≤ q) :
    (a : ℝ) ^ 2 / (q : ℝ) ^ 8 ≤ 1 / (N : ℝ) ^ 6 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hN.trans_le hNq
  rw [div_le_div_iff₀ (pow_pos hqr 8) (pow_pos hNr 6)]
  have haNr : (a : ℝ) ≤ N := by exact_mod_cast haN
  have hNqr : (N : ℝ) ≤ q := by exact_mod_cast hNq
  calc
    (a : ℝ) ^ 2 * (N : ℝ) ^ 6 ≤
        (N : ℝ) ^ 2 * (N : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) haNr 2) (by positivity)
    _ = (N : ℝ) ^ 8 := by ring
    _ ≤ (q : ℝ) ^ 8 := pow_le_pow_left₀ hNr.le hNqr 8
    _ = 1 * (q : ℝ) ^ 8 := by ring

/-- With eight `L`-bit digits and `N ≤ 2^L`, a round's collision term is
at most `N⁻⁶`; the other term is exactly the paper's bad-sample bound. -/
lemma failingAssignments_fraction_le_paper {α : Type*} [Fintype α]
    [DecidableEq α] {N q c s : ℕ}
    (hN : 0 < N) (haN : Fintype.card α ≤ N) (hNq : N ≤ q)
    (hs : s ≤ Fintype.card α) {bad : Finset (Finset α)}
    (hbad : bad ⊆ samples (Finset.univ : Finset α) s)
    (hbadFraction :
      (bad.card : ℝ) / (samples (Finset.univ : Finset α) s).card ≤
        (c : ℝ) ^ 2 / N) :
    ((failingAssignments (q ^ 8) s bad).card : ℝ) /
        (allAssignments α (q ^ 8)).card ≤
      1 / (N : ℝ) ^ 6 + (c : ℝ) ^ 2 / N := by
  have hq : 0 < q := hN.trans_le hNq
  have hbase := failingAssignments_fraction_le
    (α := α) (M := q ^ 8) (bad := bad) (pow_pos hq 8) hs hbad
  calc
    ((failingAssignments (q ^ 8) s bad).card : ℝ) /
        (allAssignments α (q ^ 8)).card ≤
      (Fintype.card α : ℝ) ^ 2 / (q ^ 8 : ℕ) +
        (bad.card : ℝ) / (samples (Finset.univ : Finset α) s).card := hbase
    _ ≤ 1 / (N : ℝ) ^ 6 + (c : ℝ) ^ 2 / N := by
      apply add_le_add
      · push_cast
        exact collision_term_le_one_div_pow_six hN haN hNq
      · exact hbadFraction

/-- The guarded regime of the program leaves less than one sixth total
failure budget over at most `L` rounds. -/
lemma paper_total_failure_le_one_six {n c L rounds : ℕ}
    (hn : 12 ≤ n) (hL : L ≤ n) (hrounds : rounds ≤ L)
    (hguard : 12 * c ^ 2 * L ≤ n) :
    (rounds : ℝ) * (1 / (n : ℝ) ^ 6 + (c : ℝ) ^ 2 / n) ≤ 1 / 6 := by
  have hnr : (0 : ℝ) < n := by positivity
  have hroundsR : (rounds : ℝ) ≤ L := by exact_mod_cast hrounds
  have hLR : (L : ℝ) ≤ n := by exact_mod_cast hL
  have hguardR : (12 : ℝ) * (c : ℝ) ^ 2 * L ≤ n := by
    exact_mod_cast hguard
  have hsample : (L : ℝ) * ((c : ℝ) ^ 2 / n) ≤ 1 / 12 := by
    calc
      (L : ℝ) * ((c : ℝ) ^ 2 / n) =
          (12 * (c : ℝ) ^ 2 * L) / (12 * n) := by
        field_simp
      _ ≤ (n : ℝ) / (12 * n) :=
        div_le_div_of_nonneg_right hguardR (by positivity)
      _ = 1 / 12 := by field_simp
  have hcollision : (L : ℝ) * (1 / (n : ℝ) ^ 6) ≤ 1 / 12 := by
    calc
      (L : ℝ) * (1 / (n : ℝ) ^ 6) ≤
          (n : ℝ) * (1 / (n : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_right hLR (by positivity)
      _ = 1 / (n : ℝ) ^ 5 := by field_simp
      _ ≤ 1 / 12 := by
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 12)
        exact_mod_cast hn.trans (Nat.le_pow (by omega : 0 < 5))
  calc
    (rounds : ℝ) * (1 / (n : ℝ) ^ 6 + (c : ℝ) ^ 2 / n) ≤
        (L : ℝ) * (1 / (n : ℝ) ^ 6 + (c : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_right hroundsR (by positivity)
    _ = (L : ℝ) * (1 / (n : ℝ) ^ 6) +
        (L : ℝ) * ((c : ℝ) ^ 2 / n) := by ring
    _ ≤ 1 / 12 + 1 / 12 := add_le_add hcollision hsample
    _ = 1 / 6 := by norm_num

end Lax235315Proofs.Construction.KeyFailureBounds
