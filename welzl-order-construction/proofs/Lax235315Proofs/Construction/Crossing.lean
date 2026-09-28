import Lax195003.WelzlOrders
import Mathlib.Data.Set.SymmDiff

/-!
Crossing-number lemmas used in the reconstruction analysis of the paper.

The principal result is `crossingNumber_le_add_two_mul`: replacing every
set by a representative at symmetric-difference distance at most `k`
increases the crossing number by at most `2k`.  This is Lemma 2.2 of the
paper, stated directly for the submitted set-system representation.
-/

namespace Lax235315Proofs.Construction.Crossing

open scoped symmDiff
open Lax195003.WelzlOrders

noncomputable section

/-- Whether `u` has a successor in the order represented by `π`. -/
def HasSuccessor {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n) : Prop :=
  ∃ v : Fin n, (π v).val = (π u).val + 1

/-- The successor of `u`, when it has one, and `u` itself otherwise. -/
noncomputable def successor {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n) : Fin n :=
  by
    classical
    exact if h : HasSuccessor π u then Classical.choose h else u

lemma successor_spec {n : ℕ} {π : Equiv.Perm (Fin n)} {u : Fin n}
    (h : HasSuccessor π u) :
    (π (successor π u)).val = (π u).val + 1 := by
  rw [successor, dif_pos h]
  exact Classical.choose_spec h

/-- The vertices whose successor lies in `D`. -/
def predecessorsOf {n : ℕ} (π : Equiv.Perm (Fin n)) (D : Set (Fin n)) :
    Set (Fin n) :=
  {u | HasSuccessor π u ∧ successor π u ∈ D}

/-- Taking the successor injects `predecessorsOf π D` into `D`. -/
lemma predecessorsOf_ncard_le {n : ℕ} (π : Equiv.Perm (Fin n))
    (D : Set (Fin n)) :
    (predecessorsOf π D).ncard ≤ D.ncard := by
  apply Set.ncard_le_ncard_of_injOn (successor π)
  · intro u hu
    exact hu.2
  · intro u hu v hv huv
    apply π.injective
    apply Fin.ext
    have hu' := successor_spec hu.1
    have hv' := successor_spec hv.1
    rw [huv] at hu'
    omega

/-- Every crossing count is at most the number of vertices. -/
lemma crossingCount_le_card {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) :
    crossingCount π X ≤ n := by
  unfold crossingCount
  simpa using Set.ncard_le_card
    {u : Fin n | ∃ v : Fin n,
      (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}

/-- A member's crossing count is bounded by the crossing number of the
set system containing it. -/
lemma crossingCount_le_crossingNumber {n : ℕ}
    {ℱ : SetSystem (Fin n)} {π : Equiv.Perm (Fin n)}
    {X : Set (Fin n)} (hX : X ∈ ℱ) :
    crossingCount π X ≤ crossingNumber ℱ π := by
  unfold crossingNumber
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro q ⟨Y, -, rfl⟩
    exact crossingCount_le_card π Y
  · exact ⟨X, hX, rfl⟩

/-- A pointwise bound on all members bounds the crossing number. -/
lemma crossingNumber_le_of_forall {n : ℕ}
    {ℱ : SetSystem (Fin n)} {π : Equiv.Perm (Fin n)} {k : ℕ}
    (h : ∀ X ∈ ℱ, crossingCount π X ≤ k) :
    crossingNumber ℱ π ≤ k := by
  unfold crossingNumber
  by_cases hℱ : ℱ.Nonempty
  · apply csSup_le
    · obtain ⟨X, hX⟩ := hℱ
      exact ⟨crossingCount π X, X, hX, rfl⟩
    · rintro q ⟨X, hX, rfl⟩
      exact h X hX
  · have hℱ' : ℱ = ∅ := Set.not_nonempty_iff_eq_empty.mp hℱ
    simp [hℱ']

/-- Changing membership on `D` can create at most two new crossings for
each vertex of `D`. -/
lemma crossingCount_le_add_two_mul_symmDiff {n : ℕ}
    (π : Equiv.Perm (Fin n)) (X Y : Set (Fin n)) :
    crossingCount π X ≤ crossingCount π Y + 2 * (X ∆ Y).ncard := by
  let CX : Set (Fin n) :=
    {u | ∃ v : Fin n,
      (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}
  let CY : Set (Fin n) :=
    {u | ∃ v : Fin n,
      (π v).val = (π u).val + 1 ∧ (u ∈ Y ↔ v ∉ Y)}
  let D : Set (Fin n) := X ∆ Y
  let P : Set (Fin n) := predecessorsOf π D
  have hsub : CX ⊆ CY ∪ (D ∪ P) := by
    intro u hu
    obtain ⟨v, huv, hcross⟩ := hu
    by_cases huD : u ∈ D
    · exact Set.mem_union_right _ (Set.mem_union_left _ huD)
    by_cases hvD : v ∈ D
    · apply Set.mem_union_right
      apply Set.mem_union_right
      refine ⟨⟨v, huv⟩, ?_⟩
      have hs : successor π u = v := by
        apply π.injective
        apply Fin.ext
        rw [successor_spec ⟨v, huv⟩, huv]
      rwa [hs]
    · apply Set.mem_union_left
      refine ⟨v, huv, ?_⟩
      have huXY : (u ∈ X) ↔ (u ∈ Y) := by
        have h := huD
        simp only [D, Set.mem_symmDiff] at h
        tauto
      have hvXY : (v ∈ X) ↔ (v ∈ Y) := by
        have h := hvD
        simp only [D, Set.mem_symmDiff] at h
        tauto
      tauto
  have hcard : CX.ncard ≤ CY.ncard + D.ncard + P.ncard := by
    calc
      CX.ncard ≤ (CY ∪ (D ∪ P)).ncard := Set.ncard_le_ncard hsub
      _ ≤ CY.ncard + (D ∪ P).ncard := Set.ncard_union_le _ _
      _ ≤ CY.ncard + (D.ncard + P.ncard) :=
        Nat.add_le_add_left (Set.ncard_union_le _ _) _
      _ = CY.ncard + D.ncard + P.ncard := by omega
  have hP : P.ncard ≤ D.ncard := predecessorsOf_ncard_le π D
  unfold crossingCount
  change CX.ncard ≤ CY.ncard + 2 * D.ncard
  omega

/-- **Near-twin replacement (paper, Lemma 2.2).** If every member of
`ℱ` is within symmetric-difference distance `k` of a representative in
`ℱ'`, an order of crossing number `m` for `ℱ'` has crossing number at
most `m + 2k` for `ℱ`. -/
lemma crossingNumber_le_add_two_mul {n k m : ℕ}
    {ℱ ℱ' : SetSystem (Fin n)} {π : Equiv.Perm (Fin n)}
    (hrep : ∀ X ∈ ℱ, ∃ Y ∈ ℱ', (X ∆ Y).ncard ≤ k)
    (hπ : crossingNumber ℱ' π ≤ m) :
    crossingNumber ℱ π ≤ m + 2 * k := by
  apply crossingNumber_le_of_forall
  intro X hX
  obtain ⟨Y, hY, hXY⟩ := hrep X hX
  exact (crossingCount_le_add_two_mul_symmDiff π X Y).trans <| by
    have hCY := (crossingCount_le_crossingNumber hY).trans hπ
    omega

end

end Lax235315Proofs.Construction.Crossing
