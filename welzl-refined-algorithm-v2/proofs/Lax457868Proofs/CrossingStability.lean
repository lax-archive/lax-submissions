import Lax195003.WelzlOrders

set_option autoImplicit false

namespace Lax457868Proofs

open Lax195003.WelzlOrders

private def crossingStarts {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) : Set (Fin n) :=
  {u | ∃ v, (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}

private def previous {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) : Fin n :=
  π.symm ⟨(π v).val - 1, lt_of_le_of_lt (Nat.sub_le _ _) (π v).isLt⟩

private lemma previous_of_consecutive {n : ℕ} (π : Equiv.Perm (Fin n))
    {u v : Fin n} (h : (π v).val = (π u).val + 1) : previous π v = u := by
  apply π.injective
  apply Fin.ext
  simp only [previous, Equiv.apply_symm_apply]
  omega

private lemma crossingStarts_subset {n : ℕ} (π : Equiv.Perm (Fin n))
    (X Y : Set (Fin n)) :
    crossingStarts π X ⊆ (crossingStarts π Y ∪
      ((X \ Y) ∪ (Y \ X))) ∪
      previous π '' ((X \ Y) ∪ (Y \ X)) := by
  intro u hu
  obtain ⟨v, hcon, hcross⟩ := hu
  by_cases huDiff : u ∈ (X \ Y) ∪ (Y \ X)
  · exact Or.inl (Or.inr huDiff)
  by_cases hvDiff : v ∈ (X \ Y) ∪ (Y \ X)
  · exact Or.inr ⟨v, hvDiff, previous_of_consecutive π hcon⟩
  · left
    left
    refine ⟨v, hcon, ?_⟩
    simp only [Set.mem_union, Set.mem_sdiff] at huDiff hvDiff
    have huEq : u ∈ X ↔ u ∈ Y := by tauto
    have hvEq : v ∈ X ↔ v ∈ Y := by tauto
    tauto

/-- Changing membership at one vertex can affect only the two consecutive pairs
incident to that vertex. -/
lemma crossingCount_le_add_two_symmDiff {n : ℕ} (π : Equiv.Perm (Fin n))
    (X Y : Set (Fin n)) :
    crossingCount π X ≤ crossingCount π Y +
      2 * ((X \ Y) ∪ (Y \ X)).ncard := by
  let D : Set (Fin n) := (X \ Y) ∪ (Y \ X)
  have hsub : crossingStarts π X ⊆
      (crossingStarts π Y ∪ D) ∪ previous π '' D :=
    crossingStarts_subset π X Y
  have hfinite : ((crossingStarts π Y ∪ D) ∪ previous π '' D).Finite :=
    Set.toFinite _
  have h₁ := Set.ncard_le_ncard hsub hfinite
  have h₂ := Set.ncard_union_le (crossingStarts π Y ∪ D) (previous π '' D)
  have h₃ := Set.ncard_union_le (crossingStarts π Y) D
  have h₄ := Set.ncard_image_le (s := D) (f := previous π) (Set.toFinite _)
  change (crossingStarts π X).ncard ≤
    (crossingStarts π Y).ncard + 2 * D.ncard
  omega

lemma crossingCount_le_sub_one {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) : crossingCount π X ≤ n - 1 := by
  by_cases hn : n = 0
  · subst n
    simp [crossingCount]
  · have hproper : crossingStarts π X ⊂ Set.univ := by
      apply Set.ssubset_univ_iff.mpr
      intro heq
      have h : π.symm ⟨n - 1, by omega⟩ ∈ crossingStarts π X := by
        rw [heq]
        trivial
      obtain ⟨v, hv, _⟩ := h
      simp only [Equiv.apply_symm_apply] at hv
      have := (π v).isLt
      omega
    have hlt := Set.ncard_lt_ncard hproper (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin] at hlt
    change (crossingStarts π X).ncard ≤ n - 1
    omega

lemma crossingNumber_le_sub_one {n : ℕ} (F : SetSystem (Fin n))
    (π : Equiv.Perm (Fin n)) : crossingNumber F π ≤ n - 1 := by
  unfold crossingNumber
  by_cases hF : F.Nonempty
  · apply csSup_le
    · obtain ⟨X, hX⟩ := hF
      exact ⟨crossingCount π X, X, hX, rfl⟩
    · rintro k ⟨X, -, rfl⟩
      exact crossingCount_le_sub_one π X
  · simp [Set.not_nonempty_iff_eq_empty.mp hF]

lemma isWelzlOrder_iff_forall_crossingCount_le {n : ℕ}
    (F : SetSystem (Fin n)) (π : Equiv.Perm (Fin n)) (m : ℕ) :
    IsWelzlOrder F π m ↔ ∀ X ∈ F, crossingCount π X ≤ m := by
  unfold IsWelzlOrder crossingNumber
  constructor
  · intro h X hXF
    have hmem : crossingCount π X ∈
        {k : ℕ | ∃ Y ∈ F, k = crossingCount π Y} := ⟨X, hXF, rfl⟩
    exact le_trans (le_csSup (by
      refine ⟨n - 1, ?_⟩
      rintro k ⟨Y, -, rfl⟩
      exact crossingCount_le_sub_one π Y) hmem) h
  · intro h
    by_cases hF : F.Nonempty
    · apply csSup_le
      · obtain ⟨X, hX⟩ := hF
        exact ⟨crossingCount π X, X, hX, rfl⟩
      · rintro k ⟨X, hXF, rfl⟩
        exact h X hXF
    · simp [Set.not_nonempty_iff_eq_empty.mp hF]

/-- A representative within `k` membership changes transfers an order's
crossing bound at cost at most `2k`. -/
lemma isWelzlOrder_of_near_representatives {n : ℕ}
    (F F' : SetSystem (Fin n)) (π : Equiv.Perm (Fin n)) (m k : ℕ)
    (hrep : ∀ X ∈ F, ∃ Y ∈ F', ((X \ Y) ∪ (Y \ X)).ncard ≤ k)
    (horder : IsWelzlOrder F' π m) : IsWelzlOrder F π (m + 2 * k) := by
  apply (isWelzlOrder_iff_forall_crossingCount_le F π (m + 2 * k)).2
  intro X hXF
  obtain ⟨Y, hY, hdist⟩ := hrep X hXF
  have hYcount := (isWelzlOrder_iff_forall_crossingCount_le F' π m).1 horder Y hY
  have hstab := crossingCount_le_add_two_symmDiff π X Y
  omega

end Lax457868Proofs
