import Lax235315Proofs.Construction.MarkingMath
import Mathlib.Tactic

/-! Finite-set semantics of the representative-selection scan. -/

namespace Lax235315Proofs.Construction.RepresentativeMath

open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.MarkingMath

lemma activeVertices_succ {active : ℕ → ℕ} {i : ℕ} :
    activeVertices (i + 1) active =
      if active i = 1 then insert i (activeVertices i active)
      else activeVertices i active := by
  by_cases hi : active i = 1
  · rw [if_pos hi]
    simp [activeVertices, Finset.range_add_one, Finset.filter_insert, hi]
  · rw [if_neg hi]
    simp [activeVertices, Finset.range_add_one, Finset.filter_insert, hi]

/-- Semantic data maintained while the increasing vertex scan selects the
first vertex of every occupied numeric class. -/
structure RepData (n current processed : ℕ) (active label : ℕ → ℕ)
    (repClass reps outActive : ℕ → ℕ) (R : Finset ℕ) : Prop where
  enum : PrefixEnumerates R.card reps R
  reps_processed : R ⊆ activeVertices processed active
  labels_injective : Set.InjOn label R
  covers : ∀ v ∈ activeVertices processed active,
    ∃ r ∈ R, label r = label v
  table_le : ∀ q < current, repClass q ≤ n
  table_empty : ∀ q < current,
    (repClass q = n ↔ ∀ r ∈ R, label r ≠ q)
  table_mem : ∀ q < current, repClass q < n →
    repClass q ∈ R ∧ label (repClass q) = q
  out_mem : ∀ v < n, outActive v = 1 ↔ v ∈ R

lemma RepData.initial {n current : ℕ} {active label reps : ℕ → ℕ} :
    RepData n current 0 active label (fun _ => n) reps (fun _ => 0) ∅ := by
  constructor
  · exact prefixEnumerates_zero reps
  · simp
  · simp [Set.InjOn]
  · simp [activeVertices]
  · simp
  · simp
  · simp
  · simp

lemma RepData.inactive {n current i : ℕ}
    {active label repClass reps outActive : ℕ → ℕ} {R : Finset ℕ}
    (h : RepData n current i active label repClass reps outActive R)
    (hi : active i ≠ 1) :
    RepData n current (i + 1) active label repClass reps outActive R := by
  have hprocessed : activeVertices (i + 1) active = activeVertices i active := by
    rw [activeVertices_succ, if_neg hi]
  refine { h with reps_processed := ?_, covers := ?_ }
  · simpa [hprocessed] using h.reps_processed
  · simpa [hprocessed] using h.covers

lemma RepData.existing {n current i q : ℕ}
    {active label repClass reps outActive : ℕ → ℕ} {R : Finset ℕ}
    (h : RepData n current i active label repClass reps outActive R)
    (hi : i < n) (hai : active i = 1) (hlabel : label i = q)
    (hq : q < current) (hexisting : repClass q ≠ n) :
    RepData n current (i + 1) active label repClass reps outActive R := by
  have hrepLt : repClass q < n := by
    have := h.table_le q hq
    omega
  have hrep := h.table_mem q hq hrepLt
  have hprocessed : activeVertices (i + 1) active =
      insert i (activeVertices i active) := by
    rw [activeVertices_succ, if_pos hai]
  refine { h with
    reps_processed := ?_
    covers := ?_ }
  · intro r hr
    rw [hprocessed]
    exact Finset.mem_insert_of_mem (h.reps_processed hr)
  · intro v hv
    rw [hprocessed] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨repClass q, hrep.1, by simpa [hlabel] using hrep.2⟩
    · exact h.covers v hv

lemma RepData.fresh {n current i q : ℕ}
    {active label repClass reps outActive : ℕ → ℕ} {R : Finset ℕ}
    (h : RepData n current i active label repClass reps outActive R)
    (hi : i < n) (hai : active i = 1) (hlabel : label i = q)
    (hq : q < current) (hfresh : repClass q = n) :
    RepData n current (i + 1) active label
      (upd repClass q i) (upd reps R.card i) (upd outActive i 1)
      (insert i R) := by
  have hnone : ∀ r ∈ R, label r ≠ q := (h.table_empty q hq).mp hfresh
  have hiR : i ∉ R := by
    intro hiR
    exact hnone i hiR hlabel
  have hprocessed : activeVertices (i + 1) active =
      insert i (activeVertices i active) := by
    rw [activeVertices_succ, if_pos hai]
  constructor
  · simpa [Finset.card_insert_of_notMem hiR] using h.enum.push hiR
  · rw [hprocessed]
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · simp
    · exact Finset.mem_insert_of_mem (h.reps_processed hr)
  · intro r hr s hs hrs
    rcases Finset.mem_insert.mp hr with hri | hr
    · subst r
      rcases Finset.mem_insert.mp hs with hsi | hs
      · subst s
        rfl
      · exfalso
        apply hnone s hs
        rw [← hrs, hlabel]
    · rcases Finset.mem_insert.mp hs with hsi | hs
      · subst s
        exfalso
        apply hnone r hr
        rw [hrs, hlabel]
      · exact h.labels_injective hr hs hrs
  · rw [hprocessed]
    intro v hv
    rcases Finset.mem_insert.mp hv with hvi | hv
    · subst v
      exact ⟨i, by simp, rfl⟩
    · obtain ⟨r, hr, hl⟩ := h.covers v hv
      exact ⟨r, Finset.mem_insert_of_mem hr, hl⟩
  · intro p hp
    by_cases hpq : p = q
    · subst p
      simp only [upd, ↓reduceIte]
      exact hi.le
    · simp only [upd, hpq, ↓reduceIte]
      exact h.table_le p hp
  · intro p hp
    by_cases hpq : p = q
    · subst p
      constructor
      · intro hin
        simp [upd] at hin
        omega
      · intro hall
        exact (hall i (by simp) (by simpa [hlabel])).elim
    · rw [show upd repClass q i p = repClass p by simp [upd, hpq]]
      rw [h.table_empty p hp]
      constructor
      · intro hall r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · simpa [hlabel] using (Ne.symm hpq)
        · exact hall r hr
      · intro hall r hr
        exact hall r (Finset.mem_insert_of_mem hr)
  · intro p hp hpN
    by_cases hpq : p = q
    · subst p
      simp only [upd, ↓reduceIte] at hpN ⊢
      exact ⟨by simp, hlabel⟩
    · have hpN' : repClass p < n := by simpa [upd, hpq] using hpN
      obtain ⟨hr, hl⟩ := h.table_mem p hp hpN'
      simp [upd, hpq, hr, hl]
  · intro v hv
    by_cases hvi : v = i
    · subst v
      simp [upd, hiR]
    · simp [upd, hvi, h.out_mem v hv]

end Lax235315Proofs.Construction.RepresentativeMath
