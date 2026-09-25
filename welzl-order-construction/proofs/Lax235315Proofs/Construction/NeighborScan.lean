import Lax235315Proofs.Construction.GraphNeighborhood
import Lax11Proofs.CCGraph
import Mathlib.Tactic

/-!
Finite-set semantics of duplicate-tolerant scans through a CSR block.
-/

namespace Lax235315Proofs.Construction.NeighborScan

open Lax11.GraphEncoding
open Lax11Proofs.CC

/-- The active target values occurring in the half-open slot interval
`[lo, hi)`.  Taking an image makes duplicate CSR entries harmless. -/
def activeTargets (target active : ℕ → ℕ) (lo hi : ℕ) : Finset ℕ :=
  ((Finset.Ico lo hi).image target).filter fun v => active v = 1

@[simp] theorem activeTargets_same (target active : ℕ → ℕ) (lo : ℕ) :
    activeTargets target active lo lo = ∅ := by
  simp [activeTargets]

theorem mem_activeTargets {target active : ℕ → ℕ} {lo hi v : ℕ} :
    v ∈ activeTargets target active lo hi ↔
      active v = 1 ∧ ∃ j, lo ≤ j ∧ j < hi ∧ target j = v := by
  simp only [activeTargets, Finset.mem_filter, Finset.mem_image,
    Finset.mem_Ico]
  aesop

/-- Extending a scan by one slot inserts precisely its active target. -/
theorem activeTargets_succ {target active : ℕ → ℕ} {lo j : ℕ}
    (hlo : lo ≤ j) :
    activeTargets target active lo (j + 1) =
      if active (target j) = 1 then
        insert (target j) (activeTargets target active lo j)
      else activeTargets target active lo j := by
  ext v
  by_cases ha : active (target j) = 1
  · rw [if_pos ha]
    constructor
    · intro hv
      rw [mem_activeTargets] at hv
      obtain ⟨hav, k, hlk, hkj, hkv⟩ := hv
      by_cases hkj' : k < j
      · apply Finset.mem_insert.mpr
        exact Or.inr ((mem_activeTargets).mpr ⟨hav, k, hlk, hkj', hkv⟩)
      · apply Finset.mem_insert.mpr
        left
        have : k = j := by omega
        simpa [this] using hkv.symm
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · apply mem_activeTargets.mpr
        exact ⟨ha, j, hlo, by omega, rfl⟩
      · rw [mem_activeTargets] at hv ⊢
        obtain ⟨hav, k, hlk, hkj, hkv⟩ := hv
        exact ⟨hav, k, hlk, by omega, hkv⟩
  · rw [if_neg ha]
    constructor
    · intro hv
      rw [mem_activeTargets] at hv ⊢
      obtain ⟨hav, k, hlk, hkj, hkv⟩ := hv
      have hk : k < j := by
        by_contra h
        have : k = j := by omega
        subst k
        exact ha (hkv ▸ hav)
      exact ⟨hav, k, hlk, hk, hkv⟩
    · intro hv
      rw [mem_activeTargets] at hv ⊢
      obtain ⟨hav, k, hlk, hkj, hkv⟩ := hv
      exact ⟨hav, k, hlk, by omega, hkv⟩

theorem activeTargets_mono {target active : ℕ → ℕ} {lo i j : ℕ}
    (hij : i ≤ j) :
    activeTargets target active lo i ⊆ activeTargets target active lo j := by
  intro v hv
  rw [mem_activeTargets] at hv ⊢
  obtain ⟨ha, k, hlk, hki, hkv⟩ := hv
  exact ⟨ha, k, hlk, hki.trans_le hij, hkv⟩

theorem activeTargets_subset_range {target active : ℕ → ℕ} {lo hi n : ℕ}
    (htarget : ∀ j, lo ≤ j → j < hi → target j < n) :
    activeTargets target active lo hi ⊆ Finset.range n := by
  intro v hv
  rw [mem_activeTargets] at hv
  obtain ⟨-, j, hlj, hjh, rfl⟩ := hv
  exact Finset.mem_range.mpr (htarget j hlj hjh)

theorem card_activeTargets_le {target active : ℕ → ℕ} {lo hi n : ℕ}
    (htarget : ∀ j, lo ≤ j → j < hi → target j < n) :
    (activeTargets target active lo hi).card ≤ n := by
  exact (Finset.card_le_card (activeTargets_subset_range htarget)).trans_eq
    (Finset.card_range n)

/-- A duplicate-free set extracted from a half-open array interval has at
most as many elements as the interval has slots. -/
theorem card_activeTargets_le_interval {target active : ℕ → ℕ}
    {lo hi : ℕ} :
    (activeTargets target active lo hi).card ≤ hi - lo := by
  calc
    (activeTargets target active lo hi).card ≤
        ((Finset.Ico lo hi).image target).card :=
      Finset.card_filter_le _ _
    _ ≤ (Finset.Ico lo hi).card := Finset.card_image_le
    _ = hi - lo := Nat.card_Ico lo hi

/-- A completed encoded block contains exactly the active graph neighbors of
its source vertex. -/
theorem mem_activeTargets_block {x : List ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (hx : EncodesGraph x n G)
    {active : ℕ → ℕ} {t v : ℕ} (ht : t < n) :
    v ∈ activeTargets (target x) active (offset x t) (offset x (t + 1)) ↔
      active v = 1 ∧ Adjn G t v := by
  rw [mem_activeTargets]
  constructor
  · rintro ⟨hav, j, hlo, hhi, hjv⟩
    exact ⟨hav, hjv ▸ adjn_of_slot hx ht hlo hhi⟩
  · rintro ⟨hav, hadj⟩
    obtain ⟨j, hlo, hhi, hjv⟩ := slot_of_adjn hx hadj
    exact ⟨hav, j, hlo, hhi, hjv⟩

end Lax235315Proofs.Construction.NeighborScan
