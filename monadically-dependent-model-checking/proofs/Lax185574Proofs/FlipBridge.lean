import Lax185574.Flips
import Lax185574Proofs.Lib.PartitionMetricConversionDefs
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Flips given by a labeling of the vertices and a symmetric Boolean
toggle on pairs of labels are exactly the flips for the partition into
the fibers of the labeling. The flip metric balls agree.
-/

namespace Lax185574Proofs.FlipBridge

open Lax185574.Flips Lax185574.GaifmanGraph
open Lax185574Proofs.Lib.PartitionMetricConversion

universe u

variable {V : Type u}

theorem isFlip_flip (G : SimpleGraph V) {p : ℕ} (part : V → Fin p)
    (toggle : Fin p → Fin p → Bool) (hsymm : ∀ i j, toggle i j = toggle j i) :
    IsFlip G (Setoid.ker part) (flip G part toggle hsymm) := by
  intro a b
  by_cases h : toggle (part a) (part b) = true
  · right
    intro x y hx hy hxy
    have hx : part x = part a := hx
    have hy : part y = part b := hy
    simp only [Lax185574Proofs.Lib.PartitionMetricConversion.flip, hx, hy, h, Xor]
    tauto
  · left
    intro x y hx hy hxy
    have hx : part x = part a := hx
    have hy : part y = part b := hy
    simp only [Lax185574Proofs.Lib.PartitionMetricConversion.flip, hx, hy, h, Bool.false_eq_true, Xor]
    tauto

/-- The pairs of labels between which a graph `H` differs from `G` on
some pair of distinct vertices. -/
noncomputable def toggleOf (G : SimpleGraph V) {p : ℕ} (part : V → Fin p)
    (H : SimpleGraph V) (i j : Fin p) : Bool :=
  open Classical in
  decide (∃ x y, part x = i ∧ part y = j ∧ x ≠ y ∧ ¬ (H.Adj x y ↔ G.Adj x y))

theorem toggleOf_symm (G : SimpleGraph V) {p : ℕ} (part : V → Fin p)
    (H : SimpleGraph V) (i j : Fin p) : toggleOf G part H i j = toggleOf G part H j i := by
  classical
  unfold toggleOf
  congr 1
  apply propext
  constructor
  · rintro ⟨x, y, hx, hy, hxy, h⟩
    exact ⟨y, x, hy, hx, hxy.symm, by rwa [H.adj_comm, G.adj_comm]⟩
  · rintro ⟨x, y, hx, hy, hxy, h⟩
    exact ⟨y, x, hy, hx, hxy.symm, by rwa [H.adj_comm, G.adj_comm]⟩

theorem eq_flip_toggleOf (G : SimpleGraph V) {p : ℕ} (part : V → Fin p)
    (H : SimpleGraph V) (hH : IsFlip G (Setoid.ker part) H) :
    H = flip G part (toggleOf G part H) (toggleOf_symm G part H) := by
  classical
  ext x y
  simp only [Lax185574Proofs.Lib.PartitionMetricConversion.flip, toggleOf,
    decide_eq_true_eq, Xor]
  by_cases hxy : x = y
  · subst hxy; simp
  rcases hH x y with h | h
  · have hn : ¬ ∃ x' y', part x' = part x ∧ part y' = part y ∧ x' ≠ y' ∧
        ¬ (H.Adj x' y' ↔ G.Adj x' y') := by
      rintro ⟨x', y', hx', hy', hxy', h'⟩
      exact h' (h x' y' hx' hy' hxy')
    have := h x y rfl rfl hxy
    simp only [hn, this]
    tauto
  · by_cases hd : ∃ x' y', part x' = part x ∧ part y' = part y ∧ x' ≠ y' ∧
        ¬ (H.Adj x' y' ↔ G.Adj x' y')
    · have := h x y rfl rfl hxy
      simp only [hd, this]
      tauto
    · exfalso
      exact hd ⟨x, y, rfl, rfl, hxy, by rw [h x y rfl rfl hxy]; tauto⟩

theorem exists_eq_flip_of_isFlip (G : SimpleGraph V) {p : ℕ} (part : V → Fin p)
    (H : SimpleGraph V) (hH : IsFlip G (Setoid.ker part) H) :
    ∃ (toggle : Fin p → Fin p → Bool) (hsymm : ∀ i j, toggle i j = toggle j i),
      H = flip G part toggle hsymm :=
  ⟨_, _, eq_flip_toggleOf G part H hH⟩

theorem partitionBall_eq_flipBall (G : SimpleGraph V) {p : ℕ} (part : V → Fin p)
    (r : ℕ) (v : V) : partitionBall G part r v = flipBall G (Setoid.ker part) r v := by
  ext u
  constructor
  · intro hu H hH
    obtain ⟨toggle, hsymm, rfl⟩ := exists_eq_flip_of_isFlip G part H hH
    exact hu toggle hsymm
  · intro hu toggle hsymm
    exact hu _ (isFlip_flip G part toggle hsymm)

/-- A labeling of a finite type by the parts of a partition. -/
noncomputable def labeling (P : Setoid V) [Finite (Quotient P)] :
    V → Fin (Nat.card (Quotient P)) :=
  fun v => (Finite.equivFin (Quotient P)) (Quotient.mk P v)

theorem ker_labeling (P : Setoid V) [Finite (Quotient P)] :
    Setoid.ker (labeling P) = P := by
  ext x y
  simp only [labeling, Setoid.ker_def, EmbeddingLike.apply_eq_iff_eq, Quotient.eq]

theorem card_quotient_ker_le {p : ℕ} (f : V → Fin p) :
    Nat.card (Quotient (Setoid.ker f)) ≤ p := by
  have hinj : Function.Injective (Quotient.lift f fun _ _ h => h : Quotient (Setoid.ker f) → Fin p) := by
    rintro ⟨a⟩ ⟨b⟩ h
    exact Quotient.sound h
  simpa using Nat.card_le_card_of_injective _ hinj

end Lax185574Proofs.FlipBridge
