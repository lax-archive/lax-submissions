import Lax185574Proofs.Lib.PartitionMetricConversionDefs
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.PartitionMetricWalks

open Lax185574Proofs.Lib.PartitionMetricConversion

universe u v

theorem within_refl {V : Type u} (G : SimpleGraph V) (x : V) (r : ℕ) :
    Within G r x x := ⟨.nil, Nat.zero_le _⟩

theorem within_edge {V : Type u} {G : SimpleGraph V} {x y : V} (h : G.Adj x y) :
    Within G 1 x y := ⟨.cons h .nil, by simp⟩

theorem within_mono {V : Type u} {G : SimpleGraph V} {x y : V} {r s : ℕ}
    (h : Within G r x y) (hrs : r ≤ s) : Within G s x y := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, hw.trans hrs⟩

theorem within_symm {V : Type u} {G : SimpleGraph V} {x y : V} {r : ℕ}
    (h : Within G r x y) : Within G r y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse, by simpa using hw⟩

theorem within_trans {V : Type u} {G : SimpleGraph V} {x y z : V} {r s : ℕ}
    (h : Within G r x y) (h' : Within G s y z) : Within G (r + s) x z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact ⟨w.append w', by simpa using Nat.add_le_add hw hw'⟩

theorem within_map {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : ∀ x y, G.Adj x y → H.Adj (f x) (f y))
    {x y : V} {r : ℕ} (h : Within G r x y) : Within H r (f x) (f y) := by
  obtain ⟨w, hw⟩ := h
  let hom : G →g H := ⟨f, fun h => hf _ _ h⟩
  exact ⟨w.map hom, by simpa using hw⟩

/-- Replacing every edge by a walk of length at most `c` expands every
walk by at most the factor `c`. -/
theorem within_edge_transfer {V : Type u} {G H : SimpleGraph V} (c : ℕ)
    (h : ∀ x y, G.Adj x y → Within H c x y)
    {x y : V} {r : ℕ} (hxy : Within G r x y) : Within H (c * r) x y := by
  obtain ⟨w, hw⟩ := hxy
  have hwalk : ∀ {x y : V} (w : G.Walk x y), Within H (c * w.length) x y := by
    intro x y w
    induction w with
    | nil => exact within_refl H _ _
    | @cons x y z hxy w ih =>
      simpa [SimpleGraph.Walk.length_cons, Nat.mul_add, Nat.add_comm] using
        within_trans (h x y hxy) ih
  exact within_mono (hwalk w) (Nat.mul_le_mul_left c hw)

end Lax185574Proofs.Lib.PartitionMetricWalks
