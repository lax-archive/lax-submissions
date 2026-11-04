import Lax185574.GaifmanGraph
import Lax185574.DistanceLogic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Basic facts about `WithinDist` and about the horizon functions ρ⁻ and ρ⁺,
used throughout the proofs about type trees. Adapted from lax-3
(nowhere-dense-model-checking), files `Lax3Proofs/WalkDistance.lean` and
`Lax3Proofs/Horizon.lean`.
-/

namespace Lax185574Proofs.WalkDistance

open Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus rhoPlus)

variable {V : Type*} {G G' : SimpleGraph V} {u v w : V} {d d' d₁ d₂ : ℕ}

/-! ### Walk distance -/

theorem withinDist_refl (G : SimpleGraph V) (d : ℕ) (v : V) : WithinDist G d v v :=
  ⟨.nil, by simp⟩

theorem withinDist_symm (h : WithinDist G d u v) : WithinDist G d v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

theorem withinDist_trans (h₁ : WithinDist G d₁ u v) (h₂ : WithinDist G d₂ v w) :
    WithinDist G (d₁ + d₂) u w := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, by rw [SimpleGraph.Walk.length_append]; omega⟩

theorem withinDist_mono (hd : d ≤ d') (h : WithinDist G d u v) : WithinDist G d' u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hd⟩

theorem withinDist_zero : WithinDist G 0 u v ↔ u = v := by
  constructor
  · rintro ⟨p, hp⟩
    exact SimpleGraph.Walk.eq_of_length_eq_zero (p := p) (by omega)
  · rintro rfl
    exact withinDist_refl G 0 u

/-- Walk distance is preserved by graph isomorphisms. -/
theorem withinDist_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) :
    WithinDist H d (e u) (e v) ↔ WithinDist G d u v := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨(p.map e.symm.toHom).copy (by simp) (by simp), ?_⟩
    simpa using hp
  · rintro ⟨p, hp⟩
    exact ⟨p.map e.toHom, by simpa using hp⟩

/-! ### Horizon functions -/

/-- ρ⁻(k, q+1) = 9^(q+1) · ρ⁺(k+1, q). -/
theorem rhoMinus_succ_eq (k q : ℕ) : rhoMinus k (q + 1) = 9 ^ (q + 1) * rhoPlus (k + 1) q := by
  rw [Lax3.DistFO.rhoPlus, Lax3.DistFO.rhoMinus, ← pow_add]
  congr 1
  ring

theorem rhoMinus_le_rhoPlus (k q : ℕ) : rhoMinus k q ≤ rhoPlus k q :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- ρ⁻(k, q+1) ≥ 2 ρ⁺(k+1, q). -/
theorem two_mul_rhoPlus_le_rhoMinus (k q : ℕ) :
    2 * rhoPlus (k + 1) q ≤ rhoMinus k (q + 1) := by
  rw [rhoMinus_succ_eq]
  have : 2 ≤ 9 ^ (q + 1) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.succ_pos q))
  exact Nat.mul_le_mul_right _ this

/-- ρ⁺(k, q+1) ≥ 2 ρ⁺(k+1, q). -/
theorem two_mul_rhoPlus_le_rhoPlus (k q : ℕ) :
    2 * rhoPlus (k + 1) q ≤ rhoPlus k (q + 1) :=
  (two_mul_rhoPlus_le_rhoMinus k q).trans (rhoMinus_le_rhoPlus k (q + 1))

end Lax185574Proofs.WalkDistance
