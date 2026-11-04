import Lax185574.GaifmanGraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
Basic facts about bounded walks: reflexivity, single edges, composition,
monotonicity in the bound and in the graph, symmetry, and transport along
graph homomorphisms.
-/

namespace Lax185574Proofs.WithinDistBasics

open Lax185574.GaifmanGraph

variable {W W' : Type*} {G : SimpleGraph W}

theorem withinDist_refl (d : ℕ) (u : W) : WithinDist G d u u :=
  ⟨.nil, by simp⟩

theorem withinDist_adj {u v : W} (h : G.Adj u v) : WithinDist G 1 u v :=
  ⟨h.toWalk, by simp⟩

theorem withinDist_mono {d e : ℕ} (hde : d ≤ e) {u v : W} (h : WithinDist G d u v) :
    WithinDist G e u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hde⟩

theorem withinDist_trans {d e : ℕ} {u v w : W} (h₁ : WithinDist G d u v)
    (h₂ : WithinDist G e v w) : WithinDist G (d + e) u w := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, by rw [SimpleGraph.Walk.length_append]; omega⟩

theorem withinDist_symm' {d : ℕ} {u v : W} (h : WithinDist G d u v) : WithinDist G d v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

theorem withinDist_map' {G' : SimpleGraph W'} (f : G →g G') {d : ℕ} {u v : W}
    (h : WithinDist G d u v) : WithinDist G' d (f u) (f v) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.map f, by simpa using hp⟩

theorem withinDist_le_graph {H : SimpleGraph W} (hGH : G ≤ H) {d : ℕ} {u v : W}
    (h : WithinDist G d u v) : WithinDist H d u v :=
  withinDist_map' (SimpleGraph.Hom.ofLE hGH) h

/-- Projecting a walk along a map that sends every edge to an edge or to
a single vertex does not increase its length. -/
theorem withinDist_of_project {K : SimpleGraph W'} (f : W' → W)
    (hf : ∀ s t, K.Adj s t → f s = f t ∨ G.Adj (f s) (f t)) {d : ℕ} {s t : W'}
    (h : WithinDist K d s t) : WithinDist G d (f s) (f t) := by
  obtain ⟨p, hp⟩ := h
  induction p generalizing d with
  | nil => exact withinDist_refl d _
  | cons hadj p ih =>
    rw [SimpleGraph.Walk.length_cons] at hp
    have := ih (d := d - 1) (by omega)
    rcases hf _ _ hadj with heq | hadj'
    · rw [heq]; exact withinDist_mono (by omega) this
    · exact withinDist_mono (by omega) (withinDist_trans (withinDist_adj hadj') this)

/-- A walk in a graph on `W'` of length at most `r`, each of whose edges
maps to a pair within distance `c`, gives a walk of length at most
`c * r`. -/
theorem withinDist_of_steps {K : SimpleGraph W'} (f : W' → W) (c : ℕ)
    (hf : ∀ s t, K.Adj s t → WithinDist G c (f s) (f t)) {r : ℕ} {s t : W'}
    (h : WithinDist K r s t) : WithinDist G (c * r) (f s) (f t) := by
  obtain ⟨p, hp⟩ := h
  induction p generalizing r with
  | nil => exact withinDist_refl _ _
  | cons hadj p ih =>
    rw [SimpleGraph.Walk.length_cons] at hp
    have := ih (r := r - 1) (by omega)
    refine withinDist_mono ?_ (withinDist_trans (hf _ _ hadj) this)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_succ, Nat.add_comm]

end Lax185574Proofs.WithinDistBasics
