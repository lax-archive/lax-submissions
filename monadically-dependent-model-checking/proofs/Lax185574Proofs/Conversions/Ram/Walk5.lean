import Lax185574Proofs.BipartiteWalks

/-!
Walks of length at most five between the two sides of a bipartite
graph, as chains of four intermediate vertices.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax185574.BipartiteGraphs Lax185574.GaifmanGraph Lax185574Proofs.BipartiteWalks

variable {α β : Type*}

/-- Alternating chains of `k` back-and-forth steps followed by one step. -/
def Chain (R : α → β → Prop) : ℕ → α → β → Prop
  | 0, a, b => R a b
  | k + 1, a, b => ∃ b' a', R a b' ∧ R a' b' ∧ Chain R k a' b

theorem Chain.first {R : α → β → Prop} : ∀ {k : ℕ} {a : α} {b : β}, Chain R k a b → ∃ b', R a b'
  | 0, _, b, h => ⟨b, h⟩
  | _ + 1, _, _, ⟨b', _, h, _⟩ => ⟨b', h⟩

theorem Chain.pad {R : α → β → Prop} : ∀ {k : ℕ} {a : α} {b : β}, Chain R k a b → Chain R (k + 1) a b
  | 0, a, b, h => ⟨b, a, h, h, h⟩
  | _ + 1, a, _, ⟨b', a', h1, h2, h3⟩ => ⟨b', a, h1, h1, ⟨b', a', h1, h2, h3⟩⟩

theorem Chain.mono {R : α → β → Prop} {k l : ℕ} (hkl : k ≤ l) {a : α} {b : β}
    (h : Chain R k a b) : Chain R l a b := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact ih.pad

theorem chain_of_walk {R : α → β → Prop} {b : β} :
    ∀ (k : ℕ) (a : α) (p : (bipartiteGraph R).Walk (.inl a) (.inr b)), p.length ≤ 2 * k + 1 →
      Chain R k a b := by
  intro k
  induction k with
  | zero =>
    intro a p hp
    match p with
    | .cons h .nil => exact (adj_inl_inr R a b).mp h
    | .cons (v := .inr b1) h (.cons h2 p') => simp at hp
    | .cons (v := .inl a1) h p' => exact absurd h (not_adj_inl_inl R _ _)
  | succ k ih =>
    intro a p hp
    match p with
    | .cons h .nil => exact Chain.pad (k := k) (Chain.mono (Nat.zero_le k) ((adj_inl_inr R a b).mp h))
    | .cons (v := .inr b1) h (.cons (v := .inl a2) h2 p') =>
      refine ⟨b1, a2, (adj_inl_inr R a b1).mp h, (adj_inr_inl R a2 b1).mp h2, ih a2 p' ?_⟩
      simp at hp; omega
    | .cons (v := .inr b1) h (.cons (v := .inr b2) h2 p') => exact absurd h2 (not_adj_inr_inr R _ _)
    | .cons (v := .inl a1) h p' => exact absurd h (not_adj_inl_inl R _ _)

theorem walk_of_chain {R : α → β → Prop} {b : β} :
    ∀ (k : ℕ) (a : α), Chain R k a b →
      ∃ p : (bipartiteGraph R).Walk (.inl a) (.inr b), p.length = 2 * k + 1
  | 0, a, h => ⟨.cons ((adj_inl_inr R a b).mpr h) .nil, rfl⟩
  | k + 1, a, ⟨b', a', h1, h2, h3⟩ => by
    obtain ⟨p, hp⟩ := walk_of_chain k a' h3
    exact ⟨.cons ((adj_inl_inr R a b').mpr h1) (.cons ((adj_inr_inl R a' b').mpr h2) p),
      by simp [hp]; omega⟩

/-- **Walks of length at most five.** -/
theorem withinDist5_iff {R : α → β → Prop} {a : α} {b : β} :
    WithinDist (bipartiteGraph R) 5 (.inl a) (.inr b) ↔
      ∃ b1 a2 b3 a4, R a b1 ∧ R a2 b1 ∧ R a2 b3 ∧ R a4 b3 ∧ R a4 b := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨b1, a2, h1, h2, b3, a4, h3, h4, h5⟩ := chain_of_walk 2 a p (by omega)
    exact ⟨b1, a2, b3, a4, h1, h2, h3, h4, h5⟩
  · rintro ⟨b1, a2, b3, a4, h1, h2, h3, h4, h5⟩
    obtain ⟨p, hp⟩ := walk_of_chain (R := R) 2 a ⟨b1, a2, h1, h2, b3, a4, h3, h4, h5⟩
    exact ⟨p, by omega⟩

end Lax185574Proofs.Conversions.Ram
