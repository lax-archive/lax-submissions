import Lax185574.BipartiteGraphs
import Lax185574Proofs.WithinDistBasics

/-!
Adjacency and walks in the bipartite graph of a relation: its edges join
the two sides, it grows with the relation, and walks between the two
sides have odd length.
-/

namespace Lax185574Proofs.BipartiteWalks

open Lax185574.BipartiteGraphs Lax185574.GaifmanGraph Lax185574Proofs.WithinDistBasics

variable {α β : Type*}

@[simp] theorem adj_inl_inr (E : α → β → Prop) (a : α) (b : β) :
    (bipartiteGraph E).Adj (.inl a) (.inr b) ↔ E a b := by
  simp [bipartiteGraph]

@[simp] theorem adj_inr_inl (E : α → β → Prop) (a : α) (b : β) :
    (bipartiteGraph E).Adj (.inr b) (.inl a) ↔ E a b := by
  simp [bipartiteGraph]

@[simp] theorem not_adj_inl_inl (E : α → β → Prop) (a a' : α) :
    ¬ (bipartiteGraph E).Adj (.inl a) (.inl a') := by
  simp [bipartiteGraph]

@[simp] theorem not_adj_inr_inr (E : α → β → Prop) (b b' : β) :
    ¬ (bipartiteGraph E).Adj (.inr b) (.inr b') := by
  simp [bipartiteGraph]

theorem bipartiteGraph_mono {E E' : α → β → Prop} (h : ∀ a b, E a b → E' a b) :
    bipartiteGraph E ≤ bipartiteGraph E' := by
  intro s t hst
  rcases s with a | b <;> rcases t with a' | b'
  · exact absurd hst (not_adj_inl_inl E _ _)
  · exact (adj_inl_inr E' _ _).mpr (h _ _ ((adj_inl_inr E _ _).mp hst))
  · exact (adj_inr_inl E' _ _).mpr (h _ _ ((adj_inr_inl E _ _).mp hst))
  · exact absurd hst (not_adj_inr_inr E _ _)

/-- Maps of the two sides that carry the relation `E` into `E'` give a
homomorphism of the bipartite graphs. -/
def bipartiteHom {α' β' : Type*} {E : α → β → Prop} {E' : α' → β' → Prop} (f : α → α')
    (g : β → β') (h : ∀ a b, E a b → E' (f a) (g b)) :
    bipartiteGraph E →g bipartiteGraph E' where
  toFun := Sum.map f g
  map_rel' := by
    intro s t hst
    rcases s with a | b <;> rcases t with a' | b'
    · exact absurd hst (not_adj_inl_inl E _ _)
    · exact (adj_inl_inr E' _ _).mpr (h _ _ ((adj_inl_inr E _ _).mp hst))
    · exact (adj_inr_inl E' _ _).mpr (h _ _ ((adj_inr_inl E _ _).mp hst))
    · exact absurd hst (not_adj_inr_inr E _ _)

/-- The side of a vertex of `α ⊕ β`. -/
def side : α ⊕ β → Bool
  | .inl _ => false
  | .inr _ => true

theorem side_ne_of_adj {E : α → β → Prop} {s t : α ⊕ β} (h : (bipartiteGraph E).Adj s t) :
    side s ≠ side t := by
  rcases s with a | b <;> rcases t with a' | b'
  · exact absurd h (not_adj_inl_inl E _ _)
  · simp [side]
  · simp [side]
  · exact absurd h (not_adj_inr_inr E _ _)

theorem length_parity {E : α → β → Prop} {s t : α ⊕ β} (p : (bipartiteGraph E).Walk s t) :
    (p.length % 2 = 0 ↔ side s = side t) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    have := side_ne_of_adj h
    revert ih this
    cases side _ <;> cases side _ <;> cases side _ <;> simp <;> omega

/-- Walks from the left side to the right side have odd length. -/
theorem odd_length {E : α → β → Prop} {a : α} {b : β}
    (p : (bipartiteGraph E).Walk (.inl a) (.inr b)) : p.length % 2 = 1 := by
  have := (length_parity p).not.mpr (by simp [side])
  omega

/-- A walk of length at most `2d + 2` from the left side to the right
side has length at most `2d + 1`. -/
theorem withinDist_odd {E : α → β → Prop} {a : α} {b : β} {d : ℕ}
    (h : WithinDist (bipartiteGraph E) (2 * d + 2) (.inl a) (.inr b)) :
    WithinDist (bipartiteGraph E) (2 * d + 1) (.inl a) (.inr b) := by
  obtain ⟨p, hp⟩ := h
  have := odd_length p
  exact ⟨p, by omega⟩

end Lax185574Proofs.BipartiteWalks
