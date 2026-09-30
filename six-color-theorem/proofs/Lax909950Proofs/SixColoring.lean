import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Maps
import Lax909950.LowDegree
import Lax909950.SixColoring

namespace Lax909950Proofs

open Lax909950 Lax68.StraightLineDrawings

/-- Pulling a straight-line drawing back along an injective map. -/
def drawingComap {V W : Type*} {G : SimpleGraph W} (D : StraightLineDrawing G)
    (f : V ↪ W) : StraightLineDrawing (G.comap f) where
  point := D.point ∘ f
  injective := D.injective.comp f.injective
  noVertexOnEdge := fun hab hca hcb =>
    D.noVertexOnEdge hab (f.injective.ne hca) (f.injective.ne hcb)
  disjointEdges := fun {a b c d} hab hcd hdisj => by
    refine D.disjointEdges hab hcd ?_
    simp only [Set.disjoint_insert_left, Set.disjoint_insert_right, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.disjoint_singleton, ne_eq] at hdisj ⊢
    simpa only [f.injective.eq_iff] using hdisj

/-- Induced subgraphs of planar graphs are planar. -/
theorem isPlanar_induce {V : Type*} {G : SimpleGraph V} (hG : Lax68.Planar.IsPlanar G)
    (s : Set V) : Lax68.Planar.IsPlanar (G.induce s) :=
  ⟨drawingComap hG.some (Function.Embedding.subtype _)⟩

/--
---
conclusion: Lax909950.SixColoring.six_colorable
---
By induction on the number of vertices: remove a vertex of degree at most $5$,
color the remaining graph, and give the removed vertex a color not used by any
of its neighbors.
-/
theorem six_colorable {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) :
    G.Colorable 6 := by
  classical
  suffices h : ∀ (n : ℕ) (V : Type _) [Finite V] (G : SimpleGraph V),
      Nat.card V = n → Lax68.Planar.IsPlanar G → G.Colorable 6 from
    h _ V G rfl hG
  intro n
  induction n with
  | zero =>
    intro V _ G hn _
    have : IsEmpty V :=
      (Nat.card_eq_zero.1 hn).resolve_right (not_infinite_iff_finite.2 inferInstance)
    exact ⟨SimpleGraph.Coloring.mk isEmptyElim fun {a} => isEmptyElim a⟩
  | succ n ih =>
    intro V _ G hn hG
    have : Nonempty V := (Nat.card_pos_iff.1 (by omega)).1
    obtain ⟨x, hx⟩ := LowDegree.exists_degree_le_five hG
    let s : Set V := {x}ᶜ
    have hs : Nat.card s = n := by
      have := Set.ncard_add_ncard_compl ({x} : Set V)
      rw [Set.ncard_singleton] at this
      rw [Nat.card_coe_set_eq]; show ({x}ᶜ : Set V).ncard = n; omega
    obtain ⟨C⟩ := ih s (G.induce s) hs (isPlanar_induce hG s)
    -- colors used by the neighbors of `x`
    let used : Set (Fin 6) := {c | ∃ y, ∃ hy : y ≠ x, G.Adj x y ∧ C ⟨y, hy⟩ = c}
    have hused : used.ncard ≤ 5 := by
      have : used ⊆ (fun y => if hy : y ≠ x then C ⟨y, hy⟩ else 0) '' G.neighborSet x := by
        rintro c ⟨y, hy, hxy, rfl⟩
        exact ⟨y, hxy, by simp [hy]⟩
      exact (Set.ncard_le_ncard this (Set.toFinite _)).trans
        (Set.ncard_image_le (Set.toFinite _)) |>.trans hx
    obtain ⟨c₀, hc₀⟩ : ∃ c, c ∉ used := by
      by_contra! h
      have : used = Set.univ := Set.eq_univ_of_forall h
      rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hused
      omega
    let col : V → Fin 6 := fun y => if hy : y ≠ x then C ⟨y, hy⟩ else c₀
    refine ⟨SimpleGraph.Coloring.mk col fun {a b} hab => ?_⟩
    by_cases ha : a = x <;> by_cases hb : b = x
    · subst ha; subst hb; exact (hab.ne rfl).elim
    · subst ha
      simp only [col, hb, ne_eq, not_false_eq_true, dite_true, not_true_eq_false, dite_false]
      exact fun h => hc₀ ⟨b, hb, hab, h.symm⟩
    · subst hb
      simp only [col, ha, ne_eq, not_false_eq_true, dite_true, not_true_eq_false, dite_false]
      exact fun h => hc₀ ⟨a, ha, hab.symm, h⟩
    · simp only [col, ha, hb, ne_eq, not_false_eq_true, dite_true]
      exact C.valid (v := ⟨a, ha⟩) (w := ⟨b, hb⟩) (by simpa using hab)

end Lax909950Proofs
