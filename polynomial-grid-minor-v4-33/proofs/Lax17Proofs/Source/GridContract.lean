import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Basic

namespace Lax17Proofs

universe u v w

/-!
# Square grid graphs

This contract file defines the finite `(g x g)` grid graph used in the
polynomial grid-minor theorem.  Vertices are indexed by pairs of `Fin g`; two
vertices are adjacent exactly when they agree in one coordinate and their other
coordinates are consecutive.
-/

namespace SimpleGraph

/-- Vertices of the square `g x g` grid. -/
abbrev GridVertex (g : ℕ) : Type :=
  Fin g × Fin g

/-- Two indices of `Fin n` are consecutive when their natural values differ by
one. -/
def FinConsecutive {n : ℕ} (a b : Fin n) : Prop :=
  a.1 + 1 = b.1 ∨ b.1 + 1 = a.1

namespace FinConsecutive

/-- A finite index is consecutive with its successor, when that successor still
lies in the same `Fin` type. -/
theorem succ {n : ℕ} (a : Fin n) (h : a.1 + 1 < n) :
    FinConsecutive a ⟨a.1 + 1, h⟩ :=
  Or.inl rfl

/-- The successor index is consecutive with the original index. -/
theorem succ_symm {n : ℕ} (a : Fin n) (h : a.1 + 1 < n) :
    FinConsecutive ⟨a.1 + 1, h⟩ a :=
  Or.inr rfl

theorem symm {n : ℕ} {a b : Fin n} (h : FinConsecutive a b) :
    FinConsecutive b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem irrefl {n : ℕ} (a : Fin n) :
    ¬ FinConsecutive a a := by
  intro h
  rcases h with h | h
  · have : a.1 < a.1 := by
      simpa [h] using Nat.lt_succ_self a.1
    exact (Nat.lt_irrefl a.1) this
  · have : a.1 < a.1 := by
      simpa [h] using Nat.lt_succ_self a.1
    exact (Nat.lt_irrefl a.1) this

end FinConsecutive

/-- Adjacency in the square `g x g` grid. -/
def GridAdj {g : ℕ} (u v : GridVertex g) : Prop :=
  (u.1 = v.1 ∧ FinConsecutive u.2 v.2) ∨
    (u.2 = v.2 ∧ FinConsecutive u.1 v.1)

/-- The square `g x g` grid graph.

For `g = 0`, the vertex type is empty.  For `g = 1`, the graph has one isolated
vertex.  The polynomial grid-minor theorem is stated only for `2 <= g`.
-/
def gridGraph (g : ℕ) : _root_.SimpleGraph (GridVertex g) where
  Adj := GridAdj
  symm := by
    intro u v h
    rcases h with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
    · exact Or.inl ⟨hrow.symm, hcol.symm⟩
    · exact Or.inr ⟨hcol.symm, hrow.symm⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨_hrow, hcol⟩ | ⟨_hcol, hrow⟩
    · exact FinConsecutive.irrefl u.2 hcol
    · exact FinConsecutive.irrefl u.1 hrow⟩

theorem gridGraph_adj_iff {g : ℕ} (u v : GridVertex g) :
    (gridGraph g).Adj u v ↔
      (u.1 = v.1 ∧ FinConsecutive u.2 v.2) ∨
        (u.2 = v.2 ∧ FinConsecutive u.1 v.1) :=
  Iff.rfl

/-- Two vertices in the same row and consecutive columns are adjacent in the
canonical grid. -/
theorem gridGraph_adj_of_same_row {g : ℕ} (r : Fin g) {c d : Fin g}
    (hcd : FinConsecutive c d) :
    (gridGraph g).Adj (r, c) (r, d) :=
  Or.inl ⟨rfl, hcd⟩

/-- Two vertices in the same column and consecutive rows are adjacent in the
canonical grid. -/
theorem gridGraph_adj_of_same_col {g : ℕ} {r s : Fin g} (c : Fin g)
    (hrs : FinConsecutive r s) :
    (gridGraph g).Adj (r, c) (s, c) :=
  Or.inr ⟨rfl, hrs⟩

/-- Horizontal successor edges of the canonical grid. -/
theorem gridGraph_adj_right {g : ℕ} (r c : Fin g)
    (hc : c.1 + 1 < g) :
    (gridGraph g).Adj (r, c) (r, ⟨c.1 + 1, hc⟩) :=
  gridGraph_adj_of_same_row r (FinConsecutive.succ c hc)

/-- Vertical successor edges of the canonical grid. -/
theorem gridGraph_adj_down {g : ℕ} (r c : Fin g)
    (hr : r.1 + 1 < g) :
    (gridGraph g).Adj (r, c) (⟨r.1 + 1, hr⟩, c) :=
  gridGraph_adj_of_same_col c (FinConsecutive.succ r hr)

/-- `H` is a `g x g` grid graph when it is isomorphic to the canonical
`gridGraph g`.

This predicate is the isomorphism-closed interface used by graph-minor
statements.  The concrete `gridGraph g` remains the canonical representative
for constructions and computations.
-/
def IsGridGraph {V : Type*} (H : _root_.SimpleGraph V) (g : ℕ) : Prop :=
  Nonempty (H ≃g gridGraph g)

@[simp] theorem gridGraph_isGridGraph (g : ℕ) :
    IsGridGraph (gridGraph g) g :=
  ⟨_root_.SimpleGraph.Iso.refl⟩

/-- The canonical `g x g` grid has `g * g` vertices. -/
@[simp] theorem card_gridVertex (g : ℕ) :
    Fintype.card (GridVertex g) = g * g := by
  simp [GridVertex]

/-- If `2 <= g`, then the canonical coordinate set for the `g x g` grid is
nontrivial. -/
theorem two_le_card_gridVertex_of_two_le {g : ℕ} (hg : 2 ≤ g) :
    2 ≤ Fintype.card (GridVertex g) := by
  rw [card_gridVertex]
  calc
    2 = 2 * 1 := by simp
    _ ≤ g * g := Nat.mul_le_mul hg (le_trans (by decide : 1 ≤ 2) hg)

namespace IsGridGraph

/-- Being a `g x g` grid graph is preserved by graph isomorphism. -/
theorem of_iso {V W : Type*}
    {H : _root_.SimpleGraph V} {H' : _root_.SimpleGraph W} {g : ℕ}
    (e : H' ≃g H) (hH : IsGridGraph H g) :
    IsGridGraph H' g := by
  rcases hH with ⟨φ⟩
  exact ⟨e.trans φ⟩

/-- The predicate `IsGridGraph` is invariant under graph isomorphism. -/
theorem iso_iff {V W : Type*}
    {H : _root_.SimpleGraph V} {H' : _root_.SimpleGraph W} {g : ℕ}
    (e : H ≃g H') :
    IsGridGraph H g ↔ IsGridGraph H' g :=
  ⟨of_iso e.symm, of_iso e⟩

/-- Any `g x g` grid graph has `g * g` vertices. -/
theorem card_eq {V : Type*} [Fintype V]
    {H : _root_.SimpleGraph V} {g : ℕ}
    (hH : IsGridGraph H g) :
    Fintype.card V = g * g := by
  rcases hH with ⟨e⟩
  simpa using e.card_eq

end IsGridGraph

end SimpleGraph

end Lax17Proofs
