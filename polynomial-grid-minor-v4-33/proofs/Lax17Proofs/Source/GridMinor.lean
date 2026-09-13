import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.MinorTransitivity

namespace Lax17Proofs

universe u v w


/-!
# Basic grid-minor constructions

This file proves elementary facts about the canonical grid graph.  In
particular, a larger canonical grid contains a smaller canonical grid as a
minor by taking singleton branch sets at the corresponding coordinates.
-/

namespace SimpleGraph

/-- The canonical grid vertex type lifted into an arbitrary universe. -/
abbrev GridVertexULift (g : ℕ) : Type u :=
  ULift.{u, 0} (GridVertex g)

/-- The canonical grid graph lifted into an arbitrary universe. -/
def gridGraphULift (g : ℕ) : _root_.SimpleGraph (GridVertexULift.{u} g) :=
  _root_.SimpleGraph.comap Equiv.ulift (gridGraph g)

/-- The lifted canonical grid is isomorphic to the canonical grid. -/
noncomputable def gridGraphULiftIso (g : ℕ) :
    gridGraphULift.{u} g ≃g gridGraph g :=
  { Equiv.ulift with
    map_rel_iff' := by
      intro u v
      rfl }

@[simp] theorem gridGraphULift_isGridGraph (g : ℕ) :
    IsGridGraph (gridGraphULift.{u} g) g :=
  ⟨gridGraphULiftIso.{u} g⟩

namespace GridVertex

/-- Embed the vertex set of a smaller canonical grid into a larger one. -/
def castLE {g h : ℕ} (hgh : g ≤ h) : GridVertex g → GridVertex h :=
  fun v => (⟨v.1.1, lt_of_lt_of_le v.1.2 hgh⟩,
    ⟨v.2.1, lt_of_lt_of_le v.2.2 hgh⟩)

/-- The coordinate embedding into a larger grid is injective. -/
theorem castLE_injective {g h : ℕ} (hgh : g ≤ h) :
    Function.Injective (castLE hgh) := by
  intro u v huv
  cases u with
  | mk ur uc =>
      cases v with
      | mk vr vc =>
          simp [castLE] at huv
          exact Prod.ext (Fin.ext huv.1) (Fin.ext huv.2)

end GridVertex

namespace FinConsecutive

/-- Consecutive finite indices remain consecutive after casting into a larger
finite type. -/
theorem castLE {g h : ℕ} (hgh : g ≤ h) {a b : Fin g}
    (hab : FinConsecutive a b) :
    FinConsecutive (⟨a.1, lt_of_lt_of_le a.2 hgh⟩ : Fin h)
      (⟨b.1, lt_of_lt_of_le b.2 hgh⟩ : Fin h) := by
  exact hab

end FinConsecutive

/-- Adjacency in a canonical grid is preserved by the coordinate embedding into
a larger grid. -/
theorem gridGraph_adj_castLE {g h : ℕ} (hgh : g ≤ h)
    {u v : GridVertex g} :
    (gridGraph g).Adj u v →
      (gridGraph h).Adj (GridVertex.castLE hgh u) (GridVertex.castLE hgh v) := by
  intro huv
  rcases huv with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · exact Or.inl ⟨by simp [GridVertex.castLE, hrow],
      FinConsecutive.castLE hgh hcol⟩
  · exact Or.inr ⟨by simp [GridVertex.castLE, hcol],
      FinConsecutive.castLE hgh hrow⟩

/-- The canonical `g x g` grid is a minor of the canonical `h x h` grid whenever
`g <= h`. -/
noncomputable def gridGraphMinorOfLE {g h : ℕ} (hgh : g ≤ h) :
    MinorModel (gridGraph g) (gridGraph h) where
  branchSet := fun v => {GridVertex.castLE hgh v}
  branch_nonempty := by
    intro v
    exact ⟨GridVertex.castLE hgh v, by simp⟩
  branch_connected := by
    intro v
    let e := GridVertex.castLE hgh v
    haveI : Nonempty {x : GridVertex h | x ∈ ({e} : Finset (GridVertex h))} :=
      ⟨⟨e, by simp⟩⟩
    haveI : Subsingleton {x : GridVertex h | x ∈ ({e} : Finset (GridVertex h))} := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : x.1 = e := by simpa using x.2
      have hy : y.1 = e := by simpa using y.2
      exact hx.trans hy.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    have hxu' : x = GridVertex.castLE hgh u := by simpa using hxu
    have hxv' : x = GridVertex.castLE hgh v := by simpa using hxv
    apply huv
    exact GridVertex.castLE_injective hgh (hxu'.symm.trans hxv')
  adjacent := by
    intro u v huv
    refine ⟨GridVertex.castLE hgh u, by simp,
      GridVertex.castLE hgh v, by simp, ?_⟩
    exact gridGraph_adj_castLE hgh huv

/-- Larger canonical grids contain smaller canonical grids as minors. -/
theorem gridGraph_isMinor_of_le {g h : ℕ} (hgh : g ≤ h) :
    IsMinor (gridGraph g) (gridGraph h) :=
  ⟨gridGraphMinorOfLE hgh⟩

/-- Larger canonical grids contain smaller grid minors. -/
theorem gridGraph_containsGridMinor_of_le {g h : ℕ} (hgh : g ≤ h) :
    ContainsGridMinor (gridGraph h) g := by
  exact ⟨GridVertex g, inferInstance, inferInstance, gridGraph g,
    gridGraph_isGridGraph g, gridGraph_isMinor_of_le hgh⟩

/-- A graph isomorphic to an `h x h` grid contains the canonical `g x g` grid
as a minor whenever `g <= h`. -/
noncomputable def gridGraphMinorOfLEIso {W : Type*} [DecidableEq W]
    {H : _root_.SimpleGraph W} {g h : ℕ}
    (hH : IsGridGraph H h) (hgh : g ≤ h) :
    MinorModel (gridGraph g) H :=
  let e := Classical.choice hH
  by
  classical
  refine {
    branchSet := fun v => {e.symm (GridVertex.castLE hgh v)}
    branch_nonempty := ?_
    branch_connected := ?_
    branch_disjoint := ?_
    adjacent := ?_
  }
  · intro v
    exact ⟨e.symm (GridVertex.castLE hgh v), by simp⟩
  · intro v
    let x := e.symm (GridVertex.castLE hgh v)
    haveI : Nonempty {y : W | y ∈ ({x} : Finset W)} :=
      ⟨⟨x, by simp⟩⟩
    haveI : Subsingleton {y : W | y ∈ ({x} : Finset W)} := by
      constructor
      intro y z
      apply Subtype.ext
      have hy : y.1 = x := by simpa using y.2
      have hz : z.1 = x := by simpa using z.2
      exact hy.trans hz.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  · intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    have hxu' : x = e.symm (GridVertex.castLE hgh u) := by simpa using hxu
    have hxv' : x = e.symm (GridVertex.castLE hgh v) := by simpa using hxv
    apply huv
    apply GridVertex.castLE_injective hgh
    apply e.symm.injective
    exact hxu'.symm.trans hxv'
  · intro u v huv
    refine ⟨e.symm (GridVertex.castLE hgh u), by simp,
      e.symm (GridVertex.castLE hgh v), by simp, ?_⟩
    exact (_root_.SimpleGraph.Iso.map_adj_iff e.symm).mpr
      (gridGraph_adj_castLE hgh huv)

/-- A graph isomorphic to a larger grid contains each smaller canonical grid as
a minor. -/
theorem gridGraph_isMinor_of_le_iso {W : Type*} [DecidableEq W]
    {H : _root_.SimpleGraph W} {g h : ℕ}
    (hH : IsGridGraph H h) (hgh : g ≤ h) :
    IsMinor (gridGraph g) H :=
  ⟨gridGraphMinorOfLEIso hH hgh⟩

namespace IsGridGraph

/-- Any graph isomorphic to an `h x h` grid contains the `g x g` grid as a
minor whenever `g <= h`. -/
theorem containsGridMinor_of_le {W : Type u} [DecidableEq W]
    {H : _root_.SimpleGraph W} {g h : ℕ}
    (hH : IsGridGraph H h) (hgh : g ≤ h) :
    ContainsGridMinor H g := by
  have hsmallH : IsMinor.{0, u} (gridGraph g) H :=
    gridGraph_isMinor_of_le_iso hH hgh
  exact ⟨GridVertexULift.{u} g, inferInstance, inferInstance,
    gridGraphULift.{u} g, gridGraphULift_isGridGraph.{u} g,
    IsMinor.of_iso_left (gridGraphULiftIso.{u} g) hsmallH⟩

/-- Any graph isomorphic to a `g x g` grid contains the `g x g` grid as a
minor. -/
theorem containsGridMinor_self {W : Type u} [DecidableEq W]
    {H : _root_.SimpleGraph W} {g : ℕ}
    (hH : IsGridGraph H g) :
    ContainsGridMinor H g :=
  hH.containsGridMinor_of_le le_rfl

end IsGridGraph

namespace ContainsGridMinor

/-- A canonical `g x g` grid minor gives grid-minor containment.  The `ULift`
bridge keeps the result universe-polymorphic in the host graph. -/
theorem of_gridGraph_isMinor {V : Type u} {G : _root_.SimpleGraph V} {g : ℕ}
    (hminor : IsMinor (gridGraph g) G) :
    ContainsGridMinor G g := by
  exact ⟨GridVertexULift.{u} g, inferInstance, inferInstance,
    gridGraphULift.{u} g, gridGraphULift_isGridGraph.{u} g,
    IsMinor.of_iso_left (gridGraphULiftIso.{u} g) hminor⟩

/-- A concrete branch-set model of the canonical grid gives grid-minor
containment. -/
theorem of_gridGraph_model {V : Type u} {G : _root_.SimpleGraph V} {g : ℕ}
    (M : MinorModel (gridGraph g) G) :
    ContainsGridMinor G g :=
  of_gridGraph_isMinor ⟨M⟩

/-- Build grid-minor containment directly from a branch-set model indexed by
the canonical grid vertices.  This is the proof target used by the explicit
path-of-sets and crossbar-grid constructions. -/
theorem of_grid_branchSets {V : Type u} {G : _root_.SimpleGraph V} {g : ℕ}
    (branchSet : GridVertex g → Finset V)
    (branch_nonempty : ∀ x : GridVertex g, (branchSet x).Nonempty)
    (branch_connected :
      ∀ x : GridVertex g, (G.induce {v : V | v ∈ branchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y → Disjoint (branchSet x) (branchSet y))
    (adjacent :
      ∀ ⦃x y : GridVertex g⦄, (gridGraph g).Adj x y →
        ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, G.Adj u v) :
    ContainsGridMinor G g :=
  of_gridGraph_model {
    branchSet := branchSet
    branch_nonempty := branch_nonempty
    branch_connected := branch_connected
    branch_disjoint := branch_disjoint
    adjacent := adjacent
  }

/-- A graph embedding of the canonical grid gives grid-minor containment. -/
theorem of_gridGraph_embedding {V : Type u} {G : _root_.SimpleGraph V}
    {g : ℕ} (e : gridGraph g ↪g G) :
    ContainsGridMinor G g :=
  of_gridGraph_isMinor (IsMinor.of_embedding e)

/-- Grid-minor containment is monotone in the requested grid order. -/
theorem of_order_le {V : Type u} {G : _root_.SimpleGraph V} {g h : ℕ}
    (hgrid : ContainsGridMinor G h) (hgh : g ≤ h) :
    ContainsGridMinor G g := by
  rcases hgrid with ⟨W, hWfin, hWdec, H, hHgrid, hminor⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  have hsmallH : IsMinor.{0, u} (gridGraph g) H :=
    gridGraph_isMinor_of_le_iso hHgrid hgh
  have hsmallG : IsMinor.{0, u} (gridGraph g) G := hsmallH.trans hminor
  exact of_gridGraph_isMinor hsmallG

end ContainsGridMinor

end SimpleGraph

end Lax17Proofs
