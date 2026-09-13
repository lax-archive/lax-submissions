import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Lax17Proofs.Source.GridMinor
import Lax17Proofs.Source.PathMinor

namespace Lax17Proofs

universe u v w


/-!
# Sparse grid from Chekuri--Chuzhoy Appendix C.1

Chekuri--Chuzhoy Corollary 3.3 constructs an auxiliary graph `G*` from `g`
horizontal rows and `g * (g - 1)` sparse vertical edges, then says that `G*`
immediately contains the `g x g` grid as a minor after suppressing degree-two
vertices.  This file formalizes a compressed version of that auxiliary graph
and proves the grid-minor containment directly by branch sets.

For each intended grid vertex `(r,c)`, the compressed graph has one or two
ports on row `r` in column block `c`: a top/bottom boundary row has one relevant
port, and an internal row has an upper and a lower port joined by a horizontal
edge.  Vertical sparse edges join the lower port of row `r` to the upper port
of row `r+1`; horizontal sparse edges join consecutive column blocks along a
row.  Contracting the one- or two-port branch set in each block gives the
canonical grid.
-/

namespace SimpleGraph

namespace SparseGrid

/-- Vertices of the compressed sparse grid used in Appendix C.1.

The Boolean port is `false` for the upper port of a row block and `true` for
the lower port.  Boundary rows have one relevant port for the minor model, but
keeping both Boolean values in the ambient type avoids a dependent vertex type.
-/
structure Vertex (g : ℕ) where
  row : Fin g
  col : Fin g
  port : Bool
deriving DecidableEq, Fintype

namespace Vertex

variable {g : ℕ}

@[ext] theorem ext {x y : Vertex g}
    (hrow : x.row = y.row) (hcol : x.col = y.col)
    (hport : x.port = y.port) : x = y := by
  cases x
  cases y
  simp_all

/-- The first relevant port of a row block, in left-to-right row order. -/
def firstPort (r : Fin g) : Bool :=
  if r.1 = 0 then true else false

/-- The last relevant port of a row block, in left-to-right row order. -/
def lastPort (r : Fin g) : Bool :=
  if r.1 + 1 = g then false else true

@[simp] theorem firstPort_top {r : Fin g} (h : r.1 = 0) :
    firstPort r = true := by
  simp [firstPort, h]

@[simp] theorem firstPort_not_top {r : Fin g} (h : r.1 ≠ 0) :
    firstPort r = false := by
  simp [firstPort, h]

@[simp] theorem lastPort_bottom {r : Fin g} (h : r.1 + 1 = g) :
    lastPort r = false := by
  simp [lastPort, h]

@[simp] theorem lastPort_not_bottom {r : Fin g} (h : r.1 + 1 ≠ g) :
    lastPort r = true := by
  simp [lastPort, h]

/-- The first relevant vertex in a row block. -/
def first (r c : Fin g) : Vertex g :=
  ⟨r, c, firstPort r⟩

/-- The last relevant vertex in a row block. -/
def last (r c : Fin g) : Vertex g :=
  ⟨r, c, lastPort r⟩

@[simp] theorem first_row (r c : Fin g) : (first r c).row = r := rfl
@[simp] theorem first_col (r c : Fin g) : (first r c).col = c := rfl
@[simp] theorem first_port (r c : Fin g) : (first r c).port = firstPort r := rfl
@[simp] theorem last_row (r c : Fin g) : (last r c).row = r := rfl
@[simp] theorem last_col (r c : Fin g) : (last r c).col = c := rfl
@[simp] theorem last_port (r c : Fin g) : (last r c).port = lastPort r := rfl

/-- Internal row blocks have two distinct relevant ports. -/
theorem first_ne_last_of_internal {r c : Fin g}
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    first r c ≠ last r c := by
  intro h
  have hport := congrArg Vertex.port h
  have hnot_top : r.1 ≠ 0 := Nat.ne_of_gt hTop
  have hnot_bottom : r.1 + 1 ≠ g := Nat.ne_of_lt hBottom
  simp [first, last, firstPort_not_top hnot_top,
    lastPort_not_bottom hnot_bottom] at hport

end Vertex

/-- Horizontal adjacency in the compressed sparse grid.

There is an internal edge between the two ports of an internal row block, and
an edge from the last port of column block `c` to the first port of column block
`c+1`.  The definition is symmetric to match `SimpleGraph`.
-/
def HorizontalAdj {g : ℕ} (x y : Vertex g) : Prop :=
  (x.row = y.row ∧ x.col = y.col ∧
      ((x.port = Vertex.firstPort x.row ∧
          y.port = Vertex.lastPort x.row ∧ x.port ≠ y.port) ∨
        (y.port = Vertex.firstPort y.row ∧
          x.port = Vertex.lastPort y.row ∧ y.port ≠ x.port))) ∨
    (x.row = y.row ∧
      ((x.col.1 + 1 = y.col.1 ∧
          x.port = Vertex.lastPort x.row ∧ y.port = Vertex.firstPort y.row) ∨
        (y.col.1 + 1 = x.col.1 ∧
          y.port = Vertex.lastPort y.row ∧ x.port = Vertex.firstPort x.row)))

/-- Vertical adjacency in the compressed sparse grid: the lower port of a row
block is joined to the upper port of the next row in the same column block. -/
def VerticalAdj {g : ℕ} (x y : Vertex g) : Prop :=
  x.col = y.col ∧
    ((x.row.1 + 1 = y.row.1 ∧ x.port = true ∧ y.port = false) ∨
      (y.row.1 + 1 = x.row.1 ∧ y.port = true ∧ x.port = false))

/-- A vertical sparse-grid edge cannot also be horizontal. -/
theorem not_horizontalAdj_of_verticalAdj {g : ℕ} {x y : Vertex g}
    (h : VerticalAdj x y) : ¬ HorizontalAdj x y := by
  intro hh
  rcases h with ⟨_hcol, hdir | hdir⟩
  · rcases hh with hsame | hnext
    · have hrow := congrArg Fin.val hsame.1
      omega
    · have hrow := congrArg Fin.val hnext.1
      omega
  · rcases hh with hsame | hnext
    · have hrow := congrArg Fin.val hsame.1
      omega
    · have hrow := congrArg Fin.val hnext.1
      omega

/-- Horizontal sparse-grid adjacency preserves the row coordinate. -/
theorem row_eq_of_horizontalAdj {g : ℕ} {x y : Vertex g}
    (h : HorizontalAdj x y) : x.row = y.row := by
  rcases h with hsame | hnext
  · exact hsame.1
  · exact hnext.1

/-- Vertical sparse-grid adjacency preserves the column coordinate. -/
theorem col_eq_of_verticalAdj {g : ℕ} {x y : Vertex g}
    (h : VerticalAdj x y) : x.col = y.col :=
  h.1

/-- Adjacency in the compressed sparse grid `G*`. -/
def Adj {g : ℕ} (x y : Vertex g) : Prop :=
  HorizontalAdj x y ∨ VerticalAdj x y

/-- The compressed sparse grid graph from Appendix C.1. -/
def graph (g : ℕ) : _root_.SimpleGraph (Vertex g) where
  Adj := Adj
  symm := by
    intro x y h
    rcases h with h | h
    · left
      rcases h with ⟨hrow, hcol, hport⟩ | ⟨hrow, h⟩
      · refine Or.inl ⟨hrow.symm, hcol.symm, ?_⟩
        rcases hport with hport | hport
        · exact Or.inr ⟨hport.1, hport.2.1, hport.2.2⟩
        · exact Or.inl ⟨hport.1, hport.2.1, hport.2.2⟩
      · exact Or.inr ⟨hrow.symm, by
          rcases h with h | h
          · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
          · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩⟩
    · right
      rcases h with ⟨hcol, h⟩
      exact ⟨hcol.symm, by
        rcases h with h | h
        · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
        · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · rcases h with ⟨_hrow, _hcol, hport⟩ | ⟨_hrow, h⟩
      · rcases hport with hport | hport
        · exact hport.2.2 rfl
        · exact hport.2.2 rfl
      · rcases h with h | h
        · omega
        · omega
    · rcases h with ⟨_hcol, h⟩
      rcases h with h | h
      · omega
      · omega⟩

/-- The one- or two-port branch set for a canonical grid vertex. -/
def branchSet {g : ℕ} (x : GridVertex g) : Finset (Vertex g) :=
  {Vertex.first x.1 x.2, Vertex.last x.1 x.2}

theorem first_mem_branchSet {g : ℕ} (x : GridVertex g) :
    Vertex.first x.1 x.2 ∈ branchSet x := by
  simp [branchSet]

theorem last_mem_branchSet {g : ℕ} (x : GridVertex g) :
    Vertex.last x.1 x.2 ∈ branchSet x := by
  simp [branchSet]

theorem mem_branchSet_row_col {g : ℕ} {x : GridVertex g} {v : Vertex g}
    (hv : v ∈ branchSet x) :
    v.row = x.1 ∧ v.col = x.2 := by
  simp [branchSet] at hv
  rcases hv with hv | hv
  · subst hv
    simp [Vertex.first]
  · subst hv
    simp [Vertex.last]

/-- Distinct canonical grid vertices have disjoint sparse-grid branch sets. -/
theorem branchSet_disjoint {g : ℕ} ⦃x y : GridVertex g⦄
    (hxy : x ≠ y) : Disjoint (branchSet x) (branchSet y) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  rcases mem_branchSet_row_col hvx with ⟨hrx, hcx⟩
  rcases mem_branchSet_row_col hvy with ⟨hry, hcy⟩
  apply hxy
  exact Prod.ext (hrx.symm.trans hry) (hcx.symm.trans hcy)

/-- The branch set assigned to a canonical grid vertex is connected. -/
theorem branchSet_connected {g : ℕ} (x : GridVertex g) :
    ((graph g).induce {v : Vertex g | v ∈ branchSet x}).Connected := by
  classical
  by_cases hport : Vertex.firstPort x.1 = Vertex.lastPort x.1
  · have hsub : Subsingleton {v : Vertex g | v ∈ branchSet x} := by
      constructor
      intro a b
      apply Subtype.ext
      rcases mem_branchSet_row_col a.2 with ⟨harow, hacol⟩
      rcases mem_branchSet_row_col b.2 with ⟨hbrow, hbcol⟩
      have haport : a.1.port = Vertex.firstPort x.1 := by
        rcases a with ⟨a, ha⟩
        simp [branchSet] at ha
        rcases ha with ha | ha
        · simp [ha, Vertex.first]
        · simp [ha, Vertex.last, hport.symm]
      have hbport : b.1.port = Vertex.firstPort x.1 := by
        rcases b with ⟨b, hb⟩
        simp [branchSet] at hb
        rcases hb with hb | hb
        · simp [hb, Vertex.first]
        · simp [hb, Vertex.last, hport.symm]
      ext
      · exact congrArg Fin.val (harow.trans hbrow.symm)
      · exact congrArg Fin.val (hacol.trans hbcol.symm)
      · exact haport.trans hbport.symm
    haveI : Nonempty {v : Vertex g | v ∈ branchSet x} :=
      ⟨⟨Vertex.first x.1 x.2, first_mem_branchSet x⟩⟩
    exact _root_.SimpleGraph.Connected.of_subsingleton
  · have hadj :
        (graph g).Adj (Vertex.first x.1 x.2) (Vertex.last x.1 x.2) := by
      left
      left
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, by
        simpa [Vertex.first, Vertex.last] using hport⟩⟩
    have hconn :
        ((graph g).induce
          ({Vertex.first x.1 x.2, Vertex.last x.1 x.2} : Set (Vertex g))).Connected :=
      _root_.SimpleGraph.induce_pair_connected_of_adj (G := graph g) hadj
    rw [show {v : Vertex g | v ∈ branchSet x} =
        ({Vertex.first x.1 x.2, Vertex.last x.1 x.2} : Set (Vertex g)) by
      ext v
      simp [branchSet]]
    exact hconn

/-- Horizontal successor branch sets are adjacent in the sparse grid. -/
theorem adjacent_right {g : ℕ} (r c : Fin g) (hc : c.1 + 1 < g) :
    ∃ u ∈ branchSet (r, c),
      ∃ v ∈ branchSet (r, ⟨c.1 + 1, hc⟩), (graph g).Adj u v := by
  refine ⟨Vertex.last r c, last_mem_branchSet (r, c), Vertex.first r ⟨c.1 + 1, hc⟩,
    first_mem_branchSet (r, ⟨c.1 + 1, hc⟩), ?_⟩
  left
  right
  refine ⟨rfl, Or.inl ?_⟩
  simp [Vertex.first, Vertex.last]

/-- Vertical successor branch sets are adjacent in the sparse grid. -/
theorem adjacent_down {g : ℕ} (r c : Fin g) (hr : r.1 + 1 < g) :
    ∃ u ∈ branchSet (r, c),
      ∃ v ∈ branchSet (⟨r.1 + 1, hr⟩, c), (graph g).Adj u v := by
  have hnot_bottom : r.1 + 1 ≠ g := Nat.ne_of_lt hr
  have hsucc_not_top : (⟨r.1 + 1, hr⟩ : Fin g).1 ≠ 0 := Nat.succ_ne_zero r.1
  refine ⟨Vertex.last r c, last_mem_branchSet (r, c),
    Vertex.first ⟨r.1 + 1, hr⟩ c,
    first_mem_branchSet (⟨r.1 + 1, hr⟩, c), ?_⟩
  right
  refine ⟨rfl, Or.inl ?_⟩
  simp [Vertex.first, Vertex.last, Vertex.lastPort_not_bottom hnot_bottom]

/-- Every canonical grid edge is represented by an edge between the
corresponding sparse-grid branch sets. -/
theorem adjacent {g : ℕ} ⦃x y : GridVertex g⦄
    (hxy : (gridGraph g).Adj x y) :
    ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, (graph g).Adj u v := by
  rcases x with ⟨xr, xc⟩
  rcases y with ⟨yr, yc⟩
  rcases hxy with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · change xr = yr at hrow
    subst yr
    rcases hcol with hsucc | hpred
    · have hc : xc.1 + 1 < g := by
        rw [hsucc]
        exact yc.2
      have hy : yc = ⟨xc.1 + 1, hc⟩ := Fin.ext hsucc.symm
      simpa [hy] using adjacent_right xr xc hc
    · have hc : yc.1 + 1 < g := by
        rw [hpred]
        exact xc.2
      have hx : xc = ⟨yc.1 + 1, hc⟩ := Fin.ext hpred.symm
      rcases adjacent_right xr yc hc with ⟨u, hu, v, hv, huv⟩
      refine ⟨v, ?_, u, ?_, (graph g).symm huv⟩
      · simpa [hx] using hv
      · exact hu
  · change xc = yc at hcol
    subst yc
    rcases hrow with hsucc | hpred
    · have hr : xr.1 + 1 < g := by
        rw [hsucc]
        exact yr.2
      have hy : yr = ⟨xr.1 + 1, hr⟩ := Fin.ext hsucc.symm
      simpa [hy] using adjacent_down xr xc hr
    · have hr : yr.1 + 1 < g := by
        rw [hpred]
        exact xr.2
      have hx : xr = ⟨yr.1 + 1, hr⟩ := Fin.ext hpred.symm
      rcases adjacent_down yr xc hr with ⟨u, hu, v, hv, huv⟩
      refine ⟨v, ?_, u, ?_, (graph g).symm huv⟩
      · simpa [hx] using hv
      · exact hu

/-- The branch-set minor model of the canonical grid in the compressed sparse
grid. -/
def minorModel (g : ℕ) : MinorModel (gridGraph g) (graph g) where
  branchSet := branchSet
  branch_nonempty := fun x =>
    ⟨Vertex.first x.1 x.2, first_mem_branchSet x⟩
  branch_connected := branchSet_connected
  branch_disjoint := @branchSet_disjoint g
  adjacent := adjacent

/-- The compressed sparse grid contains the canonical grid of the same order as
a minor. -/
theorem gridGraph_isMinor (g : ℕ) :
    IsMinor (gridGraph g) (graph g) :=
  ⟨minorModel g⟩

/-- The compressed sparse grid contains the canonical grid of the same order as
a grid minor. -/
theorem containsGridMinor (g : ℕ) :
    ContainsGridMinor (graph g) g :=
  ContainsGridMinor.of_gridGraph_isMinor (gridGraph_isMinor g)

/-- Any graph containing the compressed sparse grid as a minor contains the
canonical grid minor of the same order. -/
theorem containsGridMinor_of_minor {V : Type u} {G : _root_.SimpleGraph V}
    {g : ℕ} (hminor : IsMinor (graph g) G) :
    ContainsGridMinor G g :=
  ContainsGridMinor.of_gridGraph_isMinor ((gridGraph_isMinor g).trans hminor)

/-- A path-valued model of the compressed sparse grid already gives a
canonical grid minor. -/
theorem containsGridMinor_of_pathMinorModel {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g : ℕ}
    (M : PathMinorModel (graph g) G) :
    ContainsGridMinor G g :=
  containsGridMinor_of_minor M.isMinor

/-- A sparse-grid port is valid when it is one of the row block's first/last
ports.  For `g >= 2`, this removes the unused upper port on the top row and the
unused lower port on the bottom row. -/
def Valid {g : ℕ} (v : Vertex g) : Prop :=
  v.port = Vertex.firstPort v.row ∨ v.port = Vertex.lastPort v.row

theorem row_succ_lt_of_valid_true {g : ℕ} (hg : 2 ≤ g)
    {v : Vertex g} (hv : Valid v) (htrue : v.port = true) :
    v.row.1 + 1 < g := by
  by_contra hlt
  have hbottom : v.row.1 + 1 = g := by omega
  have hnot_top : v.row.1 ≠ 0 := by omega
  rcases hv with hfirst | hlast
  · have hfalse : v.port = false := by
      simpa [Vertex.firstPort, hnot_top] using hfirst
    simp [htrue] at hfalse
  · have hfalse : v.port = false := by
      simpa [Vertex.lastPort, hbottom] using hlast
    simp [htrue] at hfalse

theorem row_pos_of_valid_false {g : ℕ} (hg : 2 ≤ g)
    {v : Vertex g} (hv : Valid v) (hfalse : v.port = false) :
    0 < v.row.1 := by
  by_contra hpos
  have htop : v.row.1 = 0 := by omega
  have hnot_bottom : v.row.1 + 1 ≠ g := by omega
  rcases hv with hfirst | hlast
  · have htrue : v.port = true := by
      simpa [Vertex.firstPort, htop] using hfirst
    simp [hfalse] at htrue
  · have htrue : v.port = true := by
      simpa [Vertex.lastPort, hnot_bottom] using hlast
    simp [hfalse] at htrue

/-- For `g >= 2`, a row has two distinct relevant ports exactly when it is
neither the top nor the bottom row. -/
theorem firstPort_ne_lastPort_iff_internal {g : ℕ} (hg : 2 ≤ g)
    (r : Fin g) :
    Vertex.firstPort r ≠ Vertex.lastPort r ↔
      0 < r.1 ∧ r.1 + 1 < g := by
  constructor
  · intro hne
    constructor
    · by_contra htop'
      have htop : r.1 = 0 := by omega
      have hnot_bottom : r.1 + 1 ≠ g := by omega
      have heq : Vertex.firstPort r = Vertex.lastPort r := by
        simp [Vertex.firstPort_top htop, Vertex.lastPort_not_bottom hnot_bottom]
      exact hne heq
    · by_contra hbottom'
      have hbottom : r.1 + 1 = g := by omega
      have hnot_top : r.1 ≠ 0 := by omega
      have heq : Vertex.firstPort r = Vertex.lastPort r := by
        simp [Vertex.firstPort_not_top hnot_top, Vertex.lastPort_bottom hbottom]
      exact hne heq
  · rintro ⟨hTop, hBottom⟩
    have hnot_top : r.1 ≠ 0 := by omega
    have hnot_bottom : r.1 + 1 ≠ g := Nat.ne_of_lt hBottom
    simp [Vertex.firstPort_not_top hnot_top,
      Vertex.lastPort_not_bottom hnot_bottom]

/-- The compressed sparse grid with only valid ports.  This is the graph `G*`
used by the Appendix C.1 subdivision argument. -/
abbrev ValidVertex (g : ℕ) : Type :=
  {v : Vertex g // Valid v}

noncomputable instance validVertexFintype (g : ℕ) : Fintype (ValidVertex g) := by
  classical
  dsimp [ValidVertex]
  infer_instance

/-- The valid-port sparse grid. -/
def validGraph (g : ℕ) : _root_.SimpleGraph (ValidVertex g) :=
  (graph g).induce {v : Vertex g | Valid v}

namespace ValidVertex

/-- The first valid port in a row block. -/
def first {g : ℕ} (r c : Fin g) : ValidVertex g :=
  ⟨Vertex.first r c, Or.inl rfl⟩

/-- The last valid port in a row block. -/
def last {g : ℕ} (r c : Fin g) : ValidVertex g :=
  ⟨Vertex.last r c, Or.inr rfl⟩

@[simp] theorem first_val {g : ℕ} (r c : Fin g) :
    (first r c : Vertex g) = Vertex.first r c := rfl

@[simp] theorem last_val {g : ℕ} (r c : Fin g) :
    (last r c : Vertex g) = Vertex.last r c := rfl

/-- A valid vertex whose Boolean is the row's first port is definitionally the
first valid port of that row and column. -/
theorem eq_first_of_port_eq_firstPort {g : ℕ}
    (x : ValidVertex g) (hport : x.1.port = Vertex.firstPort x.1.row) :
    x = first x.1.row x.1.col := by
  apply Subtype.ext
  apply Vertex.ext <;> simp [first, Vertex.first, hport]

/-- A valid vertex whose Boolean is the row's last port is definitionally the
last valid port of that row and column. -/
theorem eq_last_of_port_eq_lastPort {g : ℕ}
    (x : ValidVertex g) (hport : x.1.port = Vertex.lastPort x.1.row) :
    x = last x.1.row x.1.col := by
  apply Subtype.ext
  apply Vertex.ext <;> simp [last, Vertex.last, hport]

/-- A valid `true` port is the last relevant port of its row. -/
theorem eq_last_of_port_true {g : ℕ} (hg : 2 ≤ g)
    (x : ValidVertex g) (htrue : x.1.port = true) :
    x = last x.1.row x.1.col := by
  apply Subtype.ext
  apply Vertex.ext <;> simp [last, Vertex.last]
  have hbottom := row_succ_lt_of_valid_true hg x.2 htrue
  simpa [Vertex.lastPort_not_bottom (Nat.ne_of_lt hbottom)] using htrue

/-- A valid `false` port is the first relevant port of its row. -/
theorem eq_first_of_port_false {g : ℕ} (hg : 2 ≤ g)
    (x : ValidVertex g) (hfalse : x.1.port = false) :
    x = first x.1.row x.1.col := by
  apply Subtype.ext
  apply Vertex.ext <;> simp [first, Vertex.first]
  have htop := row_pos_of_valid_false hg x.2 hfalse
  simpa [Vertex.firstPort_not_top (Nat.ne_of_gt htop)] using hfalse

/-- Internal row blocks have two distinct valid sparse-grid vertices. -/
theorem first_ne_last_of_internal {g : ℕ} {r c : Fin g}
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    first r c ≠ last r c := by
  intro h
  exact Vertex.first_ne_last_of_internal hTop hBottom (congrArg Subtype.val h)

/-- Valid ports in different column blocks are distinct. -/
theorem last_ne_first_of_col_ne {g : ℕ} {r c d : Fin g}
    (hcd : c ≠ d) :
    last r c ≠ first r d := by
  intro h
  exact hcd (congrArg (fun x : ValidVertex g => x.1.col) h)

end ValidVertex

/-- The one- or two-port branch set inside the valid sparse grid. -/
def validBranchSet {g : ℕ} (x : GridVertex g) : Finset (ValidVertex g) :=
  {ValidVertex.first x.1 x.2, ValidVertex.last x.1 x.2}

theorem valid_first_mem_branchSet {g : ℕ} (x : GridVertex g) :
    ValidVertex.first x.1 x.2 ∈ validBranchSet x := by
  simp [validBranchSet]

theorem valid_last_mem_branchSet {g : ℕ} (x : GridVertex g) :
    ValidVertex.last x.1 x.2 ∈ validBranchSet x := by
  simp [validBranchSet]

theorem valid_mem_branchSet_row_col {g : ℕ} {x : GridVertex g}
    {v : ValidVertex g} (hv : v ∈ validBranchSet x) :
    v.1.row = x.1 ∧ v.1.col = x.2 := by
  simp [validBranchSet] at hv
  rcases hv with hv | hv
  · subst hv
    simp [ValidVertex.first, Vertex.first]
  · subst hv
    simp [ValidVertex.last, Vertex.last]

theorem valid_branchSet_disjoint {g : ℕ} ⦃x y : GridVertex g⦄
    (hxy : x ≠ y) : Disjoint (validBranchSet x) (validBranchSet y) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  rcases valid_mem_branchSet_row_col hvx with ⟨hrx, hcx⟩
  rcases valid_mem_branchSet_row_col hvy with ⟨hry, hcy⟩
  apply hxy
  exact Prod.ext (hrx.symm.trans hry) (hcx.symm.trans hcy)

theorem valid_branchSet_connected {g : ℕ} (x : GridVertex g) :
    ((validGraph g).induce {v : ValidVertex g | v ∈ validBranchSet x}).Connected := by
  classical
  by_cases hport : Vertex.firstPort x.1 = Vertex.lastPort x.1
  · have hsub : Subsingleton {v : ValidVertex g | v ∈ validBranchSet x} := by
      constructor
      intro a b
      apply Subtype.ext
      rcases valid_mem_branchSet_row_col a.2 with ⟨harow, hacol⟩
      rcases valid_mem_branchSet_row_col b.2 with ⟨hbrow, hbcol⟩
      have haport : a.1.1.port = Vertex.firstPort x.1 := by
        rcases a with ⟨a, ha⟩
        simp [validBranchSet] at ha
        rcases ha with ha | ha
        · simp [ha, ValidVertex.first, Vertex.first]
        · simp [ha, ValidVertex.last, Vertex.last, hport.symm]
      have hbport : b.1.1.port = Vertex.firstPort x.1 := by
        rcases b with ⟨b, hb⟩
        simp [validBranchSet] at hb
        rcases hb with hb | hb
        · simp [hb, ValidVertex.first, Vertex.first]
        · simp [hb, ValidVertex.last, Vertex.last, hport.symm]
      ext
      · exact congrArg Fin.val (harow.trans hbrow.symm)
      · exact congrArg Fin.val (hacol.trans hbcol.symm)
      · exact haport.trans hbport.symm
    haveI : Nonempty {v : ValidVertex g | v ∈ validBranchSet x} :=
      ⟨⟨ValidVertex.first x.1 x.2, valid_first_mem_branchSet x⟩⟩
    exact _root_.SimpleGraph.Connected.of_subsingleton
  · have hadj :
        (validGraph g).Adj (ValidVertex.first x.1 x.2)
          (ValidVertex.last x.1 x.2) := by
      change (graph g).Adj (Vertex.first x.1 x.2) (Vertex.last x.1 x.2)
      left
      left
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, by
        simpa [Vertex.first, Vertex.last] using hport⟩⟩
    have hconn :
        ((validGraph g).induce
          ({ValidVertex.first x.1 x.2, ValidVertex.last x.1 x.2} :
            Set (ValidVertex g))).Connected :=
      _root_.SimpleGraph.induce_pair_connected_of_adj (G := validGraph g) hadj
    rw [show {v : ValidVertex g | v ∈ validBranchSet x} =
        ({ValidVertex.first x.1 x.2, ValidVertex.last x.1 x.2} :
          Set (ValidVertex g)) by
      ext v
      simp [validBranchSet]]
    exact hconn

theorem valid_adjacent {g : ℕ} ⦃x y : GridVertex g⦄
    (hxy : (gridGraph g).Adj x y) :
    ∃ u ∈ validBranchSet x, ∃ v ∈ validBranchSet y, (validGraph g).Adj u v := by
  rcases adjacent hxy with ⟨u, hu, v, hv, huv⟩
  simp [branchSet] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · refine ⟨ValidVertex.first x.1 x.2, valid_first_mem_branchSet x,
      ValidVertex.first y.1 y.2, valid_first_mem_branchSet y, ?_⟩
    subst hu
    subst hv
    change (graph g).Adj (Vertex.first x.1 x.2) (Vertex.first y.1 y.2)
    exact huv
  · refine ⟨ValidVertex.first x.1 x.2, valid_first_mem_branchSet x,
      ValidVertex.last y.1 y.2, valid_last_mem_branchSet y, ?_⟩
    subst hu
    subst hv
    change (graph g).Adj (Vertex.first x.1 x.2) (Vertex.last y.1 y.2)
    exact huv
  · refine ⟨ValidVertex.last x.1 x.2, valid_last_mem_branchSet x,
      ValidVertex.first y.1 y.2, valid_first_mem_branchSet y, ?_⟩
    subst hu
    subst hv
    change (graph g).Adj (Vertex.last x.1 x.2) (Vertex.first y.1 y.2)
    exact huv
  · refine ⟨ValidVertex.last x.1 x.2, valid_last_mem_branchSet x,
      ValidVertex.last y.1 y.2, valid_last_mem_branchSet y, ?_⟩
    subst hu
    subst hv
    change (graph g).Adj (Vertex.last x.1 x.2) (Vertex.last y.1 y.2)
    exact huv

/-- Branch-set minor model of the canonical grid in the valid sparse grid. -/
def validMinorModel (g : ℕ) : MinorModel (gridGraph g) (validGraph g) where
  branchSet := validBranchSet
  branch_nonempty := fun x =>
    ⟨ValidVertex.first x.1 x.2, valid_first_mem_branchSet x⟩
  branch_connected := valid_branchSet_connected
  branch_disjoint := @valid_branchSet_disjoint g
  adjacent := valid_adjacent

/-- The valid sparse grid contains the canonical grid as a minor. -/
theorem validGridGraph_isMinor (g : ℕ) :
    IsMinor (gridGraph g) (validGraph g) :=
  ⟨validMinorModel g⟩

/-- The valid sparse grid contains the canonical grid minor. -/
theorem validContainsGridMinor (g : ℕ) :
    ContainsGridMinor (validGraph g) g :=
  ContainsGridMinor.of_gridGraph_isMinor (validGridGraph_isMinor g)

/-- Any graph containing the valid sparse grid as a minor contains a canonical
grid minor. -/
theorem validContainsGridMinor_of_minor {V : Type u} {G : _root_.SimpleGraph V}
    {g : ℕ} (hminor : IsMinor (validGraph g) G) :
    ContainsGridMinor G g :=
  ContainsGridMinor.of_gridGraph_isMinor ((validGridGraph_isMinor g).trans hminor)

/-- A path-valued model of the valid sparse grid gives a canonical grid minor. -/
theorem validContainsGridMinor_of_pathMinorModel {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g : ℕ}
    (M : PathMinorModel (validGraph g) G) :
    ContainsGridMinor G g :=
  validContainsGridMinor_of_minor M.isMinor

end SparseGrid

end SimpleGraph

end Lax17Proofs
