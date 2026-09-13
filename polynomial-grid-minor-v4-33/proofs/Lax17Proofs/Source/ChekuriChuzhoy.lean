import Mathlib.Tactic
import Lax17Proofs.Source.ChekuriChuzhoyContract
import Lax17Proofs.Source.ChekuriChuzhoyStitchedRows
import Lax17Proofs.Source.GridMinor
import Lax17Proofs.Source.SparseGrid

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy path-of-sets grid theorem

This module formalizes the Appendix C.1 assembly that turns the stitched rows
from Chekuri--Chuzhoy Corollary 3.2 into a valid sparse-grid minor, and then
contracts the valid sparse grid to the canonical grid.  The remaining contract
boundary in this file is the earlier Corollary 3.2 dichotomy for strong
path-of-sets systems: either a direct grid minor is already present, or stitched
rows are extracted from the system.  The stitched-row branch is discharged here.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


/-- A concrete branch-set certificate for a `g x g` grid minor.

Appendix C.1 of Chekuri--Chuzhoy constructs this data from the stitched row
paths returned by Corollary 3.2: each branch set is a row segment, and the
vertical adjacencies are witnessed by the bridge paths in the even clusters. -/
structure GridAssemblyCertificate {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (g : ℕ) where
  /-- Branch set assigned to each canonical grid vertex. -/
  branchSet : GridVertex g → Finset V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ x : GridVertex g, (branchSet x).Nonempty
  /-- Every branch set induces a connected subgraph. -/
  branch_connected :
    ∀ x : GridVertex g, (G.induce {v : V | v ∈ branchSet x}).Connected
  /-- Distinct grid vertices have disjoint branch sets. -/
  branch_disjoint :
    ∀ ⦃x y : GridVertex g⦄, x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- Every canonical grid edge is represented by a host edge between the
  corresponding branch sets. -/
  adjacent :
    ∀ ⦃x y : GridVertex g⦄, (gridGraph g).Adj x y →
      ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, G.Adj u v

namespace GridAssemblyCertificate

/-- Build a grid assembly certificate when every branch set is supplied as the
vertex set of a graph path. -/
noncomputable def ofPathBranches {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g : ℕ}
    (branchPath : GridVertex g → GraphPath G)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (branchPath x).vertexSet (branchPath y).vertexSet)
    (adjacent :
      ∀ ⦃x y : GridVertex g⦄, (gridGraph g).Adj x y →
        ∃ u ∈ (branchPath x).vertexSet,
          ∃ v ∈ (branchPath y).vertexSet, G.Adj u v) :
    GridAssemblyCertificate G g where
  branchSet := fun x => (branchPath x).vertexSet
  branch_nonempty := by
    intro x
    exact ⟨(branchPath x).source, GraphPath.source_mem_vertexSet (branchPath x)⟩
  branch_connected := by
    intro x
    exact GraphPath.connected_induce_vertexSet (branchPath x)
  branch_disjoint := branch_disjoint
  adjacent := adjacent

/-- A grid assembly certificate is exactly the data needed for a grid minor. -/
theorem containsGridMinor {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g : ℕ}
    (C : GridAssemblyCertificate G g) :
    ContainsGridMinor G g :=
  ContainsGridMinor.of_grid_branchSets C.branchSet C.branch_nonempty
    C.branch_connected C.branch_disjoint C.adjacent

/-- Path-valued branch sets give a grid minor once disjointness and grid-edge
adjacency witnesses have been supplied. -/
theorem containsGridMinor_ofPathBranches {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g : ℕ}
    (branchPath : GridVertex g → GraphPath G)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (branchPath x).vertexSet (branchPath y).vertexSet)
    (adjacent :
      ∀ ⦃x y : GridVertex g⦄, (gridGraph g).Adj x y →
        ∃ u ∈ (branchPath x).vertexSet,
          ∃ v ∈ (branchPath y).vertexSet, G.Adj u v) :
    ContainsGridMinor G g :=
  (GridAssemblyCertificate.ofPathBranches branchPath branch_disjoint adjacent).containsGridMinor

end GridAssemblyCertificate

/-- Path-valued grid branch sets with only right/down successor adjacency
witnesses.  This is the shape naturally produced by the row-and-bridge
construction in Chekuri--Chuzhoy Appendix C.1. -/
structure GridPathBranchCertificate {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (g : ℕ) where
  /-- The path whose vertex set is the branch set of each grid vertex. -/
  branchPath : GridVertex g → GraphPath G
  /-- Distinct grid vertices receive disjoint path vertex sets. -/
  branch_disjoint :
    ∀ ⦃x y : GridVertex g⦄, x ≠ y →
      Disjoint (branchPath x).vertexSet (branchPath y).vertexSet
  /-- Horizontal successor grid edges are witnessed by host edges between
  branch paths. -/
  adjacent_right :
    ∀ (r c : Fin g) (hc : c.1 + 1 < g),
      ∃ u ∈ (branchPath (r, c)).vertexSet,
        ∃ v ∈ (branchPath (r, ⟨c.1 + 1, hc⟩)).vertexSet, G.Adj u v
  /-- Vertical successor grid edges are witnessed by host edges between branch
  paths. -/
  adjacent_down :
    ∀ (r c : Fin g) (hr : r.1 + 1 < g),
      ∃ u ∈ (branchPath (r, c)).vertexSet,
        ∃ v ∈ (branchPath (⟨r.1 + 1, hr⟩, c)).vertexSet, G.Adj u v

namespace GridPathBranchCertificate

/-- A right/down path-branch certificate gives the full grid assembly
certificate. -/
noncomputable def toGridAssemblyCertificate {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g : ℕ}
    (C : GridPathBranchCertificate G g) :
    GridAssemblyCertificate G g :=
  GridAssemblyCertificate.ofPathBranches C.branchPath C.branch_disjoint (by
    intro x y hxy
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
        simpa [hy] using C.adjacent_right xr xc hc
      · have hc : yc.1 + 1 < g := by
          rw [hpred]
          exact xc.2
        have hx : xc = ⟨yc.1 + 1, hc⟩ := Fin.ext hpred.symm
        rcases C.adjacent_right xr yc hc with ⟨u, hu, v, hv, huv⟩
        refine ⟨v, ?_, u, ?_, G.symm huv⟩
        · simpa [hx] using hv
        · exact hu
    · change xc = yc at hcol
      subst yc
      rcases hrow with hsucc | hpred
      · have hr : xr.1 + 1 < g := by
          rw [hsucc]
          exact yr.2
        have hy : yr = ⟨xr.1 + 1, hr⟩ := Fin.ext hsucc.symm
        simpa [hy] using C.adjacent_down xr xc hr
      · have hr : yr.1 + 1 < g := by
          rw [hpred]
          exact xr.2
        have hx : xr = ⟨yr.1 + 1, hr⟩ := Fin.ext hpred.symm
        rcases C.adjacent_down yr xc hr with ⟨u, hu, v, hv, huv⟩
        refine ⟨v, ?_, u, ?_, G.symm huv⟩
        · simpa [hx] using hv
        · exact hu)

/-- A right/down path-branch certificate gives a grid minor. -/
theorem containsGridMinor {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g : ℕ}
    (C : GridPathBranchCertificate G g) :
    ContainsGridMinor G g :=
  C.toGridAssemblyCertificate.containsGridMinor

end GridPathBranchCertificate

/-- A subdivision-style certificate for the valid sparse grid: every sparse
grid vertex is mapped to a host vertex and every sparse-grid edge is realized
by a host path with matching endpoints.

This is the formal intermediate object produced directly by the Appendix C.1
row-and-bridge construction.  A later step contracts these edge paths into a
standard branch-set minor model. -/
structure ValidSparseGridPathCertificate {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (g : ℕ) where
  /-- Image of each valid sparse-grid port. -/
  image : SparseGrid.ValidVertex g → V
  /-- Path realizing each valid sparse-grid edge. -/
  edgePath :
    ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
      (SparseGrid.validGraph g).Adj x y → GraphPath G
  /-- The chosen path starts at the image of the first endpoint. -/
  edgePath_source :
    ∀ ⦃x y : SparseGrid.ValidVertex g⦄
      (hxy : (SparseGrid.validGraph g).Adj x y),
        (edgePath hxy).source = image x
  /-- The chosen path ends at the image of the second endpoint. -/
  edgePath_target :
    ∀ ⦃x y : SparseGrid.ValidVertex g⦄
      (hxy : (SparseGrid.validGraph g).Adj x y),
        (edgePath hxy).target = image y

namespace ValidSparseGridPathCertificate

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g : ℕ}

/-- A row-major rank used to orient the valid sparse-grid edges for branch-set
allocation.  Inside a row, ports are ordered by column and then by Boolean port
(`false` before `true`), which is exactly the order in which the stitched row
encounters the relevant sparse-grid attachments. -/
def validVertexRank (x : SparseGrid.ValidVertex g) : ℕ :=
  (if x.1.port then 1 else 0) + 2 * x.1.col.1 + (2 * g) * x.1.row.1

theorem validVertexRank_injective :
    Function.Injective (validVertexRank (g := g)) := by
  intro x y hxy
  have hgpos : 0 < g := by
    exact lt_of_le_of_lt (Nat.zero_le x.1.row.1) x.1.row.2
  let bx : ℕ := if x.1.port then 1 else 0
  let byy : ℕ := if y.1.port then 1 else 0
  let dx : ℕ := bx + 2 * x.1.col.1
  let dy : ℕ := byy + 2 * y.1.col.1
  have hbx_le : bx ≤ 1 := by
    dsimp [bx]
    split <;> omega
  have hby_le : byy ≤ 1 := by
    dsimp [byy]
    split <;> omega
  have hdx_lt : dx < 2 * g := by
    dsimp [dx]
    have hxcol := x.1.col.2
    omega
  have hdy_lt : dy < 2 * g := by
    dsimp [dy]
    have hycol := y.1.col.2
    omega
  have hbase : 0 < 2 * g := Nat.mul_pos (by decide : 0 < 2) hgpos
  have hrank :
      dx + (2 * g) * x.1.row.1 = dy + (2 * g) * y.1.row.1 := by
    simpa [validVertexRank, dx, dy, bx, byy, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hxy
  have hrowVal : x.1.row.1 = y.1.row.1 := by
    have hdiv := congrArg (fun n : ℕ => n / (2 * g)) hrank
    have hdivx :
        (dx + (2 * g) * x.1.row.1) / (2 * g) = x.1.row.1 := by
      rw [Nat.add_mul_div_left dx x.1.row.1 hbase]
      rw [Nat.div_eq_of_lt hdx_lt]
      simp
    have hdivy :
        (dy + (2 * g) * y.1.row.1) / (2 * g) = y.1.row.1 := by
      rw [Nat.add_mul_div_left dy y.1.row.1 hbase]
      rw [Nat.div_eq_of_lt hdy_lt]
      simp
    simpa [hdivx, hdivy] using hdiv
  have hdigit : dx = dy := by
    have hmod := congrArg (fun n : ℕ => n % (2 * g)) hrank
    have hmodx :
        (dx + (2 * g) * x.1.row.1) % (2 * g) = dx := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hdx_lt
    have hmody :
        (dy + (2 * g) * y.1.row.1) % (2 * g) = dy := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hdy_lt
    simpa [hmodx, hmody] using hmod
  have hport : x.1.port = y.1.port := by
    dsimp [dx, dy, bx, byy] at hdigit
    by_cases hxport : x.1.port
    · by_cases hyport : y.1.port
      · simp [hxport, hyport]
      · simp [hxport, hyport] at hdigit
        omega
    · by_cases hyport : y.1.port
      · simp [hxport, hyport] at hdigit
        omega
      · simp [hxport, hyport]
  have hcolVal : x.1.col.1 = y.1.col.1 := by
    dsimp [dx, dy, bx, byy] at hdigit
    rw [hport] at hdigit
    by_cases hyport : y.1.port <;> simp [hyport] at hdigit <;> omega
  apply Subtype.ext
  apply SparseGrid.Vertex.ext
  · exact Fin.ext hrowVal
  · exact Fin.ext hcolVal
  · exact hport

theorem validVertexRank_lt_or_gt_of_ne {x y : SparseGrid.ValidVertex g}
    (hxy : x ≠ y) :
    validVertexRank x < validVertexRank y ∨
      validVertexRank y < validVertexRank x := by
  have hrank_ne : validVertexRank x ≠ validVertexRank y := by
    intro h
    exact hxy (validVertexRank_injective h)
  exact lt_or_gt_of_ne hrank_ne

theorem validVertexRank_lt_or_gt_of_adj {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    validVertexRank x < validVertexRank y ∨
      validVertexRank y < validVertexRank x :=
  validVertexRank_lt_or_gt_of_ne ((SparseGrid.validGraph g).ne_of_adj hxy)

/-- A rank-oriented horizontal sparse-grid edge is oriented in the
left-to-right row order: either from the first to the last port inside one
internal block, or from the last port of a column block to the first port of
the next block. -/
theorem horizontalAdj_forward_of_validVertexRank_lt (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hrank : validVertexRank x < validVertexRank y) :
    (x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
      x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
        y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
          x.1.port ≠ y.1.port) ∨
      (x.1.row = y.1.row ∧
        x.1.col.1 + 1 = y.1.col.1 ∧
          x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
            y.1.port = SparseGrid.Vertex.firstPort y.1.row) := by
  rcases hxy with hsame | hnext
  · rcases hsame with ⟨hrow, hcol, hports | hports⟩
    · exact Or.inl ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩
    · have hfl_ne :
          SparseGrid.Vertex.firstPort y.1.row ≠
            SparseGrid.Vertex.lastPort y.1.row := by
        intro heq
        exact hports.2.2 (hports.1.trans (heq.trans hports.2.1.symm))
      have hInternal :
          0 < y.1.row.1 ∧ y.1.row.1 + 1 < g :=
        (SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne
      have hyfalse : y.1.port = false := by
        have hnotTop : y.1.row.1 ≠ 0 := Nat.ne_of_gt hInternal.1
        simpa [SparseGrid.Vertex.firstPort_not_top hnotTop] using hports.1
      have hxtrue : x.1.port = true := by
        have hnotBottom : y.1.row.1 + 1 ≠ g := Nat.ne_of_lt hInternal.2
        simpa [SparseGrid.Vertex.lastPort_not_bottom hnotBottom] using hports.2.1
      have hrowVal : x.1.row.1 = y.1.row.1 := congrArg Fin.val hrow
      have hcolVal : x.1.col.1 = y.1.col.1 := congrArg Fin.val hcol
      have hyx : validVertexRank y < validVertexRank x := by
        simp [validVertexRank, hrowVal, hcolVal, hyfalse, hxtrue]
      omega
  · rcases hnext with ⟨hrow, hdir | hdir⟩
    · exact Or.inr ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩
    · have hrowVal : x.1.row.1 = y.1.row.1 := congrArg Fin.val hrow
      have hyx : validVertexRank y < validVertexRank x := by
        have hcolsucc : y.1.col.1 + 1 = x.1.col.1 := hdir.1
        dsimp [validVertexRank]
        rw [hrowVal]
        by_cases hyport : y.1.port <;> by_cases hxport : x.1.port <;>
          simp [hyport, hxport] <;> omega
      omega

/-- The chosen path for a sparse-grid edge starts and ends at distinct host
vertices when the endpoint map is injective. -/
theorem edgePath_source_ne_target (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    (C.edgePath hxy).source ≠ (C.edgePath hxy).target := by
  intro h
  have himage : C.image x = C.image y := by
    rw [← C.edgePath_source hxy, ← C.edgePath_target hxy]
    exact h
  exact (SparseGrid.validGraph g).ne_of_adj hxy (hinj himage)

/-- The source endpoint image lies in the drop-last path allocated from a
realized sparse-grid edge. -/
theorem image_source_mem_edgePath_dropLast
    (C : ValidSparseGridPathCertificate G g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    C.image x ∈ (C.edgePath hxy).dropLast.vertexSet := by
  have hsource : (C.edgePath hxy).dropLast.source = C.image x := by
    rw [GraphPath.dropLast_source, C.edgePath_source hxy]
  simpa [← hsource] using GraphPath.source_mem_vertexSet ((C.edgePath hxy).dropLast)

/-- The target endpoint image is not in the source-owned drop-last path of a
realized sparse-grid edge. -/
theorem image_target_not_mem_edgePath_dropLast
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    C.image y ∉ (C.edgePath hxy).dropLast.vertexSet := by
  have hne :
      (C.edgePath hxy).source ≠ (C.edgePath hxy).target :=
    C.edgePath_source_ne_target hinj hxy
  have hnot := (C.edgePath hxy).target_not_mem_dropLast_vertexSet hne
  simpa [C.edgePath_target hxy] using hnot

/-- The allocated drop-last part of a realized sparse-grid edge is contained in
the full realized edge path. -/
theorem edgePath_dropLast_vertexSet_subset
    (C : ValidSparseGridPathCertificate G g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    (C.edgePath hxy).dropLast.vertexSet ⊆ (C.edgePath hxy).vertexSet :=
  (C.edgePath hxy).dropLast_vertexSet_subset

/-- The canonical branch set associated with a path certificate: the image of
`x` together with every realized edge path directed out of `x`, with the final
endpoint removed.  The final endpoint belongs to the neighboring branch set,
and the final edge is used to witness adjacency in the minor model. -/
noncomputable def branchSet (C : ValidSparseGridPathCertificate G g)
    (x : SparseGrid.ValidVertex g) : Finset V := by
  classical
  exact {C.image x} ∪
    Finset.univ.biUnion (fun y : SparseGrid.ValidVertex g =>
      if hxy : (SparseGrid.validGraph g).Adj x y then
        (C.edgePath hxy).dropLast.vertexSet
      else
        ∅)

@[simp] theorem image_mem_branchSet
    (C : ValidSparseGridPathCertificate G g)
    (x : SparseGrid.ValidVertex g) :
    C.image x ∈ C.branchSet x := by
  classical
  simp [branchSet]

/-- Membership in the source-oriented canonical branch set. -/
theorem mem_branchSet_iff
    (C : ValidSparseGridPathCertificate G g)
    {x : SparseGrid.ValidVertex g} {v : V} :
    v ∈ C.branchSet x ↔
      v = C.image x ∨
        ∃ (y : SparseGrid.ValidVertex g)
          (hxy : (SparseGrid.validGraph g).Adj x y),
            v ∈ (C.edgePath hxy).dropLast.vertexSet := by
  classical
  constructor
  · intro hv
    rw [branchSet] at hv
    rw [Finset.mem_union] at hv
    rcases hv with hv | hv
    · left
      simpa using hv
    · rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨y, _hy, hvif⟩
      by_cases hxy : (SparseGrid.validGraph g).Adj x y
      · right
        exact ⟨y, hxy, by simpa [hxy] using hvif⟩
      · simp [hxy] at hvif
  · intro hv
    rcases hv with hv | hv
    · rw [branchSet]
      exact Finset.mem_union_left _ (by simp [hv])
    · rcases hv with ⟨y, hxy, hvpath⟩
      rw [branchSet]
      exact Finset.mem_union_right _ <|
        Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
          simpa [hxy] using hvpath⟩

/-- The penultimate vertex of the path realizing an oriented sparse-grid edge
belongs to the source endpoint's canonical branch set. -/
theorem edge_penultimate_mem_branchSet
    (C : ValidSparseGridPathCertificate G g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    (C.edgePath hxy).penultimate ∈ C.branchSet x := by
  classical
  have hmem :
      (C.edgePath hxy).penultimate ∈ (C.edgePath hxy).dropLast.vertexSet := by
    simpa using GraphPath.target_mem_vertexSet ((C.edgePath hxy).dropLast)
  rw [branchSet]
  exact Finset.mem_union_right _ <|
    Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
      simpa [hxy] using hmem⟩

/-- The canonical branch set of a path certificate is connected: every outgoing
drop-last path contains the common endpoint image of `x`. -/
theorem branchSet_connected
    (C : ValidSparseGridPathCertificate G g)
    (x : SparseGrid.ValidVertex g) :
    (G.induce {v : V | v ∈ C.branchSet x}).Connected := by
  classical
  refine G.induce_connected_of_patches (C.image x) (C.image_mem_branchSet x) ?_
  intro v hv
  change v ∈ C.branchSet x at hv
  rw [branchSet] at hv
  rw [Finset.mem_union] at hv
  rcases hv with hv | hv
  · have hv_eq : v = C.image x := by
      simpa using hv
    subst v
    refine ⟨({C.image x} : Set V), ?_, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Set.mem_singleton_iff] at hz
      simp [hz, C.image_mem_branchSet x]
    · simp
    · simp
    · exact _root_.SimpleGraph.Reachable.refl _
  · rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨y, _hy, hvif⟩
    by_cases hxy : (SparseGrid.validGraph g).Adj x y
    · have hvpath :
          v ∈ (C.edgePath hxy).dropLast.vertexSet := by
        simpa [hxy] using hvif
      let S : Set V := {z : V | z ∈ (C.edgePath hxy).dropLast.vertexSet}
      refine ⟨S, ?_, ?_, hvpath, ?_⟩
      · intro z hz
        rw [branchSet]
        exact Finset.mem_union_right _ <|
          Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
            simpa [hxy] using hz⟩
      · have hsource :
            (C.edgePath hxy).dropLast.source = C.image x := by
          rw [GraphPath.dropLast_source, C.edgePath_source hxy]
        simpa [S, ← hsource] using
          GraphPath.source_mem_vertexSet ((C.edgePath hxy).dropLast)
      · have hconn :=
          GraphPath.connected_induce_vertexSet ((C.edgePath hxy).dropLast)
        exact hconn ⟨C.image x, by
          have hsource :
              (C.edgePath hxy).dropLast.source = C.image x := by
            rw [GraphPath.dropLast_source, C.edgePath_source hxy]
          simpa [S, ← hsource] using
            GraphPath.source_mem_vertexSet ((C.edgePath hxy).dropLast)⟩
          ⟨v, hvpath⟩
    · simp [hxy] at hvif

end ValidSparseGridPathCertificate

/-- A subdivision certificate together with an allocation of the realized edge
paths into branch sets.

For each oriented sparse-grid edge `x--y`, the penultimate vertex of the
chosen path from `x` to `y` must lie in the branch set of `x`, while `image y`
lies in the branch set of `y`.  Thus the final edge of the path realizes the
minor adjacency. -/
structure ValidSparseGridAllocatedMinorCertificate {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (g : ℕ)
    extends ValidSparseGridPathCertificate G g where
  /-- Distinct sparse-grid vertices have distinct endpoint images. -/
  image_injective : Function.Injective image
  /-- Branch set assigned to each sparse-grid vertex. -/
  branchSet : SparseGrid.ValidVertex g → Finset V
  /-- The endpoint image belongs to its branch set. -/
  image_mem_branch : ∀ x : SparseGrid.ValidVertex g, image x ∈ branchSet x
  /-- Each branch set induces a connected subgraph. -/
  branch_connected :
    ∀ x : SparseGrid.ValidVertex g,
      (G.induce {v : V | v ∈ branchSet x}).Connected
  /-- Distinct branch sets are disjoint. -/
  branch_disjoint :
    ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
      x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- The penultimate vertex of each realized edge path is allocated to the
  branch set of its source sparse-grid endpoint. -/
  edge_penultimate_mem_branch :
    ∀ ⦃x y : SparseGrid.ValidVertex g⦄
      (hxy : (SparseGrid.validGraph g).Adj x y),
        (edgePath hxy).penultimate ∈ branchSet x

namespace ValidSparseGridAllocatedMinorCertificate

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g : ℕ}

/-- Convert an allocated subdivision certificate into the standard branch-set
minor model. -/
noncomputable def toMinorModel
    (C : ValidSparseGridAllocatedMinorCertificate G g) :
    MinorModel (SparseGrid.validGraph g) G where
  branchSet := C.branchSet
  branch_nonempty := by
    intro x
    exact ⟨C.image x, C.image_mem_branch x⟩
  branch_connected := C.branch_connected
  branch_disjoint := C.branch_disjoint
  adjacent := by
    intro x y hxy
    refine ⟨(C.edgePath hxy).penultimate, C.edge_penultimate_mem_branch hxy,
      C.image y, C.image_mem_branch y, ?_⟩
    have hne :
        (C.edgePath hxy).source ≠ (C.edgePath hxy).target :=
      C.toValidSparseGridPathCertificate.edgePath_source_ne_target
        C.image_injective hxy
    have hadj := (C.edgePath hxy).penultimate_adj_target hne
    simpa [C.edgePath_target hxy] using hadj

/-- An allocated subdivision certificate proves minor containment of the valid
sparse grid. -/
theorem isMinor (C : ValidSparseGridAllocatedMinorCertificate G g) :
    IsMinor (SparseGrid.validGraph g) G :=
  ⟨C.toMinorModel⟩

end ValidSparseGridAllocatedMinorCertificate

/-- A subdivision certificate together with branch sets and direct adjacency
witnesses for the valid sparse grid.

This is the flexible minor-model interface needed for the Appendix C.1
allocation step.  Unlike `ValidSparseGridAllocatedMinorCertificate`, it does not
force every oriented edge path to donate its penultimate vertex to the source
branch set.  That matters for an orientation-aware allocation, where the
internal vertices of an undirected realized edge path are assigned to exactly one
endpoint. -/
structure ValidSparseGridMinorCertificate {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (g : ℕ)
    extends ValidSparseGridPathCertificate G g where
  /-- Branch set assigned to each sparse-grid vertex. -/
  branchSet : SparseGrid.ValidVertex g → Finset V
  /-- The endpoint image belongs to its branch set. -/
  image_mem_branch : ∀ x : SparseGrid.ValidVertex g, image x ∈ branchSet x
  /-- Each branch set induces a connected subgraph. -/
  branch_connected :
    ∀ x : SparseGrid.ValidVertex g,
      (G.induce {v : V | v ∈ branchSet x}).Connected
  /-- Distinct branch sets are disjoint. -/
  branch_disjoint :
    ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
      x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- Every valid sparse-grid edge is witnessed by a host edge between the
  corresponding branch sets. -/
  adjacent :
    ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
      (SparseGrid.validGraph g).Adj x y →
        ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, G.Adj u v

namespace ValidSparseGridMinorCertificate

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g : ℕ}

/-- Convert a direct branch-set certificate into the standard minor model. -/
noncomputable def toMinorModel
    (C : ValidSparseGridMinorCertificate G g) :
    MinorModel (SparseGrid.validGraph g) G where
  branchSet := C.branchSet
  branch_nonempty := by
    intro x
    exact ⟨C.image x, C.image_mem_branch x⟩
  branch_connected := C.branch_connected
  branch_disjoint := C.branch_disjoint
  adjacent := C.adjacent

/-- A direct branch-set certificate proves minor containment of the valid sparse
grid. -/
theorem isMinor (C : ValidSparseGridMinorCertificate G g) :
    IsMinor (SparseGrid.validGraph g) G :=
  ⟨C.toMinorModel⟩

end ValidSparseGridMinorCertificate

namespace ValidSparseGridPathCertificate

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g : ℕ}

/-- If the canonical branch sets of a path certificate are disjoint, then the
certificate gives a standard minor model. -/
noncomputable def toAllocatedMinorCertificate
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (C.branchSet x) (C.branchSet y)) :
    ValidSparseGridAllocatedMinorCertificate G g where
  toValidSparseGridPathCertificate := C
  image_injective := hinj
  branchSet := C.branchSet
  image_mem_branch := C.image_mem_branchSet
  branch_connected := C.branchSet_connected
  branch_disjoint := branch_disjoint
  edge_penultimate_mem_branch := by
    intro x y hxy
    exact C.edge_penultimate_mem_branchSet hxy

/-- A path certificate with injective endpoints and disjoint canonical branch
sets proves minor containment. -/
theorem isMinor_of_branchSet_disjoint
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (C.branchSet x) (C.branchSet y)) :
    IsMinor (SparseGrid.validGraph g) G :=
  (C.toAllocatedMinorCertificate hinj branch_disjoint).isMinor

/-- Orientation-aware branch sets for a sparse-grid path certificate.  For each
undirected sparse-grid edge, only the lower-ranked endpoint absorbs the
drop-last realized path directed toward the higher-ranked endpoint.  This avoids
double-allocating the internal vertices of a realized edge path when the reverse
adjacency is considered. -/
noncomputable def orientedBranchSet (C : ValidSparseGridPathCertificate G g)
    (x : SparseGrid.ValidVertex g) : Finset V := by
  classical
  exact {C.image x} ∪
    Finset.univ.biUnion (fun y : SparseGrid.ValidVertex g =>
      if hxy : (SparseGrid.validGraph g).Adj x y ∧
          validVertexRank x < validVertexRank y then
        (C.edgePath hxy.1).dropLast.vertexSet
      else
        ∅)

@[simp] theorem image_mem_orientedBranchSet
    (C : ValidSparseGridPathCertificate G g)
    (x : SparseGrid.ValidVertex g) :
    C.image x ∈ C.orientedBranchSet x := by
  classical
  simp [orientedBranchSet]

/-- Membership in the orientation-aware branch set. -/
theorem mem_orientedBranchSet_iff
    (C : ValidSparseGridPathCertificate G g)
    {x : SparseGrid.ValidVertex g} {v : V} :
    v ∈ C.orientedBranchSet x ↔
      v = C.image x ∨
        ∃ (y : SparseGrid.ValidVertex g)
          (hxy : (SparseGrid.validGraph g).Adj x y),
            validVertexRank x < validVertexRank y ∧
              v ∈ (C.edgePath hxy).dropLast.vertexSet := by
  classical
  constructor
  · intro hv
    rw [orientedBranchSet] at hv
    rw [Finset.mem_union] at hv
    rcases hv with hv | hv
    · left
      simpa using hv
    · rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨y, _hy, hvif⟩
      by_cases hcond :
          (SparseGrid.validGraph g).Adj x y ∧
            validVertexRank x < validVertexRank y
      · right
        exact ⟨y, hcond.1, hcond.2, by simpa [hcond] using hvif⟩
      · simp [hcond] at hvif
  · intro hv
    rcases hv with hv | hv
    · rw [orientedBranchSet]
      exact Finset.mem_union_left _ (by simp [hv])
    · rcases hv with ⟨y, hxy, hrank, hvpath⟩
      rw [orientedBranchSet]
      exact Finset.mem_union_right _ <|
        Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
          have hcond :
              (SparseGrid.validGraph g).Adj x y ∧
                validVertexRank x < validVertexRank y := ⟨hxy, hrank⟩
          simpa [hcond] using hvpath⟩

/-- A reusable criterion for disjointness of the orientation-aware branch sets.

The two hypotheses are the local topological-minor separation facts one proves
from a concrete construction: endpoint images do not appear in another
source-owned drop-last path, and source-owned drop-last paths for different
sources are disjoint. -/
theorem orientedBranchSet_disjoint_of_dropLast_separated
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    (endpoint_not_mem_dropLast :
      ∀ ⦃x y z : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          validVertexRank x < validVertexRank y →
            z ≠ x → C.image z ∉ (C.edgePath hxy).dropLast.vertexSet)
    (dropLast_disjoint :
      ∀ ⦃x y z t : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y)
        (hzt : (SparseGrid.validGraph g).Adj z t),
          validVertexRank x < validVertexRank y →
            validVertexRank z < validVertexRank t →
              x ≠ z →
                Disjoint (C.edgePath hxy).dropLast.vertexSet
                  (C.edgePath hzt).dropLast.vertexSet) :
    ∀ ⦃x z : SparseGrid.ValidVertex g⦄,
      x ≠ z → Disjoint (C.orientedBranchSet x) (C.orientedBranchSet z) := by
  intro x z hxz
  rw [Finset.disjoint_left]
  intro v hvx hvz
  have hvx' := (C.mem_orientedBranchSet_iff).1 hvx
  have hvz' := (C.mem_orientedBranchSet_iff).1 hvz
  rcases hvx' with hvx_image | hvx_path
  · rcases hvz' with hvz_image | hvz_path
    · have himage : C.image x = C.image z := hvx_image.symm.trans hvz_image
      exact hxz (hinj himage)
    · rcases hvz_path with ⟨t, hzt, hrankzt, hvzt⟩
      exact endpoint_not_mem_dropLast hzt hrankzt hxz
        (by simpa [hvx_image] using hvzt)
  · rcases hvx_path with ⟨y, hxy, hrankxy, hvxy⟩
    rcases hvz' with hvz_image | hvz_path
    · exact endpoint_not_mem_dropLast hxy hrankxy hxz.symm
        (by simpa [hvz_image] using hvxy)
    · rcases hvz_path with ⟨t, hzt, hrankzt, hvzt⟩
      exact Finset.disjoint_left.mp
        (dropLast_disjoint hxy hzt hrankxy hrankzt hxz) hvxy hvzt

/-- A sharper branch-set disjointness criterion.  Endpoint images equal to the
target of an allocated edge path are excluded automatically by
`target_not_mem_dropLast_vertexSet`; the construction-specific hypothesis only
has to exclude endpoint images that are neither endpoint of the path. -/
theorem orientedBranchSet_disjoint_of_internal_dropLast_separated
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    (nonendpoint_not_mem_dropLast :
      ∀ ⦃x y z : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          validVertexRank x < validVertexRank y →
            z ≠ x → z ≠ y →
              C.image z ∉ (C.edgePath hxy).dropLast.vertexSet)
    (dropLast_disjoint :
      ∀ ⦃x y z t : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y)
        (hzt : (SparseGrid.validGraph g).Adj z t),
          validVertexRank x < validVertexRank y →
            validVertexRank z < validVertexRank t →
              x ≠ z →
                Disjoint (C.edgePath hxy).dropLast.vertexSet
                  (C.edgePath hzt).dropLast.vertexSet) :
    ∀ ⦃x z : SparseGrid.ValidVertex g⦄,
      x ≠ z → Disjoint (C.orientedBranchSet x) (C.orientedBranchSet z) := by
  refine C.orientedBranchSet_disjoint_of_dropLast_separated hinj ?_ dropLast_disjoint
  intro x y z hxy hrank hzx
  by_cases hzy : z = y
  · subst z
    exact C.image_target_not_mem_edgePath_dropLast hinj hxy
  · exact nonendpoint_not_mem_dropLast hxy hrank hzx hzy

/-- If the fixed orientation points from `x` to `y`, the penultimate vertex of
the realized `x`-to-`y` path belongs to the oriented branch set of `x`. -/
theorem edge_penultimate_mem_orientedBranchSet
    (C : ValidSparseGridPathCertificate G g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y)
    (hrank : validVertexRank x < validVertexRank y) :
    (C.edgePath hxy).penultimate ∈ C.orientedBranchSet x := by
  classical
  have hmem :
      (C.edgePath hxy).penultimate ∈ (C.edgePath hxy).dropLast.vertexSet := by
    simpa using GraphPath.target_mem_vertexSet ((C.edgePath hxy).dropLast)
  rw [orientedBranchSet]
  exact Finset.mem_union_right _ <|
    Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
      have hcond :
          (SparseGrid.validGraph g).Adj x y ∧
            validVertexRank x < validVertexRank y := ⟨hxy, hrank⟩
      simpa [hcond] using hmem⟩

/-- Each orientation-aware branch set is connected: every absorbed drop-last
edge path starts at the endpoint image of the branch set. -/
theorem orientedBranchSet_connected
    (C : ValidSparseGridPathCertificate G g)
    (x : SparseGrid.ValidVertex g) :
    (G.induce {v : V | v ∈ C.orientedBranchSet x}).Connected := by
  classical
  refine G.induce_connected_of_patches (C.image x)
    (C.image_mem_orientedBranchSet x) ?_
  intro v hv
  change v ∈ C.orientedBranchSet x at hv
  rw [orientedBranchSet] at hv
  rw [Finset.mem_union] at hv
  rcases hv with hv | hv
  · have hv_eq : v = C.image x := by
      simpa using hv
    subst v
    refine ⟨({C.image x} : Set V), ?_, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Set.mem_singleton_iff] at hz
      simp [hz, C.image_mem_orientedBranchSet x]
    · simp
    · simp
    · exact _root_.SimpleGraph.Reachable.refl _
  · rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨y, _hy, hvif⟩
    by_cases hcond :
        (SparseGrid.validGraph g).Adj x y ∧
          validVertexRank x < validVertexRank y
    · have hvpath :
          v ∈ (C.edgePath hcond.1).dropLast.vertexSet := by
        simpa [hcond] using hvif
      let S : Set V := {z : V | z ∈ (C.edgePath hcond.1).dropLast.vertexSet}
      refine ⟨S, ?_, ?_, hvpath, ?_⟩
      · intro z hz
        rw [orientedBranchSet]
        exact Finset.mem_union_right _ <|
          Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
            simpa [hcond] using hz⟩
      · have hsource :
            (C.edgePath hcond.1).dropLast.source = C.image x := by
          rw [GraphPath.dropLast_source, C.edgePath_source hcond.1]
        simpa [S, ← hsource] using
          GraphPath.source_mem_vertexSet ((C.edgePath hcond.1).dropLast)
      · have hconn :=
          GraphPath.connected_induce_vertexSet ((C.edgePath hcond.1).dropLast)
        exact hconn ⟨C.image x, by
          have hsource :
              (C.edgePath hcond.1).dropLast.source = C.image x := by
            rw [GraphPath.dropLast_source, C.edgePath_source hcond.1]
          simpa [S, ← hsource] using
            GraphPath.source_mem_vertexSet ((C.edgePath hcond.1).dropLast)⟩
          ⟨v, hvpath⟩
    · simp [hcond] at hvif

/-- The orientation-aware branch sets witness every sparse-grid edge, provided
the endpoint map is injective. -/
theorem orientedBranchSet_adjacent
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    ∃ u ∈ C.orientedBranchSet x,
      ∃ v ∈ C.orientedBranchSet y, G.Adj u v := by
  rcases validVertexRank_lt_or_gt_of_adj hxy with hrank | hrank
  · refine ⟨(C.edgePath hxy).penultimate,
      C.edge_penultimate_mem_orientedBranchSet hxy hrank,
      C.image y, C.image_mem_orientedBranchSet y, ?_⟩
    have hne :
        (C.edgePath hxy).source ≠ (C.edgePath hxy).target :=
      C.edgePath_source_ne_target hinj hxy
    have hadj := (C.edgePath hxy).penultimate_adj_target hne
    simpa [C.edgePath_target hxy] using hadj
  · have hyx : (SparseGrid.validGraph g).Adj y x :=
      (SparseGrid.validGraph g).symm hxy
    refine ⟨C.image x, C.image_mem_orientedBranchSet x,
      (C.edgePath hyx).penultimate,
      C.edge_penultimate_mem_orientedBranchSet hyx hrank, ?_⟩
    have hne :
        (C.edgePath hyx).source ≠ (C.edgePath hyx).target :=
      C.edgePath_source_ne_target hinj hyx
    have hadj := (C.edgePath hyx).penultimate_adj_target hne
    simpa [C.edgePath_target hyx] using G.symm hadj

/-- Build a direct sparse-grid minor certificate from the orientation-aware
branch sets, once their pairwise disjointness has been proved. -/
noncomputable def toMinorCertificateOfOrientedBranchSet
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (C.orientedBranchSet x) (C.orientedBranchSet y)) :
    ValidSparseGridMinorCertificate G g where
  toValidSparseGridPathCertificate := C
  branchSet := C.orientedBranchSet
  image_mem_branch := C.image_mem_orientedBranchSet
  branch_connected := C.orientedBranchSet_connected
  branch_disjoint := branch_disjoint
  adjacent := by
    intro x y hxy
    exact C.orientedBranchSet_adjacent hinj hxy

/-- A path certificate with injective endpoints and disjoint orientation-aware
branch sets proves minor containment. -/
theorem isMinor_of_orientedBranchSet_disjoint
    (C : ValidSparseGridPathCertificate G g)
    (hinj : Function.Injective C.image)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (C.orientedBranchSet x) (C.orientedBranchSet y)) :
    IsMinor (SparseGrid.validGraph g) G :=
  (C.toMinorCertificateOfOrientedBranchSet hinj branch_disjoint).isMinor

end ValidSparseGridPathCertificate

/-- The sparse vertical edge indexed by column block `c` and row gap `r`.

Appendix C.1 enumerates the `g * (g - 1)` vertical edges of `G*` from left to
right.  In Lean it is convenient to keep the two coordinates separate:
`verticalEdgeIndex g c r` is the flattened index `c * (g - 1) + r`. -/
def verticalEdgeIndex (g : ℕ) (c : Fin g) (r : Fin (g - 1)) :
    Fin (g * (g - 1)) :=
  ⟨c.1 * (g - 1) + r.1, by
    have hc : c.1 < g := c.2
    have hr : r.1 < g - 1 := r.2
    have hc_le : c.1 + 1 ≤ g := Nat.succ_le_of_lt hc
    have hlt :
        c.1 * (g - 1) + r.1 < (c.1 + 1) * (g - 1) := by
      rw [Nat.add_mul, one_mul]
      exact Nat.add_lt_add_left hr _
    exact lt_of_lt_of_le hlt (Nat.mul_le_mul_right (g - 1) hc_le)⟩

@[simp] theorem verticalEdgeIndex_val (g : ℕ) (c : Fin g)
    (r : Fin (g - 1)) :
    (verticalEdgeIndex g c r).1 = c.1 * (g - 1) + r.1 := rfl

theorem verticalEdgeIndex_lt_of_gap_lt {g : ℕ} {c : Fin g}
    {r s : Fin (g - 1)} (hrs : r.1 < s.1) :
    (verticalEdgeIndex g c r).1 < (verticalEdgeIndex g c s).1 := by
  simp [verticalEdgeIndex]
  exact hrs

theorem verticalEdgeIndex_lt_of_col_lt {g : ℕ} {c d : Fin g}
    (hcd : c.1 < d.1) (r s : Fin (g - 1)) :
    (verticalEdgeIndex g c r).1 < (verticalEdgeIndex g d s).1 := by
  have hr : r.1 < g - 1 := r.2
  have hblock :
      c.1 * (g - 1) + r.1 < (c.1 + 1) * (g - 1) := by
    rw [Nat.add_mul, one_mul]
    exact Nat.add_lt_add_left hr _
  have hnext_le : (c.1 + 1) * (g - 1) ≤ d.1 * (g - 1) := by
    exact Nat.mul_le_mul_right (g - 1) (Nat.succ_le_of_lt hcd)
  have htarget_le :
      d.1 * (g - 1) ≤ d.1 * (g - 1) + s.1 := Nat.le_add_right _ _
  simpa [verticalEdgeIndex] using lt_of_lt_of_le hblock (le_trans hnext_le htarget_le)

theorem verticalEdgeIndex_ne_of_col_ne {g : ℕ} {c d : Fin g}
    (hcd : c ≠ d) (r s : Fin (g - 1)) :
    verticalEdgeIndex g c r ≠ verticalEdgeIndex g d s := by
  intro h
  have hval := congrArg Fin.val h
  have hval_ne : c.1 ≠ d.1 := by
    intro hvals
    exact hcd (Fin.ext hvals)
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have hidx := verticalEdgeIndex_lt_of_col_lt hlt r s
    omega
  · have hidx := verticalEdgeIndex_lt_of_col_lt hgt s r
    omega

theorem verticalEdgeIndex_ne_of_gap_ne {g : ℕ} (c : Fin g)
    {r s : Fin (g - 1)} (hrs : r ≠ s) :
    verticalEdgeIndex g c r ≠ verticalEdgeIndex g c s := by
  intro h
  have hval := congrArg Fin.val h
  have hval_ne : r.1 ≠ s.1 := by
    intro hvals
    exact hrs (Fin.ext hvals)
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have hidx := verticalEdgeIndex_lt_of_gap_lt (c := c) hlt
    omega
  · have hidx := verticalEdgeIndex_lt_of_gap_lt (c := c) hgt
    omega

theorem verticalEdgeIndex_injective {g : ℕ} :
    Function.Injective (fun p : Fin g × Fin (g - 1) =>
      verticalEdgeIndex g p.1 p.2) := by
  intro p q hpq
  cases p with
  | mk c r =>
      cases q with
      | mk d s =>
          by_cases hcol : c = d
          · subst d
            by_cases hgap : r = s
            · subst s
              rfl
            · exact False.elim (verticalEdgeIndex_ne_of_gap_ne c hgap hpq)
          · exact False.elim (verticalEdgeIndex_ne_of_col_ne hcol r s hpq)

theorem verticalEdgeIndex_eq_pair {g : ℕ} {c d : Fin g}
    {r s : Fin (g - 1)}
    (h : verticalEdgeIndex g c r = verticalEdgeIndex g d s) :
    (c, r) = (d, s) :=
  verticalEdgeIndex_injective (g := g)
    (show (fun p : Fin g × Fin (g - 1) => verticalEdgeIndex g p.1 p.2) (c, r) =
        (fun p : Fin g × Fin (g - 1) => verticalEdgeIndex g p.1 p.2) (d, s) from h)

/-- The lower row of a row gap in a `g`-row grid. -/
def lowerRow (g : ℕ) (r : Fin (g - 1)) : Fin g :=
  ⟨r.1, lt_of_lt_of_le r.2 (Nat.sub_le g 1)⟩

/-- The upper row of a row gap in a `g`-row grid. -/
def upperRow (g : ℕ) (r : Fin (g - 1)) : Fin g :=
  ⟨r.1 + 1, by
    have hr : r.1 < g - 1 := r.2
    omega⟩

@[simp] theorem lowerRow_val (g : ℕ) (r : Fin (g - 1)) :
    (lowerRow g r).1 = r.1 := rfl

@[simp] theorem upperRow_val (g : ℕ) (r : Fin (g - 1)) :
    (upperRow g r).1 = r.1 + 1 := rfl

theorem lowerRow_ne_upperRow (g : ℕ) (r : Fin (g - 1)) :
    lowerRow g r ≠ upperRow g r := by
  intro h
  have hval := congrArg Fin.val h
  simp [lowerRow, upperRow] at hval

/-- The row gap immediately above a non-top row. -/
def gapAbove {g : ℕ} (r : Fin g) (_h : 0 < r.1) : Fin (g - 1) :=
  ⟨r.1 - 1, by omega⟩

/-- The row gap immediately below a non-bottom row. -/
def gapBelow {g : ℕ} (r : Fin g) (_h : r.1 + 1 < g) : Fin (g - 1) :=
  ⟨r.1, by omega⟩

@[simp] theorem gapAbove_val {g : ℕ} (r : Fin g) (h : 0 < r.1) :
    (gapAbove r h).1 = r.1 - 1 := rfl

@[simp] theorem gapBelow_val {g : ℕ} (r : Fin g) (h : r.1 + 1 < g) :
    (gapBelow r h).1 = r.1 := rfl

@[simp] theorem upperRow_gapAbove {g : ℕ} (r : Fin g) (h : 0 < r.1) :
    upperRow g (gapAbove r h) = r := by
  ext
  simp [upperRow, gapAbove]
  omega

@[simp] theorem lowerRow_gapBelow {g : ℕ} (r : Fin g)
    (h : r.1 + 1 < g) :
    lowerRow g (gapBelow r h) = r := by
  ext
  simp [lowerRow, gapBelow]

theorem gapAbove_lt_gapBelow {g : ℕ} (r : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (gapAbove r hTop).1 < (gapBelow r hBottom).1 := by
  simp [gapAbove, gapBelow]
  omega

namespace StitchedRows

/-- Reindex the stitched row packing by `Fin g`. -/
noncomputable def rowEquiv {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) : Fin g ≃ R.rows.Index :=
  (Fintype.equivFinOfCardEq (α := R.rows.Index) (by
    simpa [PathPacking.card] using R.rows_card)).symm

/-- The row-packing index corresponding to a canonical grid row. -/
noncomputable def row {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r : Fin g) : R.rows.Index :=
  R.rowEquiv r

theorem row_injective {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) :
    Function.Injective R.row :=
  R.rowEquiv.injective

theorem row_lower_ne_upper {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r : Fin (g - 1)) :
    R.row (lowerRow g r) ≠ R.row (upperRow g r) := by
  intro h
  exact lowerRow_ne_upperRow g r (R.row_injective h)

/-- The bridge path selected for the vertical sparse-grid edge at column `c`
and row gap `r`. -/
noncomputable def verticalBridge {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    R.rows.BridgeBetween (R.row (lowerRow g r)) (R.row (upperRow g r)) :=
  Classical.choose
    (R.bridge_in_even_cluster (verticalEdgeIndex g c r) (R.row_lower_ne_upper r))

theorem verticalBridge_staysIn {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridge c r).path.vertexSet ⊆
      P.cluster (evenClusterIndex g (verticalEdgeIndex g c r)) :=
  (Classical.choose_spec
    (R.bridge_in_even_cluster (verticalEdgeIndex g c r) (R.row_lower_ne_upper r)))

/-- The selected bridge, oriented from the lower row to the upper row. -/
noncomputable def verticalBridgePath {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    GraphPath G :=
  (R.verticalBridge c r).orientedPath

@[simp] theorem verticalBridgePath_vertexSet {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).vertexSet =
      (R.verticalBridge c r).path.vertexSet := by
  simp [verticalBridgePath]

theorem verticalBridgePath_staysIn {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).vertexSet ⊆
      P.cluster (evenClusterIndex g (verticalEdgeIndex g c r)) := by
  simpa using R.verticalBridge_staysIn c r

theorem verticalBridgePath_source_mem_lower {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).source ∈
      (R.rows.path (R.row (lowerRow g r))).vertexSet :=
  (R.verticalBridge c r).orientedPath_source_mem_left

theorem verticalBridgePath_target_mem_upper {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).target ∈
      (R.rows.path (R.row (upperRow g r))).vertexSet :=
  (R.verticalBridge c r).orientedPath_target_mem_right

theorem verticalBridgePath_source_mem_cluster {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).source ∈
      P.cluster (evenClusterIndex g (verticalEdgeIndex g c r)) :=
  R.verticalBridgePath_staysIn c r
    (GraphPath.source_mem_vertexSet (R.verticalBridgePath c r))

theorem verticalBridgePath_target_mem_cluster {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).target ∈
      P.cluster (evenClusterIndex g (verticalEdgeIndex g c r)) :=
  R.verticalBridgePath_staysIn c r
    (GraphPath.target_mem_vertexSet (R.verticalBridgePath c r))

/-- The selected vertical bridge is internally disjoint from the whole row
packing. -/
theorem verticalBridgePath_internallyDisjoint_rows
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).InternallyDisjointFromSet R.rows.vertexSet := by
  simpa [verticalBridgePath] using
    (R.verticalBridge c r).orientedPath_internallyDisjoint

/-- Any intersection between a selected vertical bridge and a stitched row is an
endpoint of that bridge. -/
theorem verticalBridgePath_isEndpoint_of_mem_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1))
    {a : R.rows.Index} {v : V}
    (hvBridge : v ∈ (R.verticalBridgePath c r).vertexSet)
    (hvRow : v ∈ (R.rows.path a).vertexSet) :
    (R.verticalBridgePath c r).IsEndpoint v :=
  R.verticalBridgePath_internallyDisjoint_rows c r hvBridge
    (R.rows.path_vertexSet_subset_vertexSet a hvRow)

/-- A selected vertical bridge has distinct endpoints, because its endpoints lie
on distinct node-disjoint stitched rows. -/
theorem verticalBridgePath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin (g - 1)) :
    (R.verticalBridgePath c r).source ≠
      (R.verticalBridgePath c r).target := by
  intro h
  have hrow : R.row (lowerRow g r) ≠ R.row (upperRow g r) :=
    R.row_lower_ne_upper r
  have hdis := R.rows.node_disjoint hrow
  exact Finset.disjoint_left.mp hdis
    (R.verticalBridgePath_source_mem_lower c r)
    (by simpa [h] using R.verticalBridgePath_target_mem_upper c r)

theorem verticalBridgePath_source_before_of_col_lt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.rows.path (R.row (lowerRow g r))).Before
      (R.verticalBridgePath c r).source
      (R.verticalBridgePath d r).source := by
  exact R.row_clusters_ordered (R.row (lowerRow g r))
    (evenClusterIndex_lt_of_lt
      (verticalEdgeIndex_lt_of_col_lt hcd r r))
    (R.verticalBridgePath_source_mem_lower c r)
    (R.verticalBridgePath_source_mem_cluster c r)
    (R.verticalBridgePath_source_mem_lower d r)
    (R.verticalBridgePath_source_mem_cluster d r)

/-- Row segment between lower-row bridge attachments in two column blocks. -/
noncomputable def sourceSegmentOfColLt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
  (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) : GraphPath G :=
  (R.rows.path (R.row (lowerRow g r))).segmentOfBefore
    (R.verticalBridgePath_source_before_of_col_lt hcd r)

@[simp] theorem sourceSegmentOfColLt_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.sourceSegmentOfColLt hcd r).source =
      (R.verticalBridgePath c r).source := rfl

@[simp] theorem sourceSegmentOfColLt_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.sourceSegmentOfColLt hcd r).target =
      (R.verticalBridgePath d r).source := rfl

/-- A lower-row source-to-source segment is contained in its stitched row. -/
theorem sourceSegmentOfColLt_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.sourceSegmentOfColLt hcd r).vertexSet ⊆
      (R.rows.path (R.row (lowerRow g r))).vertexSet :=
  (R.rows.path (R.row (lowerRow g r))).segmentOfBefore_vertexSet_subset
    (R.verticalBridgePath_source_before_of_col_lt hcd r)

theorem verticalBridgePath_target_before_of_col_lt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.rows.path (R.row (upperRow g r))).Before
      (R.verticalBridgePath c r).target
      (R.verticalBridgePath d r).target := by
  exact R.row_clusters_ordered (R.row (upperRow g r))
    (evenClusterIndex_lt_of_lt
      (verticalEdgeIndex_lt_of_col_lt hcd r r))
    (R.verticalBridgePath_target_mem_upper c r)
    (R.verticalBridgePath_target_mem_cluster c r)
    (R.verticalBridgePath_target_mem_upper d r)
    (R.verticalBridgePath_target_mem_cluster d r)

/-- Row segment between upper-row bridge attachments in two column blocks. -/
noncomputable def targetSegmentOfColLt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
  (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) : GraphPath G :=
  (R.rows.path (R.row (upperRow g r))).segmentOfBefore
    (R.verticalBridgePath_target_before_of_col_lt hcd r)

@[simp] theorem targetSegmentOfColLt_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.targetSegmentOfColLt hcd r).source =
      (R.verticalBridgePath c r).target := rfl

@[simp] theorem targetSegmentOfColLt_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.targetSegmentOfColLt hcd r).target =
      (R.verticalBridgePath d r).target := rfl

/-- An upper-row target-to-target segment is contained in its stitched row. -/
theorem targetSegmentOfColLt_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin (g - 1)) :
    (R.targetSegmentOfColLt hcd r).vertexSet ⊆
      (R.rows.path (R.row (upperRow g r))).vertexSet :=
  (R.rows.path (R.row (upperRow g r))).segmentOfBefore_vertexSet_subset
    (R.verticalBridgePath_target_before_of_col_lt hcd r)

theorem verticalBridgePath_target_before_source_same_col
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.rows.path (R.row r)).Before
      (R.verticalBridgePath c (gapAbove r hTop)).target
      (R.verticalBridgePath c (gapBelow r hBottom)).source := by
  have hgap :
      (verticalEdgeIndex g c (gapAbove r hTop)).1 <
        (verticalEdgeIndex g c (gapBelow r hBottom)).1 :=
    verticalEdgeIndex_lt_of_gap_lt (gapAbove_lt_gapBelow r hTop hBottom)
  have hrowAbove : upperRow g (gapAbove r hTop) = r :=
    upperRow_gapAbove r hTop
  have hrowBelow : lowerRow g (gapBelow r hBottom) = r :=
    lowerRow_gapBelow r hBottom
  exact R.row_clusters_ordered (R.row r)
    (evenClusterIndex_lt_of_lt hgap)
    (by simpa [hrowAbove] using
      R.verticalBridgePath_target_mem_upper c (gapAbove r hTop))
    (R.verticalBridgePath_target_mem_cluster c (gapAbove r hTop))
    (by simpa [hrowBelow] using
      R.verticalBridgePath_source_mem_lower c (gapBelow r hBottom))
    (R.verticalBridgePath_source_mem_cluster c (gapBelow r hBottom))

/-- Row segment inside one column block joining the upper and lower attachments
of an internal row. -/
noncomputable def internalSegmentSameCol
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
  (R : StitchedRows G g w P) (c : Fin g) (r : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) : GraphPath G :=
  (R.rows.path (R.row r)).segmentOfBefore
    (R.verticalBridgePath_target_before_source_same_col c r hTop hBottom)

@[simp] theorem internalSegmentSameCol_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.internalSegmentSameCol c r hTop hBottom).source =
      (R.verticalBridgePath c (gapAbove r hTop)).target := rfl

@[simp] theorem internalSegmentSameCol_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.internalSegmentSameCol c r hTop hBottom).target =
      (R.verticalBridgePath c (gapBelow r hBottom)).source := rfl

/-- An internal same-column row segment is contained in its stitched row. -/
theorem internalSegmentSameCol_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (c : Fin g) (r : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.internalSegmentSameCol c r hTop hBottom).vertexSet ⊆
      (R.rows.path (R.row r)).vertexSet :=
  (R.rows.path (R.row r)).segmentOfBefore_vertexSet_subset
    (R.verticalBridgePath_target_before_source_same_col c r hTop hBottom)

theorem verticalBridgePath_source_before_target_next_col
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.rows.path (R.row r)).Before
      (R.verticalBridgePath c (gapBelow r hBottom)).source
      (R.verticalBridgePath d (gapAbove r hTop)).target := by
  have hidx :
      (verticalEdgeIndex g c (gapBelow r hBottom)).1 <
        (verticalEdgeIndex g d (gapAbove r hTop)).1 :=
    verticalEdgeIndex_lt_of_col_lt hcd (gapBelow r hBottom) (gapAbove r hTop)
  have hrowSource : lowerRow g (gapBelow r hBottom) = r :=
    lowerRow_gapBelow r hBottom
  have hrowTarget : upperRow g (gapAbove r hTop) = r :=
    upperRow_gapAbove r hTop
  exact R.row_clusters_ordered (R.row r)
    (evenClusterIndex_lt_of_lt hidx)
    (by simpa [hrowSource] using
      R.verticalBridgePath_source_mem_lower c (gapBelow r hBottom))
    (R.verticalBridgePath_source_mem_cluster c (gapBelow r hBottom))
    (by simpa [hrowTarget] using
      R.verticalBridgePath_target_mem_upper d (gapAbove r hTop))
    (R.verticalBridgePath_target_mem_cluster d (gapAbove r hTop))

/-- Row segment joining the lower attachment in one column block to the upper
attachment in a later column block of the same internal row. -/
noncomputable def sourceToTargetSegmentOfColLt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) : GraphPath G :=
  (R.rows.path (R.row r)).segmentOfBefore
    (R.verticalBridgePath_source_before_target_next_col hcd r hTop hBottom)

@[simp] theorem sourceToTargetSegmentOfColLt_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.sourceToTargetSegmentOfColLt hcd r hTop hBottom).source =
      (R.verticalBridgePath c (gapBelow r hBottom)).source := rfl

@[simp] theorem sourceToTargetSegmentOfColLt_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.sourceToTargetSegmentOfColLt hcd r hTop hBottom).target =
      (R.verticalBridgePath d (gapAbove r hTop)).target := rfl

/-- A lower-to-upper segment across consecutive column blocks is contained in
its stitched row. -/
theorem sourceToTargetSegmentOfColLt_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.sourceToTargetSegmentOfColLt hcd r hTop hBottom).vertexSet ⊆
      (R.rows.path (R.row r)).vertexSet :=
  (R.rows.path (R.row r)).segmentOfBefore_vertexSet_subset
    (R.verticalBridgePath_source_before_target_next_col hcd r hTop hBottom)

/-- The host vertex representing a valid sparse-grid port in the row-and-bridge
subdivision from Appendix C.1.  A lower (`true`) port is represented by the
source of the bridge to the row below; an upper (`false`) port is represented by
the target of the bridge from the row above. -/
noncomputable def validVertexImage
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (x : SparseGrid.ValidVertex g) : V :=
  if h : x.1.port = true then
    (R.verticalBridgePath x.1.col
      (gapBelow x.1.row (SparseGrid.row_succ_lt_of_valid_true hg x.2 h))).source
  else
    (R.verticalBridgePath x.1.col
      (gapAbove x.1.row (SparseGrid.row_pos_of_valid_false hg x.2
        (Bool.eq_false_of_not_eq_true h)))).target

/-- The even-cluster bridge index incident with a valid sparse-grid port under
the Appendix C.1 construction. -/
noncomputable def validVertexIncidentIndex {g : ℕ} (hg : 2 ≤ g)
    (x : SparseGrid.ValidVertex g) : Fin (g * (g - 1)) :=
  if h : x.1.port = true then
    verticalEdgeIndex g x.1.col
      (gapBelow x.1.row (SparseGrid.row_succ_lt_of_valid_true hg x.2 h))
  else
    verticalEdgeIndex g x.1.col
      (gapAbove x.1.row (SparseGrid.row_pos_of_valid_false hg x.2
        (Bool.eq_false_of_not_eq_true h)))

theorem validVertexImage_eq_of_true
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (x : SparseGrid.ValidVertex g) (h : x.1.port = true) :
    R.validVertexImage hg x =
      (R.verticalBridgePath x.1.col
        (gapBelow x.1.row (SparseGrid.row_succ_lt_of_valid_true hg x.2 h))).source := by
  simp [validVertexImage, h]

theorem validVertexImage_eq_of_false
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (x : SparseGrid.ValidVertex g) (h : x.1.port = false) :
    R.validVertexImage hg x =
      (R.verticalBridgePath x.1.col
        (gapAbove x.1.row (SparseGrid.row_pos_of_valid_false hg x.2 h))).target := by
  have hne : ¬ x.1.port = true := by
    intro htrue
    simp [h] at htrue
  simp [validVertexImage, hne]

/-- The image of a valid sparse-grid port lies on the stitched row with the
same row coordinate. -/
theorem validVertexImage_mem_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (x : SparseGrid.ValidVertex g) :
    R.validVertexImage hg x ∈
      (R.rows.path (R.row x.1.row)).vertexSet := by
  by_cases htrue : x.1.port = true
  · have hrow :
        lowerRow g
          (gapBelow x.1.row
            (SparseGrid.row_succ_lt_of_valid_true hg x.2 htrue)) = x.1.row :=
      lowerRow_gapBelow x.1.row
        (SparseGrid.row_succ_lt_of_valid_true hg x.2 htrue)
    rw [R.validVertexImage_eq_of_true hg x htrue]
    simpa [hrow] using
      R.verticalBridgePath_source_mem_lower x.1.col
        (gapBelow x.1.row
          (SparseGrid.row_succ_lt_of_valid_true hg x.2 htrue))
  · have hfalse : x.1.port = false := Bool.eq_false_of_not_eq_true htrue
    have hrow :
        upperRow g
          (gapAbove x.1.row
            (SparseGrid.row_pos_of_valid_false hg x.2 hfalse)) = x.1.row :=
      upperRow_gapAbove x.1.row
        (SparseGrid.row_pos_of_valid_false hg x.2 hfalse)
    rw [R.validVertexImage_eq_of_false hg x hfalse]
    simpa [hrow] using
      R.verticalBridgePath_target_mem_upper x.1.col
        (gapAbove x.1.row
          (SparseGrid.row_pos_of_valid_false hg x.2 hfalse))

/-- Distinct stitched rows are node-disjoint, so two valid sparse-grid ports
with the same image must have the same row coordinate. -/
theorem row_eq_of_validVertexImage_eq
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : R.validVertexImage hg x = R.validVertexImage hg y) :
    x.1.row = y.1.row := by
  by_contra hrow
  have hidx : R.row x.1.row ≠ R.row y.1.row := by
    intro hidx
    exact hrow (R.row_injective hidx)
  have hdis := R.rows.node_disjoint hidx
  exact Finset.disjoint_left.mp hdis
    (R.validVertexImage_mem_row hg x)
    (by simpa [hxy] using R.validVertexImage_mem_row hg y)

/-- The image of a valid sparse-grid port lies in its incident even cluster. -/
theorem validVertexImage_mem_incidentCluster
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (x : SparseGrid.ValidVertex g) :
    R.validVertexImage hg x ∈
      P.cluster (evenClusterIndex g (validVertexIncidentIndex hg x)) := by
  by_cases htrue : x.1.port = true
  · rw [R.validVertexImage_eq_of_true hg x htrue]
    simpa [validVertexIncidentIndex, htrue] using
      R.verticalBridgePath_source_mem_cluster x.1.col
        (gapBelow x.1.row
          (SparseGrid.row_succ_lt_of_valid_true hg x.2 htrue))
  · have hfalse : x.1.port = false := Bool.eq_false_of_not_eq_true htrue
    rw [R.validVertexImage_eq_of_false hg x hfalse]
    simpa [validVertexIncidentIndex, htrue] using
      R.verticalBridgePath_target_mem_cluster x.1.col
        (gapAbove x.1.row
          (SparseGrid.row_pos_of_valid_false hg x.2 hfalse))

/-- Along a stitched row, valid sparse-grid ports follow the order of their
incident even clusters. -/
theorem validVertexImage_before_of_incidentIndex_lt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hrow : x.1.row = y.1.row)
    (hidx :
      (validVertexIncidentIndex hg x).1 <
        (validVertexIncidentIndex hg y).1) :
    (R.rows.path (R.row x.1.row)).Before
      (R.validVertexImage hg x) (R.validVertexImage hg y) := by
  exact R.row_clusters_ordered (R.row x.1.row)
    (evenClusterIndex_lt_of_lt hidx)
    (R.validVertexImage_mem_row hg x)
    (R.validVertexImage_mem_incidentCluster hg x)
    (by simpa [hrow] using R.validVertexImage_mem_row hg y)
    (R.validVertexImage_mem_incidentCluster hg y)

/-- A valid port whose incident cluster is earlier than the source endpoint of
a row segment is not in that segment's allocated drop-last part. -/
theorem validVertexImage_not_mem_rowSegment_dropLast_of_incidentIndex_lt_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hrowzx : z.1.row = x.1.row)
    (hidx :
      (validVertexIncidentIndex hg z).1 <
        (validVertexIncidentIndex hg x).1)
    (hxy :
      (R.rows.path (R.row x.1.row)).Before
        (R.validVertexImage hg x) (R.validVertexImage hg y)) :
    R.validVertexImage hg z ∉
      ((R.rows.path (R.row x.1.row)).segmentOfBefore hxy).dropLast.vertexSet := by
  have hzBefore :
      (R.rows.path (R.row x.1.row)).Before
        (R.validVertexImage hg z) (R.validVertexImage hg x) := by
    simpa [hrowzx] using
      R.validVertexImage_before_of_incidentIndex_lt hg hrowzx hidx
  have hne :
      R.validVertexImage hg z ≠ R.validVertexImage hg x :=
    by
      intro hEq
      have hcluster :
          evenClusterIndex g (validVertexIncidentIndex hg z) ≠
            evenClusterIndex g (validVertexIncidentIndex hg x) := by
        intro h
        have hidxEq := evenClusterIndex_injective h
        have hval := congrArg Fin.val hidxEq
        omega
      exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster)
        (R.validVertexImage_mem_incidentCluster hg z)
        (by simpa [hEq] using R.validVertexImage_mem_incidentCluster hg x)
  exact GraphPath.not_mem_segmentOfBefore_dropLast_of_before_source
    (R.rows.path (R.row x.1.row)) hxy hzBefore hne

/-- A valid port whose incident cluster is later than the target endpoint of a
row segment is not in that segment's allocated drop-last part. -/
theorem validVertexImage_not_mem_rowSegment_dropLast_of_target_incidentIndex_lt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hrowxy : x.1.row = y.1.row)
    (hrowzy : z.1.row = y.1.row)
    (hidx :
      (validVertexIncidentIndex hg y).1 <
        (validVertexIncidentIndex hg z).1)
    (hxy :
      (R.rows.path (R.row x.1.row)).Before
        (R.validVertexImage hg x) (R.validVertexImage hg y)) :
    R.validVertexImage hg z ∉
      ((R.rows.path (R.row x.1.row)).segmentOfBefore hxy).dropLast.vertexSet := by
  have hyBefore :
      (R.rows.path (R.row x.1.row)).Before
        (R.validVertexImage hg y) (R.validVertexImage hg z) := by
    have hrow : y.1.row = z.1.row := hrowzy.symm
    simpa [hrowxy] using
      R.validVertexImage_before_of_incidentIndex_lt hg hrow hidx
  have hne :
      R.validVertexImage hg z ≠ R.validVertexImage hg y :=
    by
      intro hEq
      have hcluster :
          evenClusterIndex g (validVertexIncidentIndex hg z) ≠
            evenClusterIndex g (validVertexIncidentIndex hg y) := by
        intro h
        have hidxEq := evenClusterIndex_injective h
        have hval := congrArg Fin.val hidxEq
        omega
      exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster)
        (R.validVertexImage_mem_incidentCluster hg z)
        (by simpa [hEq] using R.validVertexImage_mem_incidentCluster hg y)
  exact GraphPath.not_mem_segmentOfBefore_dropLast_of_target_before
    (R.rows.path (R.row x.1.row)) hxy hyBefore hne

/-- Concrete form of row-segment exclusion, where the segment endpoints are
given as host vertices and related to valid sparse-grid ports by explicit
equalities.  This is the convenient form for the named horizontal pieces, whose
definitions store row-order witnesses in terms of bridge endpoints. -/
theorem validVertexImage_not_mem_concrete_rowSegment_dropLast_of_incidentIndex_outside
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g} {source target : V}
    (hrowxy : x.1.row = y.1.row)
    (hrowzx : z.1.row = x.1.row)
    (hsource : R.validVertexImage hg x = source)
    (htarget : R.validVertexImage hg y = target)
    (hseg :
      (R.rows.path (R.row x.1.row)).Before source target)
    (hout :
      (validVertexIncidentIndex hg z).1 <
          (validVertexIncidentIndex hg x).1 ∨
        (validVertexIncidentIndex hg y).1 <
          (validVertexIncidentIndex hg z).1) :
    R.validVertexImage hg z ∉
      ((R.rows.path (R.row x.1.row)).segmentOfBefore hseg).dropLast.vertexSet := by
  rcases hout with hbefore | hafter
  · have hzBeforeImg :
        (R.rows.path (R.row x.1.row)).Before
          (R.validVertexImage hg z) (R.validVertexImage hg x) := by
      simpa [hrowzx] using
        R.validVertexImage_before_of_incidentIndex_lt hg hrowzx hbefore
    have hzBefore :
        (R.rows.path (R.row x.1.row)).Before
          (R.validVertexImage hg z) source := by
      rwa [hsource] at hzBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠ R.validVertexImage hg x := by
      intro hEq
      have hcluster :
          evenClusterIndex g (validVertexIncidentIndex hg z) ≠
            evenClusterIndex g (validVertexIncidentIndex hg x) := by
        intro h
        have hidxEq := evenClusterIndex_injective h
        have hval := congrArg Fin.val hidxEq
        omega
      exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster)
        (R.validVertexImage_mem_incidentCluster hg z)
        (by simpa [hEq] using R.validVertexImage_mem_incidentCluster hg x)
    have hne : R.validVertexImage hg z ≠ source := by
      rwa [← hsource]
    exact GraphPath.not_mem_segmentOfBefore_dropLast_of_before_source
      (R.rows.path (R.row x.1.row)) hseg hzBefore hne
  · have hyBeforeImg :
        (R.rows.path (R.row x.1.row)).Before
          (R.validVertexImage hg y) (R.validVertexImage hg z) := by
      have hrowyz : y.1.row = z.1.row := hrowxy.symm.trans hrowzx.symm
      simpa [hrowxy] using
        R.validVertexImage_before_of_incidentIndex_lt hg hrowyz hafter
    have hyBefore :
        (R.rows.path (R.row x.1.row)).Before target
          (R.validVertexImage hg z) := by
      rwa [htarget] at hyBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠ R.validVertexImage hg y := by
      intro hEq
      have hcluster :
          evenClusterIndex g (validVertexIncidentIndex hg z) ≠
            evenClusterIndex g (validVertexIncidentIndex hg y) := by
        intro h
        have hidxEq := evenClusterIndex_injective h
        have hval := congrArg Fin.val hidxEq
        omega
      exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster)
        (R.validVertexImage_mem_incidentCluster hg z)
        (by simpa [hEq] using R.validVertexImage_mem_incidentCluster hg y)
    have hne : R.validVertexImage hg z ≠ target := by
      rwa [← htarget]
    exact GraphPath.not_mem_segmentOfBefore_dropLast_of_target_before
      (R.rows.path (R.row x.1.row)) hseg hyBefore hne

/-- Distinct path-of-sets clusters are disjoint, so equal sparse-grid images
must come from the same incident vertical-edge index. -/
theorem incidentIndex_eq_of_validVertexImage_eq
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : R.validVertexImage hg x = R.validVertexImage hg y) :
    validVertexIncidentIndex hg x = validVertexIncidentIndex hg y := by
  by_contra hidx
  have hcluster :
      evenClusterIndex g (validVertexIncidentIndex hg x) ≠
        evenClusterIndex g (validVertexIncidentIndex hg y) := by
    intro h
    exact hidx (evenClusterIndex_injective h)
  exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster)
    (R.validVertexImage_mem_incidentCluster hg x)
    (by simpa [hxy] using R.validVertexImage_mem_incidentCluster hg y)

/-- Ports on different stitched rows have different images. -/
theorem validVertexImage_ne_of_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g} (hrow : x.1.row ≠ y.1.row) :
    R.validVertexImage hg x ≠ R.validVertexImage hg y := by
  intro hxy
  exact hrow (R.row_eq_of_validVertexImage_eq hg hxy)

/-- Ports incident with different even clusters have different images. -/
theorem validVertexImage_ne_of_incidentIndex_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hidx : validVertexIncidentIndex hg x ≠ validVertexIncidentIndex hg y) :
    R.validVertexImage hg x ≠ R.validVertexImage hg y := by
  intro hxy
  exact hidx (R.incidentIndex_eq_of_validVertexImage_eq hg hxy)

/-- The endpoint map from valid sparse-grid ports to the host graph is
injective.  The proof uses row disjointness for the row coordinate and
path-of-sets cluster disjointness plus injectivity of `verticalEdgeIndex` for
the column/port coordinate. -/
theorem validVertexImage_injective
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g) :
    Function.Injective (R.validVertexImage hg) := by
  intro x y hxy
  have hrow : x.1.row = y.1.row :=
    R.row_eq_of_validVertexImage_eq hg hxy
  have hrowVal : x.1.row.1 = y.1.row.1 := congrArg Fin.val hrow
  have hidx : validVertexIncidentIndex hg x = validVertexIncidentIndex hg y :=
    R.incidentIndex_eq_of_validVertexImage_eq hg hxy
  by_cases hxtrue : x.1.port = true
  · by_cases hytrue : y.1.port = true
    · have hidx' :
          verticalEdgeIndex g x.1.col
              (gapBelow x.1.row
                (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue)) =
            verticalEdgeIndex g y.1.col
              (gapBelow y.1.row
                (SparseGrid.row_succ_lt_of_valid_true hg y.2 hytrue)) := by
        simpa [validVertexIncidentIndex, hxtrue, hytrue] using hidx
      have hpair := verticalEdgeIndex_eq_pair hidx'
      have hcol : x.1.col = y.1.col := congrArg Prod.fst hpair
      have hport : x.1.port = y.1.port := hxtrue.trans hytrue.symm
      apply Subtype.ext
      exact SparseGrid.Vertex.ext hrow hcol hport
    · have hyfalse : y.1.port = false := Bool.eq_false_of_not_eq_true hytrue
      have hidx' :
          verticalEdgeIndex g x.1.col
              (gapBelow x.1.row
                (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue)) =
            verticalEdgeIndex g y.1.col
              (gapAbove y.1.row
                (SparseGrid.row_pos_of_valid_false hg y.2 hyfalse)) := by
        simpa [validVertexIncidentIndex, hxtrue, hytrue] using hidx
      have hpair := verticalEdgeIndex_eq_pair hidx'
      have hgap :
          gapBelow x.1.row
              (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue) =
            gapAbove y.1.row
              (SparseGrid.row_pos_of_valid_false hg y.2 hyfalse) :=
        congrArg Prod.snd hpair
      have hgapVal : x.1.row.1 = y.1.row.1 - 1 := by
        simpa [gapBelow, gapAbove] using congrArg Fin.val hgap
      have hypos : 0 < y.1.row.1 :=
        SparseGrid.row_pos_of_valid_false hg y.2 hyfalse
      omega
  · have hxfalse : x.1.port = false := Bool.eq_false_of_not_eq_true hxtrue
    by_cases hytrue : y.1.port = true
    · have hidx' :
          verticalEdgeIndex g x.1.col
              (gapAbove x.1.row
                (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse)) =
            verticalEdgeIndex g y.1.col
              (gapBelow y.1.row
                (SparseGrid.row_succ_lt_of_valid_true hg y.2 hytrue)) := by
        simpa [validVertexIncidentIndex, hxtrue, hytrue] using hidx
      have hpair := verticalEdgeIndex_eq_pair hidx'
      have hgap :
          gapAbove x.1.row
              (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse) =
            gapBelow y.1.row
              (SparseGrid.row_succ_lt_of_valid_true hg y.2 hytrue) :=
        congrArg Prod.snd hpair
      have hgapVal : x.1.row.1 - 1 = y.1.row.1 := by
        simpa [gapBelow, gapAbove] using congrArg Fin.val hgap
      have hxpos : 0 < x.1.row.1 :=
        SparseGrid.row_pos_of_valid_false hg x.2 hxfalse
      omega
    · have hyfalse : y.1.port = false := Bool.eq_false_of_not_eq_true hytrue
      have hidx' :
          verticalEdgeIndex g x.1.col
              (gapAbove x.1.row
                (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse)) =
            verticalEdgeIndex g y.1.col
              (gapAbove y.1.row
                (SparseGrid.row_pos_of_valid_false hg y.2 hyfalse)) := by
        simpa [validVertexIncidentIndex, hxtrue, hytrue] using hidx
      have hpair := verticalEdgeIndex_eq_pair hidx'
      have hcol : x.1.col = y.1.col := congrArg Prod.fst hpair
      have hport : x.1.port = y.1.port := hxfalse.trans hyfalse.symm
      apply Subtype.ext
      exact SparseGrid.Vertex.ext hrow hcol hport

/-- The two endpoints of a vertical sparse-grid edge are incident with the same
even cluster. -/
theorem validVertexIncidentIndex_eq_of_verticalAdj {g : ℕ} (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    validVertexIncidentIndex hg x = validVertexIncidentIndex hg y := by
  rcases hxy with ⟨hcol, hdir | hdir⟩
  · rcases hdir with ⟨hrow, hxtrue, hyfalse⟩
    have hynot : ¬ y.1.port = true := by
      intro htrue
      simp [hyfalse] at htrue
    have hr : x.1.row.1 + 1 < g := by
      rw [hrow]
      exact y.1.row.2
    have hgap :
        gapAbove y.1.row
            (SparseGrid.row_pos_of_valid_false hg y.2 hyfalse) =
          gapBelow x.1.row hr := by
      ext
      simp [gapAbove, gapBelow]
      omega
    simp [validVertexIncidentIndex, hxtrue, hynot, hcol, hgap]
  · rcases hdir with ⟨hrow, hytrue, hxfalse⟩
    have hxnot : ¬ x.1.port = true := by
      intro htrue
      simp [hxfalse] at htrue
    have hr : y.1.row.1 + 1 < g := by
      rw [hrow]
      exact x.1.row.2
    have hgap :
        gapAbove x.1.row
            (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse) =
          gapBelow y.1.row hr := by
      ext
      simp [gapAbove, gapBelow]
      omega
    simp [validVertexIncidentIndex, hxnot, hytrue, hcol.symm, hgap]

/-- If two rank-oriented vertical sparse-grid edges use the same incident
bridge index, then their sources are the same valid sparse-grid vertex. -/
theorem eq_of_verticalAdj_incidentIndex_eq_of_rank_lt {g : ℕ} (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hzt : SparseGrid.VerticalAdj z.1 t.1)
    (hidx : validVertexIncidentIndex hg x = validVertexIncidentIndex hg z)
    (hrankxy :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hrankzt :
      ValidSparseGridPathCertificate.validVertexRank z <
        ValidSparseGridPathCertificate.validVertexRank t) :
    x = z := by
  by_cases hxtrue : x.1.port = true
  · by_cases hztrue : z.1.port = true
    · have hidx' :
          verticalEdgeIndex g x.1.col
              (gapBelow x.1.row
                (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue)) =
            verticalEdgeIndex g z.1.col
              (gapBelow z.1.row
                (SparseGrid.row_succ_lt_of_valid_true hg z.2 hztrue)) := by
        simpa [validVertexIncidentIndex, hxtrue, hztrue] using hidx
      have hpair := verticalEdgeIndex_eq_pair hidx'
      have hcol : x.1.col = z.1.col := congrArg Prod.fst hpair
      have hgap :
          gapBelow x.1.row
              (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue) =
            gapBelow z.1.row
              (SparseGrid.row_succ_lt_of_valid_true hg z.2 hztrue) :=
        congrArg Prod.snd hpair
      have hrow : x.1.row = z.1.row := by
        apply Fin.ext
        have hval := congrArg Fin.val hgap
        simpa [gapBelow] using hval
      have hxlast := SparseGrid.ValidVertex.eq_last_of_port_true hg x hxtrue
      have hzlast := SparseGrid.ValidVertex.eq_last_of_port_true hg z hztrue
      rw [hxlast, hzlast, hrow, hcol]
    · have hzfalse : z.1.port = false := Bool.eq_false_of_not_eq_true hztrue
      rcases hxy with ⟨hcolxy, hdirxy | hdirxy⟩
      · rcases hdirxy with ⟨hrowxy, _hxtrue', hyfalse⟩
        rcases hzt with ⟨hcolzt, hdirzt | hdirzt⟩
        · exact False.elim (by simpa [hzfalse] using hdirzt.2.1)
        · rcases hdirzt with ⟨hrowzt, httrue, _hzfalse'⟩
          have hidx' :
              verticalEdgeIndex g x.1.col
                  (gapBelow x.1.row
                    (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue)) =
                verticalEdgeIndex g z.1.col
                  (gapAbove z.1.row
                    (SparseGrid.row_pos_of_valid_false hg z.2 hzfalse)) := by
            simpa [validVertexIncidentIndex, hxtrue, hztrue] using hidx
          have hpair := verticalEdgeIndex_eq_pair hidx'
          have hxz_col : x.1.col = z.1.col := congrArg Prod.fst hpair
          have hgap :
              gapBelow x.1.row
                  (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue) =
                gapAbove z.1.row
                  (SparseGrid.row_pos_of_valid_false hg z.2 hzfalse) :=
            congrArg Prod.snd hpair
          have hzrow : z.1.row.1 = x.1.row.1 + 1 := by
            have hval := congrArg Fin.val hgap
            have hzpos := SparseGrid.row_pos_of_valid_false hg z.2 hzfalse
            simp [gapBelow, gapAbove] at hval
            omega
          have hzy : z = y := by
            apply Subtype.ext
            apply SparseGrid.Vertex.ext
            · apply Fin.ext
              omega
            · exact hxz_col.symm.trans hcolxy
            · exact hzfalse.trans hyfalse.symm
          have htx : t = x := by
            apply Subtype.ext
            apply SparseGrid.Vertex.ext
            · apply Fin.ext
              omega
            · exact hcolzt.symm.trans hxz_col.symm
            · exact httrue.trans hxtrue.symm
          have hcontr :
              ValidSparseGridPathCertificate.validVertexRank y <
                ValidSparseGridPathCertificate.validVertexRank x := by
            simpa [hzy, htx] using hrankzt
          omega
      · rcases hdirxy with ⟨_hrowxy, hytrue, hxfalse⟩
        exact False.elim (by
          simp [hxtrue] at hxfalse)
  · have hxfalse : x.1.port = false := Bool.eq_false_of_not_eq_true hxtrue
    by_cases hztrue : z.1.port = true
    · rcases hxy with ⟨hcolxy, hdirxy | hdirxy⟩
      · rcases hdirxy with ⟨_hrowxy, hxtrue', _hyfalse⟩
        exact False.elim (by
          simp [hxfalse] at hxtrue')
      · rcases hdirxy with ⟨hrowxy, hytrue, _hxfalse'⟩
        rcases hzt with ⟨hcolzt, hdirzt | hdirzt⟩
        · rcases hdirzt with ⟨hrowzt, _hztrue', htfalse⟩
          have hidx' :
              verticalEdgeIndex g x.1.col
                  (gapAbove x.1.row
                    (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse)) =
                verticalEdgeIndex g z.1.col
                  (gapBelow z.1.row
                    (SparseGrid.row_succ_lt_of_valid_true hg z.2 hztrue)) := by
            simpa [validVertexIncidentIndex, hxtrue, hztrue] using hidx
          have hpair := verticalEdgeIndex_eq_pair hidx'
          have hxz_col : x.1.col = z.1.col := congrArg Prod.fst hpair
          have hgap :
              gapAbove x.1.row
                  (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse) =
                gapBelow z.1.row
                  (SparseGrid.row_succ_lt_of_valid_true hg z.2 hztrue) :=
            congrArg Prod.snd hpair
          have hxrow : x.1.row.1 = z.1.row.1 + 1 := by
            have hval := congrArg Fin.val hgap
            have hxpos := SparseGrid.row_pos_of_valid_false hg x.2 hxfalse
            simp [gapBelow, gapAbove] at hval
            omega
          have hzy : z = y := by
            apply Subtype.ext
            apply SparseGrid.Vertex.ext
            · apply Fin.ext
              omega
            · exact hxz_col.symm.trans hcolxy
            · exact hztrue.trans hytrue.symm
          have htx : t = x := by
            apply Subtype.ext
            apply SparseGrid.Vertex.ext
            · apply Fin.ext
              omega
            · exact hcolzt.symm.trans hxz_col.symm
            · exact htfalse.trans hxfalse.symm
          have hcontr :
              ValidSparseGridPathCertificate.validVertexRank y <
                ValidSparseGridPathCertificate.validVertexRank x := by
            simpa [hzy, htx] using hrankzt
          omega
        · rcases hdirzt with ⟨_hrowzt, httrue, hzfalse⟩
          exact False.elim (by
            simp [hztrue] at hzfalse)
    · have hzfalse : z.1.port = false := Bool.eq_false_of_not_eq_true hztrue
      have hidx' :
          verticalEdgeIndex g x.1.col
              (gapAbove x.1.row
                (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse)) =
            verticalEdgeIndex g z.1.col
              (gapAbove z.1.row
                (SparseGrid.row_pos_of_valid_false hg z.2 hzfalse)) := by
        simpa [validVertexIncidentIndex, hxtrue, hztrue] using hidx
      have hpair := verticalEdgeIndex_eq_pair hidx'
      have hcol : x.1.col = z.1.col := congrArg Prod.fst hpair
      have hgap :
          gapAbove x.1.row
              (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse) =
            gapAbove z.1.row
              (SparseGrid.row_pos_of_valid_false hg z.2 hzfalse) :=
        congrArg Prod.snd hpair
      have hrow : x.1.row = z.1.row := by
        apply Fin.ext
        have hval := congrArg Fin.val hgap
        have hxpos := SparseGrid.row_pos_of_valid_false hg x.2 hxfalse
        have hzpos := SparseGrid.row_pos_of_valid_false hg z.2 hzfalse
        simp [gapAbove] at hval
        omega
      have hxfirst := SparseGrid.ValidVertex.eq_first_of_port_false hg x hxfalse
      have hzfirst := SparseGrid.ValidVertex.eq_first_of_port_false hg z hzfalse
      rw [hxfirst, hzfirst, hrow, hcol]

/-- The flattened incident even-cluster index is ordered by column, regardless
of which valid port in the row block is used. -/
theorem validVertexIncidentIndex_lt_of_col_lt {g : ℕ} (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g} (hcol : x.1.col.1 < y.1.col.1) :
    (validVertexIncidentIndex hg x).1 <
      (validVertexIncidentIndex hg y).1 := by
  by_cases hxtrue : x.1.port = true
  · by_cases hytrue : y.1.port = true
    · have hlt := verticalEdgeIndex_lt_of_col_lt (g := g) hcol
        (gapBelow x.1.row
          (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue))
        (gapBelow y.1.row
          (SparseGrid.row_succ_lt_of_valid_true hg y.2 hytrue))
      simpa [validVertexIncidentIndex, hxtrue, hytrue] using hlt
    · have hyfalse : y.1.port = false := Bool.eq_false_of_not_eq_true hytrue
      have hlt := verticalEdgeIndex_lt_of_col_lt (g := g) hcol
        (gapBelow x.1.row
          (SparseGrid.row_succ_lt_of_valid_true hg x.2 hxtrue))
        (gapAbove y.1.row
          (SparseGrid.row_pos_of_valid_false hg y.2 hyfalse))
      simpa [validVertexIncidentIndex, hxtrue, hytrue] using hlt
  · have hxfalse : x.1.port = false := Bool.eq_false_of_not_eq_true hxtrue
    by_cases hytrue : y.1.port = true
    · have hlt := verticalEdgeIndex_lt_of_col_lt (g := g) hcol
        (gapAbove x.1.row
          (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse))
        (gapBelow y.1.row
          (SparseGrid.row_succ_lt_of_valid_true hg y.2 hytrue))
      simpa [validVertexIncidentIndex, hxtrue, hytrue] using hlt
    · have hyfalse : y.1.port = false := Bool.eq_false_of_not_eq_true hytrue
      have hlt := verticalEdgeIndex_lt_of_col_lt (g := g) hcol
        (gapAbove x.1.row
          (SparseGrid.row_pos_of_valid_false hg x.2 hxfalse))
        (gapAbove y.1.row
          (SparseGrid.row_pos_of_valid_false hg y.2 hyfalse))
      simpa [validVertexIncidentIndex, hxtrue, hytrue] using hlt

/-- On an internal row block, the first valid port is incident with the bridge
above the row and the last valid port with the bridge below the row, so the
first incident index is strictly smaller. -/
theorem validVertexIncidentIndex_first_lt_last_of_internal {g : ℕ}
    (hg : 2 ≤ g) (r c : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (validVertexIncidentIndex hg (SparseGrid.ValidVertex.first r c)).1 <
      (validVertexIncidentIndex hg (SparseGrid.ValidVertex.last r c)).1 := by
  have hgap : (gapAbove r hTop).1 < (gapBelow r hBottom).1 := by
    simp [gapAbove, gapBelow]
    omega
  have hlt := verticalEdgeIndex_lt_of_gap_lt (g := g) (c := c) hgap
  have hnotTop : r.1 ≠ 0 := Nat.ne_of_gt hTop
  have hnotBottom : r.1 + 1 ≠ g := Nat.ne_of_lt hBottom
  simpa [validVertexIncidentIndex, SparseGrid.ValidVertex.first,
    SparseGrid.ValidVertex.last, SparseGrid.Vertex.first,
    SparseGrid.Vertex.last, SparseGrid.Vertex.firstPort_not_top hnotTop,
    SparseGrid.Vertex.lastPort_not_bottom hnotBottom] using hlt

/-- On a fixed sparse-grid row, the row-major rank and the flattened incident
bridge index induce the same strict order on valid ports. -/
theorem validVertexIncidentIndex_lt_of_same_row_validVertexRank_lt {g : ℕ}
    (hg : 2 ≤ g) {x y : SparseGrid.ValidVertex g}
    (hrow : x.1.row = y.1.row)
    (hrank :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y) :
    (validVertexIncidentIndex hg x).1 <
      (validVertexIncidentIndex hg y).1 := by
  rcases lt_trichotomy x.1.col.1 y.1.col.1 with hcol_lt | hcol_eq | hcol_gt
  · exact validVertexIncidentIndex_lt_of_col_lt hg hcol_lt
  · have hrowVal : x.1.row.1 = y.1.row.1 := congrArg Fin.val hrow
    have hcolVal : x.1.col.1 = y.1.col.1 := hcol_eq
    have hxfalse : x.1.port = false := by
      by_contra hxnot
      have hxtrue : x.1.port = true := Bool.eq_true_of_not_eq_false hxnot
      dsimp [ValidSparseGridPathCertificate.validVertexRank] at hrank
      rw [hrowVal, hcolVal] at hrank
      by_cases hytrue : y.1.port <;> simp [hxtrue, hytrue] at hrank
    have hytrue : y.1.port = true := by
      by_contra hynot
      have hyfalse : y.1.port = false := Bool.eq_false_of_not_eq_true hynot
      dsimp [ValidSparseGridPathCertificate.validVertexRank] at hrank
      rw [hrowVal, hcolVal] at hrank
      simp [hxfalse, hyfalse] at hrank
    have hcol : x.1.col = y.1.col := Fin.ext hcol_eq
    have hxfirst := SparseGrid.ValidVertex.eq_first_of_port_false hg x hxfalse
    have hylast := SparseGrid.ValidVertex.eq_last_of_port_true hg y hytrue
    have hTop : 0 < x.1.row.1 :=
      SparseGrid.row_pos_of_valid_false hg x.2 hxfalse
    have hBottom : x.1.row.1 + 1 < g := by
      have hyBottom := SparseGrid.row_succ_lt_of_valid_true hg y.2 hytrue
      rwa [hrowVal]
    rw [hxfirst, hylast]
    simpa [hrow, hcol] using
      validVertexIncidentIndex_first_lt_last_of_internal hg x.1.row x.1.col
        hTop hBottom
  · have hrowVal : x.1.row.1 = y.1.row.1 := congrArg Fin.val hrow
    have hyrankx :
        ValidSparseGridPathCertificate.validVertexRank y <
          ValidSparseGridPathCertificate.validVertexRank x := by
      dsimp [ValidSparseGridPathCertificate.validVertexRank]
      rw [hrowVal]
      by_cases hxport : x.1.port <;> by_cases hyport : y.1.port <;>
        simp [hxport, hyport] <;> omega
    omega

/-- For consecutive column blocks in one row, every other valid port has
incident index either before the left endpoint or after the right endpoint. -/
theorem validVertexIncidentIndex_outside_next_col_of_ne {g : ℕ}
    (hg : 2 ≤ g) (r c d : Fin g) (hcd : c.1 + 1 = d.1)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r d) :
    (validVertexIncidentIndex hg z).1 <
        (validVertexIncidentIndex hg
          (SparseGrid.ValidVertex.last r c)).1 ∨
      (validVertexIncidentIndex hg
          (SparseGrid.ValidVertex.first r d)).1 <
        (validVertexIncidentIndex hg z).1 := by
  rcases lt_trichotomy z.1.col.1 c.1 with hzc_lt | hzc_eq | hzc_gt
  · left
    exact validVertexIncidentIndex_lt_of_col_lt hg hzc_lt
  · have hzcolc : z.1.col = c := Fin.ext hzc_eq
    rcases z.2 with hfirstPort | hlastPort
    · have hzfirstc : z = SparseGrid.ValidVertex.first r c := by
        apply Subtype.ext
        apply SparseGrid.Vertex.ext
        · exact hrow
        · exact hzcolc
        · simpa [SparseGrid.ValidVertex.first, SparseGrid.Vertex.first, hrow] using
            hfirstPort
      have hfirst_ne_last :
          SparseGrid.ValidVertex.first r c ≠
            SparseGrid.ValidVertex.last r c := by
        intro h
        exact hzlast (hzfirstc.trans h)
      have hport_ne :
          SparseGrid.Vertex.firstPort r ≠ SparseGrid.Vertex.lastPort r := by
        intro hport
        exact hfirst_ne_last (by
          apply Subtype.ext
          apply SparseGrid.Vertex.ext <;>
            simp [SparseGrid.ValidVertex.first, SparseGrid.ValidVertex.last,
              SparseGrid.Vertex.first, SparseGrid.Vertex.last, hport])
      rcases (SparseGrid.firstPort_ne_lastPort_iff_internal hg r).1 hport_ne with
        ⟨hTop, hBottom⟩
      left
      simpa [hzfirstc] using
        validVertexIncidentIndex_first_lt_last_of_internal hg r c hTop hBottom
    · have hzlastc : z = SparseGrid.ValidVertex.last r c := by
        apply Subtype.ext
        apply SparseGrid.Vertex.ext
        · exact hrow
        · exact hzcolc
        · simpa [SparseGrid.ValidVertex.last, SparseGrid.Vertex.last, hrow] using
            hlastPort
      exact False.elim (hzlast hzlastc)
  · rcases lt_trichotomy z.1.col.1 d.1 with hzd_lt | hzd_eq | hzd_gt
    · omega
    · have hzcold : z.1.col = d := Fin.ext hzd_eq
      rcases z.2 with hfirstPort | hlastPort
      · have hzfirstd : z = SparseGrid.ValidVertex.first r d := by
          apply Subtype.ext
          apply SparseGrid.Vertex.ext
          · exact hrow
          · exact hzcold
          · simpa [SparseGrid.ValidVertex.first, SparseGrid.Vertex.first, hrow] using
              hfirstPort
        exact False.elim (hzfirst hzfirstd)
      · have hzlastd : z = SparseGrid.ValidVertex.last r d := by
          apply Subtype.ext
          apply SparseGrid.Vertex.ext
          · exact hrow
          · exact hzcold
          · simpa [SparseGrid.ValidVertex.last, SparseGrid.Vertex.last, hrow] using
              hlastPort
        have hfirst_ne_last :
            SparseGrid.ValidVertex.first r d ≠
              SparseGrid.ValidVertex.last r d := by
          intro h
          exact hzfirst (hzlastd.trans h.symm)
        have hport_ne :
            SparseGrid.Vertex.firstPort r ≠ SparseGrid.Vertex.lastPort r := by
          intro hport
          exact hfirst_ne_last (by
            apply Subtype.ext
            apply SparseGrid.Vertex.ext <;>
              simp [SparseGrid.ValidVertex.first, SparseGrid.ValidVertex.last,
                SparseGrid.Vertex.first, SparseGrid.Vertex.last, hport])
        rcases (SparseGrid.firstPort_ne_lastPort_iff_internal hg r).1 hport_ne with
          ⟨hTop, hBottom⟩
        right
        simpa [hzlastd] using
          validVertexIncidentIndex_first_lt_last_of_internal hg r d hTop hBottom
    · right
      exact validVertexIncidentIndex_lt_of_col_lt hg hzd_gt

theorem validVertexImage_last_of_not_bottom
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hBottom : r.1 + 1 < g) :
    R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
      (R.verticalBridgePath c (gapBelow r hBottom)).source := by
  have hport : (SparseGrid.ValidVertex.last r c).1.port = true := by
    simp [SparseGrid.ValidVertex.last, SparseGrid.Vertex.last,
      SparseGrid.Vertex.lastPort_not_bottom (Nat.ne_of_lt hBottom)]
  simpa [SparseGrid.ValidVertex.last, SparseGrid.Vertex.last, gapBelow] using
    R.validVertexImage_eq_of_true hg (SparseGrid.ValidVertex.last r c) hport

theorem validVertexImage_first_of_not_top
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hTop : 0 < r.1) :
    R.validVertexImage hg (SparseGrid.ValidVertex.first r c) =
      (R.verticalBridgePath c (gapAbove r hTop)).target := by
  have hport : (SparseGrid.ValidVertex.first r c).1.port = false := by
    simp [SparseGrid.ValidVertex.first, SparseGrid.Vertex.first,
      SparseGrid.Vertex.firstPort_not_top (Nat.ne_of_gt hTop)]
  simpa [SparseGrid.ValidVertex.first, SparseGrid.Vertex.first, gapAbove] using
    R.validVertexImage_eq_of_false hg (SparseGrid.ValidVertex.first r c) hport

/-- On the top row, the first valid sparse-grid port is represented by the
source of the bridge immediately below the row. -/
theorem validVertexImage_first_of_top
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hTop : r.1 = 0) :
    R.validVertexImage hg (SparseGrid.ValidVertex.first r c) =
      (R.verticalBridgePath c (gapBelow r (by omega))).source := by
  have hport : (SparseGrid.ValidVertex.first r c).1.port = true := by
    simp [SparseGrid.ValidVertex.first, SparseGrid.Vertex.first,
      SparseGrid.Vertex.firstPort_top hTop]
  simpa [SparseGrid.ValidVertex.first, SparseGrid.Vertex.first, gapBelow] using
    R.validVertexImage_eq_of_true hg (SparseGrid.ValidVertex.first r c) hport

/-- On the bottom row, the last valid sparse-grid port is represented by the
target of the bridge immediately above the row. -/
theorem validVertexImage_last_of_bottom
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hBottom : r.1 + 1 = g) :
    R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
      (R.verticalBridgePath c (gapAbove r (by omega))).target := by
  have hport : (SparseGrid.ValidVertex.last r c).1.port = false := by
    simp [SparseGrid.ValidVertex.last, SparseGrid.Vertex.last,
      SparseGrid.Vertex.lastPort_bottom hBottom]
  simpa [SparseGrid.ValidVertex.last, SparseGrid.Vertex.last, gapAbove] using
    R.validVertexImage_eq_of_false hg (SparseGrid.ValidVertex.last r c) hport

/-- The bridge path realizing a vertical sparse-grid edge. -/
noncomputable def verticalSparseEdgePath
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r c : Fin g) (hr : r.1 + 1 < g) :
    GraphPath G :=
  R.verticalBridgePath c (gapBelow r hr)

@[simp] theorem verticalSparseEdgePath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hr : r.1 + 1 < g) :
    (R.verticalSparseEdgePath r c hr).source =
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
  exact (R.validVertexImage_last_of_not_bottom hg r c hr).symm

@[simp] theorem verticalSparseEdgePath_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hr : r.1 + 1 < g) :
    (R.verticalSparseEdgePath r c hr).target =
      R.validVertexImage hg
        (SparseGrid.ValidVertex.first ⟨r.1 + 1, hr⟩ c) := by
  have hTop : 0 < (⟨r.1 + 1, hr⟩ : Fin g).1 := Nat.succ_pos r.1
  have h := R.validVertexImage_first_of_not_top hg
    (⟨r.1 + 1, hr⟩ : Fin g) c hTop
  simpa [verticalSparseEdgePath, gapAbove, gapBelow] using h.symm

/-- A vertical sparse-edge path stays in its designated even cluster. -/
theorem verticalSparseEdgePath_vertexSet_subset_cluster
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r c : Fin g) (hr : r.1 + 1 < g) :
    (R.verticalSparseEdgePath r c hr).vertexSet ⊆
      P.cluster (evenClusterIndex g (verticalEdgeIndex g c (gapBelow r hr))) := by
  simpa [verticalSparseEdgePath] using
    R.verticalBridgePath_staysIn c (gapBelow r hr)

/-- A vertical sparse-edge path is internally disjoint from the row packing. -/
theorem verticalSparseEdgePath_internallyDisjoint_rows
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r c : Fin g) (hr : r.1 + 1 < g) :
    (R.verticalSparseEdgePath r c hr).InternallyDisjointFromSet R.rows.vertexSet := by
  simpa [verticalSparseEdgePath] using
    R.verticalBridgePath_internallyDisjoint_rows c (gapBelow r hr)

/-- A vertical sparse-edge path has distinct endpoints. -/
theorem verticalSparseEdgePath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r c : Fin g) (hr : r.1 + 1 < g) :
    (R.verticalSparseEdgePath r c hr).source ≠
      (R.verticalSparseEdgePath r c hr).target := by
  simpa [verticalSparseEdgePath] using
    R.verticalBridgePath_source_ne_target c (gapBelow r hr)

/-- The row segment realizing the internal sparse-grid edge between the two
valid ports of one internal row block. -/
noncomputable def horizontalInternalEdgePath
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r c : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) : GraphPath G :=
  R.internalSegmentSameCol c r hTop hBottom

@[simp] theorem horizontalInternalEdgePath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalInternalEdgePath r c hTop hBottom).source =
      R.validVertexImage hg (SparseGrid.ValidVertex.first r c) := by
  exact (R.validVertexImage_first_of_not_top hg r c hTop).symm

@[simp] theorem horizontalInternalEdgePath_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalInternalEdgePath r c hTop hBottom).target =
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
  exact (R.validVertexImage_last_of_not_bottom hg r c hBottom).symm

/-- An internal horizontal sparse-edge path is contained in its stitched row. -/
theorem horizontalInternalEdgePath_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (r c : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalInternalEdgePath r c hTop hBottom).vertexSet ⊆
      (R.rows.path (R.row r)).vertexSet :=
  R.internalSegmentSameCol_vertexSet_subset_row c r hTop hBottom

/-- An internal horizontal sparse-edge path has distinct endpoints. -/
theorem horizontalInternalEdgePath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g) (r c : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalInternalEdgePath r c hTop hBottom).source ≠
      (R.horizontalInternalEdgePath r c hTop hBottom).target := by
  intro h
  have himage :
      R.validVertexImage hg (SparseGrid.ValidVertex.first r c) =
        R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
    rw [← R.horizontalInternalEdgePath_source hg r c hTop hBottom,
      ← R.horizontalInternalEdgePath_target hg r c hTop hBottom]
    exact h
  exact SparseGrid.ValidVertex.first_ne_last_of_internal hTop hBottom
    (R.validVertexImage_injective hg himage)

/-- A valid port on the same row as an internal horizontal edge is outside the
allocated drop-last segment when its incident cluster lies before the first
endpoint or after the last endpoint. -/
theorem validVertexImage_not_mem_horizontalInternalEdgePath_dropLast_of_incidentIndex_outside
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hout :
      (validVertexIncidentIndex hg z).1 <
          (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.first r c)).1 ∨
        (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.last r c)).1 <
          (validVertexIncidentIndex hg z).1) :
    R.validVertexImage hg z ∉
      (R.horizontalInternalEdgePath r c hTop hBottom).dropLast.vertexSet := by
  have hfirst :
      R.validVertexImage hg (SparseGrid.ValidVertex.first r c) =
        (R.verticalBridgePath c (gapAbove r hTop)).target :=
    R.validVertexImage_first_of_not_top hg r c hTop
  have hlast :
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
        (R.verticalBridgePath c (gapBelow r hBottom)).source :=
    R.validVertexImage_last_of_not_bottom hg r c hBottom
  rcases hout with hbefore | hafter
  · have hzBeforeImg :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg z)
          (R.validVertexImage hg (SparseGrid.ValidVertex.first r c)) := by
      simpa [hrow] using
        R.validVertexImage_before_of_incidentIndex_lt
          hg hrow hbefore
    have hzBefore :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg z)
          ((R.verticalBridgePath c (gapAbove r hTop)).target) := by
      rwa [hfirst] at hzBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠
          R.validVertexImage hg (SparseGrid.ValidVertex.first r c) := by
      intro hEq
      have hcluster :
          evenClusterIndex g (validVertexIncidentIndex hg z) ≠
            evenClusterIndex g
              (validVertexIncidentIndex hg (SparseGrid.ValidVertex.first r c)) := by
        intro h
        have hidxEq := evenClusterIndex_injective h
        have hval := congrArg Fin.val hidxEq
        omega
      exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster)
        (R.validVertexImage_mem_incidentCluster hg z)
        (by simpa [hEq] using
          (R.validVertexImage_mem_incidentCluster hg
            (SparseGrid.ValidVertex.first r c)))
    have hne :
        R.validVertexImage hg z ≠
          (R.verticalBridgePath c (gapAbove r hTop)).target := by
      rwa [← hfirst]
    simpa [horizontalInternalEdgePath, internalSegmentSameCol] using
      GraphPath.not_mem_segmentOfBefore_dropLast_of_before_source
        (R.rows.path (R.row r))
        (R.verticalBridgePath_target_before_source_same_col c r hTop hBottom)
        hzBefore hne
  · have hyBeforeImg :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg (SparseGrid.ValidVertex.last r c))
          (R.validVertexImage hg z) := by
      simpa [hrow] using
        R.validVertexImage_before_of_incidentIndex_lt
          hg hrow.symm hafter
    have hyBefore :
        (R.rows.path (R.row r)).Before
          ((R.verticalBridgePath c (gapBelow r hBottom)).source)
          (R.validVertexImage hg z) := by
      rwa [hlast] at hyBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠
          R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
      intro hEq
      have hcluster :
          evenClusterIndex g (validVertexIncidentIndex hg z) ≠
            evenClusterIndex g
              (validVertexIncidentIndex hg (SparseGrid.ValidVertex.last r c)) := by
        intro h
        have hidxEq := evenClusterIndex_injective h
        have hval := congrArg Fin.val hidxEq
        omega
      exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster)
        (R.validVertexImage_mem_incidentCluster hg z)
        (by simpa [hEq] using
          (R.validVertexImage_mem_incidentCluster hg
            (SparseGrid.ValidVertex.last r c)))
    have hne :
        R.validVertexImage hg z ≠
          (R.verticalBridgePath c (gapBelow r hBottom)).source := by
      rwa [← hlast]
    simpa [horizontalInternalEdgePath, internalSegmentSameCol] using
      GraphPath.not_mem_segmentOfBefore_dropLast_of_target_before
        (R.rows.path (R.row r))
        (R.verticalBridgePath_target_before_source_same_col c r hTop hBottom)
        hyBefore hne

/-- For an internal row block, every other valid port on the same row lies
strictly before the block's first port or strictly after its last port in the
incident-cluster order. -/
theorem validVertexIncidentIndex_outside_internal_of_ne
    {g : ℕ} (hg : 2 ≤ g) (r c : Fin g)
    (hTop : 0 < r.1) (hBottom : r.1 + 1 < g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r c)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c) :
    (validVertexIncidentIndex hg z).1 <
        (validVertexIncidentIndex hg
          (SparseGrid.ValidVertex.first r c)).1 ∨
      (validVertexIncidentIndex hg
          (SparseGrid.ValidVertex.last r c)).1 <
        (validVertexIncidentIndex hg z).1 := by
  have hnotTop : r.1 ≠ 0 := Nat.ne_of_gt hTop
  have hnotBottom : r.1 + 1 ≠ g := Nat.ne_of_lt hBottom
  rcases z with ⟨⟨zr, zc, zp⟩, hzvalid⟩
  simp at hrow
  subst zr
  rcases hzvalid with hzport | hzport
  · have hzp : zp = false := by
      simpa [SparseGrid.Vertex.firstPort_not_top hnotTop] using hzport
    rcases lt_trichotomy zc.1 c.1 with hlt | heq | hgt
    · left
      have hlt' := verticalEdgeIndex_lt_of_col_lt (g := g)
        (c := zc) (d := c) hlt (gapAbove r hTop) (gapAbove r hTop)
      simpa [validVertexIncidentIndex, SparseGrid.ValidVertex.first,
        SparseGrid.Vertex.first, SparseGrid.Vertex.firstPort_not_top hnotTop,
        hzp, gapAbove] using hlt'
    · have hcol : zc = c := Fin.ext heq
      exact False.elim (hzfirst (by
        apply Subtype.ext
        apply SparseGrid.Vertex.ext <;>
          simp [SparseGrid.ValidVertex.first, SparseGrid.Vertex.first, hcol,
            hzp, SparseGrid.Vertex.firstPort_not_top hnotTop]))
    · right
      have hlt' := verticalEdgeIndex_lt_of_col_lt (g := g)
        (c := c) (d := zc) hgt (gapBelow r hBottom) (gapAbove r hTop)
      simpa [validVertexIncidentIndex, SparseGrid.ValidVertex.first,
        SparseGrid.ValidVertex.last, SparseGrid.Vertex.first, SparseGrid.Vertex.last,
        SparseGrid.Vertex.firstPort_not_top hnotTop,
        SparseGrid.Vertex.lastPort_not_bottom hnotBottom, hzp, gapAbove, gapBelow]
        using hlt'
  · have hzp : zp = true := by
      simpa [SparseGrid.Vertex.lastPort_not_bottom hnotBottom] using hzport
    rcases lt_trichotomy zc.1 c.1 with hlt | heq | hgt
    · left
      have hlt' := verticalEdgeIndex_lt_of_col_lt (g := g)
        (c := zc) (d := c) hlt (gapBelow r hBottom) (gapAbove r hTop)
      simpa [validVertexIncidentIndex, SparseGrid.ValidVertex.first,
        SparseGrid.ValidVertex.last, SparseGrid.Vertex.first, SparseGrid.Vertex.last,
        SparseGrid.Vertex.firstPort_not_top hnotTop,
        SparseGrid.Vertex.lastPort_not_bottom hnotBottom, hzp, gapAbove, gapBelow]
        using hlt'
    · have hcol : zc = c := Fin.ext heq
      exact False.elim (hzlast (by
        apply Subtype.ext
        apply SparseGrid.Vertex.ext <;>
          simp [SparseGrid.ValidVertex.last, SparseGrid.Vertex.last, hcol,
            hzp, SparseGrid.Vertex.lastPort_not_bottom hnotBottom]))
    · right
      have hlt' := verticalEdgeIndex_lt_of_col_lt (g := g)
        (c := c) (d := zc) hgt (gapBelow r hBottom) (gapBelow r hBottom)
      simpa [validVertexIncidentIndex, SparseGrid.ValidVertex.last,
        SparseGrid.Vertex.last, SparseGrid.Vertex.lastPort_not_bottom hnotBottom,
        hzp, gapBelow] using hlt'

/-- A same-row valid port that is neither endpoint of an internal horizontal
edge does not lie in that edge's allocated drop-last path. -/
theorem validVertexImage_not_mem_horizontalInternalEdgePath_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r c)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c) :
    R.validVertexImage hg z ∉
      (R.horizontalInternalEdgePath r c hTop hBottom).dropLast.vertexSet :=
  R.validVertexImage_not_mem_horizontalInternalEdgePath_dropLast_of_incidentIndex_outside
    hg r c hTop hBottom hrow
    (validVertexIncidentIndex_outside_internal_of_ne hg r c hTop hBottom
      hrow hzfirst hzlast)

/-- Reverse-orientation form of
`validVertexImage_not_mem_horizontalInternalEdgePath_dropLast_of_ne`. -/
theorem validVertexImage_not_mem_horizontalInternalEdgePath_reverse_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (r c : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r c)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c) :
    R.validVertexImage hg z ∉
      (R.horizontalInternalEdgePath r c hTop hBottom).reverse.dropLast.vertexSet := by
  have hnot :=
    R.validVertexImage_not_mem_horizontalInternalEdgePath_dropLast_of_ne
      hg r c hTop hBottom hrow hzfirst hzlast
  have hneTarget :
      R.validVertexImage hg z ≠
        (R.horizontalInternalEdgePath r c hTop hBottom).target := by
    rw [R.horizontalInternalEdgePath_target hg r c hTop hBottom]
    intro h
    exact hzlast (R.validVertexImage_injective hg h)
  exact GraphPath.not_mem_reverse_dropLast_of_not_mem_dropLast_of_ne_target
    (R.horizontalInternalEdgePath r c hTop hBottom)
    (R.horizontalInternalEdgePath_source_ne_target hg r c hTop hBottom)
    hnot hneTarget

/-- Top-row horizontal sparse-grid edge path between consecutive column
blocks. -/
noncomputable def horizontalTopEdgePath
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : r.1 = 0) : GraphPath G :=
  R.sourceSegmentOfColLt hcd (gapBelow r (by omega))

@[simp] theorem horizontalTopEdgePath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (r : Fin g) (hTop : r.1 = 0) :
    (R.horizontalTopEdgePath hcd r hTop).source =
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
  exact (R.validVertexImage_last_of_not_bottom hg r c (by omega)).symm

@[simp] theorem horizontalTopEdgePath_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (r : Fin g) (hTop : r.1 = 0) :
    (R.horizontalTopEdgePath hcd r hTop).target =
      R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
  exact (R.validVertexImage_first_of_top hg r d hTop).symm

/-- A top-row horizontal sparse-edge path is contained in the top stitched row. -/
theorem horizontalTopEdgePath_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : r.1 = 0) :
    (R.horizontalTopEdgePath hcd r hTop).vertexSet ⊆
      (R.rows.path (R.row r)).vertexSet := by
  have hrow : lowerRow g (gapBelow r (by omega)) = r :=
    lowerRow_gapBelow r (by omega)
  simpa [horizontalTopEdgePath, hrow] using
    R.sourceSegmentOfColLt_vertexSet_subset_row hcd (gapBelow r (by omega))

/-- A top-row horizontal sparse-edge path has distinct endpoints. -/
theorem horizontalTopEdgePath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (r : Fin g) (hTop : r.1 = 0) :
    (R.horizontalTopEdgePath hcd r hTop).source ≠
      (R.horizontalTopEdgePath hcd r hTop).target := by
  intro h
  have hcd_ne : c ≠ d := by
    intro hcols
    have := congrArg Fin.val hcols
    omega
  have himage :
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
        R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
    rw [← R.horizontalTopEdgePath_source hg hcd r hTop,
      ← R.horizontalTopEdgePath_target hg hcd r hTop]
    exact h
  exact SparseGrid.ValidVertex.last_ne_first_of_col_ne hcd_ne
    (R.validVertexImage_injective hg himage)

/-- A valid port on the top row is outside a top horizontal edge segment when
its incident cluster is before the source endpoint or after the target
endpoint. -/
theorem validVertexImage_not_mem_horizontalTopEdgePath_dropLast_of_incidentIndex_outside
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : r.1 = 0)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hout :
      (validVertexIncidentIndex hg z).1 <
          (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.last r c)).1 ∨
        (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.first r d)).1 <
          (validVertexIncidentIndex hg z).1) :
    R.validVertexImage hg z ∉
      (R.horizontalTopEdgePath hcd r hTop).dropLast.vertexSet := by
  have hBottom : r.1 + 1 < g := by omega
  have hlast :
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
        (R.verticalBridgePath c (gapBelow r hBottom)).source :=
    R.validVertexImage_last_of_not_bottom hg r c hBottom
  have hfirst :
      R.validVertexImage hg (SparseGrid.ValidVertex.first r d) =
        (R.verticalBridgePath d (gapBelow r hBottom)).source := by
    simpa [gapBelow] using R.validVertexImage_first_of_top hg r d hTop
  rcases hout with hbefore | hafter
  · have hzBeforeImg :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg z)
          (R.validVertexImage hg (SparseGrid.ValidVertex.last r c)) := by
      simpa [hrow, SparseGrid.ValidVertex.last, SparseGrid.Vertex.last] using
        R.validVertexImage_before_of_incidentIndex_lt
          (x := z) (y := SparseGrid.ValidVertex.last r c) hg
          (by simp [hrow, SparseGrid.ValidVertex.last, SparseGrid.Vertex.last])
          hbefore
    have hzBefore :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg z)
          (R.verticalBridgePath c (gapBelow r hBottom)).source := by
      rwa [hlast] at hzBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠
          R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
      have hidx :
          validVertexIncidentIndex hg z ≠
            validVertexIncidentIndex hg (SparseGrid.ValidVertex.last r c) := by
        intro hEq
        have hval := congrArg Fin.val hEq
        omega
      exact R.validVertexImage_ne_of_incidentIndex_ne hg hidx
    have hne :
        R.validVertexImage hg z ≠
          (R.verticalBridgePath c (gapBelow r hBottom)).source := by
      rwa [← hlast]
    simpa [horizontalTopEdgePath, sourceSegmentOfColLt] using
      GraphPath.not_mem_segmentOfBefore_dropLast_of_before_source
        (R.rows.path (R.row r))
        (R.verticalBridgePath_source_before_of_col_lt hcd (gapBelow r hBottom))
        hzBefore hne
  · have hfirstBeforeImg :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg (SparseGrid.ValidVertex.first r d))
          (R.validVertexImage hg z) := by
      simpa [hrow, SparseGrid.ValidVertex.first, SparseGrid.Vertex.first] using
        R.validVertexImage_before_of_incidentIndex_lt
          (x := SparseGrid.ValidVertex.first r d) (y := z) hg
          (by simp [hrow, SparseGrid.ValidVertex.first, SparseGrid.Vertex.first])
          hafter
    have hfirstBefore :
        (R.rows.path (R.row r)).Before
          (R.verticalBridgePath d (gapBelow r hBottom)).source
          (R.validVertexImage hg z) := by
      rwa [hfirst] at hfirstBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠
          R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
      have hidx :
          validVertexIncidentIndex hg z ≠
            validVertexIncidentIndex hg (SparseGrid.ValidVertex.first r d) := by
        intro hEq
        have hval := congrArg Fin.val hEq
        omega
      exact R.validVertexImage_ne_of_incidentIndex_ne hg hidx
    have hne :
        R.validVertexImage hg z ≠
          (R.verticalBridgePath d (gapBelow r hBottom)).source := by
      rwa [← hfirst]
    simpa [horizontalTopEdgePath, sourceSegmentOfColLt] using
      GraphPath.not_mem_segmentOfBefore_dropLast_of_target_before
        (R.rows.path (R.row r))
        (R.verticalBridgePath_source_before_of_col_lt hcd (gapBelow r hBottom))
        hfirstBefore hne

/-- A same-row valid port that is neither endpoint of a top-row horizontal
edge between consecutive column blocks does not lie in that edge's allocated
drop-last path. -/
theorem validVertexImage_not_mem_horizontalTopEdgePath_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (hsucc : c.1 + 1 = d.1)
    (r : Fin g) (hTop : r.1 = 0)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r d) :
    R.validVertexImage hg z ∉
      (R.horizontalTopEdgePath hcd r hTop).dropLast.vertexSet :=
  R.validVertexImage_not_mem_horizontalTopEdgePath_dropLast_of_incidentIndex_outside
    hg hcd r hTop hrow
    (validVertexIncidentIndex_outside_next_col_of_ne hg r c d hsucc hrow
      hzlast hzfirst)

/-- Reverse-orientation form of
`validVertexImage_not_mem_horizontalTopEdgePath_dropLast_of_ne`. -/
theorem validVertexImage_not_mem_horizontalTopEdgePath_reverse_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (hsucc : c.1 + 1 = d.1)
    (r : Fin g) (hTop : r.1 = 0)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r d) :
    R.validVertexImage hg z ∉
      (R.horizontalTopEdgePath hcd r hTop).reverse.dropLast.vertexSet := by
  have hnot :=
    R.validVertexImage_not_mem_horizontalTopEdgePath_dropLast_of_ne
      hg hcd hsucc r hTop hrow hzlast hzfirst
  have hneTarget :
      R.validVertexImage hg z ≠
        (R.horizontalTopEdgePath hcd r hTop).target := by
    rw [R.horizontalTopEdgePath_target hg hcd r hTop]
    intro h
    exact hzfirst (R.validVertexImage_injective hg h)
  exact GraphPath.not_mem_reverse_dropLast_of_not_mem_dropLast_of_ne_target
    (R.horizontalTopEdgePath hcd r hTop)
    (R.horizontalTopEdgePath_source_ne_target hg hcd r hTop)
    hnot hneTarget

/-- Bottom-row horizontal sparse-grid edge path between consecutive column
blocks. -/
noncomputable def horizontalBottomEdgePath
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hBottom : r.1 + 1 = g) : GraphPath G :=
  R.targetSegmentOfColLt hcd (gapAbove r (by omega))

@[simp] theorem horizontalBottomEdgePath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (r : Fin g) (hBottom : r.1 + 1 = g) :
    (R.horizontalBottomEdgePath hcd r hBottom).source =
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
  exact (R.validVertexImage_last_of_bottom hg r c hBottom).symm

@[simp] theorem horizontalBottomEdgePath_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (r : Fin g) (hBottom : r.1 + 1 = g) :
    (R.horizontalBottomEdgePath hcd r hBottom).target =
      R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
  exact (R.validVertexImage_first_of_not_top hg r d (by omega)).symm

/-- A bottom-row horizontal sparse-edge path is contained in the bottom stitched
row. -/
theorem horizontalBottomEdgePath_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hBottom : r.1 + 1 = g) :
    (R.horizontalBottomEdgePath hcd r hBottom).vertexSet ⊆
      (R.rows.path (R.row r)).vertexSet := by
  have hrow : upperRow g (gapAbove r (by omega)) = r :=
    upperRow_gapAbove r (by omega)
  simpa [horizontalBottomEdgePath, hrow] using
    R.targetSegmentOfColLt_vertexSet_subset_row hcd (gapAbove r (by omega))

/-- A bottom-row horizontal sparse-edge path has distinct endpoints. -/
theorem horizontalBottomEdgePath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (r : Fin g) (hBottom : r.1 + 1 = g) :
    (R.horizontalBottomEdgePath hcd r hBottom).source ≠
      (R.horizontalBottomEdgePath hcd r hBottom).target := by
  intro h
  have hcd_ne : c ≠ d := by
    intro hcols
    have := congrArg Fin.val hcols
    omega
  have himage :
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
        R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
    rw [← R.horizontalBottomEdgePath_source hg hcd r hBottom,
      ← R.horizontalBottomEdgePath_target hg hcd r hBottom]
    exact h
  exact SparseGrid.ValidVertex.last_ne_first_of_col_ne hcd_ne
    (R.validVertexImage_injective hg himage)

/-- A valid port on the bottom row is outside a bottom horizontal edge segment
when its incident cluster is before the source endpoint or after the target
endpoint. -/
theorem validVertexImage_not_mem_horizontalBottomEdgePath_dropLast_of_incidentIndex_outside
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hBottom : r.1 + 1 = g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hout :
      (validVertexIncidentIndex hg z).1 <
          (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.last r c)).1 ∨
        (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.first r d)).1 <
          (validVertexIncidentIndex hg z).1) :
    R.validVertexImage hg z ∉
      (R.horizontalBottomEdgePath hcd r hBottom).dropLast.vertexSet := by
  have hTop : 0 < r.1 := by omega
  have hlast :
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
        (R.verticalBridgePath c (gapAbove r hTop)).target := by
    simpa [gapAbove] using R.validVertexImage_last_of_bottom hg r c hBottom
  have hfirst :
      R.validVertexImage hg (SparseGrid.ValidVertex.first r d) =
        (R.verticalBridgePath d (gapAbove r hTop)).target :=
    R.validVertexImage_first_of_not_top hg r d hTop
  rcases hout with hbefore | hafter
  · have hzBeforeImg :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg z)
          (R.validVertexImage hg (SparseGrid.ValidVertex.last r c)) := by
      simpa [hrow, SparseGrid.ValidVertex.last, SparseGrid.Vertex.last] using
        R.validVertexImage_before_of_incidentIndex_lt
          (x := z) (y := SparseGrid.ValidVertex.last r c) hg
          (by simp [hrow, SparseGrid.ValidVertex.last, SparseGrid.Vertex.last])
          hbefore
    have hzBefore :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg z)
          (R.verticalBridgePath c (gapAbove r hTop)).target := by
      rwa [hlast] at hzBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠
          R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
      have hidx :
          validVertexIncidentIndex hg z ≠
            validVertexIncidentIndex hg (SparseGrid.ValidVertex.last r c) := by
        intro hEq
        have hval := congrArg Fin.val hEq
        omega
      exact R.validVertexImage_ne_of_incidentIndex_ne hg hidx
    have hne :
        R.validVertexImage hg z ≠
          (R.verticalBridgePath c (gapAbove r hTop)).target := by
      rwa [← hlast]
    simpa [horizontalBottomEdgePath, targetSegmentOfColLt] using
      GraphPath.not_mem_segmentOfBefore_dropLast_of_before_source
        (R.rows.path (R.row (upperRow g (gapAbove r hTop))))
        (R.verticalBridgePath_target_before_of_col_lt hcd (gapAbove r hTop))
        (by simpa using hzBefore) hne
  · have hfirstBeforeImg :
        (R.rows.path (R.row r)).Before
          (R.validVertexImage hg (SparseGrid.ValidVertex.first r d))
          (R.validVertexImage hg z) := by
      simpa [hrow, SparseGrid.ValidVertex.first, SparseGrid.Vertex.first] using
        R.validVertexImage_before_of_incidentIndex_lt
          (x := SparseGrid.ValidVertex.first r d) (y := z) hg
          (by simp [hrow, SparseGrid.ValidVertex.first, SparseGrid.Vertex.first])
          hafter
    have hfirstBefore :
        (R.rows.path (R.row r)).Before
          (R.verticalBridgePath d (gapAbove r hTop)).target
          (R.validVertexImage hg z) := by
      rwa [hfirst] at hfirstBeforeImg
    have hneImg :
        R.validVertexImage hg z ≠
          R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
      have hidx :
          validVertexIncidentIndex hg z ≠
            validVertexIncidentIndex hg (SparseGrid.ValidVertex.first r d) := by
        intro hEq
        have hval := congrArg Fin.val hEq
        omega
      exact R.validVertexImage_ne_of_incidentIndex_ne hg hidx
    have hne :
        R.validVertexImage hg z ≠
          (R.verticalBridgePath d (gapAbove r hTop)).target := by
      rwa [← hfirst]
    simpa [horizontalBottomEdgePath, targetSegmentOfColLt] using
      GraphPath.not_mem_segmentOfBefore_dropLast_of_target_before
        (R.rows.path (R.row (upperRow g (gapAbove r hTop))))
        (R.verticalBridgePath_target_before_of_col_lt hcd (gapAbove r hTop))
        (by simpa using hfirstBefore) hne

/-- A same-row valid port that is neither endpoint of a bottom-row horizontal
edge between consecutive column blocks does not lie in that edge's allocated
drop-last path. -/
theorem validVertexImage_not_mem_horizontalBottomEdgePath_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (hsucc : c.1 + 1 = d.1)
    (r : Fin g) (hBottom : r.1 + 1 = g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r d) :
    R.validVertexImage hg z ∉
      (R.horizontalBottomEdgePath hcd r hBottom).dropLast.vertexSet :=
  R.validVertexImage_not_mem_horizontalBottomEdgePath_dropLast_of_incidentIndex_outside
    hg hcd r hBottom hrow
    (validVertexIncidentIndex_outside_next_col_of_ne hg r c d hsucc hrow
      hzlast hzfirst)

/-- Reverse-orientation form of
`validVertexImage_not_mem_horizontalBottomEdgePath_dropLast_of_ne`. -/
theorem validVertexImage_not_mem_horizontalBottomEdgePath_reverse_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (hsucc : c.1 + 1 = d.1)
    (r : Fin g) (hBottom : r.1 + 1 = g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r d) :
    R.validVertexImage hg z ∉
      (R.horizontalBottomEdgePath hcd r hBottom).reverse.dropLast.vertexSet := by
  have hnot :=
    R.validVertexImage_not_mem_horizontalBottomEdgePath_dropLast_of_ne
      hg hcd hsucc r hBottom hrow hzlast hzfirst
  have hneTarget :
      R.validVertexImage hg z ≠
        (R.horizontalBottomEdgePath hcd r hBottom).target := by
    rw [R.horizontalBottomEdgePath_target hg hcd r hBottom]
    intro h
    exact hzfirst (R.validVertexImage_injective hg h)
  exact GraphPath.not_mem_reverse_dropLast_of_not_mem_dropLast_of_ne_target
    (R.horizontalBottomEdgePath hcd r hBottom)
    (R.horizontalBottomEdgePath_source_ne_target hg hcd r hBottom)
    hnot hneTarget

/-- Internal-row horizontal sparse-grid edge path between consecutive column
blocks. -/
noncomputable def horizontalMiddleEdgePath
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    GraphPath G :=
  R.sourceToTargetSegmentOfColLt hcd r hTop hBottom

@[simp] theorem horizontalMiddleEdgePath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalMiddleEdgePath hcd r hTop hBottom).source =
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) := by
  exact (R.validVertexImage_last_of_not_bottom hg r c hBottom).symm

@[simp] theorem horizontalMiddleEdgePath_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalMiddleEdgePath hcd r hTop hBottom).target =
      R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
  exact (R.validVertexImage_first_of_not_top hg r d hTop).symm

/-- An internal-row horizontal sparse-edge path between column blocks is
contained in its stitched row. -/
theorem horizontalMiddleEdgePath_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalMiddleEdgePath hcd r hTop hBottom).vertexSet ⊆
      (R.rows.path (R.row r)).vertexSet :=
  R.sourceToTargetSegmentOfColLt_vertexSet_subset_row hcd r hTop hBottom

/-- An internal-row horizontal sparse-edge path between column blocks has
distinct endpoints. -/
theorem horizontalMiddleEdgePath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g) :
    (R.horizontalMiddleEdgePath hcd r hTop hBottom).source ≠
      (R.horizontalMiddleEdgePath hcd r hTop hBottom).target := by
  intro h
  have hcd_ne : c ≠ d := by
    intro hcols
    have := congrArg Fin.val hcols
    omega
  have himage :
      R.validVertexImage hg (SparseGrid.ValidVertex.last r c) =
        R.validVertexImage hg (SparseGrid.ValidVertex.first r d) := by
    rw [← R.horizontalMiddleEdgePath_source hg hcd r hTop hBottom,
      ← R.horizontalMiddleEdgePath_target hg hcd r hTop hBottom]
    exact h
  exact SparseGrid.ValidVertex.last_ne_first_of_col_ne hcd_ne
    (R.validVertexImage_injective hg himage)

/-- A valid port on the same row as a middle horizontal edge is outside the
allocated drop-last segment when its incident cluster lies before the source
endpoint or after the target endpoint. -/
theorem validVertexImage_not_mem_horizontalMiddleEdgePath_dropLast_of_incidentIndex_outside
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hout :
      (validVertexIncidentIndex hg z).1 <
          (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.last r c)).1 ∨
        (validVertexIncidentIndex hg
            (SparseGrid.ValidVertex.first r d)).1 <
          (validVertexIncidentIndex hg z).1) :
    R.validVertexImage hg z ∉
      (R.horizontalMiddleEdgePath hcd r hTop hBottom).dropLast.vertexSet := by
  simpa [horizontalMiddleEdgePath, sourceToTargetSegmentOfColLt] using
    R.validVertexImage_not_mem_concrete_rowSegment_dropLast_of_incidentIndex_outside
      (x := SparseGrid.ValidVertex.last r c)
      (y := SparseGrid.ValidVertex.first r d) (z := z)
      (source := (R.verticalBridgePath c (gapBelow r hBottom)).source)
      (target := (R.verticalBridgePath d (gapAbove r hTop)).target)
      hg rfl hrow
      (R.validVertexImage_last_of_not_bottom hg r c hBottom)
      (R.validVertexImage_first_of_not_top hg r d hTop)
      (R.verticalBridgePath_source_before_target_next_col hcd r hTop hBottom)
      hout

/-- A same-row valid port that is neither endpoint of an internal-row
horizontal edge between consecutive column blocks does not lie in that edge's
allocated drop-last path. -/
theorem validVertexImage_not_mem_horizontalMiddleEdgePath_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (hsucc : c.1 + 1 = d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r d) :
    R.validVertexImage hg z ∉
      (R.horizontalMiddleEdgePath hcd r hTop hBottom).dropLast.vertexSet :=
  R.validVertexImage_not_mem_horizontalMiddleEdgePath_dropLast_of_incidentIndex_outside
    hg hcd r hTop hBottom hrow
    (validVertexIncidentIndex_outside_next_col_of_ne hg r c d hsucc hrow
      hzlast hzfirst)

/-- Reverse-orientation form of
`validVertexImage_not_mem_horizontalMiddleEdgePath_dropLast_of_ne`. -/
theorem validVertexImage_not_mem_horizontalMiddleEdgePath_reverse_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {c d : Fin g} (hcd : c.1 < d.1) (hsucc : c.1 + 1 = d.1)
    (r : Fin g) (hTop : 0 < r.1) (hBottom : r.1 + 1 < g)
    {z : SparseGrid.ValidVertex g} (hrow : z.1.row = r)
    (hzlast : z ≠ SparseGrid.ValidVertex.last r c)
    (hzfirst : z ≠ SparseGrid.ValidVertex.first r d) :
    R.validVertexImage hg z ∉
      (R.horizontalMiddleEdgePath hcd r hTop hBottom).reverse.dropLast.vertexSet := by
  have hnot :=
    R.validVertexImage_not_mem_horizontalMiddleEdgePath_dropLast_of_ne
      hg hcd hsucc r hTop hBottom hrow hzlast hzfirst
  have hneTarget :
      R.validVertexImage hg z ≠
        (R.horizontalMiddleEdgePath hcd r hTop hBottom).target := by
    rw [R.horizontalMiddleEdgePath_target hg hcd r hTop hBottom]
    intro h
    exact hzfirst (R.validVertexImage_injective hg h)
  exact GraphPath.not_mem_reverse_dropLast_of_not_mem_dropLast_of_ne_target
    (R.horizontalMiddleEdgePath hcd r hTop hBottom)
    (R.horizontalMiddleEdgePath_source_ne_target hg hcd r hTop hBottom)
    hnot hneTarget

/-- Explicit path realizing a vertical sparse-grid adjacency.

The selector branches on decidable coordinate/port conditions instead of
eliminating the adjacency proof into data.  This keeps the chosen path
transparent enough for later separation lemmas. -/
noncomputable def verticalAdjPath
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    GraphPath G := by
  classical
  by_cases hforward :
      x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false
  · exact R.verticalSparseEdgePath x.1.row x.1.col (by
      rw [hforward.2.1]
      exact y.1.row.2)
  · have hback :
        y.1.col = x.1.col ∧
          y.1.row.1 + 1 = x.1.row.1 ∧
            y.1.port = true ∧ x.1.port = false := by
      rcases hxy with ⟨hcol, hdir | hdir⟩
      · exact False.elim (hforward ⟨hcol, hdir.1, hdir.2.1, hdir.2.2⟩)
      · exact ⟨hcol.symm, hdir.1, hdir.2.1, hdir.2.2⟩
    exact (R.verticalSparseEdgePath y.1.row y.1.col (by
      rw [hback.2.1]
      exact x.1.row.2)).reverse

/-- In the forward orientation, the explicit vertical adjacency selector is the
corresponding bridge path. -/
theorem verticalAdjPath_eq_forward
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hforward :
      x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false) :
    R.verticalAdjPath hxy =
      R.verticalSparseEdgePath x.1.row x.1.col (by
        rw [hforward.2.1]
        exact y.1.row.2) := by
  unfold verticalAdjPath
  simp [hforward]

/-- In the backward orientation, the explicit vertical adjacency selector is the
reverse of the corresponding bridge path. -/
theorem verticalAdjPath_eq_backward
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hback :
      y.1.col = x.1.col ∧
        y.1.row.1 + 1 = x.1.row.1 ∧
          y.1.port = true ∧ x.1.port = false) :
    R.verticalAdjPath hxy =
      (R.verticalSparseEdgePath y.1.row y.1.col (by
        rw [hback.2.1]
        exact x.1.row.2)).reverse := by
  unfold verticalAdjPath
  have hnot :
      ¬ (x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false) := by
    intro hforward
    have htrue : x.1.port = true := hforward.2.2.1
    have hfalse : x.1.port = false := hback.2.2.2
    simp [hfalse] at htrue
  simp [hnot]

/-- The explicit vertical adjacency path starts at the image of the first
sparse-grid endpoint. -/
theorem verticalAdjPath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    (R.verticalAdjPath hxy).source = R.validVertexImage hg x := by
  classical
  by_cases hforward :
      x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false
  · rw [R.verticalAdjPath_eq_forward hxy hforward]
    have hxlast := SparseGrid.ValidVertex.eq_last_of_port_true hg x hforward.2.2.1
    exact (R.verticalSparseEdgePath_source hg x.1.row x.1.col (by
      rw [hforward.2.1]
      exact y.1.row.2)).trans (by rw [← hxlast])
  · have hback :
        y.1.col = x.1.col ∧
          y.1.row.1 + 1 = x.1.row.1 ∧
            y.1.port = true ∧ x.1.port = false := by
      rcases hxy with ⟨hcol, hdir | hdir⟩
      · exact False.elim (hforward ⟨hcol, hdir.1, hdir.2.1, hdir.2.2⟩)
      · exact ⟨hcol.symm, hdir.1, hdir.2.1, hdir.2.2⟩
    rw [R.verticalAdjPath_eq_backward hxy hback]
    have hxfirst := SparseGrid.ValidVertex.eq_first_of_port_false hg x hback.2.2.2
    have hxrow :
        (⟨y.1.row.1 + 1, by
          rw [hback.2.1]
          exact x.1.row.2⟩ : Fin g) = x.1.row :=
      Fin.ext hback.2.1
    calc
      ((R.verticalSparseEdgePath y.1.row y.1.col (by
          rw [hback.2.1]
          exact x.1.row.2)).reverse).source =
          (R.verticalSparseEdgePath y.1.row y.1.col (by
            rw [hback.2.1]
            exact x.1.row.2)).target := rfl
      _ = R.validVertexImage hg
            (SparseGrid.ValidVertex.first
              (⟨y.1.row.1 + 1, by
                rw [hback.2.1]
                exact x.1.row.2⟩ : Fin g) y.1.col) := by
        exact R.verticalSparseEdgePath_target hg y.1.row y.1.col (by
          rw [hback.2.1]
          exact x.1.row.2)
      _ = R.validVertexImage hg
            (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
        rw [hxrow, hback.1]
      _ = R.validVertexImage hg x := by
        rw [← hxfirst]

/-- The explicit vertical adjacency path ends at the image of the second
sparse-grid endpoint. -/
theorem verticalAdjPath_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    (R.verticalAdjPath hxy).target = R.validVertexImage hg y := by
  classical
  by_cases hforward :
      x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false
  · rw [R.verticalAdjPath_eq_forward hxy hforward]
    have hyfirst := SparseGrid.ValidVertex.eq_first_of_port_false hg y hforward.2.2.2
    have hyrow :
        (⟨x.1.row.1 + 1, by
          rw [hforward.2.1]
          exact y.1.row.2⟩ : Fin g) = y.1.row :=
      Fin.ext hforward.2.1
    calc
      (R.verticalSparseEdgePath x.1.row x.1.col (by
          rw [hforward.2.1]
          exact y.1.row.2)).target =
          R.validVertexImage hg
            (SparseGrid.ValidVertex.first
              (⟨x.1.row.1 + 1, by
                rw [hforward.2.1]
                exact y.1.row.2⟩ : Fin g) x.1.col) := by
        exact R.verticalSparseEdgePath_target hg x.1.row x.1.col (by
          rw [hforward.2.1]
          exact y.1.row.2)
      _ = R.validVertexImage hg
            (SparseGrid.ValidVertex.first y.1.row y.1.col) := by
        rw [hyrow, hforward.1]
      _ = R.validVertexImage hg y := by
        rw [← hyfirst]
  · have hback :
        y.1.col = x.1.col ∧
          y.1.row.1 + 1 = x.1.row.1 ∧
            y.1.port = true ∧ x.1.port = false := by
      rcases hxy with ⟨hcol, hdir | hdir⟩
      · exact False.elim (hforward ⟨hcol, hdir.1, hdir.2.1, hdir.2.2⟩)
      · exact ⟨hcol.symm, hdir.1, hdir.2.1, hdir.2.2⟩
    rw [R.verticalAdjPath_eq_backward hxy hback]
    have hylast := SparseGrid.ValidVertex.eq_last_of_port_true hg y hback.2.2.1
    calc
      ((R.verticalSparseEdgePath y.1.row y.1.col (by
          rw [hback.2.1]
          exact x.1.row.2)).reverse).target =
          (R.verticalSparseEdgePath y.1.row y.1.col (by
            rw [hback.2.1]
            exact x.1.row.2)).source := rfl
      _ = R.validVertexImage hg
            (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
        exact R.verticalSparseEdgePath_source hg y.1.row y.1.col (by
          rw [hback.2.1]
          exact x.1.row.2)
      _ = R.validVertexImage hg y := by
        rw [← hylast]

/-- The explicit vertical adjacency path is internally disjoint from the row
packing, in either sparse-grid orientation. -/
theorem verticalAdjPath_internallyDisjoint_rows
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    (R.verticalAdjPath hxy).InternallyDisjointFromSet R.rows.vertexSet := by
  classical
  by_cases hforward :
      x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false
  · rw [R.verticalAdjPath_eq_forward hxy hforward]
    exact R.verticalSparseEdgePath_internallyDisjoint_rows x.1.row x.1.col (by
      rw [hforward.2.1]
      exact y.1.row.2)
  · have hback :
        y.1.col = x.1.col ∧
          y.1.row.1 + 1 = x.1.row.1 ∧
            y.1.port = true ∧ x.1.port = false := by
      rcases hxy with ⟨hcol, hdir | hdir⟩
      · exact False.elim (hforward ⟨hcol, hdir.1, hdir.2.1, hdir.2.2⟩)
      · exact ⟨hcol.symm, hdir.1, hdir.2.1, hdir.2.2⟩
    rw [R.verticalAdjPath_eq_backward hxy hback]
    exact (GraphPath.reverse_internallyDisjointFromSet
      (R.verticalSparseEdgePath y.1.row y.1.col (by
        rw [hback.2.1]
        exact x.1.row.2)) R.rows.vertexSet).2
      (R.verticalSparseEdgePath_internallyDisjoint_rows y.1.row y.1.col (by
        rw [hback.2.1]
        exact x.1.row.2))

/-- The explicit vertical adjacency path stays inside the incident even cluster
of its source endpoint. -/
theorem verticalAdjPath_vertexSet_subset_incidentCluster
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    (R.verticalAdjPath hxy).vertexSet ⊆
      P.cluster (evenClusterIndex g (validVertexIncidentIndex hg x)) := by
  classical
  by_cases hforward :
      x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false
  · rw [R.verticalAdjPath_eq_forward hxy hforward]
    simpa [validVertexIncidentIndex, hforward.2.2.1] using
      R.verticalSparseEdgePath_vertexSet_subset_cluster x.1.row x.1.col (by
        rw [hforward.2.1]
        exact y.1.row.2)
  · have hback :
        y.1.col = x.1.col ∧
          y.1.row.1 + 1 = x.1.row.1 ∧
            y.1.port = true ∧ x.1.port = false := by
      rcases hxy with ⟨hcol, hdir | hdir⟩
      · exact False.elim (hforward ⟨hcol, hdir.1, hdir.2.1, hdir.2.2⟩)
      · exact ⟨hcol.symm, hdir.1, hdir.2.1, hdir.2.2⟩
    rw [R.verticalAdjPath_eq_backward hxy hback]
    have hxnot : ¬ x.1.port = true := by
      intro htrue
      simp [hback.2.2.2] at htrue
    have hr : y.1.row.1 + 1 < g := by
      rw [hback.2.1]
      exact x.1.row.2
    have hgap :
        gapAbove x.1.row
            (SparseGrid.row_pos_of_valid_false hg x.2 hback.2.2.2) =
          gapBelow y.1.row hr := by
      ext
      simp [gapAbove, gapBelow]
      omega
    have hidx :
        validVertexIncidentIndex hg x =
          verticalEdgeIndex g y.1.col (gapBelow y.1.row hr) := by
      simp [validVertexIncidentIndex, hxnot, hback.1, hgap]
    rw [hidx]
    simpa using R.verticalSparseEdgePath_vertexSet_subset_cluster y.1.row y.1.col hr

/-- The allocated drop-last part of a vertical adjacency path stays inside the
source endpoint's incident even cluster. -/
theorem verticalAdjPath_dropLast_subset_incidentCluster
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    (R.verticalAdjPath hxy).dropLast.vertexSet ⊆
      P.cluster (evenClusterIndex g (validVertexIncidentIndex hg x)) := by
  intro v hv
  exact R.verticalAdjPath_vertexSet_subset_incidentCluster hg hxy
    ((R.verticalAdjPath hxy).dropLast_vertexSet_subset hv)

/-- A vertical adjacency path has distinct endpoints under the stitched-row
embedding. -/
theorem verticalAdjPath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    (R.verticalAdjPath hxy).source ≠ (R.verticalAdjPath hxy).target := by
  intro h
  have himage : R.validVertexImage hg x = R.validVertexImage hg y := by
    rw [← R.verticalAdjPath_source hg hxy, ← R.verticalAdjPath_target hg hxy]
    exact h
  exact (SparseGrid.validGraph g).ne_of_adj (Or.inr hxy)
    (R.validVertexImage_injective hg himage)

/-- The target endpoint of a vertical adjacency path is not in its allocated
drop-last part. -/
theorem verticalAdjPath_target_not_mem_dropLast
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    R.validVertexImage hg y ∉ (R.verticalAdjPath hxy).dropLast.vertexSet := by
  have hnot :=
    (R.verticalAdjPath hxy).target_not_mem_dropLast_vertexSet
      (R.verticalAdjPath_source_ne_target hg hxy)
  simpa [R.verticalAdjPath_target hg hxy] using hnot

/-- If a vertical adjacency path meets a stitched row, that row vertex is an
endpoint of the vertical path. -/
theorem verticalAdjPath_isEndpoint_of_mem_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    {a : R.rows.Index} {v : V}
    (hvPath : v ∈ (R.verticalAdjPath hxy).vertexSet)
    (hvRow : v ∈ (R.rows.path a).vertexSet) :
    (R.verticalAdjPath hxy).IsEndpoint v :=
  R.verticalAdjPath_internallyDisjoint_rows hxy hvPath
    (R.rows.path_vertexSet_subset_vertexSet a hvRow)

/-- The drop-last part of a vertical adjacency path can meet a stitched row
only at its source endpoint. -/
theorem verticalAdjPath_dropLast_mem_row_eq_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    {a : R.rows.Index} {v : V}
    (hvPath : v ∈ (R.verticalAdjPath hxy).dropLast.vertexSet)
    (hvRow : v ∈ (R.rows.path a).vertexSet) :
    v = R.validVertexImage hg x := by
  have hvFull :
      v ∈ (R.verticalAdjPath hxy).vertexSet :=
    (R.verticalAdjPath hxy).dropLast_vertexSet_subset hvPath
  have hendpoint :=
    R.verticalAdjPath_isEndpoint_of_mem_row hxy hvFull hvRow
  rcases hendpoint with hsource | htarget
  · rw [hsource, R.verticalAdjPath_source hg hxy]
  · have hne := R.verticalAdjPath_source_ne_target hg hxy
    have hnot :=
      (R.verticalAdjPath hxy).target_not_mem_dropLast_vertexSet hne
    exact False.elim (hnot (by simpa [htarget] using hvPath))

/-- No endpoint image other than the source image lies in the allocated
drop-last part of a vertical adjacency path. -/
theorem validVertexImage_not_mem_verticalAdjPath_dropLast_of_ne_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hzx : z ≠ x) :
    R.validVertexImage hg z ∉ (R.verticalAdjPath hxy).dropLast.vertexSet := by
  intro hzmem
  have himage :
      R.validVertexImage hg z = R.validVertexImage hg x :=
    R.verticalAdjPath_dropLast_mem_row_eq_source hg hxy hzmem
      (R.validVertexImage_mem_row hg z)
  exact hzx (R.validVertexImage_injective hg himage)

/-- Explicit path realizing a horizontal sparse-grid adjacency.

Same-block adjacencies use the internal row segment between the two relevant
ports.  Successor-column adjacencies use the row segment crossing the
corresponding even cluster, specialized to the top, bottom, or internal row
case. -/
noncomputable def horizontalAdjPath
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    GraphPath G := by
  classical
  by_cases hsameForward :
      x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
        x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
          y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
            x.1.port ≠ y.1.port
  · have hfl_ne :
        SparseGrid.Vertex.firstPort x.1.row ≠
          SparseGrid.Vertex.lastPort x.1.row := by
      intro heq
      exact hsameForward.2.2.2.2
        (hsameForward.2.2.1.trans (heq.trans hsameForward.2.2.2.1.symm))
    exact R.horizontalInternalEdgePath x.1.row x.1.col
      ((SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 hfl_ne).1
      ((SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 hfl_ne).2
  · by_cases hsameBackward :
        x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          y.1.port = SparseGrid.Vertex.firstPort y.1.row ∧
            x.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
              y.1.port ≠ x.1.port
    · have hfl_ne :
          SparseGrid.Vertex.firstPort y.1.row ≠
            SparseGrid.Vertex.lastPort y.1.row := by
        intro heq
        exact hsameBackward.2.2.2.2
          (hsameBackward.2.2.1.trans (heq.trans hsameBackward.2.2.2.1.symm))
      exact (R.horizontalInternalEdgePath y.1.row y.1.col
        ((SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne).1
        ((SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne).2).reverse
    · by_cases hnextForward :
          x.1.row = y.1.row ∧
            x.1.col.1 + 1 = y.1.col.1 ∧
              x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
                y.1.port = SparseGrid.Vertex.firstPort y.1.row
      · have hcd : x.1.col.1 < y.1.col.1 := by omega
        by_cases hTop : x.1.row.1 = 0
        · exact R.horizontalTopEdgePath hcd x.1.row hTop
        · by_cases hBottom : x.1.row.1 + 1 = g
          · exact R.horizontalBottomEdgePath hcd x.1.row hBottom
          · exact R.horizontalMiddleEdgePath hcd x.1.row (by omega) (by omega)
      · have hnextBackward :
            x.1.row = y.1.row ∧
              y.1.col.1 + 1 = x.1.col.1 ∧
                y.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
                  x.1.port = SparseGrid.Vertex.firstPort x.1.row := by
          rcases hxy with hsame | hnext
          · rcases hsame with ⟨hrow, hcol, hports | hports⟩
            · exact False.elim
                (hsameForward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
            · exact False.elim
                (hsameBackward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
          · rcases hnext with ⟨hrow, hdir | hdir⟩
            · exact False.elim
                (hnextForward ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩)
            · exact ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩
        have hcd : y.1.col.1 < x.1.col.1 := by omega
        by_cases hTop : y.1.row.1 = 0
        · exact (R.horizontalTopEdgePath hcd y.1.row hTop).reverse
        · by_cases hBottom : y.1.row.1 + 1 = g
          · exact (R.horizontalBottomEdgePath hcd y.1.row hBottom).reverse
          · exact (R.horizontalMiddleEdgePath hcd y.1.row (by omega) (by omega)).reverse

/-
/-- The explicit horizontal adjacency path starts at the image of the first
sparse-grid endpoint. -/
theorem horizontalAdjPath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).source = R.validVertexImage hg x := by
  classical
  by_cases hsameForward :
      x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
        x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
          y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
            x.1.port ≠ y.1.port
  · have hfl_ne :
        SparseGrid.Vertex.firstPort x.1.row ≠
          SparseGrid.Vertex.lastPort x.1.row := by
      intro heq
      exact hsameForward.2.2.2.2
        (hsameForward.2.2.1.trans (heq.trans hsameForward.2.2.2.1.symm))
    let hInternal :=
      (SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 hfl_ne
    have hpath :
        R.horizontalAdjPath hg hxy =
          R.horizontalInternalEdgePath x.1.row x.1.col
            hInternal.1 hInternal.2 := by
      unfold horizontalAdjPath
      simp [hsameForward, hfl_ne, hInternal]
    rw [hpath]
    have hxfirst :=
      SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x
        hsameForward.2.2.1
    calc
      (R.horizontalInternalEdgePath x.1.row x.1.col hInternal.1 hInternal.2).source =
          R.validVertexImage hg
            (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
        exact R.horizontalInternalEdgePath_source hg x.1.row x.1.col
          hInternal.1 hInternal.2
      _ = R.validVertexImage hg x := by
        rw [← hxfirst]
  · by_cases hsameBackward :
        x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          y.1.port = SparseGrid.Vertex.firstPort y.1.row ∧
            x.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
              y.1.port ≠ x.1.port
    · have hfl_ne :
          SparseGrid.Vertex.firstPort y.1.row ≠
            SparseGrid.Vertex.lastPort y.1.row := by
        intro heq
        exact hsameBackward.2.2.2.2
          (hsameBackward.2.2.1.trans (heq.trans hsameBackward.2.2.2.1.symm))
      let hInternal :=
        (SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne
      have hpath :
          R.horizontalAdjPath hg hxy =
            (R.horizontalInternalEdgePath y.1.row y.1.col
              hInternal.1 hInternal.2).reverse := by
        unfold horizontalAdjPath
        simp [hsameForward, hsameBackward, hfl_ne, hInternal]
      rw [hpath]
      have hxlast' :
          x.1.port = SparseGrid.Vertex.lastPort x.1.row := by
        rw [hsameBackward.1]
        exact hsameBackward.2.2.2.1
      have hxlast :=
        SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x hxlast'
      calc
        ((R.horizontalInternalEdgePath y.1.row y.1.col
            hInternal.1 hInternal.2).reverse).source =
            (R.horizontalInternalEdgePath y.1.row y.1.col
              hInternal.1 hInternal.2).target := rfl
        _ = R.validVertexImage hg
              (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
          exact R.horizontalInternalEdgePath_target hg y.1.row y.1.col
            hInternal.1 hInternal.2
        _ = R.validVertexImage hg
              (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
          rw [← hsameBackward.1, ← hsameBackward.2.1]
        _ = R.validVertexImage hg x := by
          rw [← hxlast]
    · by_cases hnextForward :
          x.1.row = y.1.row ∧
            x.1.col.1 + 1 = y.1.col.1 ∧
              x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
                y.1.port = SparseGrid.Vertex.firstPort y.1.row
      · have hcd : x.1.col.1 < y.1.col.1 := by omega
        have hxlast :=
          SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x
            hnextForward.2.2.1
        by_cases hTop : x.1.row.1 = 0
        · have hpath :
              R.horizontalAdjPath hg hxy =
                R.horizontalTopEdgePath hcd x.1.row hTop := by
            unfold horizontalAdjPath
            simp [hsameForward, hsameBackward, hnextForward, hTop]
          rw [hpath]
          calc
            (R.horizontalTopEdgePath hcd x.1.row hTop).source =
                R.validVertexImage hg
                  (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
              exact R.horizontalTopEdgePath_source hg hcd x.1.row hTop
            _ = R.validVertexImage hg x := by
              rw [← hxlast]
        · by_cases hBottom : x.1.row.1 + 1 = g
          · have hpath :
                R.horizontalAdjPath hg hxy =
                  R.horizontalBottomEdgePath hcd x.1.row hBottom := by
              unfold horizontalAdjPath
              simp [hsameForward, hsameBackward, hnextForward, hTop, hBottom]
            rw [hpath]
            calc
              (R.horizontalBottomEdgePath hcd x.1.row hBottom).source =
                  R.validVertexImage hg
                    (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
                exact R.horizontalBottomEdgePath_source hg hcd x.1.row hBottom
              _ = R.validVertexImage hg x := by
                rw [← hxlast]
          · have hTopPos : 0 < x.1.row.1 := by omega
            have hBottomLt : x.1.row.1 + 1 < g := by omega
            have hpath :
                R.horizontalAdjPath hg hxy =
                  R.horizontalMiddleEdgePath hcd x.1.row hTopPos hBottomLt := by
              unfold horizontalAdjPath
              simp [hsameForward, hsameBackward, hnextForward, hTop, hBottom]
            rw [hpath]
            calc
              (R.horizontalMiddleEdgePath hcd x.1.row hTopPos hBottomLt).source =
                  R.validVertexImage hg
                    (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
                exact R.horizontalMiddleEdgePath_source hg hcd x.1.row hTopPos
                  hBottomLt
              _ = R.validVertexImage hg x := by
                rw [← hxlast]
      · have hnextBackward :
            x.1.row = y.1.row ∧
              y.1.col.1 + 1 = x.1.col.1 ∧
                y.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
                  x.1.port = SparseGrid.Vertex.firstPort x.1.row := by
          rcases hxy with hsame | hnext
          · rcases hsame with ⟨hrow, hcol, hports | hports⟩
            · exact False.elim
                (hsameForward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
            · exact False.elim
                (hsameBackward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
          · rcases hnext with ⟨hrow, hdir | hdir⟩
            · exact False.elim
                (hnextForward ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩)
            · exact ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩
        have hcd : y.1.col.1 < x.1.col.1 := by omega
        have hxfirst :=
          SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x
            hnextBackward.2.2.2
        by_cases hTop : y.1.row.1 = 0
        · have hpath :
              R.horizontalAdjPath hg hxy =
                (R.horizontalTopEdgePath hcd y.1.row hTop).reverse := by
            unfold horizontalAdjPath
            simp [hsameForward, hsameBackward, hnextForward, hTop]
          rw [hpath]
          calc
            ((R.horizontalTopEdgePath hcd y.1.row hTop).reverse).source =
                (R.horizontalTopEdgePath hcd y.1.row hTop).target := rfl
            _ = R.validVertexImage hg
                  (SparseGrid.ValidVertex.first y.1.row x.1.col) := by
              exact R.horizontalTopEdgePath_target hg hcd y.1.row hTop
            _ = R.validVertexImage hg
                  (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
              rw [← hnextBackward.1]
            _ = R.validVertexImage hg x := by
              rw [← hxfirst]
        · by_cases hBottom : y.1.row.1 + 1 = g
          · have hpath :
                R.horizontalAdjPath hg hxy =
                  (R.horizontalBottomEdgePath hcd y.1.row hBottom).reverse := by
              unfold horizontalAdjPath
              simp [hsameForward, hsameBackward, hnextForward, hTop, hBottom]
            rw [hpath]
            calc
              ((R.horizontalBottomEdgePath hcd y.1.row hBottom).reverse).source =
                  (R.horizontalBottomEdgePath hcd y.1.row hBottom).target := rfl
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first y.1.row x.1.col) := by
                exact R.horizontalBottomEdgePath_target hg hcd y.1.row hBottom
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
                rw [← hnextBackward.1]
              _ = R.validVertexImage hg x := by
                rw [← hxfirst]
          · have hTopPos : 0 < y.1.row.1 := by omega
            have hBottomLt : y.1.row.1 + 1 < g := by omega
            have hpath :
                R.horizontalAdjPath hg hxy =
                  (R.horizontalMiddleEdgePath hcd y.1.row hTopPos
                    hBottomLt).reverse := by
              unfold horizontalAdjPath
              simp [hsameForward, hsameBackward, hnextForward, hTop, hBottom]
            rw [hpath]
            calc
              ((R.horizontalMiddleEdgePath hcd y.1.row hTopPos
                  hBottomLt).reverse).source =
                  (R.horizontalMiddleEdgePath hcd y.1.row hTopPos
                    hBottomLt).target := rfl
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first y.1.row x.1.col) := by
                exact R.horizontalMiddleEdgePath_target hg hcd y.1.row hTopPos
                  hBottomLt
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
                rw [← hnextBackward.1]
              _ = R.validVertexImage hg x := by
                rw [← hxfirst]

-/

/-- The explicit horizontal adjacency path starts at the image of the first
sparse-grid endpoint. -/
theorem horizontalAdjPath_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).source = R.validVertexImage hg x := by
  classical
  by_cases hsameForward :
      x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
        x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
          y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
            x.1.port ≠ y.1.port
  · have hxfirst :=
      SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x
        hsameForward.2.2.1
    unfold horizontalAdjPath
    rw [dif_pos hsameForward]
    rw [R.horizontalInternalEdgePath_source hg]
    rw [← hxfirst]
  · by_cases hsameBackward :
        x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          y.1.port = SparseGrid.Vertex.firstPort y.1.row ∧
            x.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
              y.1.port ≠ x.1.port
    · have hxlast' :
          x.1.port = SparseGrid.Vertex.lastPort x.1.row := by
        rw [hsameBackward.1]
        exact hsameBackward.2.2.2.1
      have hxlast :=
        SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x hxlast'
      have hfl_ne :
          SparseGrid.Vertex.firstPort y.1.row ≠
            SparseGrid.Vertex.lastPort y.1.row := by
        intro heq
        exact hsameBackward.2.2.2.2
          (hsameBackward.2.2.1.trans (heq.trans hsameBackward.2.2.2.1.symm))
      have hInternal :=
        (SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne
      unfold horizontalAdjPath
      rw [dif_neg hsameForward, dif_pos hsameBackward]
      change (R.horizontalInternalEdgePath y.1.row y.1.col
          hInternal.1 hInternal.2).target =
        R.validVertexImage hg x
      rw [R.horizontalInternalEdgePath_target hg y.1.row y.1.col
        hInternal.1 hInternal.2]
      rw [← hsameBackward.1, ← hsameBackward.2.1, ← hxlast]
    · by_cases hnextForward :
          x.1.row = y.1.row ∧
            x.1.col.1 + 1 = y.1.col.1 ∧
              x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
                y.1.port = SparseGrid.Vertex.firstPort y.1.row
      · have hxlast :=
          SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x
            hnextForward.2.2.1
        by_cases hTop : x.1.row.1 = 0
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
            dif_pos hTop]
          rw [R.horizontalTopEdgePath_source hg]
          rw [← hxlast]
        · by_cases hBottom : x.1.row.1 + 1 = g
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
              dif_neg hTop, dif_pos hBottom]
            rw [R.horizontalBottomEdgePath_source hg]
            rw [← hxlast]
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
              dif_neg hTop, dif_neg hBottom]
            rw [R.horizontalMiddleEdgePath_source hg]
            rw [← hxlast]
      · have hnextBackward :
            x.1.row = y.1.row ∧
              y.1.col.1 + 1 = x.1.col.1 ∧
                y.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
                  x.1.port = SparseGrid.Vertex.firstPort x.1.row := by
          rcases hxy with hsame | hnext
          · rcases hsame with ⟨hrow, hcol, hports | hports⟩
            · exact False.elim
                (hsameForward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
            · exact False.elim
                (hsameBackward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
          · rcases hnext with ⟨hrow, hdir | hdir⟩
            · exact False.elim
                (hnextForward ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩)
            · exact ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩
        have hxfirst :=
          SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x
            hnextBackward.2.2.2
        have hcd : y.1.col.1 < x.1.col.1 := by omega
        by_cases hTop : y.1.row.1 = 0
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
            dif_pos hTop]
          change (R.horizontalTopEdgePath hcd y.1.row hTop).target =
            R.validVertexImage hg x
          rw [R.horizontalTopEdgePath_target hg]
          rw [← hnextBackward.1, ← hxfirst]
        · by_cases hBottom : y.1.row.1 + 1 = g
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
              dif_neg hTop, dif_pos hBottom]
            change (R.horizontalBottomEdgePath hcd y.1.row hBottom).target =
              R.validVertexImage hg x
            rw [R.horizontalBottomEdgePath_target hg]
            rw [← hnextBackward.1, ← hxfirst]
          · unfold horizontalAdjPath
            have hTopPos : 0 < y.1.row.1 := by omega
            have hBottomLt : y.1.row.1 + 1 < g := by omega
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
              dif_neg hTop, dif_neg hBottom]
            change (R.horizontalMiddleEdgePath hcd y.1.row hTopPos
              hBottomLt).target = R.validVertexImage hg x
            rw [R.horizontalMiddleEdgePath_target hg hcd y.1.row hTopPos
              hBottomLt]
            rw [← hnextBackward.1, ← hxfirst]

/-- The explicit horizontal adjacency path ends at the image of the second
sparse-grid endpoint. -/
theorem horizontalAdjPath_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).target = R.validVertexImage hg y := by
  classical
  by_cases hsameForward :
      x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
        x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
          y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
            x.1.port ≠ y.1.port
  · have hylast' :
        y.1.port = SparseGrid.Vertex.lastPort y.1.row := by
      rw [← hsameForward.1]
      exact hsameForward.2.2.2.1
    have hylast :=
      SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y hylast'
    unfold horizontalAdjPath
    rw [dif_pos hsameForward]
    rw [R.horizontalInternalEdgePath_target hg]
    rw [hsameForward.1, hsameForward.2.1, ← hylast]
  · by_cases hsameBackward :
        x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          y.1.port = SparseGrid.Vertex.firstPort y.1.row ∧
            x.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
              y.1.port ≠ x.1.port
    · have hfl_ne :
          SparseGrid.Vertex.firstPort y.1.row ≠
            SparseGrid.Vertex.lastPort y.1.row := by
        intro heq
        exact hsameBackward.2.2.2.2
          (hsameBackward.2.2.1.trans (heq.trans hsameBackward.2.2.2.1.symm))
      have hInternal :=
        (SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne
      have hyfirst :=
        SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y
          hsameBackward.2.2.1
      unfold horizontalAdjPath
      rw [dif_neg hsameForward, dif_pos hsameBackward]
      change (R.horizontalInternalEdgePath y.1.row y.1.col
          hInternal.1 hInternal.2).source =
        R.validVertexImage hg y
      rw [R.horizontalInternalEdgePath_source hg y.1.row y.1.col
        hInternal.1 hInternal.2]
      rw [← hyfirst]
    · by_cases hnextForward :
          x.1.row = y.1.row ∧
            x.1.col.1 + 1 = y.1.col.1 ∧
              x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
                y.1.port = SparseGrid.Vertex.firstPort y.1.row
      · have hyfirst :=
          SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y
            hnextForward.2.2.2
        by_cases hTop : x.1.row.1 = 0
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
            dif_pos hTop]
          rw [R.horizontalTopEdgePath_target hg]
          rw [hnextForward.1, ← hyfirst]
        · by_cases hBottom : x.1.row.1 + 1 = g
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
              dif_neg hTop, dif_pos hBottom]
            rw [R.horizontalBottomEdgePath_target hg]
            rw [hnextForward.1, ← hyfirst]
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
              dif_neg hTop, dif_neg hBottom]
            rw [R.horizontalMiddleEdgePath_target hg]
            rw [hnextForward.1, ← hyfirst]
      · have hnextBackward :
            x.1.row = y.1.row ∧
              y.1.col.1 + 1 = x.1.col.1 ∧
                y.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
                  x.1.port = SparseGrid.Vertex.firstPort x.1.row := by
          rcases hxy with hsame | hnext
          · rcases hsame with ⟨hrow, hcol, hports | hports⟩
            · exact False.elim
                (hsameForward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
            · exact False.elim
                (hsameBackward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
          · rcases hnext with ⟨hrow, hdir | hdir⟩
            · exact False.elim
                (hnextForward ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩)
            · exact ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩
        have hylast :=
          SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y
            hnextBackward.2.2.1
        have hcd : y.1.col.1 < x.1.col.1 := by omega
        by_cases hTop : y.1.row.1 = 0
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
            dif_pos hTop]
          change (R.horizontalTopEdgePath hcd y.1.row hTop).source =
            R.validVertexImage hg y
          rw [R.horizontalTopEdgePath_source hg]
          rw [← hylast]
        · by_cases hBottom : y.1.row.1 + 1 = g
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
              dif_neg hTop, dif_pos hBottom]
            change (R.horizontalBottomEdgePath hcd y.1.row hBottom).source =
              R.validVertexImage hg y
            rw [R.horizontalBottomEdgePath_source hg]
            rw [← hylast]
          · unfold horizontalAdjPath
            have hTopPos : 0 < y.1.row.1 := by omega
            have hBottomLt : y.1.row.1 + 1 < g := by omega
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
              dif_neg hTop, dif_neg hBottom]
            change (R.horizontalMiddleEdgePath hcd y.1.row hTopPos
              hBottomLt).source = R.validVertexImage hg y
            rw [R.horizontalMiddleEdgePath_source hg hcd y.1.row hTopPos
              hBottomLt]
            rw [← hylast]

/-- A horizontal adjacency path has distinct endpoints under the stitched-row
embedding. -/
theorem horizontalAdjPath_source_ne_target
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).source ≠ (R.horizontalAdjPath hg hxy).target := by
  intro h
  have himage : R.validVertexImage hg x = R.validVertexImage hg y := by
    rw [← R.horizontalAdjPath_source hg hxy, ← R.horizontalAdjPath_target hg hxy]
    exact h
  exact (SparseGrid.validGraph g).ne_of_adj (Or.inl hxy)
    (R.validVertexImage_injective hg himage)

/-- A rank-oriented horizontal sparse-grid edge is exactly a certified segment
of the stitched row of its source endpoint.  The endpoints are exposed as raw
host vertices so the witness is the one stored by the concrete row segment
definition. -/
theorem exists_horizontalAdjPath_segment_of_validVertexRank_lt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hrank :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y) :
    ∃ (a b : V)
      (hbefore : (R.rows.path (R.row x.1.row)).Before a b),
        R.horizontalAdjPath hg hxy =
            (R.rows.path (R.row x.1.row)).segmentOfBefore hbefore ∧
          a = R.validVertexImage hg x ∧
            b = R.validVertexImage hg y := by
  classical
  rcases
    ValidSparseGridPathCertificate.horizontalAdj_forward_of_validVertexRank_lt
      hg hxy hrank with hsame | hnext
  · rcases hsame with ⟨hrow, hcol, hxfirstPort, hylastPort, hport_ne⟩
    have hfl_ne :
        SparseGrid.Vertex.firstPort x.1.row ≠
          SparseGrid.Vertex.lastPort x.1.row := by
      intro h
      exact hport_ne (hxfirstPort.trans (h.trans hylastPort.symm))
    let hInternal :=
      (SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 hfl_ne
    let a : V :=
      (R.verticalBridgePath x.1.col (gapAbove x.1.row hInternal.1)).target
    let b : V :=
      (R.verticalBridgePath x.1.col (gapBelow x.1.row hInternal.2)).source
    let hbefore :
        (R.rows.path (R.row x.1.row)).Before a b :=
      R.verticalBridgePath_target_before_source_same_col x.1.col x.1.row
        hInternal.1 hInternal.2
    refine ⟨a, b, hbefore, ?_, ?_, ?_⟩
    · unfold horizontalAdjPath
      rw [dif_pos ⟨hrow, hcol, hxfirstPort, hylastPort, hport_ne⟩]
      rfl
    · have hxfirst :=
        SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x hxfirstPort
      dsimp [a]
      rw [← R.validVertexImage_first_of_not_top hg x.1.row x.1.col
        hInternal.1, ← hxfirst]
    · have hylastPort' :
          y.1.port = SparseGrid.Vertex.lastPort y.1.row := by
        rw [← hrow]
        exact hylastPort
      have hylast :=
        SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y hylastPort'
      dsimp [b]
      rw [← R.validVertexImage_last_of_not_bottom hg x.1.row x.1.col
        hInternal.2, hrow, hcol, ← hylast]
  · rcases hnext with ⟨hrow, hsucc, hxlastPort, hyfirstPort⟩
    have hcd : x.1.col.1 < y.1.col.1 := by omega
    have hsameForward_not :
        ¬ (x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
            y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
              x.1.port ≠ y.1.port) := by
      intro h
      have hcolVal := congrArg Fin.val h.2.1
      omega
    have hsameBackward_not :
        ¬ (x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          y.1.port = SparseGrid.Vertex.firstPort y.1.row ∧
            x.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
              y.1.port ≠ x.1.port) := by
      intro h
      have hcolVal := congrArg Fin.val h.2.1
      omega
    have hnextForward :
        x.1.row = y.1.row ∧
          x.1.col.1 + 1 = y.1.col.1 ∧
            x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
              y.1.port = SparseGrid.Vertex.firstPort y.1.row :=
      ⟨hrow, hsucc, hxlastPort, hyfirstPort⟩
    have hxlast :=
      SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x hxlastPort
    have hyfirst :=
      SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y hyfirstPort
    by_cases hTop : x.1.row.1 = 0
    · let hBottom : x.1.row.1 + 1 < g := by omega
      let a : V :=
        (R.verticalBridgePath x.1.col (gapBelow x.1.row hBottom)).source
      let b : V :=
        (R.verticalBridgePath y.1.col (gapBelow x.1.row hBottom)).source
      let hbefore :
          (R.rows.path (R.row x.1.row)).Before a b :=
        R.verticalBridgePath_source_before_of_col_lt hcd
          (gapBelow x.1.row hBottom)
      refine ⟨a, b, hbefore, ?_, ?_, ?_⟩
      · unfold horizontalAdjPath
        rw [dif_neg hsameForward_not, dif_neg hsameBackward_not,
          dif_pos hnextForward, dif_pos hTop]
        rfl
      · dsimp [a]
        rw [← R.validVertexImage_last_of_not_bottom hg x.1.row x.1.col
          hBottom, ← hxlast]
      · dsimp [b]
        rw [← R.validVertexImage_first_of_top hg x.1.row y.1.col hTop,
          hrow, ← hyfirst]
    · by_cases hBottomEq : x.1.row.1 + 1 = g
      · let hTopPos : 0 < x.1.row.1 := by omega
        let a : V :=
          (R.verticalBridgePath x.1.col (gapAbove x.1.row hTopPos)).target
        let b : V :=
          (R.verticalBridgePath y.1.col (gapAbove x.1.row hTopPos)).target
        let hbefore :
            (R.rows.path (R.row x.1.row)).Before a b :=
          by
            simpa [a, b, upperRow_gapAbove] using
              R.verticalBridgePath_target_before_of_col_lt hcd
                (gapAbove x.1.row hTopPos)
        refine ⟨a, b, hbefore, ?_, ?_, ?_⟩
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward_not, dif_neg hsameBackward_not,
            dif_pos hnextForward, dif_neg hTop, dif_pos hBottomEq]
          simp [horizontalBottomEdgePath, targetSegmentOfColLt, upperRow_gapAbove]
        · dsimp [a]
          rw [← R.validVertexImage_last_of_bottom hg x.1.row x.1.col
            hBottomEq, ← hxlast]
        · dsimp [b]
          rw [← R.validVertexImage_first_of_not_top hg x.1.row y.1.col
            hTopPos, hrow, ← hyfirst]
      · let hTopPos : 0 < x.1.row.1 := by omega
        let hBottom : x.1.row.1 + 1 < g := by omega
        let a : V :=
          (R.verticalBridgePath x.1.col (gapBelow x.1.row hBottom)).source
        let b : V :=
          (R.verticalBridgePath y.1.col (gapAbove x.1.row hTopPos)).target
        let hbefore :
            (R.rows.path (R.row x.1.row)).Before a b :=
          R.verticalBridgePath_source_before_target_next_col hcd x.1.row
            hTopPos hBottom
        refine ⟨a, b, hbefore, ?_, ?_, ?_⟩
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward_not, dif_neg hsameBackward_not,
            dif_pos hnextForward, dif_neg hTop, dif_neg hBottomEq]
          rfl
        · dsimp [a]
          rw [← R.validVertexImage_last_of_not_bottom hg x.1.row x.1.col
            hBottom, ← hxlast]
        · dsimp [b]
          rw [← R.validVertexImage_first_of_not_top hg x.1.row y.1.col
            hTopPos, hrow, ← hyfirst]

/-- If `z` is a later valid port on the same row than the source of a
rank-oriented horizontal edge `x--y`, then the target image of that edge occurs
before the image of `z` on the stitched row.  Equality `y = z` is handled by
reflexivity of the path order. -/
theorem horizontalAdj_target_before_of_source_validVertexRank_lt
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hrankxy :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hrowzx : z.1.row = x.1.row)
    (hrankxz :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank z) :
    (R.rows.path (R.row x.1.row)).Before
      (R.validVertexImage hg y) (R.validVertexImage hg z) := by
  classical
  by_cases hyz : y = z
  · have hzmem :
        R.validVertexImage hg z ∈
          (R.rows.path (R.row x.1.row)).vertexSet := by
      simpa [hrowzx] using R.validVertexImage_mem_row hg z
    simpa [hyz] using
      (R.rows.path (R.row x.1.row)).before_refl hzmem
  have hidxxz :
      (validVertexIncidentIndex hg x).1 <
        (validVertexIncidentIndex hg z).1 :=
    validVertexIncidentIndex_lt_of_same_row_validVertexRank_lt hg
      hrowzx.symm hrankxz
  have hrowxy : x.1.row = y.1.row :=
    SparseGrid.row_eq_of_horizontalAdj hxy
  have hrowyz : y.1.row = z.1.row := by
    exact hrowxy.symm.trans hrowzx.symm
  rcases
    ValidSparseGridPathCertificate.horizontalAdj_forward_of_validVertexRank_lt
      hg hxy hrankxy with hsame | hnext
  · rcases hsame with ⟨_hrow, hcol, hxfirstPort, hylastPort, hport_ne⟩
    have hfl_ne :
        SparseGrid.Vertex.firstPort x.1.row ≠
          SparseGrid.Vertex.lastPort x.1.row := by
      intro h
      exact hport_ne (hxfirstPort.trans (h.trans hylastPort.symm))
    let hInternal :=
      (SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 hfl_ne
    have hxfirst :=
      SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x hxfirstPort
    have hylastPort' :
        y.1.port = SparseGrid.Vertex.lastPort y.1.row := by
      rw [← hrowxy]
      exact hylastPort
    have hylast :=
      SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y hylastPort'
    have hzx : z ≠ x := by
      intro h
      subst z
      omega
    have hzfirst : z ≠ SparseGrid.ValidVertex.first x.1.row x.1.col := by
      intro hz
      exact hzx (by rw [hxfirst, hz])
    have hzlast : z ≠ SparseGrid.ValidVertex.last x.1.row x.1.col := by
      intro hz
      exact hyz (hylast.trans (by simp [hz, hrowxy, hcol]))
    have hout :=
      validVertexIncidentIndex_outside_internal_of_ne hg x.1.row x.1.col
        hInternal.1 hInternal.2 hrowzx hzfirst hzlast
    rcases hout with hbefore | hafter
    · have hidxzx :
          (validVertexIncidentIndex hg z).1 <
            (validVertexIncidentIndex hg x).1 := by
        rw [hxfirst]
        exact hbefore
      omega
    · have hidxyz :
          (validVertexIncidentIndex hg y).1 <
            (validVertexIncidentIndex hg z).1 := by
        rw [hylast]
        rw [← hrowxy, ← hcol]
        exact hafter
      have hbefore :=
        R.validVertexImage_before_of_incidentIndex_lt hg hrowyz hidxyz
      simpa [hrowxy] using hbefore
  · rcases hnext with ⟨_hrow, hsucc, hxlastPort, hyfirstPort⟩
    have hxlast :=
      SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x hxlastPort
    have hyfirst :=
      SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y hyfirstPort
    have hzx : z ≠ x := by
      intro h
      subst z
      omega
    have hzlast : z ≠ SparseGrid.ValidVertex.last x.1.row x.1.col := by
      intro hz
      exact hzx (by rw [hxlast, hz])
    have hzfirst : z ≠ SparseGrid.ValidVertex.first x.1.row y.1.col := by
      intro hz
      exact hyz (hyfirst.trans (by simp [hz, hrowxy]))
    have hout :=
      validVertexIncidentIndex_outside_next_col_of_ne hg x.1.row x.1.col
        y.1.col hsucc hrowzx hzlast hzfirst
    rcases hout with hbefore | hafter
    · have hidxzx :
          (validVertexIncidentIndex hg z).1 <
            (validVertexIncidentIndex hg x).1 := by
        rw [hxlast]
        exact hbefore
      omega
    · have hidxyz :
          (validVertexIncidentIndex hg y).1 <
            (validVertexIncidentIndex hg z).1 := by
        rw [hyfirst]
        rw [← hrowxy]
        exact hafter
      have hbefore :=
        R.validVertexImage_before_of_incidentIndex_lt hg hrowyz hidxyz
      simpa [hrowxy] using hbefore

/-- The target endpoint of a horizontal adjacency path is not in its allocated
drop-last part. -/
theorem horizontalAdjPath_target_not_mem_dropLast
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    R.validVertexImage hg y ∉ (R.horizontalAdjPath hg hxy).dropLast.vertexSet := by
  have hnot :=
    (R.horizontalAdjPath hg hxy).target_not_mem_dropLast_vertexSet
      (R.horizontalAdjPath_source_ne_target hg hxy)
  simpa [R.horizontalAdjPath_target hg hxy] using hnot

/-- Every explicit horizontal sparse-grid edge path is contained in the stitched
row of its first endpoint. -/
theorem horizontalAdjPath_vertexSet_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).vertexSet ⊆
      (R.rows.path (R.row x.1.row)).vertexSet := by
  classical
  by_cases hsameForward :
      x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
        x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
          y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
            x.1.port ≠ y.1.port
  · unfold horizontalAdjPath
    rw [dif_pos hsameForward]
    exact R.horizontalInternalEdgePath_vertexSet_subset_row x.1.row x.1.col
      ((SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 (by
        intro heq
        exact hsameForward.2.2.2.2
          (hsameForward.2.2.1.trans (heq.trans hsameForward.2.2.2.1.symm)))).1
      ((SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 (by
        intro heq
        exact hsameForward.2.2.2.2
          (hsameForward.2.2.1.trans (heq.trans hsameForward.2.2.2.1.symm)))).2
  · by_cases hsameBackward :
        x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          y.1.port = SparseGrid.Vertex.firstPort y.1.row ∧
            x.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
              y.1.port ≠ x.1.port
    · have hfl_ne :
          SparseGrid.Vertex.firstPort y.1.row ≠
            SparseGrid.Vertex.lastPort y.1.row := by
        intro heq
        exact hsameBackward.2.2.2.2
          (hsameBackward.2.2.1.trans (heq.trans hsameBackward.2.2.2.1.symm))
      have hInternal :=
        (SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne
      unfold horizontalAdjPath
      rw [dif_neg hsameForward, dif_pos hsameBackward]
      simpa [hsameBackward.1] using
        R.horizontalInternalEdgePath_vertexSet_subset_row y.1.row y.1.col
          hInternal.1 hInternal.2
    · by_cases hnextForward :
          x.1.row = y.1.row ∧
            x.1.col.1 + 1 = y.1.col.1 ∧
              x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
                y.1.port = SparseGrid.Vertex.firstPort y.1.row
      · have hcd : x.1.col.1 < y.1.col.1 := by omega
        by_cases hTop : x.1.row.1 = 0
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
            dif_pos hTop]
          exact R.horizontalTopEdgePath_vertexSet_subset_row hcd x.1.row hTop
        · by_cases hBottom : x.1.row.1 + 1 = g
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
              dif_neg hTop, dif_pos hBottom]
            exact R.horizontalBottomEdgePath_vertexSet_subset_row hcd x.1.row
              hBottom
          · have hTopPos : 0 < x.1.row.1 := by omega
            have hBottomLt : x.1.row.1 + 1 < g := by omega
            unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_pos hnextForward,
              dif_neg hTop, dif_neg hBottom]
            exact R.horizontalMiddleEdgePath_vertexSet_subset_row hcd x.1.row
              hTopPos hBottomLt
      · have hnextBackward :
            x.1.row = y.1.row ∧
              y.1.col.1 + 1 = x.1.col.1 ∧
                y.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
                  x.1.port = SparseGrid.Vertex.firstPort x.1.row := by
          rcases hxy with hsame | hnext
          · rcases hsame with ⟨hrow, hcol, hports | hports⟩
            · exact False.elim
                (hsameForward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
            · exact False.elim
                (hsameBackward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
          · rcases hnext with ⟨hrow, hdir | hdir⟩
            · exact False.elim
                (hnextForward ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩)
            · exact ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩
        have hcd : y.1.col.1 < x.1.col.1 := by omega
        by_cases hTop : y.1.row.1 = 0
        · unfold horizontalAdjPath
          rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
            dif_pos hTop]
          simpa [hnextBackward.1] using
            R.horizontalTopEdgePath_vertexSet_subset_row hcd y.1.row hTop
        · by_cases hBottom : y.1.row.1 + 1 = g
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
              dif_neg hTop, dif_pos hBottom]
            simpa [hnextBackward.1] using
              R.horizontalBottomEdgePath_vertexSet_subset_row hcd y.1.row hBottom
          · have hTopPos : 0 < y.1.row.1 := by omega
            have hBottomLt : y.1.row.1 + 1 < g := by omega
            unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward, dif_neg hnextForward,
              dif_neg hTop, dif_neg hBottom]
            simpa [hnextBackward.1] using
              R.horizontalMiddleEdgePath_vertexSet_subset_row hcd y.1.row
                hTopPos hBottomLt

/-- Every explicit horizontal sparse-grid edge path is also contained in the
stitched row of its second endpoint. -/
theorem horizontalAdjPath_vertexSet_subset_target_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).vertexSet ⊆
      (R.rows.path (R.row y.1.row)).vertexSet := by
  have hrow : x.1.row = y.1.row := SparseGrid.row_eq_of_horizontalAdj hxy
  simpa [hrow] using R.horizontalAdjPath_vertexSet_subset_row hg hxy

/-- The allocated drop-last part of a horizontal adjacency path is contained in
the stitched row of its source endpoint. -/
theorem horizontalAdjPath_dropLast_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).dropLast.vertexSet ⊆
      (R.rows.path (R.row x.1.row)).vertexSet := by
  intro v hv
  exact R.horizontalAdjPath_vertexSet_subset_row hg hxy
    ((R.horizontalAdjPath hg hxy).dropLast_vertexSet_subset hv)

/-- The allocated drop-last part of a horizontal adjacency path is contained in
the stitched row of its target endpoint. -/
theorem horizontalAdjPath_dropLast_subset_target_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    (R.horizontalAdjPath hg hxy).dropLast.vertexSet ⊆
      (R.rows.path (R.row y.1.row)).vertexSet := by
  intro v hv
  exact R.horizontalAdjPath_vertexSet_subset_target_row hg hxy
    ((R.horizontalAdjPath hg hxy).dropLast_vertexSet_subset hv)

/-- Endpoint images on different stitched rows cannot lie in the allocated
drop-last part of a horizontal adjacency path. -/
theorem validVertexImage_not_mem_horizontalAdjPath_dropLast_of_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hrow : z.1.row ≠ x.1.row) :
    R.validVertexImage hg z ∉ (R.horizontalAdjPath hg hxy).dropLast.vertexSet := by
  intro hzmem
  have hzRowZ :
      R.validVertexImage hg z ∈
        (R.rows.path (R.row z.1.row)).vertexSet :=
    R.validVertexImage_mem_row hg z
  have hzRowX :
      R.validVertexImage hg z ∈
        (R.rows.path (R.row x.1.row)).vertexSet :=
    R.horizontalAdjPath_vertexSet_subset_row hg hxy
      ((R.horizontalAdjPath hg hxy).dropLast_vertexSet_subset hzmem)
  have hrowIndex : R.row z.1.row ≠ R.row x.1.row := by
    intro h
    exact hrow (R.row_injective h)
  exact Finset.disjoint_left.mp (R.rows.node_disjoint hrowIndex) hzRowZ hzRowX

/-- No non-endpoint valid sparse-grid image lies in the allocated drop-last
part of a horizontal adjacency path. -/
theorem validVertexImage_not_mem_horizontalAdjPath_dropLast_of_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    R.validVertexImage hg z ∉ (R.horizontalAdjPath hg hxy).dropLast.vertexSet := by
  by_cases hrowzx : z.1.row = x.1.row
  · by_cases hsameForward :
        x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
          x.1.port = SparseGrid.Vertex.firstPort x.1.row ∧
            y.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
              x.1.port ≠ y.1.port
    · have hfl_ne :
          SparseGrid.Vertex.firstPort x.1.row ≠
            SparseGrid.Vertex.lastPort x.1.row := by
        intro heq
        exact hsameForward.2.2.2.2
          (hsameForward.2.2.1.trans (heq.trans hsameForward.2.2.2.1.symm))
      rcases (SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 hfl_ne with
        ⟨hTop, hBottom⟩
      have hxfirst :=
        SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x
          hsameForward.2.2.1
      have hylast : y = SparseGrid.ValidVertex.last y.1.row y.1.col :=
        SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y
          (by simpa [hsameForward.1] using hsameForward.2.2.2.1)
      have hzfirst : z ≠ SparseGrid.ValidVertex.first x.1.row x.1.col := by
        intro hz
        exact hzx (by rw [hz, ← hxfirst])
      have hzlast : z ≠ SparseGrid.ValidVertex.last x.1.row x.1.col := by
        intro hz
        exact hzy (by
          calc
            z = SparseGrid.ValidVertex.last x.1.row x.1.col := hz
            _ = SparseGrid.ValidVertex.last y.1.row y.1.col := by
              rw [hsameForward.1, hsameForward.2.1]
            _ = y := hylast.symm)
      unfold horizontalAdjPath
      rw [dif_pos hsameForward]
      exact R.validVertexImage_not_mem_horizontalInternalEdgePath_dropLast_of_ne
        hg x.1.row x.1.col hTop hBottom hrowzx hzfirst hzlast
    · by_cases hsameBackward :
          x.1.row = y.1.row ∧ x.1.col = y.1.col ∧
            y.1.port = SparseGrid.Vertex.firstPort y.1.row ∧
              x.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
                y.1.port ≠ x.1.port
      · have hfl_ne :
            SparseGrid.Vertex.firstPort y.1.row ≠
              SparseGrid.Vertex.lastPort y.1.row := by
          intro heq
          exact hsameBackward.2.2.2.2
            (hsameBackward.2.2.1.trans
              (heq.trans hsameBackward.2.2.2.1.symm))
        rcases (SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne with
          ⟨hTop, hBottom⟩
        have hyfirst :=
          SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y
            hsameBackward.2.2.1
        have hxlast : x = SparseGrid.ValidVertex.last x.1.row x.1.col :=
          SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x
            (by simpa [hsameBackward.1] using hsameBackward.2.2.2.1)
        have hrowzy : z.1.row = y.1.row := hrowzx.trans hsameBackward.1
        have hzfirst : z ≠ SparseGrid.ValidVertex.first y.1.row y.1.col := by
          intro hz
          exact hzy (by rw [hz, ← hyfirst])
        have hzlast : z ≠ SparseGrid.ValidVertex.last y.1.row y.1.col := by
          intro hz
          exact hzx (by
            calc
              z = SparseGrid.ValidVertex.last y.1.row y.1.col := hz
              _ = SparseGrid.ValidVertex.last x.1.row x.1.col := by
                rw [← hsameBackward.1, ← hsameBackward.2.1]
              _ = x := hxlast.symm)
        unfold horizontalAdjPath
        rw [dif_neg hsameForward, dif_pos hsameBackward]
        exact
          R.validVertexImage_not_mem_horizontalInternalEdgePath_reverse_dropLast_of_ne
            hg y.1.row y.1.col hTop hBottom hrowzy hzfirst hzlast
      · by_cases hnextForward :
            x.1.row = y.1.row ∧
              x.1.col.1 + 1 = y.1.col.1 ∧
                x.1.port = SparseGrid.Vertex.lastPort x.1.row ∧
                  y.1.port = SparseGrid.Vertex.firstPort y.1.row
        · have hcd : x.1.col.1 < y.1.col.1 := by omega
          have hxlast :=
            SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x
              hnextForward.2.2.1
          have hyfirst :=
            SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y
              hnextForward.2.2.2
          have hzlast : z ≠ SparseGrid.ValidVertex.last x.1.row x.1.col := by
            intro hz
            exact hzx (by rw [hz, ← hxlast])
          have hzfirst :
              z ≠ SparseGrid.ValidVertex.first x.1.row y.1.col := by
            intro hz
            exact hzy (by
              calc
                z = SparseGrid.ValidVertex.first x.1.row y.1.col := hz
                _ = SparseGrid.ValidVertex.first y.1.row y.1.col := by
                  rw [hnextForward.1]
                _ = y := hyfirst.symm)
          by_cases hTop : x.1.row.1 = 0
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward,
              dif_pos hnextForward, dif_pos hTop]
            exact R.validVertexImage_not_mem_horizontalTopEdgePath_dropLast_of_ne
              hg hcd hnextForward.2.1 x.1.row hTop hrowzx hzlast hzfirst
          · by_cases hBottom : x.1.row.1 + 1 = g
            · unfold horizontalAdjPath
              rw [dif_neg hsameForward, dif_neg hsameBackward,
                dif_pos hnextForward, dif_neg hTop, dif_pos hBottom]
              exact R.validVertexImage_not_mem_horizontalBottomEdgePath_dropLast_of_ne
                hg hcd hnextForward.2.1 x.1.row hBottom hrowzx hzlast hzfirst
            · have hTopPos : 0 < x.1.row.1 := by omega
              have hBottomLt : x.1.row.1 + 1 < g := by omega
              unfold horizontalAdjPath
              rw [dif_neg hsameForward, dif_neg hsameBackward,
                dif_pos hnextForward, dif_neg hTop, dif_neg hBottom]
              exact R.validVertexImage_not_mem_horizontalMiddleEdgePath_dropLast_of_ne
                hg hcd hnextForward.2.1 x.1.row hTopPos hBottomLt hrowzx
                hzlast hzfirst
        · have hnextBackward :
              x.1.row = y.1.row ∧
                y.1.col.1 + 1 = x.1.col.1 ∧
                  y.1.port = SparseGrid.Vertex.lastPort y.1.row ∧
                    x.1.port = SparseGrid.Vertex.firstPort x.1.row := by
            rcases hxy with hsame | hnext
            · rcases hsame with ⟨hrow, hcol, hports | hports⟩
              · exact False.elim
                  (hsameForward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
              · exact False.elim
                  (hsameBackward ⟨hrow, hcol, hports.1, hports.2.1, hports.2.2⟩)
            · rcases hnext with ⟨hrow, hdir | hdir⟩
              · exact False.elim
                  (hnextForward ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩)
              · exact ⟨hrow, hdir.1, hdir.2.1, hdir.2.2⟩
          have hcd : y.1.col.1 < x.1.col.1 := by omega
          have hylast :=
            SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y
              hnextBackward.2.2.1
          have hxfirst :=
            SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x
              hnextBackward.2.2.2
          have hrowzy : z.1.row = y.1.row := hrowzx.trans hnextBackward.1
          have hzlast : z ≠ SparseGrid.ValidVertex.last y.1.row y.1.col := by
            intro hz
            exact hzy (by rw [hz, ← hylast])
          have hzfirst :
              z ≠ SparseGrid.ValidVertex.first y.1.row x.1.col := by
            intro hz
            exact hzx (by
              calc
                z = SparseGrid.ValidVertex.first y.1.row x.1.col := hz
                _ = SparseGrid.ValidVertex.first x.1.row x.1.col := by
                  rw [← hnextBackward.1]
                _ = x := hxfirst.symm)
          by_cases hTop : y.1.row.1 = 0
          · unfold horizontalAdjPath
            rw [dif_neg hsameForward, dif_neg hsameBackward,
              dif_neg hnextForward, dif_pos hTop]
            exact
              R.validVertexImage_not_mem_horizontalTopEdgePath_reverse_dropLast_of_ne
                hg hcd hnextBackward.2.1 y.1.row hTop hrowzy hzlast hzfirst
          · by_cases hBottom : y.1.row.1 + 1 = g
            · unfold horizontalAdjPath
              rw [dif_neg hsameForward, dif_neg hsameBackward,
                dif_neg hnextForward, dif_neg hTop, dif_pos hBottom]
              exact
                R.validVertexImage_not_mem_horizontalBottomEdgePath_reverse_dropLast_of_ne
                  hg hcd hnextBackward.2.1 y.1.row hBottom hrowzy hzlast hzfirst
            · have hTopPos : 0 < y.1.row.1 := by omega
              have hBottomLt : y.1.row.1 + 1 < g := by omega
              unfold horizontalAdjPath
              rw [dif_neg hsameForward, dif_neg hsameBackward,
                dif_neg hnextForward, dif_neg hTop, dif_neg hBottom]
              exact
                R.validVertexImage_not_mem_horizontalMiddleEdgePath_reverse_dropLast_of_ne
                  hg hcd hnextBackward.2.1 y.1.row hTopPos hBottomLt hrowzy
                  hzlast hzfirst
  · exact R.validVertexImage_not_mem_horizontalAdjPath_dropLast_of_row_ne
      hg hxy hrowzx

/-- A vertical allocated path and a horizontal allocated path are disjoint when
their source sparse-grid vertices lie on different stitched rows. -/
theorem verticalAdjPath_dropLast_disjoint_horizontalAdjPath_dropLast_of_source_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hzt : SparseGrid.HorizontalAdj z.1 t.1)
    (hrow : x.1.row ≠ z.1.row) :
    Disjoint (R.verticalAdjPath hxy).dropLast.vertexSet
      (R.horizontalAdjPath hg hzt).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvVertical hvHorizontal
  have hvRow :
      v ∈ (R.rows.path (R.row z.1.row)).vertexSet :=
    R.horizontalAdjPath_vertexSet_subset_row hg hzt
      ((R.horizontalAdjPath hg hzt).dropLast_vertexSet_subset hvHorizontal)
  have hvSource :
      v = R.validVertexImage hg x :=
    R.verticalAdjPath_dropLast_mem_row_eq_source hg hxy hvVertical hvRow
  have hnot :=
    R.validVertexImage_not_mem_horizontalAdjPath_dropLast_of_row_ne
      hg hzt hrow
  exact hnot (by simpa [hvSource] using hvHorizontal)

/-- Symmetric form of mixed disjointness for horizontal then vertical allocated
paths with source vertices on different stitched rows. -/
theorem horizontalAdjPath_dropLast_disjoint_verticalAdjPath_dropLast_of_source_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hzt : SparseGrid.VerticalAdj z.1 t.1)
    (hrow : x.1.row ≠ z.1.row) :
    Disjoint (R.horizontalAdjPath hg hxy).dropLast.vertexSet
      (R.verticalAdjPath hzt).dropLast.vertexSet :=
  (R.verticalAdjPath_dropLast_disjoint_horizontalAdjPath_dropLast_of_source_row_ne
    hg hzt hxy hrow.symm).symm

/-- A vertical allocated path and a horizontal allocated path are disjoint as
soon as their allocated source sparse-grid vertices are different.  If the
vertical path meets the horizontal row, it does so only at its source image;
that image is not in the horizontal drop-last path unless it is the horizontal
source, which is excluded by hypothesis. -/
theorem verticalAdjPath_dropLast_disjoint_horizontalAdjPath_dropLast
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hzt : SparseGrid.HorizontalAdj z.1 t.1)
    (hxz : x ≠ z) :
    Disjoint (R.verticalAdjPath hxy).dropLast.vertexSet
      (R.horizontalAdjPath hg hzt).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvVertical hvHorizontal
  have hvRow :
      v ∈ (R.rows.path (R.row z.1.row)).vertexSet :=
    R.horizontalAdjPath_vertexSet_subset_row hg hzt
      ((R.horizontalAdjPath hg hzt).dropLast_vertexSet_subset hvHorizontal)
  have hvSource :
      v = R.validVertexImage hg x :=
    R.verticalAdjPath_dropLast_mem_row_eq_source hg hxy hvVertical hvRow
  by_cases hxt : x = t
  · have hnot :=
      R.horizontalAdjPath_target_not_mem_dropLast hg hzt
    exact hnot (by simpa [hvSource, hxt] using hvHorizontal)
  · have hnot :=
      R.validVertexImage_not_mem_horizontalAdjPath_dropLast_of_ne
        hg hzt hxz hxt
    exact hnot (by simpa [hvSource] using hvHorizontal)

/-- Symmetric form of mixed vertical/horizontal disjointness with distinct
allocated sources. -/
theorem horizontalAdjPath_dropLast_disjoint_verticalAdjPath_dropLast
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hzt : SparseGrid.VerticalAdj z.1 t.1)
    (hxz : x ≠ z) :
    Disjoint (R.horizontalAdjPath hg hxy).dropLast.vertexSet
      (R.verticalAdjPath hzt).dropLast.vertexSet :=
  (R.verticalAdjPath_dropLast_disjoint_horizontalAdjPath_dropLast
    hg hzt hxy hxz.symm).symm

/-- Vertical allocated paths in different incident even clusters are disjoint. -/
theorem verticalAdjPath_dropLast_disjoint_of_incidentIndex_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hzt : SparseGrid.VerticalAdj z.1 t.1)
    (hidx : validVertexIncidentIndex hg x ≠ validVertexIncidentIndex hg z) :
    Disjoint (R.verticalAdjPath hxy).dropLast.vertexSet
      (R.verticalAdjPath hzt).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvXY hvZT
  have hvClusterX :
      v ∈ P.cluster (evenClusterIndex g (validVertexIncidentIndex hg x)) :=
    R.verticalAdjPath_vertexSet_subset_incidentCluster hg hxy
      ((R.verticalAdjPath hxy).dropLast_vertexSet_subset hvXY)
  have hvClusterZ :
      v ∈ P.cluster (evenClusterIndex g (validVertexIncidentIndex hg z)) :=
    R.verticalAdjPath_vertexSet_subset_incidentCluster hg hzt
      ((R.verticalAdjPath hzt).dropLast_vertexSet_subset hvZT)
  have hcluster :
      evenClusterIndex g (validVertexIncidentIndex hg x) ≠
        evenClusterIndex g (validVertexIncidentIndex hg z) := by
    intro h
    exact hidx (evenClusterIndex_injective h)
  exact Finset.disjoint_left.mp (P.cluster_disjoint hcluster) hvClusterX hvClusterZ

/-- Two horizontal allocated paths with source vertices on different stitched
rows are disjoint. -/
theorem horizontalAdjPath_dropLast_disjoint_of_source_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hzt : SparseGrid.HorizontalAdj z.1 t.1)
    (hrow : x.1.row ≠ z.1.row) :
    Disjoint (R.horizontalAdjPath hg hxy).dropLast.vertexSet
      (R.horizontalAdjPath hg hzt).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvXY hvZT
  have hvRowX :
      v ∈ (R.rows.path (R.row x.1.row)).vertexSet :=
    R.horizontalAdjPath_vertexSet_subset_row hg hxy
      ((R.horizontalAdjPath hg hxy).dropLast_vertexSet_subset hvXY)
  have hvRowZ :
      v ∈ (R.rows.path (R.row z.1.row)).vertexSet :=
    R.horizontalAdjPath_vertexSet_subset_row hg hzt
      ((R.horizontalAdjPath hg hzt).dropLast_vertexSet_subset hvZT)
  have hrowIndex : R.row x.1.row ≠ R.row z.1.row := by
    intro h
    exact hrow (R.row_injective h)
  exact Finset.disjoint_left.mp (R.rows.node_disjoint hrowIndex) hvRowX hvRowZ

/-- Two rank-oriented horizontal allocated paths with distinct sources are
disjoint.  On different stitched rows this is row disjointness; on the same
row, the rank order makes the two half-open row segments ordered. -/
theorem horizontalAdjPath_dropLast_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hzt : SparseGrid.HorizontalAdj z.1 t.1)
    (hrankxy :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hrankzt :
      ValidSparseGridPathCertificate.validVertexRank z <
        ValidSparseGridPathCertificate.validVertexRank t)
    (hxz : x ≠ z) :
    Disjoint (R.horizontalAdjPath hg hxy).dropLast.vertexSet
      (R.horizontalAdjPath hg hzt).dropLast.vertexSet := by
  classical
  by_cases hrow : x.1.row = z.1.row
  · rcases
      R.exists_horizontalAdjPath_segment_of_validVertexRank_lt hg hxy hrankxy with
      ⟨a, b, hab, hpathXY, ha, hb⟩
    rcases
      R.exists_horizontalAdjPath_segment_of_validVertexRank_lt hg hzt hrankzt with
      ⟨c, d, hcdZ, hpathZT, hc, hd⟩
    have hcd :
        (R.rows.path (R.row x.1.row)).Before c d := by
      simpa [← hrow] using hcdZ
    have hpathZT' :
        R.horizontalAdjPath hg hzt =
          (R.rows.path (R.row x.1.row)).segmentOfBefore hcd := by
      simpa [← hrow, hcd] using hpathZT
    have hxzRankNe :
        ValidSparseGridPathCertificate.validVertexRank x ≠
          ValidSparseGridPathCertificate.validVertexRank z := by
      intro h
      exact hxz (ValidSparseGridPathCertificate.validVertexRank_injective h)
    rcases lt_or_gt_of_ne hxzRankNe with hxRankLt | hzRankLt
    · have hbc :
          (R.rows.path (R.row x.1.row)).Before b c := by
        have htarget :=
          R.horizontalAdj_target_before_of_source_validVertexRank_lt hg
            hxy hrankxy hrow.symm hxRankLt
        simpa [hb, hc] using htarget
      have hne : a ≠ b := by
        intro habEq
        have himage : R.validVertexImage hg x = R.validVertexImage hg y := by
          rw [← ha, ← hb]
          exact habEq
        exact (SparseGrid.validGraph g).ne_of_adj (Or.inl hxy)
          (R.validVertexImage_injective hg himage)
      rw [hpathXY, hpathZT']
      exact GraphPath.segmentOfBefore_dropLast_disjoint_of_target_before_source
        (R.rows.path (R.row x.1.row)) hab hcd hbc hne
    · have hda :
          (R.rows.path (R.row x.1.row)).Before d a := by
        have htarget :=
          R.horizontalAdj_target_before_of_source_validVertexRank_lt hg
            hzt hrankzt hrow hzRankLt
        simpa [← hrow, hd, ha] using htarget
      have hne : c ≠ d := by
        intro hcdEq
        have himage : R.validVertexImage hg z = R.validVertexImage hg t := by
          rw [← hc, ← hd]
          exact hcdEq
        exact (SparseGrid.validGraph g).ne_of_adj (Or.inl hzt)
          (R.validVertexImage_injective hg himage)
      rw [hpathXY, hpathZT']
      exact (GraphPath.segmentOfBefore_dropLast_disjoint_of_target_before_source
        (R.rows.path (R.row x.1.row)) hcd hab hda hne).symm
  · exact R.horizontalAdjPath_dropLast_disjoint_of_source_row_ne hg hxy hzt hrow

/-- Any vertical adjacency of the valid sparse grid is realized by the
corresponding selected bridge path, with the endpoints normalized to the
orientation of the sparse-grid edge. -/
theorem exists_verticalAdjPathWithEndpoints
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1) :
    ∃ Q : GraphPath G,
      Q.source = R.validVertexImage hg x ∧
        Q.target = R.validVertexImage hg y := by
  rcases hxy with ⟨hcol, hdir | hdir⟩
  · rcases hdir with ⟨hrow, htrue, hfalse⟩
    have hr : x.1.row.1 + 1 < g := by
      rw [hrow]
      exact y.1.row.2
    refine ⟨R.verticalSparseEdgePath x.1.row x.1.col hr, ?_, ?_⟩
    · have hxlast := SparseGrid.ValidVertex.eq_last_of_port_true hg x htrue
      calc
        (R.verticalSparseEdgePath x.1.row x.1.col hr).source =
            R.validVertexImage hg
              (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
          exact R.verticalSparseEdgePath_source hg x.1.row x.1.col hr
        _ = R.validVertexImage hg x := by
          rw [← hxlast]
    · have hyfirst := SparseGrid.ValidVertex.eq_first_of_port_false hg y hfalse
      have hyrow : (⟨x.1.row.1 + 1, hr⟩ : Fin g) = y.1.row := Fin.ext hrow
      have hfirst :
          SparseGrid.ValidVertex.first (⟨x.1.row.1 + 1, hr⟩ : Fin g) x.1.col =
            SparseGrid.ValidVertex.first y.1.row y.1.col := by
        rw [hyrow, hcol]
      calc
        (R.verticalSparseEdgePath x.1.row x.1.col hr).target =
            R.validVertexImage hg
              (SparseGrid.ValidVertex.first
                (⟨x.1.row.1 + 1, hr⟩ : Fin g) x.1.col) := by
          exact R.verticalSparseEdgePath_target hg x.1.row x.1.col hr
        _ = R.validVertexImage hg (SparseGrid.ValidVertex.first y.1.row y.1.col) := by
          rw [hfirst]
        _ = R.validVertexImage hg y := by
          rw [← hyfirst]
  · rcases hdir with ⟨hrow, htrue, hfalse⟩
    have hr : y.1.row.1 + 1 < g := by
      rw [hrow]
      exact x.1.row.2
    refine ⟨(R.verticalSparseEdgePath y.1.row y.1.col hr).reverse, ?_, ?_⟩
    · have hxfirst := SparseGrid.ValidVertex.eq_first_of_port_false hg x hfalse
      have hxrow : (⟨y.1.row.1 + 1, hr⟩ : Fin g) = x.1.row := Fin.ext hrow
      have hfirst :
          SparseGrid.ValidVertex.first (⟨y.1.row.1 + 1, hr⟩ : Fin g) y.1.col =
            SparseGrid.ValidVertex.first x.1.row x.1.col := by
        rw [hxrow, ← hcol]
      calc
        ((R.verticalSparseEdgePath y.1.row y.1.col hr).reverse).source =
            (R.verticalSparseEdgePath y.1.row y.1.col hr).target := rfl
        _ = R.validVertexImage hg
              (SparseGrid.ValidVertex.first
                (⟨y.1.row.1 + 1, hr⟩ : Fin g) y.1.col) := by
          exact R.verticalSparseEdgePath_target hg y.1.row y.1.col hr
        _ = R.validVertexImage hg (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
          rw [hfirst]
        _ = R.validVertexImage hg x := by
          rw [← hxfirst]
    · have hylast := SparseGrid.ValidVertex.eq_last_of_port_true hg y htrue
      calc
        ((R.verticalSparseEdgePath y.1.row y.1.col hr).reverse).target =
            (R.verticalSparseEdgePath y.1.row y.1.col hr).source := rfl
        _ = R.validVertexImage hg
              (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
          exact R.verticalSparseEdgePath_source hg y.1.row y.1.col hr
        _ = R.validVertexImage hg y := by
          rw [← hylast]

/-- Any horizontal adjacency of the valid sparse grid is realized by the
appropriate row segment, with the endpoints normalized to the orientation of
the sparse-grid edge. -/
theorem exists_horizontalAdjPathWithEndpoints
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1) :
    ∃ Q : GraphPath G,
      Q.source = R.validVertexImage hg x ∧
        Q.target = R.validVertexImage hg y := by
  rcases hxy with hsame | hnext
  · rcases hsame with ⟨hrow, hcol, hports | hports⟩
    · rcases hports with ⟨hxfirst, hylast, hne⟩
      have hfl_ne :
          SparseGrid.Vertex.firstPort x.1.row ≠
            SparseGrid.Vertex.lastPort x.1.row := by
        intro heq
        exact hne (hxfirst.trans (heq.trans hylast.symm))
      rcases (SparseGrid.firstPort_ne_lastPort_iff_internal hg x.1.row).1 hfl_ne with
        ⟨hTop, hBottom⟩
      refine ⟨R.horizontalInternalEdgePath x.1.row x.1.col hTop hBottom, ?_, ?_⟩
      · have hxfirst' :=
          SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x hxfirst
        calc
          (R.horizontalInternalEdgePath x.1.row x.1.col hTop hBottom).source =
              R.validVertexImage hg
                (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
            exact R.horizontalInternalEdgePath_source hg x.1.row x.1.col hTop hBottom
          _ = R.validVertexImage hg x := by
            rw [← hxfirst']
      · have hylast' : y.1.port = SparseGrid.Vertex.lastPort y.1.row := by
          rw [← hrow]
          exact hylast
        have hylast_norm :=
          SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y hylast'
        calc
          (R.horizontalInternalEdgePath x.1.row x.1.col hTop hBottom).target =
              R.validVertexImage hg
                (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
            exact R.horizontalInternalEdgePath_target hg x.1.row x.1.col hTop hBottom
          _ = R.validVertexImage hg
                (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
            rw [hrow, hcol]
          _ = R.validVertexImage hg y := by
            rw [← hylast_norm]
    · rcases hports with ⟨hyfirst, hxlast, hne⟩
      have hfl_ne :
          SparseGrid.Vertex.firstPort y.1.row ≠
            SparseGrid.Vertex.lastPort y.1.row := by
        intro heq
        exact hne (hyfirst.trans (heq.trans hxlast.symm))
      rcases (SparseGrid.firstPort_ne_lastPort_iff_internal hg y.1.row).1 hfl_ne with
        ⟨hTop, hBottom⟩
      refine ⟨(R.horizontalInternalEdgePath y.1.row y.1.col hTop hBottom).reverse, ?_, ?_⟩
      · have hxlast' : x.1.port = SparseGrid.Vertex.lastPort x.1.row := by
          rw [hrow]
          exact hxlast
        have hxlast_norm :=
          SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x hxlast'
        calc
          ((R.horizontalInternalEdgePath y.1.row y.1.col hTop hBottom).reverse).source =
              (R.horizontalInternalEdgePath y.1.row y.1.col hTop hBottom).target := rfl
          _ = R.validVertexImage hg
                (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
            exact R.horizontalInternalEdgePath_target hg y.1.row y.1.col hTop hBottom
          _ = R.validVertexImage hg
                (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
            rw [← hrow, ← hcol]
          _ = R.validVertexImage hg x := by
            rw [← hxlast_norm]
      · have hyfirst_norm :=
          SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y hyfirst
        calc
          ((R.horizontalInternalEdgePath y.1.row y.1.col hTop hBottom).reverse).target =
              (R.horizontalInternalEdgePath y.1.row y.1.col hTop hBottom).source := rfl
          _ = R.validVertexImage hg
                (SparseGrid.ValidVertex.first y.1.row y.1.col) := by
            exact R.horizontalInternalEdgePath_source hg y.1.row y.1.col hTop hBottom
          _ = R.validVertexImage hg y := by
            rw [← hyfirst_norm]
  · rcases hnext with ⟨hrow, hdir | hdir⟩
    · rcases hdir with ⟨hcolsucc, hxlast, hyfirst⟩
      have hcd : x.1.col.1 < y.1.col.1 := by omega
      have hxlast_norm :=
        SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort x hxlast
      have hyfirst_norm :=
        SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort y hyfirst
      by_cases hTop : x.1.row.1 = 0
      · refine ⟨R.horizontalTopEdgePath hcd x.1.row hTop, ?_, ?_⟩
        · calc
            (R.horizontalTopEdgePath hcd x.1.row hTop).source =
                R.validVertexImage hg
                  (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
              exact R.horizontalTopEdgePath_source hg hcd x.1.row hTop
            _ = R.validVertexImage hg x := by
              rw [← hxlast_norm]
        · calc
            (R.horizontalTopEdgePath hcd x.1.row hTop).target =
                R.validVertexImage hg
                  (SparseGrid.ValidVertex.first x.1.row y.1.col) := by
              exact R.horizontalTopEdgePath_target hg hcd x.1.row hTop
            _ = R.validVertexImage hg
                  (SparseGrid.ValidVertex.first y.1.row y.1.col) := by
              rw [hrow]
            _ = R.validVertexImage hg y := by
              rw [← hyfirst_norm]
      · by_cases hBottomEq : x.1.row.1 + 1 = g
        · refine ⟨R.horizontalBottomEdgePath hcd x.1.row hBottomEq, ?_, ?_⟩
          · calc
              (R.horizontalBottomEdgePath hcd x.1.row hBottomEq).source =
                  R.validVertexImage hg
                    (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
                exact R.horizontalBottomEdgePath_source hg hcd x.1.row hBottomEq
              _ = R.validVertexImage hg x := by
                rw [← hxlast_norm]
          · calc
              (R.horizontalBottomEdgePath hcd x.1.row hBottomEq).target =
                  R.validVertexImage hg
                    (SparseGrid.ValidVertex.first x.1.row y.1.col) := by
                exact R.horizontalBottomEdgePath_target hg hcd x.1.row hBottomEq
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first y.1.row y.1.col) := by
                rw [hrow]
              _ = R.validVertexImage hg y := by
                rw [← hyfirst_norm]
        · have hTopPos : 0 < x.1.row.1 := by omega
          have hBottom : x.1.row.1 + 1 < g := by omega
          refine ⟨R.horizontalMiddleEdgePath hcd x.1.row hTopPos hBottom, ?_, ?_⟩
          · calc
              (R.horizontalMiddleEdgePath hcd x.1.row hTopPos hBottom).source =
                  R.validVertexImage hg
                    (SparseGrid.ValidVertex.last x.1.row x.1.col) := by
                exact R.horizontalMiddleEdgePath_source hg hcd x.1.row hTopPos hBottom
              _ = R.validVertexImage hg x := by
                rw [← hxlast_norm]
          · calc
              (R.horizontalMiddleEdgePath hcd x.1.row hTopPos hBottom).target =
                  R.validVertexImage hg
                    (SparseGrid.ValidVertex.first x.1.row y.1.col) := by
                exact R.horizontalMiddleEdgePath_target hg hcd x.1.row hTopPos hBottom
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first y.1.row y.1.col) := by
                rw [hrow]
              _ = R.validVertexImage hg y := by
                rw [← hyfirst_norm]
    · rcases hdir with ⟨hcolsucc, hylast, hxfirst⟩
      have hcd : y.1.col.1 < x.1.col.1 := by omega
      have hylast_norm :=
        SparseGrid.ValidVertex.eq_last_of_port_eq_lastPort y hylast
      have hxfirst_norm :=
        SparseGrid.ValidVertex.eq_first_of_port_eq_firstPort x hxfirst
      by_cases hTop : y.1.row.1 = 0
      · refine ⟨(R.horizontalTopEdgePath hcd y.1.row hTop).reverse, ?_, ?_⟩
        · calc
            ((R.horizontalTopEdgePath hcd y.1.row hTop).reverse).source =
                (R.horizontalTopEdgePath hcd y.1.row hTop).target := rfl
            _ = R.validVertexImage hg
                  (SparseGrid.ValidVertex.first y.1.row x.1.col) := by
              exact R.horizontalTopEdgePath_target hg hcd y.1.row hTop
            _ = R.validVertexImage hg
                  (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
              rw [← hrow]
            _ = R.validVertexImage hg x := by
              rw [← hxfirst_norm]
        · calc
            ((R.horizontalTopEdgePath hcd y.1.row hTop).reverse).target =
                (R.horizontalTopEdgePath hcd y.1.row hTop).source := rfl
            _ = R.validVertexImage hg
                  (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
              exact R.horizontalTopEdgePath_source hg hcd y.1.row hTop
            _ = R.validVertexImage hg y := by
              rw [← hylast_norm]
      · by_cases hBottomEq : y.1.row.1 + 1 = g
        · refine ⟨(R.horizontalBottomEdgePath hcd y.1.row hBottomEq).reverse, ?_, ?_⟩
          · calc
              ((R.horizontalBottomEdgePath hcd y.1.row hBottomEq).reverse).source =
                  (R.horizontalBottomEdgePath hcd y.1.row hBottomEq).target := rfl
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first y.1.row x.1.col) := by
                exact R.horizontalBottomEdgePath_target hg hcd y.1.row hBottomEq
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
                rw [← hrow]
              _ = R.validVertexImage hg x := by
                rw [← hxfirst_norm]
          · calc
              ((R.horizontalBottomEdgePath hcd y.1.row hBottomEq).reverse).target =
                  (R.horizontalBottomEdgePath hcd y.1.row hBottomEq).source := rfl
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
                exact R.horizontalBottomEdgePath_source hg hcd y.1.row hBottomEq
              _ = R.validVertexImage hg y := by
                rw [← hylast_norm]
        · have hTopPos : 0 < y.1.row.1 := by omega
          have hBottom : y.1.row.1 + 1 < g := by omega
          refine ⟨(R.horizontalMiddleEdgePath hcd y.1.row hTopPos hBottom).reverse, ?_, ?_⟩
          · calc
              ((R.horizontalMiddleEdgePath hcd y.1.row hTopPos hBottom).reverse).source =
                  (R.horizontalMiddleEdgePath hcd y.1.row hTopPos hBottom).target := rfl
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first y.1.row x.1.col) := by
                exact R.horizontalMiddleEdgePath_target hg hcd y.1.row hTopPos hBottom
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.first x.1.row x.1.col) := by
                rw [← hrow]
              _ = R.validVertexImage hg x := by
                rw [← hxfirst_norm]
          · calc
              ((R.horizontalMiddleEdgePath hcd y.1.row hTopPos hBottom).reverse).target =
                  (R.horizontalMiddleEdgePath hcd y.1.row hTopPos hBottom).source := rfl
              _ = R.validVertexImage hg
                    (SparseGrid.ValidVertex.last y.1.row y.1.col) := by
                exact R.horizontalMiddleEdgePath_source hg hcd y.1.row hTopPos hBottom
              _ = R.validVertexImage hg y := by
                rw [← hylast_norm]

/-- Every adjacency of the valid sparse grid is realized by a host path with
the mapped endpoints. -/
theorem exists_validSparseGridAdjPathWithEndpoints
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y) :
    ∃ Q : GraphPath G,
      Q.source = R.validVertexImage hg x ∧
        Q.target = R.validVertexImage hg y := by
  change SparseGrid.Adj x.1 y.1 at hxy
  rcases hxy with hhorizontal | hvertical
  · exact ⟨R.horizontalAdjPath hg hhorizontal,
      R.horizontalAdjPath_source hg hhorizontal,
      R.horizontalAdjPath_target hg hhorizontal⟩
  · exact ⟨R.verticalAdjPath hvertical,
      R.verticalAdjPath_source hg hvertical,
      R.verticalAdjPath_target hg hvertical⟩

/-- The row-and-bridge construction gives a path certificate for the entire
valid sparse grid. -/
noncomputable def validSparseGridPathCertificate
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g) :
    ValidSparseGridPathCertificate G g where
  image := R.validVertexImage hg
  edgePath := by
    intro x y hxy
    change SparseGrid.Adj x.1 y.1 at hxy
    by_cases hhorizontal : SparseGrid.HorizontalAdj x.1 y.1
    · exact R.horizontalAdjPath hg hhorizontal
    · have hvertical : SparseGrid.VerticalAdj x.1 y.1 := by
        rcases hxy with hhorizontal' | hvertical
        · exact False.elim (hhorizontal hhorizontal')
        · exact hvertical
      exact R.verticalAdjPath hvertical
  edgePath_source := by
    intro x y hxy
    change SparseGrid.Adj x.1 y.1 at hxy
    by_cases hhorizontal : SparseGrid.HorizontalAdj x.1 y.1
    · simpa [hhorizontal] using R.horizontalAdjPath_source hg hhorizontal
    · have hvertical : SparseGrid.VerticalAdj x.1 y.1 := by
        rcases hxy with hhorizontal' | hvertical
        · exact False.elim (hhorizontal hhorizontal')
        · exact hvertical
      simpa [hhorizontal] using R.verticalAdjPath_source hg hvertical
  edgePath_target := by
    intro x y hxy
    change SparseGrid.Adj x.1 y.1 at hxy
    by_cases hhorizontal : SparseGrid.HorizontalAdj x.1 y.1
    · simpa [hhorizontal] using R.horizontalAdjPath_target hg hhorizontal
    · have hvertical : SparseGrid.VerticalAdj x.1 y.1 := by
        rcases hxy with hhorizontal' | hvertical
        · exact False.elim (hhorizontal hhorizontal')
        · exact hvertical
      simpa [hhorizontal] using R.verticalAdjPath_target hg hvertical

/-- The stitched-row sparse-grid path certificate uses the explicit row-segment
selector for horizontal sparse-grid edges. -/
theorem validSparseGridPathCertificate_edgePath_of_horizontal
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)) =
        R.horizontalAdjPath hg hhorizontal := by
  simp [validSparseGridPathCertificate, hhorizontal]

/-- Drop-last vertex sets for horizontal edges in the stitched-row certificate
are the drop-last sets of the explicit row-segment selector. -/
theorem validSparseGridPathCertificate_dropLast_of_horizontal
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)).dropLast.vertexSet =
        (R.horizontalAdjPath hg hhorizontal).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal]

/-- The allocated drop-last part of a horizontal certificate edge stays inside
the stitched row of its source endpoint. -/
theorem validSparseGridPathCertificate_horizontal_dropLast_subset_row
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)).dropLast.vertexSet ⊆
        (R.rows.path (R.row x.1.row)).vertexSet := by
  intro v hv
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal] at hv
  exact R.horizontalAdjPath_vertexSet_subset_row hg hhorizontal
    ((R.horizontalAdjPath hg hhorizontal).dropLast_vertexSet_subset hv)

/-- Endpoint images on different stitched rows cannot lie in the allocated
drop-last part of a horizontal certificate edge. -/
theorem validSparseGridPathCertificate_validVertexImage_not_mem_horizontal_dropLast_of_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1)
    (hrow : z.1.row ≠ x.1.row) :
    R.validVertexImage hg z ∉
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal]
  exact R.validVertexImage_not_mem_horizontalAdjPath_dropLast_of_row_ne hg
    hhorizontal hrow

/-- Horizontal certificate edges satisfy endpoint exclusion for endpoint images
that lie on a different stitched row from the source. -/
theorem validSparseGridPathCertificate_horizontal_nonendpoint_not_mem_dropLast_of_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1)
    (_hrank :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (_hzx : z ≠ x) (_hzy : z ≠ y)
    (hrow : z.1.row ≠ x.1.row) :
    R.validVertexImage hg z ∉
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)).dropLast.vertexSet :=
  R.validSparseGridPathCertificate_validVertexImage_not_mem_horizontal_dropLast_of_row_ne
    hg hhorizontal hrow

/-- Horizontal certificate edges satisfy endpoint exclusion for every
non-endpoint valid sparse-grid image. -/
theorem validSparseGridPathCertificate_horizontal_nonendpoint_not_mem_dropLast
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1)
    (_hrank :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    R.validVertexImage hg z ∉
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal]
  exact R.validVertexImage_not_mem_horizontalAdjPath_dropLast_of_ne
    hg hhorizontal hzx hzy

/-- The stitched-row sparse-grid path certificate uses the explicit bridge
selector for vertical sparse-grid edges. -/
theorem validSparseGridPathCertificate_edgePath_of_vertical
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)) =
        R.verticalAdjPath hvertical := by
  have hnot := SparseGrid.not_horizontalAdj_of_verticalAdj hvertical
  simp [validSparseGridPathCertificate, hnot]

/-- Drop-last vertex sets for vertical edges in the stitched-row certificate are
the drop-last sets of the explicit bridge selector. -/
theorem validSparseGridPathCertificate_dropLast_of_vertical
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)).dropLast.vertexSet =
        (R.verticalAdjPath hvertical).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical]

/-- The allocated drop-last part of a vertical certificate edge stays inside
the source endpoint's incident even cluster. -/
theorem validSparseGridPathCertificate_vertical_dropLast_subset_incidentCluster
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)).dropLast.vertexSet ⊆
        P.cluster (evenClusterIndex g (validVertexIncidentIndex hg x)) := by
  intro v hv
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical] at hv
  exact R.verticalAdjPath_vertexSet_subset_incidentCluster hg hvertical
    ((R.verticalAdjPath hvertical).dropLast_vertexSet_subset hv)

/-- A vertical certificate edge's allocated drop-last path can meet a stitched
row only at the source endpoint image. -/
theorem validSparseGridPathCertificate_vertical_dropLast_mem_row_eq_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1)
    {a : R.rows.Index} {v : V}
    (hvPath :
      v ∈ ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)).dropLast.vertexSet)
    (hvRow : v ∈ (R.rows.path a).vertexSet) :
    v = R.validVertexImage hg x := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical] at hvPath
  exact R.verticalAdjPath_dropLast_mem_row_eq_source hg hvertical hvPath hvRow

/-- No non-source endpoint image lies in the allocated drop-last part of a
vertical certificate edge. -/
theorem validSparseGridPathCertificate_validVertexImage_not_mem_vertical_dropLast_of_ne_source
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1)
    (hzx : z ≠ x) :
    R.validVertexImage hg z ∉
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical]
  exact R.validVertexImage_not_mem_verticalAdjPath_dropLast_of_ne_source hg
    hvertical hzx

/-- Vertical certificate edges satisfy the endpoint-exclusion hypothesis used
by the internal drop-last separation criterion. -/
theorem validSparseGridPathCertificate_vertical_nonendpoint_not_mem_dropLast
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1)
    (_hrank :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hzx : z ≠ x) (_hzy : z ≠ y) :
    R.validVertexImage hg z ∉
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)).dropLast.vertexSet :=
  R.validSparseGridPathCertificate_validVertexImage_not_mem_vertical_dropLast_of_ne_source
    hg hvertical hzx

/-- Every certificate edge excludes all valid sparse-grid images other than
its endpoints from its allocated drop-last path. -/
theorem validSparseGridPathCertificate_nonendpoint_not_mem_dropLast
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y)
    (hrank :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    R.validVertexImage hg z ∉
      ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet := by
  change SparseGrid.Adj x.1 y.1 at hxy
  rcases hxy with hhorizontal | hvertical
  · simpa using
      R.validSparseGridPathCertificate_horizontal_nonendpoint_not_mem_dropLast
        hg hhorizontal hrank hzx hzy
  · simpa using
      R.validSparseGridPathCertificate_vertical_nonendpoint_not_mem_dropLast
        hg hvertical hrank hzx hzy

/-- Certificate-level mixed disjointness for a vertical and a horizontal
allocated path whose source vertices lie on different stitched rows. -/
theorem validSparseGridPathCertificate_vertical_horizontal_dropLast_disjoint_of_source_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1)
    (hhorizontal : SparseGrid.HorizontalAdj z.1 t.1)
    (hrow : x.1.row ≠ z.1.row) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inl hhorizontal)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical,
    R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal]
  exact R.verticalAdjPath_dropLast_disjoint_horizontalAdjPath_dropLast_of_source_row_ne
    hg hvertical hhorizontal hrow

/-- Certificate-level mixed disjointness for a horizontal and a vertical
allocated path whose source vertices lie on different stitched rows. -/
theorem validSparseGridPathCertificate_horizontal_vertical_dropLast_disjoint_of_source_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1)
    (hvertical : SparseGrid.VerticalAdj z.1 t.1)
    (hrow : x.1.row ≠ z.1.row) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inr hvertical)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal,
    R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical]
  exact R.horizontalAdjPath_dropLast_disjoint_verticalAdjPath_dropLast_of_source_row_ne
    hg hhorizontal hvertical hrow

/-- Certificate-level mixed disjointness for a vertical and a horizontal
allocated path with distinct allocated sources. -/
theorem validSparseGridPathCertificate_vertical_horizontal_dropLast_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1)
    (hhorizontal : SparseGrid.HorizontalAdj z.1 t.1)
    (hxz : x ≠ z) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inl hhorizontal)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical,
    R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal]
  exact R.verticalAdjPath_dropLast_disjoint_horizontalAdjPath_dropLast
    hg hvertical hhorizontal hxz

/-- Certificate-level mixed disjointness for a horizontal and a vertical
allocated path with distinct allocated sources. -/
theorem validSparseGridPathCertificate_horizontal_vertical_dropLast_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hhorizontal : SparseGrid.HorizontalAdj x.1 y.1)
    (hvertical : SparseGrid.VerticalAdj z.1 t.1)
    (hxz : x ≠ z) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inl hhorizontal)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inr hvertical)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hhorizontal,
    R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical]
  exact R.horizontalAdjPath_dropLast_disjoint_verticalAdjPath_dropLast
    hg hhorizontal hvertical hxz

/-- Certificate-level disjointness for two horizontal allocated paths whose
source vertices lie on different stitched rows. -/
theorem validSparseGridPathCertificate_horizontal_dropLast_disjoint_of_source_row_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hzt : SparseGrid.HorizontalAdj z.1 t.1)
    (hrow : x.1.row ≠ z.1.row) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inl hxy)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inl hzt)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hxy,
    R.validSparseGridPathCertificate_edgePath_of_horizontal hg hzt]
  exact R.horizontalAdjPath_dropLast_disjoint_of_source_row_ne hg hxy hzt hrow

/-- Certificate-level disjointness for two vertical allocated paths whose
source endpoints are incident with different even clusters. -/
theorem validSparseGridPathCertificate_vertical_dropLast_disjoint_of_incidentIndex_ne
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hzt : SparseGrid.VerticalAdj z.1 t.1)
    (hidx : validVertexIncidentIndex hg x ≠ validVertexIncidentIndex hg z) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inr hxy)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inr hzt)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hxy,
    R.validSparseGridPathCertificate_edgePath_of_vertical hg hzt]
  exact R.verticalAdjPath_dropLast_disjoint_of_incidentIndex_ne hg hxy hzt hidx

/-- Certificate-level disjointness for two rank-oriented vertical allocated
paths with distinct sources. -/
theorem validSparseGridPathCertificate_vertical_dropLast_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.VerticalAdj x.1 y.1)
    (hzt : SparseGrid.VerticalAdj z.1 t.1)
    (hrankxy :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hrankzt :
      ValidSparseGridPathCertificate.validVertexRank z <
        ValidSparseGridPathCertificate.validVertexRank t)
    (hxz : x ≠ z) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inr hxy)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inr hzt)).dropLast.vertexSet := by
  by_cases hidx : validVertexIncidentIndex hg x = validVertexIncidentIndex hg z
  · exact False.elim
      (hxz (eq_of_verticalAdj_incidentIndex_eq_of_rank_lt hg hxy hzt hidx
        hrankxy hrankzt))
  · exact R.validSparseGridPathCertificate_vertical_dropLast_disjoint_of_incidentIndex_ne
      hg hxy hzt hidx

/-- Certificate-level disjointness for two rank-oriented horizontal allocated
paths with distinct sources. -/
theorem validSparseGridPathCertificate_horizontal_dropLast_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : SparseGrid.HorizontalAdj x.1 y.1)
    (hzt : SparseGrid.HorizontalAdj z.1 t.1)
    (hrankxy :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hrankzt :
      ValidSparseGridPathCertificate.validVertexRank z <
        ValidSparseGridPathCertificate.validVertexRank t)
    (hxz : x ≠ z) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj x y from Or.inl hxy)).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath
        (show (SparseGrid.validGraph g).Adj z t from Or.inl hzt)).dropLast.vertexSet := by
  rw [R.validSparseGridPathCertificate_edgePath_of_horizontal hg hxy,
    R.validSparseGridPathCertificate_edgePath_of_horizontal hg hzt]
  exact R.horizontalAdjPath_dropLast_disjoint hg hxy hzt hrankxy hrankzt hxz

/-- All rank-oriented allocated paths in the stitched-row sparse-grid
certificate have pairwise disjoint drop-last vertex sets, except when their
allocated source is the same. -/
theorem validSparseGridPathCertificate_dropLast_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y z t : SparseGrid.ValidVertex g}
    (hxy : (SparseGrid.validGraph g).Adj x y)
    (hzt : (SparseGrid.validGraph g).Adj z t)
    (hrankxy :
      ValidSparseGridPathCertificate.validVertexRank x <
        ValidSparseGridPathCertificate.validVertexRank y)
    (hrankzt :
      ValidSparseGridPathCertificate.validVertexRank z <
        ValidSparseGridPathCertificate.validVertexRank t)
    (hxz : x ≠ z) :
    Disjoint
      ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet
      ((R.validSparseGridPathCertificate hg).edgePath hzt).dropLast.vertexSet := by
  change SparseGrid.Adj x.1 y.1 at hxy
  change SparseGrid.Adj z.1 t.1 at hzt
  rcases hxy with hxyH | hxyV
  · rcases hzt with hztH | hztV
    · simpa using
        R.validSparseGridPathCertificate_horizontal_dropLast_disjoint
          hg hxyH hztH hrankxy hrankzt hxz
    · simpa using
        R.validSparseGridPathCertificate_horizontal_vertical_dropLast_disjoint
          hg hxyH hztV hxz
  · rcases hzt with hztH | hztV
    · simpa using
        R.validSparseGridPathCertificate_vertical_horizontal_dropLast_disjoint
          hg hxyV hztH hxz
    · simpa using
        R.validSparseGridPathCertificate_vertical_dropLast_disjoint
          hg hxyV hztV hrankxy hrankzt hxz

/-- Forward vertical certificate edges are exactly the corresponding bridge
path. -/
theorem validSparseGridPathCertificate_edgePath_eq_vertical_forward
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1)
    (hforward :
      x.1.col = y.1.col ∧
        x.1.row.1 + 1 = y.1.row.1 ∧
          x.1.port = true ∧ y.1.port = false) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)) =
        R.verticalSparseEdgePath x.1.row x.1.col (by
          rw [hforward.2.1]
          exact y.1.row.2) := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical,
    R.verticalAdjPath_eq_forward hvertical hforward]

/-- Backward vertical certificate edges are exactly the reverse of the
corresponding bridge path. -/
theorem validSparseGridPathCertificate_edgePath_eq_vertical_backward
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    {x y : SparseGrid.ValidVertex g}
    (hvertical : SparseGrid.VerticalAdj x.1 y.1)
    (hback :
      y.1.col = x.1.col ∧
        y.1.row.1 + 1 = x.1.row.1 ∧
          y.1.port = true ∧ x.1.port = false) :
    ((R.validSparseGridPathCertificate hg).edgePath
      (show (SparseGrid.validGraph g).Adj x y from Or.inr hvertical)) =
        (R.verticalSparseEdgePath y.1.row y.1.col (by
          rw [hback.2.1]
          exact x.1.row.2)).reverse := by
  rw [R.validSparseGridPathCertificate_edgePath_of_vertical hg hvertical,
    R.verticalAdjPath_eq_backward hvertical hback]

/-- Build an allocated minor certificate from the explicit branch-set
obligations left after the row-and-bridge path construction. -/
noncomputable def validSparseGridAllocatedMinorCertificate
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branchSet : SparseGrid.ValidVertex g → Finset V)
    (image_mem_branch :
      ∀ x : SparseGrid.ValidVertex g,
        R.validVertexImage hg x ∈ branchSet x)
    (branch_connected :
      ∀ x : SparseGrid.ValidVertex g,
        (G.induce {v : V | v ∈ branchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (branchSet x) (branchSet y))
    (edge_penultimate_mem_branch :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          ((R.validSparseGridPathCertificate hg).edgePath hxy).penultimate ∈
            branchSet x) :
    ValidSparseGridAllocatedMinorCertificate G g where
  toValidSparseGridPathCertificate := R.validSparseGridPathCertificate hg
  image_injective := R.validVertexImage_injective hg
  branchSet := branchSet
  image_mem_branch := image_mem_branch
  branch_connected := branch_connected
  branch_disjoint := branch_disjoint
  edge_penultimate_mem_branch := edge_penultimate_mem_branch

/-- Appendix C.1's remaining assembly target: the stitched rows realize the
valid sparse grid `G*` as a minor of the host graph. -/
def RealizesValidSparseGrid {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (_R : StitchedRows G g w P) : Prop :=
  IsMinor (SparseGrid.validGraph g) G

/-- Build a direct sparse-grid minor certificate from the concrete branch-set
obligations left after the row-and-bridge path construction. -/
noncomputable def validSparseGridMinorCertificate
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branchSet : SparseGrid.ValidVertex g → Finset V)
    (image_mem_branch :
      ∀ x : SparseGrid.ValidVertex g,
        R.validVertexImage hg x ∈ branchSet x)
    (branch_connected :
      ∀ x : SparseGrid.ValidVertex g,
        (G.induce {v : V | v ∈ branchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (branchSet x) (branchSet y))
    (adjacent :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        (SparseGrid.validGraph g).Adj x y →
          ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, G.Adj u v) :
    ValidSparseGridMinorCertificate G g where
  toValidSparseGridPathCertificate := R.validSparseGridPathCertificate hg
  branchSet := branchSet
  image_mem_branch := image_mem_branch
  branch_connected := branch_connected
  branch_disjoint := branch_disjoint
  adjacent := adjacent

/-- The direct branch-set obligations are sufficient to realize the valid sparse
grid as a minor. -/
theorem realizesValidSparseGrid_of_branchSets
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branchSet : SparseGrid.ValidVertex g → Finset V)
    (image_mem_branch :
      ∀ x : SparseGrid.ValidVertex g,
        R.validVertexImage hg x ∈ branchSet x)
    (branch_connected :
      ∀ x : SparseGrid.ValidVertex g,
        (G.induce {v : V | v ∈ branchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (branchSet x) (branchSet y))
    (adjacent :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        (SparseGrid.validGraph g).Adj x y →
          ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, G.Adj u v) :
    R.RealizesValidSparseGrid :=
  (R.validSparseGridMinorCertificate hg branchSet image_mem_branch
    branch_connected branch_disjoint adjacent).isMinor

/-- The direct sparse-grid branch-set obligations imply the desired grid minor. -/
theorem containsGridMinor_of_branchSets
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branchSet : SparseGrid.ValidVertex g → Finset V)
    (image_mem_branch :
      ∀ x : SparseGrid.ValidVertex g,
        R.validVertexImage hg x ∈ branchSet x)
    (branch_connected :
      ∀ x : SparseGrid.ValidVertex g,
        (G.induce {v : V | v ∈ branchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (branchSet x) (branchSet y))
    (adjacent :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        (SparseGrid.validGraph g).Adj x y →
          ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, G.Adj u v) :
    ContainsGridMinor G g :=
  SparseGrid.validContainsGridMinor_of_minor
    (R.realizesValidSparseGrid_of_branchSets hg branchSet image_mem_branch
      branch_connected branch_disjoint adjacent)

/-- For the fixed orientation-aware allocation of the stitched-row path
certificate, pairwise branch-set disjointness is the only remaining obligation
for realizing the valid sparse grid. -/
theorem realizesValidSparseGrid_of_orientedBranchSet_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y →
          Disjoint ((R.validSparseGridPathCertificate hg).orientedBranchSet x)
            ((R.validSparseGridPathCertificate hg).orientedBranchSet y)) :
    R.RealizesValidSparseGrid :=
  (R.validSparseGridPathCertificate hg).isMinor_of_orientedBranchSet_disjoint
    (R.validVertexImage_injective hg) branch_disjoint

/-- The fixed orientation-aware allocation of the stitched-row path certificate
gives the desired grid minor once its branch sets are pairwise disjoint. -/
theorem containsGridMinor_of_orientedBranchSet_disjoint
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y →
          Disjoint ((R.validSparseGridPathCertificate hg).orientedBranchSet x)
            ((R.validSparseGridPathCertificate hg).orientedBranchSet y)) :
    ContainsGridMinor G g :=
  SparseGrid.validContainsGridMinor_of_minor
    (R.realizesValidSparseGrid_of_orientedBranchSet_disjoint hg branch_disjoint)

/-- Endpoint/drop-last separation for the stitched-row path certificate implies
that the valid sparse grid is realized as a minor. -/
theorem realizesValidSparseGrid_of_dropLast_separated
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (endpoint_not_mem_dropLast :
      ∀ ⦃x y z : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            z ≠ x →
              R.validVertexImage hg z ∉
                ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet)
    (dropLast_disjoint :
      ∀ ⦃x y z t : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y)
        (hzt : (SparseGrid.validGraph g).Adj z t),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            ValidSparseGridPathCertificate.validVertexRank z <
                ValidSparseGridPathCertificate.validVertexRank t →
              x ≠ z →
                Disjoint
                  ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet
                  ((R.validSparseGridPathCertificate hg).edgePath hzt).dropLast.vertexSet) :
    R.RealizesValidSparseGrid := by
  let C := R.validSparseGridPathCertificate hg
  exact R.realizesValidSparseGrid_of_orientedBranchSet_disjoint hg
    (C.orientedBranchSet_disjoint_of_dropLast_separated
      (R.validVertexImage_injective hg) endpoint_not_mem_dropLast dropLast_disjoint)

/-- Endpoint/drop-last separation for the stitched-row path certificate implies
the desired grid minor. -/
theorem containsGridMinor_of_dropLast_separated
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (endpoint_not_mem_dropLast :
      ∀ ⦃x y z : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            z ≠ x →
              R.validVertexImage hg z ∉
                ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet)
    (dropLast_disjoint :
      ∀ ⦃x y z t : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y)
        (hzt : (SparseGrid.validGraph g).Adj z t),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            ValidSparseGridPathCertificate.validVertexRank z <
                ValidSparseGridPathCertificate.validVertexRank t →
              x ≠ z →
                Disjoint
                  ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet
                  ((R.validSparseGridPathCertificate hg).edgePath hzt).dropLast.vertexSet) :
    ContainsGridMinor G g :=
  SparseGrid.validContainsGridMinor_of_minor
    (R.realizesValidSparseGrid_of_dropLast_separated hg endpoint_not_mem_dropLast
      dropLast_disjoint)

/-- The sharper endpoint/drop-last separation criterion for the stitched-row
path certificate: endpoint images that are actual targets of allocated paths are
handled automatically, so the supplied endpoint-exclusion hypothesis only covers
non-endpoints. -/
theorem realizesValidSparseGrid_of_internal_dropLast_separated
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (nonendpoint_not_mem_dropLast :
      ∀ ⦃x y z : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            z ≠ x → z ≠ y →
              R.validVertexImage hg z ∉
                ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet)
    (dropLast_disjoint :
      ∀ ⦃x y z t : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y)
        (hzt : (SparseGrid.validGraph g).Adj z t),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            ValidSparseGridPathCertificate.validVertexRank z <
                ValidSparseGridPathCertificate.validVertexRank t →
              x ≠ z →
                Disjoint
                  ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet
                  ((R.validSparseGridPathCertificate hg).edgePath hzt).dropLast.vertexSet) :
    R.RealizesValidSparseGrid := by
  let C := R.validSparseGridPathCertificate hg
  exact R.realizesValidSparseGrid_of_orientedBranchSet_disjoint hg
    (C.orientedBranchSet_disjoint_of_internal_dropLast_separated
      (R.validVertexImage_injective hg) nonendpoint_not_mem_dropLast dropLast_disjoint)

/-- The sharper endpoint/drop-last separation criterion implies the desired grid
minor. -/
theorem containsGridMinor_of_internal_dropLast_separated
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (nonendpoint_not_mem_dropLast :
      ∀ ⦃x y z : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            z ≠ x → z ≠ y →
              R.validVertexImage hg z ∉
                ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet)
    (dropLast_disjoint :
      ∀ ⦃x y z t : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y)
        (hzt : (SparseGrid.validGraph g).Adj z t),
          ValidSparseGridPathCertificate.validVertexRank x <
              ValidSparseGridPathCertificate.validVertexRank y →
            ValidSparseGridPathCertificate.validVertexRank z <
                ValidSparseGridPathCertificate.validVertexRank t →
              x ≠ z →
                Disjoint
                  ((R.validSparseGridPathCertificate hg).edgePath hxy).dropLast.vertexSet
                  ((R.validSparseGridPathCertificate hg).edgePath hzt).dropLast.vertexSet) :
    ContainsGridMinor G g :=
  SparseGrid.validContainsGridMinor_of_minor
    (R.realizesValidSparseGrid_of_internal_dropLast_separated hg
      nonendpoint_not_mem_dropLast dropLast_disjoint)

/-- The concrete row-and-bridge path certificate extracted from stitched rows
realizes the valid sparse grid as a minor. -/
theorem realizesValidSparseGrid
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g) :
    R.RealizesValidSparseGrid := by
  exact R.realizesValidSparseGrid_of_internal_dropLast_separated hg
    (by
      intro x y z hxy hrank hzx hzy
      exact R.validSparseGridPathCertificate_nonendpoint_not_mem_dropLast
        hg hxy hrank hzx hzy)
    (by
      intro x y z t hxy hzt hrankxy hrankzt hxz
      exact R.validSparseGridPathCertificate_dropLast_disjoint
        hg hxy hzt hrankxy hrankzt hxz)

/-- Stitched rows of the Appendix C.1 form contain the canonical `g x g` grid
minor. -/
theorem containsGridMinor
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g) :
    ContainsGridMinor G g :=
  SparseGrid.validContainsGridMinor_of_minor (R.realizesValidSparseGrid hg)

/-- The remaining concrete branch-set obligations are sufficient to realize
the valid sparse grid as a minor. -/
theorem realizesValidSparseGrid_of_allocatedBranchSets
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branchSet : SparseGrid.ValidVertex g → Finset V)
    (image_mem_branch :
      ∀ x : SparseGrid.ValidVertex g,
        R.validVertexImage hg x ∈ branchSet x)
    (branch_connected :
      ∀ x : SparseGrid.ValidVertex g,
        (G.induce {v : V | v ∈ branchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (branchSet x) (branchSet y))
    (edge_penultimate_mem_branch :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          ((R.validSparseGridPathCertificate hg).edgePath hxy).penultimate ∈
            branchSet x) :
    R.RealizesValidSparseGrid :=
  (R.validSparseGridAllocatedMinorCertificate hg branchSet image_mem_branch
    branch_connected branch_disjoint edge_penultimate_mem_branch).isMinor

/-- The allocated branch-set obligations imply the desired grid minor. -/
theorem containsGridMinor_of_allocatedBranchSets
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hg : 2 ≤ g)
    (branchSet : SparseGrid.ValidVertex g → Finset V)
    (image_mem_branch :
      ∀ x : SparseGrid.ValidVertex g,
        R.validVertexImage hg x ∈ branchSet x)
    (branch_connected :
      ∀ x : SparseGrid.ValidVertex g,
        (G.induce {v : V | v ∈ branchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄,
        x ≠ y → Disjoint (branchSet x) (branchSet y))
    (edge_penultimate_mem_branch :
      ∀ ⦃x y : SparseGrid.ValidVertex g⦄
        (hxy : (SparseGrid.validGraph g).Adj x y),
          ((R.validSparseGridPathCertificate hg).edgePath hxy).penultimate ∈
            branchSet x) :
    ContainsGridMinor G g :=
  SparseGrid.validContainsGridMinor_of_minor
    (R.realizesValidSparseGrid_of_allocatedBranchSets hg branchSet
      image_mem_branch branch_connected branch_disjoint edge_penultimate_mem_branch)

/-- Once the stitched rows have been assembled into the valid sparse grid, the
canonical `g x g` grid minor follows from the formalized `G*` contraction. -/
theorem containsGridMinor_of_realizesValidSparseGrid
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (hR : R.RealizesValidSparseGrid) :
    ContainsGridMinor G g :=
  SparseGrid.validContainsGridMinor_of_minor hR

/-- Forget the localization of the bridges. -/
theorem hasPairwiseBridges {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    {P : PathOfSetsSystem G (2 * g * (g - 1)) w}
    (R : StitchedRows G g w P) (i : Fin (g * (g - 1))) :
    R.rows.HasPairwiseBridges := by
  intro a b hab
  rcases R.bridge_in_even_cluster i hab with ⟨β, _hβ⟩
  exact ⟨β⟩

end StitchedRows

/-- Chekuri--Chuzhoy Corollary 3.2, specialized to the parameters used in the
Corollary 3.3 path-of-sets-to-grid step, as an explicit proof input.

This is the paper-level dichotomy before the stitched-row branch is assembled
into a valid sparse grid.  Keeping it as a named input lets downstream
composition theorems avoid depending on the broad contract declaration once a
full formal proof of Corollary 3.2 is supplied. -/
def Corollary32Input : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ},
      2 ≤ g →
        (P : StrongPathOfSetsSystem G
          (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) →
          ContainsGridMinor G g ∨
            Nonempty
              (StitchedRows G g (16 * g ^ 2 + 10 * g)
                P.toPathOfSetsSystem)

/-- Chekuri--Chuzhoy Corollary 3.2 follows from the local Theorem 3.1 input
and the remaining row-stitching input.

The proof formalizes the first half of Appendix C: apply the local routing
theorem in each even one-based cluster.  If any application returns a grid
minor, the corollary is done; otherwise the collected local outputs are passed
to the stitching input. -/
theorem corollary32Input_of_localRoutingInput_and_stitchingInput
    (hlocal : LocalRoutingInput.{u}) (hstitch : StitchingInput.{u}) :
    Corollary32Input.{u} := by
  intro V hVfin hVdec G g hg P
  letI : Fintype V := hVfin
  letI : DecidableEq V := hVdec
  rcases gridMinor_or_evenClusterOutputs_of_localRoutingInput_corollary33Width
      hlocal G hg P with hgrid | houtputs
  · exact Or.inl hgrid
  · rcases houtputs with ⟨E⟩
    exact Or.inr (hstitch G hg P E (StitchingPieces.canonicalOfTwoLe P E hg))

/-- Cluster-faithful variant of
`corollary32Input_of_localRoutingInput_and_stitchingInput`.

This matches Chekuri--Chuzhoy Theorem 3.1 more closely: each local routing
call receives the connectedness of the current path-of-sets cluster from the
path-of-sets system. -/
theorem corollary32Input_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : LocalRoutingClusterInput.{u}) (hstitch : StitchingInput.{u}) :
    Corollary32Input.{u} := by
  intro V hVfin hVdec G g hg P
  letI : Fintype V := hVfin
  letI : DecidableEq V := hVdec
  rcases gridMinor_or_evenClusterOutputs_of_localRoutingClusterInput_corollary33Width
      hlocal G hg P with hgrid | houtputs
  · exact Or.inl hgrid
  · rcases houtputs with ⟨E⟩
    exact Or.inr (hstitch G hg P E (StitchingPieces.canonicalOfTwoLe P E hg))


/-- A strong path-of-sets system whose length and width dominate the
Chekuri--Chuzhoy Corollary 3.3 thresholds contains a `g x g` grid minor. -/
theorem containsGridMinor_of_strongPathOfSets_ge_of_corollary32Input
    (hinput : Corollary32Input.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (hg : 2 ≤ g)
    (hell : 2 * g * (g - 1) ≤ ell)
    (hw : 16 * g ^ 2 + 10 * g ≤ w)
    (P : StrongPathOfSetsSystem G ell w) :
    ContainsGridMinor G g := by
  have hell_pos : 0 < 2 * g * (g - 1) := by
    exact Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2)
      (lt_of_lt_of_le (by decide : 0 < 2) hg)) (Nat.sub_pos_of_lt hg)
  have hw_pos : 0 < 16 * g ^ 2 + 10 * g := by
    exact Nat.add_pos_left
      (Nat.mul_pos (by decide : 0 < 16)
        (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))) _
  let P' := (P.restrictLength hell_pos hell).restrictWidth hw_pos hw
  rcases hinput G hg P' with hgrid | hrows
  · exact hgrid
  · rcases hrows with ⟨R⟩
    exact R.containsGridMinor hg

/-- Same path-of-sets-to-grid theorem, using the split Chekuri--Chuzhoy inputs:
local routing inside every even cluster plus the remaining row stitching. -/
theorem containsGridMinor_of_strongPathOfSets_ge_of_localRoutingInput_and_stitchingInput
    (hlocal : LocalRoutingInput.{u}) (hstitch : StitchingInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (hg : 2 ≤ g)
    (hell : 2 * g * (g - 1) ≤ ell)
    (hw : 16 * g ^ 2 + 10 * g ≤ w)
    (P : StrongPathOfSetsSystem G ell w) :
    ContainsGridMinor G g :=
  containsGridMinor_of_strongPathOfSets_ge_of_corollary32Input
    (corollary32Input_of_localRoutingInput_and_stitchingInput hlocal hstitch)
    G hg hell hw P

/-- Same path-of-sets-to-grid theorem, using the cluster-faithful split
Chekuri--Chuzhoy inputs: local routing inside every connected even cluster plus
the remaining row stitching. -/
theorem containsGridMinor_of_strongPathOfSets_ge_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : LocalRoutingClusterInput.{u}) (hstitch : StitchingInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (hg : 2 ≤ g)
    (hell : 2 * g * (g - 1) ≤ ell)
    (hw : 16 * g ^ 2 + 10 * g ≤ w)
    (P : StrongPathOfSetsSystem G ell w) :
    ContainsGridMinor G g :=
  containsGridMinor_of_strongPathOfSets_ge_of_corollary32Input
    (corollary32Input_of_localRoutingClusterInput_and_stitchingInput
      hlocal hstitch)
    G hg hell hw P


end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
