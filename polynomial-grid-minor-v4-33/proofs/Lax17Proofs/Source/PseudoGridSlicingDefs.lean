import Lax17Proofs.Source.PseudoGrid

namespace Lax17Proofs

universe u v w

/-!
# Definitions for pseudo-grid slicing

This file contains definition-only material for Section 4.2 of Chuzhoy--Tan:
unique linkages and `M`-slicings of a linkage.  The contract file states the
paper's Section 4.2 results using these definitions, and the proof file proves
the currently formalized self-contained parts without importing the contract.
-/

namespace SimpleGraph


namespace PathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- The indices of paths in a packing that meet a finite vertex set. -/
noncomputable def hitSet (P : PathPacking G S T) (U : Finset V) :
    Finset P.Index := by
  classical
  exact Finset.univ.filter fun i => ¬ Disjoint (P.path i).vertexSet U

theorem mem_hitSet (P : PathPacking G S T) (U : Finset V) (i : P.Index) :
    i ∈ P.hitSet U ↔ ¬ Disjoint (P.path i).vertexSet U := by
  classical
  simp [hitSet]

end PathPacking

namespace PerfectPathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B : Finset V}

/-- The linkage uses every vertex of the ambient graph.  In Section 4.2 this
is applied after replacing the graph by `H''`, whose vertices are exactly the
vertices of the row linkage. -/
def SpansVertices (R : PerfectPathPacking G A B) : Prop :=
  ∀ v : V, v ∈ R.toPathPacking.vertexSet

/-- The perfect linkage is unique, up to its edge set.  This matches the form
needed by the Robertson--Seymour slicing lemma: every perfect `A`--`B` linkage
in the same graph has the same trace. -/
def IsUniqueLinkage (R : PerfectPathPacking G A B) : Prop :=
  R.SpansVertices ∧
    ∀ R' : PerfectPathPacking G A B,
      R'.toPathPacking.edgeSet = R.toPathPacking.edgeSet

end PerfectPathPacking

/-- An `M`-slicing of an oriented perfect linkage.  For each linkage path,
`cut r 0` is the source, `cut r M` is the target, and the cut vertices are
monotone along the orientation of that path. -/
structure PathSlicing {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B : Finset V} (R : PerfectPathPacking G A B) (M : ℕ) where
  /-- Cut vertex number `t` on row path `r`. -/
  cut : R.Index → Fin (M + 1) → V
  /-- Every cut vertex lies on its row path. -/
  cut_mem : ∀ r t, cut r t ∈ (R.path r).vertexSet
  /-- The first cut is the `A`-endpoint of the row path. -/
  cut_zero : ∀ r, cut r 0 = (R.path r).source
  /-- The last cut is the `B`-endpoint of the row path. -/
  cut_last : ∀ r, cut r (Fin.last M) = (R.path r).target
  /-- Cut vertices appear in the declared order along every row path. -/
  cut_monotone :
    ∀ r ⦃s t : Fin (M + 1)⦄, s ≤ t →
      (R.path r).Before (cut r s) (cut r t)

namespace PathSlicing

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {M : ℕ}
variable {R : PerfectPathPacking G A B}

/-- A path crosses the threshold `t` of a ranking if it contains vertices on
both sides of the cut `{v | rank v < t}` / `{v | t ≤ rank v}`.

This is the form used in Lemma 4.5: after deleting the separator `S_t`, there
is no path connecting the lower side to the upper side.  The lower/upper
vertices need not be the endpoints of the path. -/
def GraphPathCrossesRankThreshold (rank : V → ℕ) (t : ℕ)
    (P : GraphPath G) : Prop :=
  ∃ y ∈ P.vertexSet, ∃ z ∈ P.vertexSet, rank y < t ∧ t ≤ rank z

/-- The formal output of Chuzhoy--Tan Lemma 4.5.

The paper states this as a bijection `μ : V(G) -> {1, ..., |V(G)|}`.  We use a
zero-based ranking into `ℕ`; injectivity plus `rank_lt_card` is the same finite
data.  The separator field says that the threshold separator `S_t` blocks every
path whose endpoints are on different sides of the threshold. -/
structure LinkageOrdering
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B : Finset V} (R : PerfectPathPacking G A B) where
  /-- The zero-based Robertson--Seymour topological order. -/
  rank : V → ℕ
  /-- The ranking is injective. -/
  rank_injective : Function.Injective rank
  /-- Every rank lies below the number of vertices. -/
  rank_lt_card : ∀ v : V, rank v < Fintype.card V
  /-- Along each linkage path, strict path order implies strict rank order. -/
  row_strict :
    ∀ r ⦃u v : V⦄,
      u ∈ (R.path r).vertexSet →
        v ∈ (R.path r).vertexSet →
          (R.path r).Before u v →
            u ≠ v →
              rank u < rank v
  /-- The unique row vertex selected for threshold `t`; in the paper this is
  the first vertex of the row whose `μ`-value is at least `t`, or the row's
  last vertex if no such vertex exists.  We use zero-based ranks, so `t = 0`
  gives the source endpoint and `t = |V|` gives the target endpoint. -/
  separatorVertex : ℕ → R.Index → V
  /-- The selected threshold vertex lies on its row. -/
  separatorVertex_mem :
    ∀ t r, separatorVertex t r ∈ (R.path r).vertexSet
  /-- Threshold `0` selects the first endpoint of every row. -/
  separatorVertex_zero :
    ∀ r, separatorVertex 0 r = (R.path r).source
  /-- Threshold `|V|` selects the last endpoint of every row. -/
  separatorVertex_card :
    ∀ r, separatorVertex (Fintype.card V) r = (R.path r).target
  /-- Vertices with rank below the threshold occur before the selected
  threshold vertex on their row. -/
  below_before_separator :
    ∀ t r ⦃v : V⦄,
      v ∈ (R.path r).vertexSet →
        rank v < t →
          (R.path r).Before v (separatorVertex t r)
  /-- Vertices with rank at or above the threshold occur after the selected
  threshold vertex on their row. -/
  separator_before_above :
    ∀ t r ⦃v : V⦄,
      v ∈ (R.path r).vertexSet →
        t ≤ rank v →
          (R.path r).Before (separatorVertex t r) v
  /-- Threshold vertices are monotone along each row. -/
  separatorVertex_monotone :
    ∀ r ⦃s t : ℕ⦄, s ≤ t →
      (R.path r).Before (separatorVertex s r) (separatorVertex t r)
  /-- The threshold separator `S_t`. -/
  separatorSet : ℕ → Finset V
  /-- The threshold separator is exactly the set of selected row vertices. -/
  separatorSet_eq :
    ∀ t, separatorSet t =
      Finset.univ.image fun r : R.Index => separatorVertex t r
  /-- Later threshold separators are contained in the earlier separator plus
  the earlier upper side.  This is the set-theoretic fact used in
  Observation 4.7 to prove monotonicity of `Q1(S_t)`. -/
  separatorSet_subset_separator_union_above :
    ∀ ⦃s t : ℕ⦄, s ≤ t →
      separatorSet t ⊆ separatorSet s ∪
        (Finset.univ.filter fun v : V => s ≤ rank v)
  /-- Advancing the threshold by one can only remove row-separator vertices
  whose rank is exactly the old threshold.  In the paper's construction this
  is immediate from choosing, on each row, the first vertex whose order is at
  least the threshold.  It is the structural input behind Observation 4.7's
  one-step growth bound for `Q1(S_t)`. -/
  separatorSet_sdiff_succ_subset_rankLevel :
    ∀ ⦃t : ℕ⦄, t < Fintype.card V →
      separatorSet t \ separatorSet (t + 1) ⊆
        (Finset.univ.filter fun v : V => rank v = t)
  /-- Every threshold separator has at most one vertex from each row path. -/
  separator_card_le : ∀ t : ℕ, (separatorSet t).card ≤ R.card
  /-- The separator blocks all paths that contain vertices on both sides of the
  threshold. -/
  separator_blocks :
    ∀ (t : ℕ) (P : GraphPath G),
      GraphPathCrossesRankThreshold rank t P →
        ∃ v ∈ P.vertexSet, v ∈ separatorSet t

namespace LinkageOrdering

variable {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {R : PerfectPathPacking G A B}

/-- The vertices ranked before threshold `t`. -/
noncomputable def belowSet (theta : LinkageOrdering R) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => theta.rank v < t

/-- The vertices ranked at or after threshold `t`. -/
noncomputable def aboveSet (theta : LinkageOrdering R) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => t ≤ theta.rank v

/-- The paths hitting the threshold separator `S_t`; this is `Q0(S_t)` in the
paper. -/
noncomputable def qZero (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) : Finset Qpack.Index :=
  Qpack.hitSet (theta.separatorSet t)

/-- Paths disjoint from `S_t` that hit the lower side `Y_t`; this is `Q1(S_t)`
in the paper's equivalent definition. -/
noncomputable def qOne (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) : Finset Qpack.Index :=
  Qpack.hitSet (theta.belowSet t) \ theta.qZero Qpack t

/-- Paths disjoint from `S_t` that hit the upper side `Z_t`; this is
`Q2(S_t)` in the paper's equivalent definition. -/
noncomputable def qTwo (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) : Finset Qpack.Index :=
  Qpack.hitSet (theta.aboveSet t) \ theta.qZero Qpack t

end LinkageOrdering

/-- A monotone sequence of Robertson--Seymour thresholds used to turn a
linkage ordering into a concrete path slicing.  Thresholds are zero-based:
`0` gives the source cut and `|V|` gives the target cut. -/
structure ThresholdSequence
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B : Finset V} (R : PerfectPathPacking G A B)
    (theta : LinkageOrdering R) (M : ℕ) where
  /-- The threshold used for each cut position. -/
  threshold : Fin (M + 1) → ℕ
  /-- The first threshold selects the source endpoint of every row. -/
  threshold_zero : threshold 0 = 0
  /-- The final threshold selects the target endpoint of every row. -/
  threshold_last : threshold (Fin.last M) = Fintype.card V
  /-- Thresholds are nondecreasing. -/
  threshold_monotone : ∀ ⦃s t : Fin (M + 1)⦄, s ≤ t →
    threshold s ≤ threshold t

/-- Every path in `Qpack` intersects at least one path of the linkage `R`.
This is the intersection hypothesis in Chuzhoy--Tan Theorem 4.6. -/
def PathPackingIntersectsLinkage
    (R : PerfectPathPacking G A B) (Qpack : PathPacking G S T) : Prop :=
  ∀ q : Qpack.Index,
    ∃ r : R.Index,
      ¬ Disjoint (Qpack.path q).vertexSet (R.path r).vertexSet

/-- The directed dependency relation from Appendix B of Chuzhoy--Tan.

`LinkageDependency R u v` means that the auxiliary directed graph used to prove
Lemma 4.5 contains the directed edge `u -> v`.  Type-1 dependencies follow the
orientation of a row path.  Type-2 dependencies say that, on some row, a later
witness vertex adjacent to `v` forces every earlier vertex on that row to
precede `v` in the topological ordering. -/
def LinkageDependency
    (R : PerfectPathPacking G A B) (u v : V) : Prop :=
  (∃ r : R.Index,
    u ∈ (R.path r).vertexSet ∧
      v ∈ (R.path r).vertexSet ∧
        (R.path r).Before u v ∧ u ≠ v) ∨
    ∃ r r' : R.Index,
      r ≠ r' ∧
        u ∈ (R.path r).vertexSet ∧
          v ∈ (R.path r').vertexSet ∧
            ∃ w : V,
              w ∈ (R.path r).vertexSet ∧
                (R.path r).Before u w ∧
                  u ≠ w ∧ G.Adj w v

/-- The auxiliary paths whose endpoints cross a ranking threshold. -/
noncomputable def pathsCrossingThreshold (rank : V → ℕ)
    (Qpack : PathPacking G S T) (t : ℕ) : Finset Qpack.Index := by
  classical
  exact Finset.univ.filter fun q =>
    GraphPathCrossesRankThreshold rank t (Qpack.path q)

theorem mem_pathsCrossingThreshold (rank : V → ℕ)
    (Qpack : PathPacking G S T) (t : ℕ) (q : Qpack.Index) :
    q ∈ pathsCrossingThreshold rank Qpack t ↔
      GraphPathCrossesRankThreshold rank t (Qpack.path q) := by
  classical
  simp [pathsCrossingThreshold]

/-- The slice between consecutive cuts on one row path, represented as a
predicate rather than a constructed subpath.  This is the paper's strict
segment `σ_i(R)`: both cut vertices are excluded. -/
def SliceInterior (sigma : PathSlicing R M) (r : R.Index)
    (i : Fin M) (v : V) : Prop :=
  v ∈ (R.path r).vertexSet ∧
    (R.path r).Before (sigma.cut r i.castSucc) v ∧
      (R.path r).Before v (sigma.cut r i.succ) ∧
        v ≠ sigma.cut r i.castSucc ∧
          v ≠ sigma.cut r i.succ

/-- A path of another packing lies in slice `i` when every intersection point
with the row linkage belongs to the corresponding row slice. -/
def PathInSlice (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (q : Qpack.Index) : Prop :=
  ∀ ⦃r : R.Index⦄ ⦃v : V⦄,
    v ∈ (Qpack.path q).vertexSet →
      v ∈ (R.path r).vertexSet →
        sigma.SliceInterior r i v

/-- The subfamily of `Qpack` whose row-linkage intersections lie in slice
`i`. -/
noncomputable def pathsInSlice (sigma : PathSlicing R M)
    (Qpack : PathPacking G S T) (i : Fin M) : Finset Qpack.Index := by
  classical
  exact Finset.univ.filter fun q => sigma.PathInSlice Qpack i q

theorem mem_pathsInSlice
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (q : Qpack.Index) :
    q ∈ sigma.pathsInSlice Qpack i ↔ sigma.PathInSlice Qpack i q := by
  classical
  simp [pathsInSlice]

/-- The width condition for an `M`-slicing: every slice captures at least `w`
paths from the auxiliary family. -/
def WidthAtLeast (sigma : PathSlicing R M)
    (Qpack : PathPacking G S T) (w : ℕ) : Prop :=
  ∀ i : Fin M, w ≤ (sigma.pathsInSlice Qpack i).card

/-- The theorem statement of Chuzhoy--Tan Theorem 4.6 in the current finite
formal vocabulary. -/
def Theorem46Statement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B S T : Finset V} (R : PerfectPathPacking G A B)
    (Qpack : PathPacking G S T) (M w : ℕ),
      0 < M →
        0 < w →
          R.IsUniqueLinkage →
            PathPackingIntersectsLinkage R Qpack →
              M * w + (M + 1) * R.card ≤ Qpack.card →
                ∃ sigma : PathSlicing R M, sigma.WidthAtLeast Qpack w

end PathSlicing

end SimpleGraph

end Lax17Proofs
