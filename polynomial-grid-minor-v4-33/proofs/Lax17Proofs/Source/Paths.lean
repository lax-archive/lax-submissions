import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Lax17Proofs.Source.Degree

namespace Lax17Proofs

universe u v w

/-!
# Paths and linkages for the grid-minor proof

This file formalizes the path-family language used in Section 2 of
Chuzhoy--Tan's proof of the polynomial grid-minor theorem.  A `GraphPath` is a
mathlib walk with no repeated vertices, bundled with its endpoints.  A
`PathPacking` is a finite indexed family of such paths connecting two finite
vertex sets.
-/

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G H G' : _root_.SimpleGraph V}
variable {u v : V}

@[simp] theorem getVert_transfer (p : G.Walk u v)
    (hp : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) (n : ℕ) :
    (p.transfer H hp).getVert n = p.getVert n := by
  induction p generalizing n with
  | nil =>
      simp
  | cons _ p ih =>
      cases n with
      | zero => simp
      | succ n => simp [_root_.SimpleGraph.Walk.transfer, ih]

@[simp] theorem penultimate_transfer (p : G.Walk u v)
    (hp : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) :
    (p.transfer H hp).penultimate = p.penultimate := by
  simp [_root_.SimpleGraph.Walk.penultimate]

@[simp] theorem getVert_mapLe (hGG' : G ≤ G') (p : G.Walk u v)
    (n : ℕ) :
    (p.mapLe hGG').getVert n = p.getVert n := by
  simpa [_root_.SimpleGraph.Walk.mapLe] using
    (_root_.SimpleGraph.Walk.getVert_map
      (f := _root_.SimpleGraph.Hom.ofLE hGG') (p := p) n)

@[simp] theorem penultimate_mapLe (hGG' : G ≤ G') (p : G.Walk u v) :
    (p.mapLe hGG').penultimate = p.penultimate := by
  have hlen : (p.mapLe hGG').length = p.length := by
    simpa [_root_.SimpleGraph.Walk.mapLe] using
      (_root_.SimpleGraph.Walk.length_map
        (f := _root_.SimpleGraph.Hom.ofLE hGG') (p := p))
  change (p.mapLe hGG').getVert ((p.mapLe hGG').length - 1) =
    p.getVert (p.length - 1)
  rw [hlen]
  simp

/-- In a nontrivial simple walk, the final endpoint does not occur in the
half-open support obtained by dropping the last vertex. -/
theorem end_not_mem_support_dropLast_toFinset_of_isPath [DecidableEq V]
    (p : G.Walk u v) (hp : p.IsPath) :
    v ∉ p.support.dropLast.toFinset := by
  classical
  intro hv
  have hvList : v ∈ p.support.dropLast := by
    simpa using hv
  have hconcat : p.support.dropLast ++ [v] = p.support := by
    have hlast : p.support.getLast p.support_ne_nil = v :=
      _root_.SimpleGraph.Walk.getLast_support p
    have hreplace :
        p.support.dropLast ++ [v] =
          p.support.dropLast ++
            [p.support.getLast p.support_ne_nil] :=
      congrArg (fun a => p.support.dropLast ++ [a]) hlast.symm
    exact hreplace.trans
      (List.dropLast_append_getLast (l := p.support) p.support_ne_nil)
  have hnodup : (p.support.dropLast ++ [v]).Nodup := by
    simpa [hconcat] using hp.support_nodup
  have hdisj : List.Disjoint p.support.dropLast [v] :=
    List.disjoint_of_nodup_append hnodup
  rw [List.disjoint_iff_ne] at hdisj
  exact hdisj v hvList v (by simp) rfl

end Walk

/-- A graph-theoretic path in a simple graph, bundled with its endpoints. -/
structure GraphPath {V : Type*} (G : _root_.SimpleGraph V) where
  /-- The first endpoint of the path. -/
  source : V
  /-- The second endpoint of the path. -/
  target : V
  /-- The underlying walk from `source` to `target`. -/
  walk : G.Walk source target
  /-- The walk has no repeated vertices. -/
  isPath : walk.IsPath

namespace GraphPath

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- The length-zero path at a vertex. -/
def refl (G : _root_.SimpleGraph V) (v : V) : GraphPath G where
  source := v
  target := v
  walk := _root_.SimpleGraph.Walk.nil
  isPath := _root_.SimpleGraph.Walk.IsPath.nil

/-- The finite set of vertices appearing on a graph path. -/
noncomputable def vertexSet (P : GraphPath G) : Finset V :=
  P.walk.support.toFinset

/-- The finite set of edges appearing on a graph path. -/
noncomputable def edgeSet (P : GraphPath G) : Finset (Sym2 V) :=
  P.walk.edges.toFinset

/-- The penultimate vertex of a graph path, using mathlib's convention that it
is the unique vertex for a length-zero path. -/
def penultimate (P : GraphPath G) : V :=
  P.walk.penultimate

/-- Every edge of a graph path is an edge of the ambient graph. -/
theorem edgeSet_subset_edgeSet (P : GraphPath G) :
    ↑P.edgeSet ⊆ G.edgeSet := by
  intro e he
  exact P.walk.edges_subset_edgeSet (by simpa [edgeSet] using he)

/-- A vertex is one of the two endpoints of a graph path. -/
def IsEndpoint (P : GraphPath G) (v : V) : Prop :=
  v = P.source ∨ v = P.target

/-- Reverse the orientation of a graph path. -/
def reverse (P : GraphPath G) : GraphPath G where
  source := P.target
  target := P.source
  walk := P.walk.reverse
  isPath := P.isPath.reverse

omit [DecidableEq V] in
@[simp] theorem reverse_source (P : GraphPath G) :
    P.reverse.source = P.target := rfl

omit [DecidableEq V] in
@[simp] theorem reverse_target (P : GraphPath G) :
    P.reverse.target = P.source := rfl

@[simp] theorem reverse_vertexSet (P : GraphPath G) :
    P.reverse.vertexSet = P.vertexSet := by
  classical
  simp [reverse, vertexSet]

@[simp] theorem reverse_edgeSet (P : GraphPath G) :
    P.reverse.edgeSet = P.edgeSet := by
  classical
  simp [reverse, edgeSet]

@[simp] theorem source_mem_vertexSet (P : GraphPath G) :
    P.source ∈ P.vertexSet := by
  classical
  simp [vertexSet]

@[simp] theorem target_mem_vertexSet (P : GraphPath G) :
    P.target ∈ P.vertexSet := by
  classical
  simp [vertexSet]

omit [DecidableEq V] in
/-- A graph path with distinct endpoints has nonempty edge sequence. -/
theorem walk_not_nil_of_source_ne_target (P : GraphPath G)
    (h : P.source ≠ P.target) : ¬ P.walk.Nil := by
  intro hnil
  exact h hnil.eq

/-- The penultimate vertex of a nontrivial graph path lies on the path. -/
theorem penultimate_mem_vertexSet (P : GraphPath G)
    (h : P.source ≠ P.target) :
    P.penultimate ∈ P.vertexSet := by
  classical
  have hmemDrop :
      P.penultimate ∈ P.walk.support.dropLast :=
    P.walk.penultimate_mem_dropLast_support
      (P.walk_not_nil_of_source_ne_target h)
  simp [penultimate, vertexSet]

omit [DecidableEq V] in
/-- The final edge of a nontrivial graph path joins its penultimate vertex to
the target. -/
theorem penultimate_adj_target (P : GraphPath G)
    (h : P.source ≠ P.target) :
    G.Adj P.penultimate P.target := by
  simpa [penultimate] using
    P.walk.adj_penultimate (P.walk_not_nil_of_source_ne_target h)

omit [DecidableEq V] in
/-- Remove the last edge of a graph path, ending at the penultimate vertex. -/
def dropLast (P : GraphPath G) : GraphPath G where
  source := P.source
  target := P.penultimate
  walk := P.walk.dropLast
  isPath := by
    exact _root_.SimpleGraph.Walk.isPath_of_isSubwalk
      ((_root_.SimpleGraph.Walk.isSubwalk_rfl P.walk).dropLast) P.isPath

omit [DecidableEq V] in
@[simp] theorem dropLast_source (P : GraphPath G) :
    P.dropLast.source = P.source := rfl

omit [DecidableEq V] in
@[simp] theorem dropLast_target (P : GraphPath G) :
    P.dropLast.target = P.penultimate := rfl

@[simp] theorem dropLast_vertexSet_of_not_nil (P : GraphPath G)
    (h : P.source ≠ P.target) :
    P.dropLast.vertexSet = P.walk.support.dropLast.toFinset := by
  classical
  exact congrArg List.toFinset
    (P.walk.support_dropLast (P.walk_not_nil_of_source_ne_target h))

/-- The target of a nontrivial simple path is not in the drop-last path. -/
theorem target_not_mem_dropLast_vertexSet (P : GraphPath G)
    (h : P.source ≠ P.target) :
    P.target ∉ P.dropLast.vertexSet := by
  classical
  rw [P.dropLast_vertexSet_of_not_nil h]
  intro hv
  have hvList : P.target ∈ P.walk.support.dropLast := by
    simpa using hv
  have hconcat : P.walk.support.dropLast ++ [P.target] = P.walk.support := by
    have hlast : P.walk.support.getLast P.walk.support_ne_nil = P.target :=
      _root_.SimpleGraph.Walk.getLast_support P.walk
    have hreplace :
        P.walk.support.dropLast ++ [P.target] =
          P.walk.support.dropLast ++
            [P.walk.support.getLast P.walk.support_ne_nil] :=
      congrArg (fun a => P.walk.support.dropLast ++ [a]) hlast.symm
    exact hreplace.trans
      (List.dropLast_append_getLast (l := P.walk.support) P.walk.support_ne_nil)
  have hnodup : (P.walk.support.dropLast ++ [P.target]).Nodup := by
    simpa [hconcat] using P.isPath.support_nodup
  have hdisj : List.Disjoint P.walk.support.dropLast [P.target] :=
    List.disjoint_of_nodup_append hnodup
  rw [List.disjoint_iff_ne] at hdisj
  exact hdisj P.target hvList P.target (by simp) rfl

/-- On a nontrivial path, the vertex set is the drop-last vertex set together
with the target endpoint. -/
theorem mem_vertexSet_iff_mem_dropLast_or_eq_target (P : GraphPath G)
    (h : P.source ≠ P.target) (v : V) :
    v ∈ P.vertexSet ↔ v ∈ P.dropLast.vertexSet ∨ v = P.target := by
  classical
  have hconcat : P.walk.support.dropLast ++ [P.target] = P.walk.support := by
    have hlast : P.walk.support.getLast P.walk.support_ne_nil = P.target :=
      _root_.SimpleGraph.Walk.getLast_support P.walk
    have hreplace :
        P.walk.support.dropLast ++ [P.target] =
          P.walk.support.dropLast ++
            [P.walk.support.getLast P.walk.support_ne_nil] :=
      congrArg (fun a => P.walk.support.dropLast ++ [a]) hlast.symm
    exact hreplace.trans
      (List.dropLast_append_getLast (l := P.walk.support) P.walk.support_ne_nil)
  rw [P.dropLast_vertexSet_of_not_nil h]
  constructor
  · intro hv
    have hvSupport : v ∈ P.walk.support := by
      simpa [vertexSet] using hv
    have hvAppend : v ∈ P.walk.support.dropLast ++ [P.target] := by
      simpa [hconcat] using hvSupport
    rcases List.mem_append.mp hvAppend with hvDrop | hvTarget
    · exact Or.inl (by simpa using hvDrop)
    · exact Or.inr (by simpa using hvTarget)
  · rintro (hv | rfl)
    · have hvSupportDrop : v ∈ P.walk.support.dropLast := by
        simpa using hv
      have hvAppend : v ∈ P.walk.support.dropLast ++ [P.target] :=
        List.mem_append_left _ hvSupportDrop
      have hvSupport : v ∈ P.walk.support := by
        simpa [hconcat] using hvAppend
      exact by
        simpa [vertexSet] using hvSupport
    · exact P.target_mem_vertexSet

/-- If a non-target vertex is excluded from a path's allocated drop-last part,
then it is also excluded from the allocated drop-last part of the reversed
path. -/
theorem not_mem_reverse_dropLast_of_not_mem_dropLast_of_ne_target
    (P : GraphPath G) (h : P.source ≠ P.target) {v : V}
    (hnot : v ∉ P.dropLast.vertexSet) (hne : v ≠ P.target) :
    v ∉ P.reverse.dropLast.vertexSet := by
  intro hv
  have hvPath : v ∈ P.vertexSet := by
    have hvSupport : v ∈ P.reverse.walk.dropLast.support := by
      simpa [dropLast, vertexSet] using hv
    have hsub :
        P.reverse.walk.dropLast.support ⊆ P.reverse.walk.support :=
      ((_root_.SimpleGraph.Walk.isSubwalk_rfl P.reverse.walk).dropLast).support_subset
    have hvRev : v ∈ P.reverse.vertexSet := by
      simpa [vertexSet] using hsub hvSupport
    simpa using hvRev
  rcases (P.mem_vertexSet_iff_mem_dropLast_or_eq_target h v).1 hvPath with
    hvDrop | hvTarget
  · exact hnot hvDrop
  · exact hne hvTarget

/-- The drop-last path uses only vertices of the original path. -/
theorem dropLast_vertexSet_subset (P : GraphPath G) :
    P.dropLast.vertexSet ⊆ P.vertexSet := by
  intro v hv
  have hvSupport : v ∈ P.walk.dropLast.support := by
    simpa [dropLast, vertexSet] using hv
  have hsub :
      P.walk.dropLast.support ⊆ P.walk.support :=
    ((_root_.SimpleGraph.Walk.isSubwalk_rfl P.walk).dropLast).support_subset
  exact by
    simpa [vertexSet] using hsub hvSupport

/-- The initial segment of a graph path ending at a specified vertex on the
path. -/
noncomputable def takeUntil (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet) :
    GraphPath G where
  source := P.source
  target := v
  walk := P.walk.takeUntil v (by simpa [vertexSet] using hv)
  isPath := by
    exact _root_.SimpleGraph.Walk.isPath_of_isSubwalk
      (P.walk.isSubwalk_takeUntil (by simpa [vertexSet] using hv)) P.isPath

/-- The terminal segment of a graph path starting at a specified vertex on the
path. -/
noncomputable def dropUntil (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet) :
    GraphPath G where
  source := v
  target := P.target
  walk := P.walk.dropUntil v (by simpa [vertexSet] using hv)
  isPath := by
    exact _root_.SimpleGraph.Walk.isPath_of_isSubwalk
      (P.walk.isSubwalk_dropUntil (by simpa [vertexSet] using hv)) P.isPath

@[simp] theorem takeUntil_source (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).source = P.source := rfl

@[simp] theorem takeUntil_target (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).target = v := rfl

@[simp] theorem dropUntil_source (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).source = v := rfl

@[simp] theorem dropUntil_target (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).target = P.target := rfl

/-- An initial segment uses only vertices from the original path. -/
theorem takeUntil_vertexSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).vertexSet ⊆ P.vertexSet := by
  classical
  intro x hx
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have hx' : x ∈ (P.walk.takeUntil v hv').support := by
    simpa [takeUntil, vertexSet] using hx
  exact by
    simpa [vertexSet] using P.walk.support_takeUntil_subset hv' hx'

/-- A terminal segment uses only vertices from the original path. -/
theorem dropUntil_vertexSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).vertexSet ⊆ P.vertexSet := by
  classical
  intro x hx
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have hx' : x ∈ (P.walk.dropUntil v hv').support := by
    simpa [dropUntil, vertexSet] using hx
  exact by
    simpa [vertexSet] using P.walk.support_dropUntil_subset hv' hx'

/-- A terminal segment uses only edges from the original path. -/
theorem dropUntil_edgeSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).edgeSet ⊆ P.edgeSet := by
  classical
  intro e he
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have he' : e ∈ (P.walk.dropUntil v hv').edges := by
    simpa [dropUntil, edgeSet] using he
  exact by
    simpa [edgeSet] using P.walk.edges_dropUntil_subset hv' he'

/-- An initial segment uses only edges from the original path. -/
theorem takeUntil_edgeSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).edgeSet ⊆ P.edgeSet := by
  classical
  intro e he
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have he' : e ∈ (P.walk.takeUntil v hv').edges := by
    simpa [takeUntil, edgeSet] using he
  exact by
    simpa [edgeSet] using P.walk.edges_takeUntil_subset hv' he'

/-- An internal vertex of a simple graph path is incident with two distinct
edges of the path. -/
theorem exists_two_edgeSet_incident_of_mem_vertexSet_of_not_endpoint
    (P : GraphPath G) {x : V}
    (hx : x ∈ P.vertexSet) (hx_source : x ≠ P.source)
    (hx_target : x ≠ P.target) :
    ∃ e₁ ∈ P.edgeSet, x ∈ e₁ ∧
      ∃ e₂ ∈ P.edgeSet, x ∈ e₂ ∧ e₁ ≠ e₂ := by
  classical
  let Q := P.takeUntil hx
  have hQne : Q.source ≠ Q.target := by
    intro h
    exact hx_source (by simpa [Q] using h.symm)
  let e₁ : Sym2 V := s(Q.penultimate, Q.target)
  have he₁Qwalk : e₁ ∈ Q.walk.edges := by
    exact Q.walk.mk_penultimate_end_mem_edges
      (Q.walk_not_nil_of_source_ne_target hQne)
  have he₁Q : e₁ ∈ Q.edgeSet := by
    exact List.mem_toFinset.mpr (by simpa [Q, e₁, GraphPath.edgeSet] using he₁Qwalk)
  have he₁P : e₁ ∈ P.edgeSet := P.takeUntil_edgeSet_subset hx he₁Q
  have hx_e₁ : x ∈ e₁ := by
    simp [e₁, Q]
  let R := P.dropUntil hx
  have hRne : R.source ≠ R.target := by
    intro h
    exact hx_target (by simpa [R] using h)
  let e₂ : Sym2 V := s(R.source, R.walk.snd)
  have he₂Rwalk : e₂ ∈ R.walk.edges := by
    exact R.walk.mk_start_snd_mem_edges
      (R.walk_not_nil_of_source_ne_target hRne)
  have he₂R : e₂ ∈ R.edgeSet := by
    exact List.mem_toFinset.mpr (by simpa [R, e₂, GraphPath.edgeSet] using he₂Rwalk)
  have he₂P : e₂ ∈ P.edgeSet := P.dropUntil_edgeSet_subset hx he₂R
  have hx_e₂ : x ∈ e₂ := by
    simp [e₂, R]
  have hne : e₁ ≠ e₂ := by
    intro heq
    have hxwalk : x ∈ P.walk.support := by simpa [GraphPath.vertexSet] using hx
    have hdisj := P.isPath.isTrail.disjoint_edges_takeUntil_dropUntil hxwalk
    have he₁List : e₁ ∈ (P.walk.takeUntil x hxwalk).edges := by
      simpa [Q, e₁, GraphPath.takeUntil] using he₁Qwalk
    have he₂List : e₂ ∈ (P.walk.dropUntil x hxwalk).edges := by
      simpa [R, e₂, GraphPath.dropUntil] using he₂Rwalk
    exact hdisj he₁List (by simpa [heq] using he₂List)
  exact ⟨e₁, he₁P, hx_e₁, e₂, he₂P, hx_e₂, hne⟩

/-- If a simple graph path has equal endpoints, then every vertex on it is that
endpoint. -/
theorem eq_source_of_source_eq_target_of_mem_vertexSet
    (P : GraphPath G) (hst : P.source = P.target) {v : V}
    (hv : v ∈ P.vertexSet) :
    v = P.source := by
  cases P with
  | mk source target walk isPath =>
      dsimp at hst hv ⊢
      subst target
      have hwalk : walk = _root_.SimpleGraph.Walk.nil :=
        (_root_.SimpleGraph.Walk.isPath_iff_eq_nil walk).mp isPath
      simpa [GraphPath.vertexSet, hwalk] using hv

/-- Any vertex on a nontrivial graph path is incident with some edge of the
path. -/
theorem exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
    (P : GraphPath G) (hne : P.source ≠ P.target)
    {x : V} (hx : x ∈ P.vertexSet) :
    ∃ e ∈ P.edgeSet, x ∈ e := by
  classical
  by_cases hxt : x = P.target
  · refine ⟨s(P.penultimate, P.target), ?_, ?_⟩
    · have hewalk :
          s(P.penultimate, P.target) ∈ P.walk.edges :=
        P.walk.mk_penultimate_end_mem_edges
          (P.walk_not_nil_of_source_ne_target hne)
      exact List.mem_toFinset.mpr (by simpa [GraphPath.penultimate] using hewalk)
    · simp [hxt]
  · let Q := P.dropUntil hx
    have hneQ : Q.source ≠ Q.target := by
      simpa [Q] using hxt
    refine ⟨s(Q.source, Q.walk.snd), ?_, ?_⟩
    · have heQwalk : s(Q.source, Q.walk.snd) ∈ Q.walk.edges :=
        Q.walk.mk_start_snd_mem_edges
          (Q.walk_not_nil_of_source_ne_target hneQ)
      have heQ : s(Q.source, Q.walk.snd) ∈ Q.edgeSet :=
        List.mem_toFinset.mpr (by simpa [GraphPath.edgeSet] using heQwalk)
      exact P.dropUntil_edgeSet_subset hx heQ
    · simp [Q]

/-- A graph path with distinct endpoints has a nonempty edge set. -/
theorem edgeSet_nonempty_of_source_ne_target
    (P : GraphPath G) (hne : P.source ≠ P.target) :
    P.edgeSet.Nonempty := by
  rcases P.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hne (GraphPath.source_mem_vertexSet P) with ⟨e, he, _⟩
  exact ⟨e, he⟩

/-- Splitting a path at a vertex and appending the two resulting pieces
recovers the original walk. -/
theorem takeUntil_append_dropUntil_walk (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).walk.append (P.dropUntil hv).walk = P.walk := by
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  simp [takeUntil, dropUntil, P.walk.take_spec hv']

/-- The segment of a path between two vertices, when the second lies on the
terminal segment beginning at the first.  This formulation keeps the order
witness explicit and avoids committing later proofs to a particular numerical
indexing of vertices along the walk. -/
noncomputable def between (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    GraphPath G :=
  (P.dropUntil ha).takeUntil hb

@[simp] theorem between_source (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).source = a := rfl

@[simp] theorem between_target (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).target = b := rfl

/-- A segment between two vertices of a path uses only vertices from the
original path. -/
theorem between_vertexSet_subset (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).vertexSet ⊆ P.vertexSet := by
  exact subset_trans
    ((P.dropUntil ha).takeUntil_vertexSet_subset hb)
    (P.dropUntil_vertexSet_subset ha)

/-- A segment between two vertices of a path uses only edges from the
original path. -/
theorem between_edgeSet_subset (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).edgeSet ⊆ P.edgeSet := by
  exact subset_trans
    ((P.dropUntil ha).takeUntil_edgeSet_subset hb)
    (P.dropUntil_edgeSet_subset ha)

/-- Vertex `a` appears no later than vertex `b` along an oriented graph path. -/
def Before (P : GraphPath G) (a b : V) : Prop :=
  ∃ ha : a ∈ P.vertexSet, b ∈ (P.dropUntil ha).vertexSet

/-- Every path vertex appears before itself. -/
theorem before_refl (P : GraphPath G) {a : V} (ha : a ∈ P.vertexSet) :
    P.Before a a := by
  exact ⟨ha, GraphPath.source_mem_vertexSet (P.dropUntil ha)⟩

/-- The path segment certified by a `Before` witness. -/
noncomputable def segmentOfBefore (P : GraphPath G) {a b : V}
    (h : P.Before a b) : GraphPath G :=
  P.between h.choose h.choose_spec

@[simp] theorem segmentOfBefore_source (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).source = a := rfl

@[simp] theorem segmentOfBefore_target (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).target = b := rfl

theorem segmentOfBefore_vertexSet_subset (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).vertexSet ⊆ P.vertexSet :=
  P.between_vertexSet_subset h.choose h.choose_spec

/-- The path segment certified by a `Before` witness uses only edges from the
original path. -/
theorem segmentOfBefore_edgeSet_subset (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).edgeSet ⊆ P.edgeSet :=
  P.between_edgeSet_subset h.choose h.choose_spec

/-- The zero-based position of a vertex in the support list of an oriented
path.  Vertices outside the path get the list length, following `List.idxOf`;
order lemmas below use it only for vertices known to lie on the path. -/
noncomputable def vertexIndex (P : GraphPath G) (v : V) : ℕ :=
  P.walk.support.idxOf v

private theorem list_idxOf_le_succ_of_sym2_mem_zipWith_tail
    {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {a b : α}
    (hmem : s(a, b) ∈ List.zipWith (s(·, ·)) l l.tail) :
    l.idxOf b ≤ l.idxOf a + 1 := by
  classical
  rcases (List.exists_mem_iff_getElem
      (l := List.zipWith (s(·, ·)) l l.tail)
      (p := fun e : Sym2 α => e = s(a, b))).1 ⟨s(a, b), hmem, rfl⟩ with
    ⟨n, hn, hget⟩
  have hn_len : n + 1 < l.length := by
    have hn' : n < min l.length l.tail.length := by
      simpa [List.length_zipWith] using hn
    have htail : l.tail.length = l.length - 1 := List.length_tail
    omega
  have hn0 : n < l.length := by omega
  have hn1 : n + 1 < l.length := hn_len
  have htail_get :
      l.tail[n]'(by simpa [List.length_tail] using hn) =
        l[n + 1]'hn1 := by
    simp
  have hedge :
      s(l[n]'hn0, l[n + 1]'hn1) = s(a, b) := by
    simpa [List.getElem_zipWith, htail_get] using hget
  have hidx_n : l.idxOf (l[n]'hn0) = n :=
    hl.idxOf_getElem n hn0
  have hidx_succ : l.idxOf (l[n + 1]'hn1) = n + 1 :=
    hl.idxOf_getElem (n + 1) hn1
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hia : l.idxOf a = n := by simpa [← ha] using hidx_n
    have hib : l.idxOf b = n + 1 := by simpa [← hb] using hidx_succ
    omega
  · have hia : l.idxOf a = n + 1 := by simpa [← hb] using hidx_succ
    have hib : l.idxOf b = n := by simpa [← ha] using hidx_n
    omega

/-- If an unordered edge occurs in a simple path, the two endpoint indices
along the path differ by at most one in either orientation. -/
theorem edge_vertexIndex_le_succ (P : GraphPath G) {u v : V}
    (he : s(u, v) ∈ P.edgeSet) :
    P.vertexIndex v ≤ P.vertexIndex u + 1 := by
  classical
  have heWalk : s(u, v) ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [edgeSet] using he)
  rw [_root_.SimpleGraph.Walk.edges_eq_zipWith_support] at heWalk
  simpa [vertexIndex] using
    list_idxOf_le_succ_of_sym2_mem_zipWith_tail
      P.isPath.support_nodup heWalk

/-- Both endpoints of an edge used by a graph path occur on that path. -/
theorem endpoints_mem_vertexSet_of_edgeSet
    (P : GraphPath G) {x y : V}
    (he : s(x, y) ∈ P.edgeSet) :
    x ∈ P.vertexSet ∧ y ∈ P.vertexSet := by
  classical
  have heWalk : s(x, y) ∈ P.walk.edges :=
    List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using he)
  constructor
  · simpa [GraphPath.vertexSet] using
      P.walk.fst_mem_support_of_mem_edges heWalk
  · simpa [GraphPath.vertexSet] using
      P.walk.snd_mem_support_of_mem_edges heWalk

@[simp] theorem source_vertexIndex (P : GraphPath G) :
    P.vertexIndex P.source = 0 := by
  classical
  rw [vertexIndex]
  exact (List.idxOf_eq_zero_iff_head_eq P.walk.support_ne_nil).2 (by simp)

@[simp] theorem target_vertexIndex (P : GraphPath G) :
    P.vertexIndex P.target = P.walk.length := by
  classical
  rw [vertexIndex]
  have hidx :=
    P.isPath.support_nodup.idxOf_getElem P.walk.length
      (by rw [_root_.SimpleGraph.Walk.length_support]; exact Nat.lt_succ_self _)
  simpa [_root_.SimpleGraph.Walk.support_getElem_length] using hidx

/-- A graph path has as many distinct unordered edges as its walk length. -/
@[simp] theorem edgeSet_card (P : GraphPath G) :
    P.edgeSet.card = P.walk.length := by
  classical
  rw [edgeSet]
  calc
    P.walk.edges.toFinset.card = P.walk.edges.length :=
      List.toFinset_card_of_nodup P.isPath.isTrail.edges_nodup
    _ = P.walk.length := _root_.SimpleGraph.Walk.length_edges P.walk

private theorem list_idxOf_le_of_mem_drop_nodup {α : Type*} [DecidableEq α]
    {l : List α} (hl : l.Nodup) {a b : α} (ha : a ∈ l)
    (hb : b ∈ l.drop (l.idxOf a)) :
    l.idxOf a ≤ l.idxOf b := by
  classical
  let n := l.idxOf a
  have hnlt : n < l.length := by
    simpa [n] using (List.idxOf_lt_length_iff.2 ha)
  have hsplit : l.take n ++ l.drop n = l := List.take_append_drop n l
  have hnodup : (l.take n ++ l.drop n).Nodup := by
    simpa [hsplit] using hl
  have hdisj : List.Disjoint (l.take n) (l.drop n) :=
    List.disjoint_of_nodup_append hnodup
  have hbnot : b ∉ l.take n := by
    intro hb'
    exact hdisj hb' (by simpa [n] using hb)
  have hidx :
      (l.take n ++ l.drop n).idxOf b =
        (l.take n).length + (l.drop n).idxOf b :=
    List.idxOf_append_of_notMem hbnot
  have hlen_take : (l.take n).length = n := by
    simp [n, Nat.min_eq_left hnlt.le]
  calc
    l.idxOf a = n := rfl
    _ ≤ (l.take n).length + (l.drop n).idxOf b := by
      rw [hlen_take]
      omega
    _ = l.idxOf b := by
      simpa [hsplit] using hidx.symm

private theorem list_mem_drop_idxOf_of_le {α : Type*} [DecidableEq α]
    {l : List α} {a b : α} (hb : b ∈ l)
    (hidx : l.idxOf a ≤ l.idxOf b) :
    b ∈ l.drop (l.idxOf a) := by
  classical
  let n := l.idxOf a
  let m := l.idxOf b - n
  have hblt : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hb
  have hmlt : m < (l.drop n).length := by
    simp [m, n]
    omega
  refine List.mem_iff_getElem.2 ⟨m, hmlt, ?_⟩
  rw [List.getElem_drop]
  have hadd : n + m = l.idxOf b := by
    simp [m, n]
    omega
  have hsumlt : n + m < l.length := by
    have : m < l.length - n := by
      simpa [List.length_drop] using hmlt
    omega
  exact (getElem_congr (c := l) (d := l) rfl hadd hsumlt).trans
    (List.getElem_idxOf hblt)

private theorem list_idxOf_eq_add_idxOf_drop_of_mem_drop_nodup
    {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l.drop (l.idxOf a)) :
    l.idxOf b = l.idxOf a + (l.drop (l.idxOf a)).idxOf b := by
  classical
  let n := l.idxOf a
  have hnlt : n < l.length := by
    simpa [n] using (List.idxOf_lt_length_iff.2 ha)
  have hsplit : l.take n ++ l.drop n = l := List.take_append_drop n l
  have hnodup : (l.take n ++ l.drop n).Nodup := by
    simpa [hsplit] using hl
  have hdisj : List.Disjoint (l.take n) (l.drop n) :=
    List.disjoint_of_nodup_append hnodup
  have hbnot : b ∉ l.take n := by
    intro hb'
    exact hdisj hb' (by simpa [n] using hb)
  have hidx :
      (l.take n ++ l.drop n).idxOf b =
        (l.take n).length + (l.drop n).idxOf b :=
    List.idxOf_append_of_notMem hbnot
  have hlen_take : (l.take n).length = n := by
    simp [n, Nat.min_eq_left hnlt.le]
  calc
    l.idxOf b = (l.take n ++ l.drop n).idxOf b := by simp [hsplit]
    _ = (l.take n).length + (l.drop n).idxOf b := hidx
    _ = l.idxOf a + (l.drop (l.idxOf a)).idxOf b := by
      simp [n, hlen_take]

private theorem list_idxOf_le_of_mem_take_idxOf_succ
    {α : Type*} [DecidableEq α] {l : List α} {a b : α}
    (ha : a ∈ l.take (l.idxOf b + 1)) :
    l.idxOf a ≤ l.idxOf b := by
  have haList : a ∈ l := List.mem_of_mem_take ha
  have hlt : l.idxOf a < l.idxOf b + 1 := by
    simpa using (List.mem_take_iff_idxOf_lt haList).1 ha
  omega

theorem before_iff_vertexIndex_le (P : GraphPath G) {a b : V} :
    P.Before a b ↔
      a ∈ P.vertexSet ∧ b ∈ P.vertexSet ∧
        P.vertexIndex a ≤ P.vertexIndex b := by
  classical
  constructor
  · rintro ⟨ha, hb⟩
    have haSupport : a ∈ P.walk.support := by simpa [vertexSet] using ha
    have hbDrop :
        b ∈ P.walk.support.drop (P.walk.support.idxOf a) := by
      have hidxle : P.walk.support.idxOf a ≤ P.walk.length := by
        have hlt : P.walk.support.idxOf a < P.walk.support.length :=
          List.idxOf_lt_length_iff.2 haSupport
        rw [P.walk.length_support] at hlt
        omega
      have hbSupport :
          b ∈ (P.walk.dropUntil a haSupport).support := by
        simpa [dropUntil, vertexSet] using hb
      simpa [_root_.SimpleGraph.Walk.dropUntil_eq_drop,
        _root_.SimpleGraph.Walk.drop_support_eq_support_drop_min,
        Nat.min_eq_left hidxle] using hbSupport
    have hbSupport : b ∈ P.walk.support :=
      List.mem_of_mem_drop hbDrop
    exact ⟨ha, by simpa [vertexSet] using hbSupport,
      by
        simpa [vertexIndex] using
          list_idxOf_le_of_mem_drop_nodup P.isPath.support_nodup
            haSupport hbDrop⟩
  · rintro ⟨ha, hb, hidx⟩
    refine ⟨ha, ?_⟩
    have hbSupport : b ∈ P.walk.support := by simpa [vertexSet] using hb
    have hbDrop :
        b ∈ P.walk.support.drop (P.walk.support.idxOf a) :=
      list_mem_drop_idxOf_of_le hbSupport (by simpa [vertexIndex] using hidx)
    have haSupport : a ∈ P.walk.support := by simpa [vertexSet] using ha
    have hbDropUntil :
        b ∈ (P.walk.dropUntil a haSupport).support := by
      have hidxle : P.walk.support.idxOf a ≤ P.walk.length := by
        have hlt : P.walk.support.idxOf a < P.walk.support.length :=
          List.idxOf_lt_length_iff.2 haSupport
        rw [P.walk.length_support] at hlt
        omega
      simpa [_root_.SimpleGraph.Walk.dropUntil_eq_drop,
        _root_.SimpleGraph.Walk.drop_support_eq_support_drop_min,
        Nat.min_eq_left hidxle] using hbDrop
    simpa [dropUntil, vertexSet] using hbDropUntil

/-- The source of an oriented path occurs before every vertex of the path. -/
theorem source_before_of_mem (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet) :
    P.Before P.source v := by
  classical
  have hsourceIndex : P.vertexIndex P.source = 0 := by
    rw [vertexIndex]
    exact (List.idxOf_eq_zero_iff_head_eq P.walk.support_ne_nil).2 (by
      simp)
  refine (P.before_iff_vertexIndex_le).2
    ⟨GraphPath.source_mem_vertexSet P, hv, ?_⟩
  rw [hsourceIndex]
  exact Nat.zero_le _

/-- Every path vertex occurs before the target in the path order. -/
theorem before_target_of_mem (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    P.Before v P.target := by
  exact ⟨hv, by simpa using GraphPath.target_mem_vertexSet (P.dropUntil hv)⟩

/-- Dropping a path at its source leaves every original path vertex available. -/
theorem mem_dropUntil_source_of_mem (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    v ∈ (P.dropUntil (GraphPath.source_mem_vertexSet P)).vertexSet := by
  simpa using (P.source_before_of_mem hv).choose_spec

/-- The path order is transitive. -/
theorem before_trans (P : GraphPath G) {a b c : V}
    (hab : P.Before a b) (hbc : P.Before b c) :
    P.Before a c := by
  classical
  have hab' := (P.before_iff_vertexIndex_le).1 hab
  have hbc' := (P.before_iff_vertexIndex_le).1 hbc
  exact (P.before_iff_vertexIndex_le).2
    ⟨hab'.1, hbc'.2.1, Nat.le_trans hab'.2.2 hbc'.2.2⟩

/-- On a simple path, two vertices that occur before each other are equal. -/
theorem before_antisymm (P : GraphPath G) {a b : V}
    (hab : P.Before a b) (hba : P.Before b a) :
    a = b := by
  classical
  have hab' := (P.before_iff_vertexIndex_le).1 hab
  have hba' := (P.before_iff_vertexIndex_le).1 hba
  have hidx : P.vertexIndex a = P.vertexIndex b :=
    Nat.le_antisymm hab'.2.2 hba'.2.2
  have halt : P.vertexIndex a < P.walk.support.length := by
    simpa [vertexIndex, vertexSet] using
      (List.idxOf_lt_length_iff.2 (by simpa [vertexSet] using hab'.1 :
        a ∈ P.walk.support))
  have hblt : P.vertexIndex b < P.walk.support.length := by
    simpa [vertexIndex, vertexSet] using
      (List.idxOf_lt_length_iff.2 (by simpa [vertexSet] using hba'.1 :
        b ∈ P.walk.support))
  have halt' : P.walk.support.idxOf a < P.walk.support.length := by
    simpa [vertexIndex] using halt
  have hblt' : P.walk.support.idxOf b < P.walk.support.length := by
    simpa [vertexIndex] using hblt
  have ha_get :
      P.walk.support[P.vertexIndex a]'halt = a := by
    simp [vertexIndex]
  have hb_get :
      P.walk.support[P.vertexIndex b]'hblt = b := by
    simp [vertexIndex]
  have ha_get' :
      P.walk.support[P.vertexIndex b]'hblt = a := by
    simpa [hidx] using ha_get
  exact ha_get'.symm.trans hb_get

/-- If `b` occurs strictly after `a` on a simple path, then the suffix from
`b` no longer contains `a`. -/
theorem not_mem_dropUntil_of_mem_dropUntil_ne
    (P : GraphPath G) {a b : V} (ha : a ∈ P.vertexSet)
    (hb : b ∈ (P.dropUntil ha).vertexSet) (hne : b ≠ a) :
    a ∉ (P.dropUntil (P.dropUntil_vertexSet_subset ha hb)).vertexSet := by
  intro haSuffix
  have hab : P.Before a b := ⟨ha, hb⟩
  have hba : P.Before b a :=
    ⟨P.dropUntil_vertexSet_subset ha hb, haSuffix⟩
  exact hne (P.before_antisymm hba hab)

/-- If `b` lies on the suffix of a path starting at `a`, then the suffix
starting at `b` is contained in the suffix starting at `a`. -/
theorem dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
    (P : GraphPath G) {a b : V} (ha : a ∈ P.vertexSet)
    (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.dropUntil (P.dropUntil_vertexSet_subset ha hb)).vertexSet ⊆
      (P.dropUntil ha).vertexSet := by
  intro v hv
  have hab : P.Before a b := ⟨ha, hb⟩
  have hbv : P.Before b v :=
    ⟨P.dropUntil_vertexSet_subset ha hb, hv⟩
  exact (P.before_trans hab hbv).choose_spec

/-- The index of a vertex on a terminal segment is its offset in the terminal
segment plus the index of the segment source. -/
theorem vertexIndex_eq_add_vertexIndex_dropUntil (P : GraphPath G)
    {a v : V} (ha : a ∈ P.vertexSet)
    (hv : v ∈ (P.dropUntil ha).vertexSet) :
    P.vertexIndex v = P.vertexIndex a + (P.dropUntil ha).vertexIndex v := by
  classical
  have haSupport : a ∈ P.walk.support := by simpa [vertexSet] using ha
  have hidxle : P.walk.support.idxOf a ≤ P.walk.length := by
    have hlt : P.walk.support.idxOf a < P.walk.support.length :=
      List.idxOf_lt_length_iff.2 haSupport
    rw [P.walk.length_support] at hlt
    omega
  have hsupport :
      (P.walk.dropUntil a haSupport).support =
        P.walk.support.drop (P.walk.support.idxOf a) := by
    simp [_root_.SimpleGraph.Walk.dropUntil_eq_drop,
      _root_.SimpleGraph.Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left hidxle]
  have hvDrop :
      v ∈ P.walk.support.drop (P.walk.support.idxOf a) := by
    have hvSupport :
        v ∈ (P.walk.dropUntil a haSupport).support := by
      simpa [dropUntil, vertexSet] using hv
    simpa [hsupport] using hvSupport
  have hidx :=
    list_idxOf_eq_add_idxOf_drop_of_mem_drop_nodup
      P.isPath.support_nodup haSupport hvDrop
  simpa [vertexIndex, dropUntil, hsupport] using hidx

/-- Every vertex of a certified segment occurs after the segment source in the
ambient path. -/
theorem before_of_mem_segmentOfBefore_left (P : GraphPath G) {a b v : V}
    (h : P.Before a b) (hv : v ∈ (P.segmentOfBefore h).vertexSet) :
    P.Before a v := by
  exact ⟨h.choose,
    (P.dropUntil h.choose).takeUntil_vertexSet_subset h.choose_spec hv⟩

/-- Every vertex of a certified segment occurs before the segment target in the
ambient path. -/
theorem before_of_mem_segmentOfBefore_right (P : GraphPath G) {a b v : V}
    (h : P.Before a b) (hv : v ∈ (P.segmentOfBefore h).vertexSet) :
    P.Before v b := by
  classical
  let Q : GraphPath G := P.dropUntil h.choose
  have hbQ : b ∈ Q.vertexSet := by
    simpa [Q] using h.choose_spec
  have hvTakeSupport :
      v ∈ (Q.walk.takeUntil b (by simpa [vertexSet] using hbQ)).support := by
    simpa [Q, segmentOfBefore, between, takeUntil, vertexSet] using hv
  have hvTakeList :
      v ∈ Q.walk.support.take (Q.walk.support.idxOf b + 1) := by
    simpa [_root_.SimpleGraph.Walk.takeUntil_eq_take,
      _root_.SimpleGraph.Walk.take_support_eq_support_take_succ] using
      hvTakeSupport
  have hvQ : v ∈ Q.vertexSet := by
    exact by
      simpa [Q, vertexSet] using List.mem_of_mem_take hvTakeList
  have hidxQ : Q.vertexIndex v ≤ Q.vertexIndex b := by
    simpa [vertexIndex] using
      list_idxOf_le_of_mem_take_idxOf_succ hvTakeList
  have hPv :
      P.vertexIndex v = P.vertexIndex a + Q.vertexIndex v := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hvQ
  have hPb :
      P.vertexIndex b = P.vertexIndex a + Q.vertexIndex b := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hbQ
  have hvP : v ∈ P.vertexSet := P.segmentOfBefore_vertexSet_subset h hv
  have hbP : b ∈ P.vertexSet := ((P.before_iff_vertexIndex_le).1 h).2.1
  refine (P.before_iff_vertexIndex_le).2 ⟨hvP, hbP, ?_⟩
  rw [hPv, hPb]
  exact Nat.add_le_add_left hidxQ (P.vertexIndex a)

/-- Every vertex of the prefix `takeUntil b` occurs before `b` in the ambient
path. -/
theorem before_of_mem_takeUntil (P : GraphPath G) {b v : V}
    (hb : b ∈ P.vertexSet) (hv : v ∈ (P.takeUntil hb).vertexSet) :
    P.Before v b := by
  classical
  have hvTakeSupport :
      v ∈ (P.walk.takeUntil b (by simpa [vertexSet] using hb)).support := by
    simpa [takeUntil, vertexSet] using hv
  have hvTakeList :
      v ∈ P.walk.support.take (P.walk.support.idxOf b + 1) := by
    simpa [_root_.SimpleGraph.Walk.takeUntil_eq_take,
      _root_.SimpleGraph.Walk.take_support_eq_support_take_succ] using
      hvTakeSupport
  have hvP : v ∈ P.vertexSet := by
    simpa [vertexSet] using List.mem_of_mem_take hvTakeList
  have hidx : P.vertexIndex v ≤ P.vertexIndex b := by
    simpa [vertexIndex] using
      list_idxOf_le_of_mem_take_idxOf_succ hvTakeList
  exact (P.before_iff_vertexIndex_le).2 ⟨hvP, hb, hidx⟩

/-- If a vertex occurs before the target of a prefix, then it lies in that
prefix. -/
theorem mem_takeUntil_of_before (P : GraphPath G) {b v : V}
    (hb : b ∈ P.vertexSet) (hv : P.Before v b) :
    v ∈ (P.takeUntil hb).vertexSet := by
  classical
  have hv' := (P.before_iff_vertexIndex_le).1 hv
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv'.1
  have hvTakeList :
      v ∈ P.walk.support.take (P.walk.support.idxOf b + 1) := by
    have hidx : P.walk.support.idxOf v < P.walk.support.idxOf b + 1 := by
      simpa [vertexIndex] using Nat.lt_succ_of_le hv'.2.2
    exact (List.mem_take_iff_idxOf_lt hvSupport).2 hidx
  have hvTakeSupport :
      v ∈ (P.walk.takeUntil b (by simpa [vertexSet] using hb)).support := by
    simpa [_root_.SimpleGraph.Walk.takeUntil_eq_take,
      _root_.SimpleGraph.Walk.take_support_eq_support_take_succ] using
      hvTakeList
  simpa [takeUntil, vertexSet] using hvTakeSupport

/-- A vertex between the endpoints of a certified segment lies in the segment.
-/
theorem mem_segmentOfBefore_of_before_of_before (P : GraphPath G) {a b v : V}
    (h : P.Before a b) (hav : P.Before a v) (hvb : P.Before v b) :
    v ∈ (P.segmentOfBefore h).vertexSet := by
  classical
  let Q : GraphPath G := P.dropUntil h.choose
  have hbQ : b ∈ Q.vertexSet := by
    simpa [Q] using h.choose_spec
  have hvQ : v ∈ Q.vertexSet := by
    simpa [Q] using hav.choose_spec
  have hvbP := (P.before_iff_vertexIndex_le).1 hvb
  have hvPidx :
      P.vertexIndex v = P.vertexIndex a + Q.vertexIndex v := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hvQ
  have hbPidx :
      P.vertexIndex b = P.vertexIndex a + Q.vertexIndex b := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hbQ
  have hidxQ : Q.vertexIndex v ≤ Q.vertexIndex b := by
    omega
  have hv_before_b_Q : Q.Before v b :=
    (Q.before_iff_vertexIndex_le).2 ⟨hvQ, hbQ, hidxQ⟩
  have hvTake : v ∈ (Q.takeUntil hbQ).vertexSet :=
    Q.mem_takeUntil_of_before hbQ hv_before_b_Q
  simpa [segmentOfBefore, between, Q] using hvTake

/-- The first vertex of `P`, in the path order, that lies in a finite set
`U`, assuming `P` meets `U`. -/
noncomputable def firstHitVertex (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : V :=
  Classical.choose (Finset.exists_min_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem firstHitVertex_spec (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.firstHitVertex U hne ∈ P.vertexSet ∩ U ∧
      ∀ v ∈ P.vertexSet ∩ U,
        P.vertexIndex (P.firstHitVertex U hne) ≤ P.vertexIndex v :=
  Classical.choose_spec
    (Finset.exists_min_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem firstHitVertex_mem_vertexSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.firstHitVertex U hne ∈ P.vertexSet :=
  (Finset.mem_inter.1 (P.firstHitVertex_spec U hne).1).1

theorem firstHitVertex_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.firstHitVertex U hne ∈ U :=
  (Finset.mem_inter.1 (P.firstHitVertex_spec U hne).1).2

/-- Every later hit of `U` occurs after the first hit in the path order. -/
theorem firstHitVertex_before_of_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvP : v ∈ P.vertexSet) (hvU : v ∈ U) :
    P.Before (P.firstHitVertex U hne) v := by
  refine (P.before_iff_vertexIndex_le).2
    ⟨P.firstHitVertex_mem_vertexSet U hne, hvP, ?_⟩
  exact (P.firstHitVertex_spec U hne).2 v (Finset.mem_inter.2 ⟨hvP, hvU⟩)

/-- A vertex of `U` on the prefix ending at the first hit is the first hit
itself. -/
theorem eq_firstHitVertex_of_mem_takeUntil_of_mem_set
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvPrefix :
      v ∈ (P.takeUntil (P.firstHitVertex_mem_vertexSet U hne)).vertexSet)
    (hvU : v ∈ U) :
    v = P.firstHitVertex U hne := by
  have hvP : v ∈ P.vertexSet :=
    P.takeUntil_vertexSet_subset (P.firstHitVertex_mem_vertexSet U hne) hvPrefix
  have hv_first : P.Before v (P.firstHitVertex U hne) :=
    P.before_of_mem_takeUntil (P.firstHitVertex_mem_vertexSet U hne) hvPrefix
  have hfirst_v : P.Before (P.firstHitVertex U hne) v :=
    P.firstHitVertex_before_of_mem_set U hne hvP hvU
  exact P.before_antisymm hv_first hfirst_v

/-- The prefix of `P` ending at its first hit of `U`. -/
noncomputable def cleanPrefixToSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : GraphPath G :=
  P.takeUntil (P.firstHitVertex_mem_vertexSet U hne)

@[simp] theorem cleanPrefixToSet_source (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).source = P.source := rfl

@[simp] theorem cleanPrefixToSet_target (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).target = P.firstHitVertex U hne := rfl

theorem cleanPrefixToSet_target_mem (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).target ∈ U := by
  simpa using P.firstHitVertex_mem_set U hne

theorem cleanPrefixToSet_vertexSet_subset (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).vertexSet ⊆ P.vertexSet :=
  P.takeUntil_vertexSet_subset (P.firstHitVertex_mem_vertexSet U hne)

/-- The last vertex of `P`, in the path order, that lies in a finite set
`U`, assuming `P` meets `U`. -/
noncomputable def lastHitVertex (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : V :=
  Classical.choose (Finset.exists_max_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem lastHitVertex_spec (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.lastHitVertex U hne ∈ P.vertexSet ∩ U ∧
      ∀ v ∈ P.vertexSet ∩ U,
        P.vertexIndex v ≤ P.vertexIndex (P.lastHitVertex U hne) :=
  Classical.choose_spec
    (Finset.exists_max_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem lastHitVertex_mem_vertexSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.lastHitVertex U hne ∈ P.vertexSet :=
  (Finset.mem_inter.1 (P.lastHitVertex_spec U hne).1).1

theorem lastHitVertex_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.lastHitVertex U hne ∈ U :=
  (Finset.mem_inter.1 (P.lastHitVertex_spec U hne).1).2

/-- Every hit of `U` occurs before the last hit in the path order. -/
theorem before_lastHitVertex_of_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvP : v ∈ P.vertexSet) (hvU : v ∈ U) :
    P.Before v (P.lastHitVertex U hne) := by
  refine (P.before_iff_vertexIndex_le).2
    ⟨hvP, P.lastHitVertex_mem_vertexSet U hne, ?_⟩
  exact (P.lastHitVertex_spec U hne).2 v (Finset.mem_inter.2 ⟨hvP, hvU⟩)

/-- A vertex of `U` on the suffix starting at the last hit is the last hit
itself. -/
theorem eq_lastHitVertex_of_mem_dropUntil_of_mem_set
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvSuffix :
      v ∈ (P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)).vertexSet)
    (hvU : v ∈ U) :
    v = P.lastHitVertex U hne := by
  have hvP : v ∈ P.vertexSet :=
    P.dropUntil_vertexSet_subset (P.lastHitVertex_mem_vertexSet U hne) hvSuffix
  have hlast_v : P.Before (P.lastHitVertex U hne) v :=
    ⟨P.lastHitVertex_mem_vertexSet U hne, hvSuffix⟩
  have hv_last : P.Before v (P.lastHitVertex U hne) :=
    P.before_lastHitVertex_of_mem_set U hne hvP hvU
  exact P.before_antisymm hv_last hlast_v

/-- The suffix of `P` starting at its last hit of `U`. -/
noncomputable def cleanSuffixFromSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : GraphPath G :=
  P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)

@[simp] theorem cleanSuffixFromSet_source (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).source = P.lastHitVertex U hne := rfl

@[simp] theorem cleanSuffixFromSet_target (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).target = P.target := rfl

theorem cleanSuffixFromSet_source_mem (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).source ∈ U := by
  simpa using P.lastHitVertex_mem_set U hne

theorem cleanSuffixFromSet_vertexSet_subset (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).vertexSet ⊆ P.vertexSet :=
  P.dropUntil_vertexSet_subset (P.lastHitVertex_mem_vertexSet U hne)

/-- The last-hit suffix uses only edges from the original path. -/
theorem cleanSuffixFromSet_edgeSet_subset (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).edgeSet ⊆ P.edgeSet :=
  P.dropUntil_edgeSet_subset (P.lastHitVertex_mem_vertexSet U hne)

/-- A vertex strictly before the source of a certified segment is not on that
segment. -/
theorem not_mem_segmentOfBefore_of_before_source (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before z a)
    (hne : z ≠ a) :
    z ∉ (P.segmentOfBefore h).vertexSet := by
  intro hzmem
  exact hne (P.before_antisymm hz (P.before_of_mem_segmentOfBefore_left h hzmem))

/-- A vertex strictly after the target of a certified segment is not on that
segment. -/
theorem not_mem_segmentOfBefore_of_target_before (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before b z)
    (hne : z ≠ b) :
    z ∉ (P.segmentOfBefore h).vertexSet := by
  intro hzmem
  exact hne ((P.before_antisymm
    (P.before_of_mem_segmentOfBefore_right h hzmem) hz))

/-- A vertex strictly before the source of a certified segment is not in the
drop-last part of that segment. -/
theorem not_mem_segmentOfBefore_dropLast_of_before_source (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before z a)
    (hne : z ≠ a) :
    z ∉ (P.segmentOfBefore h).dropLast.vertexSet := by
  intro hzmem
  exact P.not_mem_segmentOfBefore_of_before_source h hz hne
    ((P.segmentOfBefore h).dropLast_vertexSet_subset hzmem)

/-- A vertex strictly after the target of a certified segment is not in the
drop-last part of that segment. -/
theorem not_mem_segmentOfBefore_dropLast_of_target_before (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before b z)
    (hne : z ≠ b) :
    z ∉ (P.segmentOfBefore h).dropLast.vertexSet := by
  intro hzmem
  exact P.not_mem_segmentOfBefore_of_target_before h hz hne
    ((P.segmentOfBefore h).dropLast_vertexSet_subset hzmem)

/-- If two certified segments of a simple path are ordered with the target of
the first before the source of the second, then any common vertex forces the
two boundary vertices to coincide and the common vertex is that boundary. -/
theorem eq_boundary_of_mem_segments_of_target_before_source
    (P : GraphPath G) {a b c d v : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hvab : v ∈ (P.segmentOfBefore hab).vertexSet)
    (hvcd : v ∈ (P.segmentOfBefore hcd).vertexSet) :
    v = b ∧ b = c := by
  have hvb : P.Before v b :=
    P.before_of_mem_segmentOfBefore_right hab hvab
  have hcv : P.Before c v :=
    P.before_of_mem_segmentOfBefore_left hcd hvcd
  have hcb : P.Before c b := P.before_trans hcv hvb
  have hbc_eq : b = c := P.before_antisymm hbc hcb
  have hbv : P.Before b v := by
    simpa [hbc_eq] using hcv
  exact ⟨P.before_antisymm hvb hbv, hbc_eq⟩

/-- Disjointness of ordered half-open path segments. -/
theorem segmentOfBefore_dropLast_disjoint_of_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : a ≠ b) :
    Disjoint (P.segmentOfBefore hab).dropLast.vertexSet
      (P.segmentOfBefore hcd).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet :=
    (P.segmentOfBefore hab).dropLast_vertexSet_subset hvab
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet :=
    (P.segmentOfBefore hcd).dropLast_vertexSet_subset hvcd
  rcases P.eq_boundary_of_mem_segments_of_target_before_source hab hcd hbc
      hvabSeg hvcdSeg with ⟨rfl, _⟩
  exact (P.segmentOfBefore hab).target_not_mem_dropLast_vertexSet (by
    simpa using hne) hvab

/-- If two certified segments are ordered with a strict gap between the first
target and the second source, then their full vertex sets are disjoint. -/
theorem segmentOfBefore_disjoint_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).vertexSet
      (P.segmentOfBefore hcd).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  exact hne
    (P.eq_boundary_of_mem_segments_of_target_before_source hab hcd hbc
      hvab hvcd).2

/-- A reversed first segment is disjoint from a later segment when the first
target is strictly before the later source. -/
theorem reverse_segmentOfBefore_dropLast_disjoint_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).reverse.dropLast.vertexSet
      (P.segmentOfBefore hcd).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hab).reverse.vertexSet :=
      (P.segmentOfBefore hab).reverse.dropLast_vertexSet_subset hvab
    simpa using hvRev
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet :=
    (P.segmentOfBefore hcd).dropLast_vertexSet_subset hvcd
  exact Finset.disjoint_left.mp
    (P.segmentOfBefore_disjoint_of_strict_target_before_source hab hcd hbc hne)
    hvabSeg hvcdSeg

/-- A segment is disjoint from the reversed form of a later segment when the
first target is strictly before the later source. -/
theorem segmentOfBefore_dropLast_disjoint_reverse_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).dropLast.vertexSet
      (P.segmentOfBefore hcd).reverse.dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet :=
    (P.segmentOfBefore hab).dropLast_vertexSet_subset hvab
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hcd).reverse.vertexSet :=
      (P.segmentOfBefore hcd).reverse.dropLast_vertexSet_subset hvcd
    simpa using hvRev
  exact Finset.disjoint_left.mp
    (P.segmentOfBefore_disjoint_of_strict_target_before_source hab hcd hbc hne)
    hvabSeg hvcdSeg

/-- Reversed ordered segments are disjoint when their underlying full segments
have a strict gap. -/
theorem reverse_segmentOfBefore_dropLast_disjoint_reverse_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).reverse.dropLast.vertexSet
      (P.segmentOfBefore hcd).reverse.dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hab).reverse.vertexSet :=
      (P.segmentOfBefore hab).reverse.dropLast_vertexSet_subset hvab
    simpa using hvRev
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hcd).reverse.vertexSet :=
      (P.segmentOfBefore hcd).reverse.dropLast_vertexSet_subset hvcd
    simpa using hvRev
  exact Finset.disjoint_left.mp
    (P.segmentOfBefore_disjoint_of_strict_target_before_source hab hcd hbc hne)
    hvabSeg hvcdSeg

/-- A path has a path-shaped trace on a finite vertex set when the vertices it
uses inside that set are exactly the vertices of another graph path. -/
def TraceOn (P : GraphPath G) (U : Finset V) : Prop :=
  ∃ Q : GraphPath G, Q.vertexSet = P.vertexSet ∩ U

/-- The vertices of a graph path induce a connected subgraph. -/
theorem connected_induce_vertexSet (P : GraphPath G) :
    (G.induce {v : V | v ∈ P.vertexSet}).Connected := by
  have hset :
      (↑P.vertexSet : Set V) = {v : V | v ∈ P.walk.support} := by
    ext v
    simp [vertexSet]
  rw [show {v : V | v ∈ P.vertexSet} = (↑P.vertexSet : Set V) by rfl]
  rw [hset]
  exact P.walk.connected_induce_support

/-- Cycle-erasure for a walk, packaged as a `GraphPath`.

This is the graph-path version of mathlib's `Walk.toPath`: it keeps the same
endpoints and chooses a simple subwalk of the original walk. -/
noncomputable def ofWalk {s t : V} (W : G.Walk s t) : GraphPath G where
  source := s
  target := t
  walk := W.toPath
  isPath := _root_.SimpleGraph.Path.isPath W.toPath

@[simp] theorem ofWalk_source {s t : V} (W : G.Walk s t) :
    (ofWalk W).source = s := rfl

@[simp] theorem ofWalk_target {s t : V} (W : G.Walk s t) :
    (ofWalk W).target = t := rfl

/-- The cycle-erased path uses only vertices of the original walk. -/
theorem ofWalk_vertexSet_subset {s t : V} (W : G.Walk s t) :
    (ofWalk W).vertexSet ⊆ W.support.toFinset := by
  classical
  intro v hv
  have hv_support :
      v ∈ ((W.toPath : G.Walk s t).support) := by
    simpa [ofWalk, vertexSet] using hv
  have hsub :
      (W.toPath : G.Walk s t).support ⊆ W.support :=
    _root_.SimpleGraph.Walk.support_toPath_subset W
  exact by
    simpa using hsub hv_support

/-- The cycle-erased path uses only edges of the original walk. -/
theorem ofWalk_edgeSet_subset {s t : V} (W : G.Walk s t) :
    (ofWalk W).edgeSet ⊆ W.edges.toFinset := by
  classical
  intro e he
  have he_edges :
      e ∈ ((W.toPath : G.Walk s t).edges) := by
    simpa [ofWalk, edgeSet] using he
  have hsub :
      (W.toPath : G.Walk s t).edges ⊆ W.edges :=
    _root_.SimpleGraph.Walk.edges_toPath_subset W
  exact by
    simpa using hsub he_edges

/-- Concatenate two compatible paths and erase any cycle in the resulting walk.

This is the primitive needed for rerouting operations that are naturally
described as concatenated walks followed by deletion of closed subwalks. -/
noncomputable def appendWithEqToPath (P Q : GraphPath G)
    (h : P.target = Q.source) : GraphPath G :=
  ofWalk (P.walk.append (Q.walk.copy h.symm rfl))

@[simp] theorem appendWithEqToPath_source (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).source = P.source := rfl

@[simp] theorem appendWithEqToPath_target (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).target = Q.target := rfl

/-- The cycle-erased concatenation uses only vertices of the two pieces. -/
theorem appendWithEqToPath_vertexSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
  classical
  intro v hv
  have hvW :
      v ∈ (P.walk.append (Q.walk.copy h.symm rfl)).support.toFinset :=
    ofWalk_vertexSet_subset (P.walk.append (Q.walk.copy h.symm rfl)) hv
  simpa [appendWithEqToPath, vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] using hvW

/-- The cycle-erased concatenation uses only edges of the two pieces. -/
theorem appendWithEqToPath_edgeSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).edgeSet ⊆ P.edgeSet ∪ Q.edgeSet := by
  classical
  intro e he
  have heW :
      e ∈ (P.walk.append (Q.walk.copy h.symm rfl)).edges.toFinset :=
    ofWalk_edgeSet_subset (P.walk.append (Q.walk.copy h.symm rfl)) he
  simpa [appendWithEqToPath, edgeSet,
    _root_.SimpleGraph.Walk.edges_append] using heW

/-- Concatenate three compatible paths and erase cycles after the
concatenation.  The definition is expressed by two binary concatenations so it
can reuse the endpoint and support API for `appendWithEqToPath`. -/
noncomputable def append3WithEqToPath (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    GraphPath G :=
  (P.appendWithEqToPath Q hPQ).appendWithEqToPath R (by simpa using hQR)

@[simp] theorem append3WithEqToPath_source (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).source = P.source := rfl

@[simp] theorem append3WithEqToPath_target (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).target = R.target := rfl

/-- The cycle-erased three-piece concatenation uses only vertices from the
three input paths. -/
theorem append3WithEqToPath_vertexSet_subset (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).vertexSet ⊆
      P.vertexSet ∪ Q.vertexSet ∪ R.vertexSet := by
  classical
  intro v hv
  have hv₂ :
      v ∈ (P.appendWithEqToPath Q hPQ).vertexSet ∪ R.vertexSet :=
    (P.appendWithEqToPath Q hPQ).appendWithEqToPath_vertexSet_subset R
      (by simpa using hQR) hv
  rcases Finset.mem_union.1 hv₂ with hvPQ | hvR
  · have hv₁ : v ∈ P.vertexSet ∪ Q.vertexSet :=
      P.appendWithEqToPath_vertexSet_subset Q hPQ hvPQ
    exact Finset.mem_union.2 (Or.inl hv₁)
  · exact Finset.mem_union.2 (Or.inr hvR)

/-- The cycle-erased three-piece concatenation uses only edges from the three
input paths. -/
theorem append3WithEqToPath_edgeSet_subset (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).edgeSet ⊆
      P.edgeSet ∪ Q.edgeSet ∪ R.edgeSet := by
  classical
  intro e he
  have he₂ :
      e ∈ (P.appendWithEqToPath Q hPQ).edgeSet ∪ R.edgeSet :=
    (P.appendWithEqToPath Q hPQ).appendWithEqToPath_edgeSet_subset R
      (by simpa using hQR) he
  rcases Finset.mem_union.1 he₂ with hePQ | heR
  · have he₁ : e ∈ P.edgeSet ∪ Q.edgeSet :=
      P.appendWithEqToPath_edgeSet_subset Q hPQ hePQ
    exact Finset.mem_union.2 (Or.inl he₁)
  · exact Finset.mem_union.2 (Or.inr heR)

/-- Concatenate four compatible paths and erase cycles after the
concatenation.  This is the path-level operation used by the cross
replacement: retained row piece, transversal segment, retained row piece, and
then any later cleanup can again be treated as a graph path. -/
noncomputable def append4WithEqToPath (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) : GraphPath G :=
  (P.append3WithEqToPath Q R hPQ hQR).appendWithEqToPath S (by simpa using hRS)

@[simp] theorem append4WithEqToPath_source (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).source = P.source := rfl

@[simp] theorem append4WithEqToPath_target (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).target = S.target := rfl

/-- The cycle-erased four-piece concatenation uses only vertices from the
four input paths. -/
theorem append4WithEqToPath_vertexSet_subset (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).vertexSet ⊆
      P.vertexSet ∪ Q.vertexSet ∪ R.vertexSet ∪ S.vertexSet := by
  classical
  intro v hv
  have hv₂ :
      v ∈ (P.append3WithEqToPath Q R hPQ hQR).vertexSet ∪ S.vertexSet :=
    (P.append3WithEqToPath Q R hPQ hQR).appendWithEqToPath_vertexSet_subset S
      (by simpa using hRS) hv
  rcases Finset.mem_union.1 hv₂ with hvPQR | hvS
  · have hv₁ : v ∈ P.vertexSet ∪ Q.vertexSet ∪ R.vertexSet :=
      P.append3WithEqToPath_vertexSet_subset Q R hPQ hQR hvPQR
    exact Finset.mem_union.2 (Or.inl hv₁)
  · exact Finset.mem_union.2 (Or.inr hvS)

/-- The cycle-erased four-piece concatenation uses only edges from the four
input paths. -/
theorem append4WithEqToPath_edgeSet_subset (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).edgeSet ⊆
      P.edgeSet ∪ Q.edgeSet ∪ R.edgeSet ∪ S.edgeSet := by
  classical
  intro e he
  have he₂ :
      e ∈ (P.append3WithEqToPath Q R hPQ hQR).edgeSet ∪ S.edgeSet :=
    (P.append3WithEqToPath Q R hPQ hQR).appendWithEqToPath_edgeSet_subset S
      (by simpa using hRS) he
  rcases Finset.mem_union.1 he₂ with hePQR | heS
  · have he₁ : e ∈ P.edgeSet ∪ Q.edgeSet ∪ R.edgeSet :=
      P.append3WithEqToPath_edgeSet_subset Q R hPQ hQR hePQR
    exact Finset.mem_union.2 (Or.inl he₁)
  · exact Finset.mem_union.2 (Or.inr heS)

/-- Choose a simple path between two vertices in a connected finite induced
subgraph. -/
noncomputable def ofConnectedInduce
    (U : Finset V)
    (hconn : (G.induce {v : V | v ∈ U}).Connected)
    (s t : V) (hs : s ∈ U) (ht : t ∈ U) : GraphPath G := by
  classical
  let Uset : Set V := {v : V | v ∈ U}
  let R :
      (G.induce Uset).Reachable
        (⟨s, by simpa [Uset] using hs⟩ : Uset)
        (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    hconn.preconnected _ _
  let W : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    Classical.choice R
  let Psub := W.toPath
  refine
    { source := s
      target := t
      walk := ?_
      isPath := ?_ }
  · exact (Psub : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset)).map
        (_root_.SimpleGraph.Embedding.induce Uset).toHom
  · exact _root_.SimpleGraph.Walk.map_isPath_of_injective
      (f := (_root_.SimpleGraph.Embedding.induce Uset).toHom)
      (by
        intro a b h
        exact Subtype.ext h)
      Psub.property

/-- The path chosen in a connected induced subgraph stays inside the inducing
finite set. -/
theorem ofConnectedInduce_vertexSet_subset
    (U : Finset V)
    (hconn : (G.induce {v : V | v ∈ U}).Connected)
    (s t : V) (hs : s ∈ U) (ht : t ∈ U) :
    (ofConnectedInduce U hconn s t hs ht).vertexSet ⊆ U := by
  classical
  intro v hv
  let Uset : Set V := {v : V | v ∈ U}
  let R :
      (G.induce Uset).Reachable
        (⟨s, by simpa [Uset] using hs⟩ : Uset)
        (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    hconn.preconnected _ _
  let W : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    Classical.choice R
  let Psub := W.toPath
  let mapped :
      G.Walk s t :=
    (Psub : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset)).map
        (_root_.SimpleGraph.Embedding.induce Uset).toHom
  have hvSupport : v ∈ mapped.support := by
    simpa [ofConnectedInduce, vertexSet, Uset, R, W, Psub, mapped] using hv
  have hvSupport' :
      v ∈ (((Psub : (G.induce Uset).Walk
        (⟨s, by simpa [Uset] using hs⟩ : Uset)
        (⟨t, by simpa [Uset] using ht⟩ : Uset)).map
          (_root_.SimpleGraph.Embedding.induce Uset).toHom).support) := by
    simpa [mapped] using hvSupport
  rw [_root_.SimpleGraph.Walk.support_map] at hvSupport'
  rcases List.mem_map.1 hvSupport' with ⟨w, _hw, hwv⟩
  subst hwv
  exact w.2

@[simp] theorem refl_vertexSet (v : V) :
    (GraphPath.refl G v).vertexSet = {v} := by
  classical
  simp [GraphPath.refl, vertexSet]

omit [DecidableEq V] in
@[simp] theorem refl_source (v : V) :
    (GraphPath.refl G v).source = v := rfl

omit [DecidableEq V] in
@[simp] theorem refl_target (v : V) :
    (GraphPath.refl G v).target = v := rfl

/-- Map a graph path to a supergraph on the same vertex type. -/
def mapLe (P : GraphPath G) {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    GraphPath H where
  source := P.source
  target := P.target
  walk := P.walk.mapLe hGH
  isPath := by
    rw [_root_.SimpleGraph.Walk.isPath_def]
    rw [_root_.SimpleGraph.Walk.support_mapLe_eq_support]
    exact P.isPath.support_nodup

@[simp] theorem mapLe_vertexSet (P : GraphPath G)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).vertexSet = P.vertexSet := by
  classical
  simp [mapLe, vertexSet, _root_.SimpleGraph.Walk.support_mapLe_eq_support]

@[simp] theorem mapLe_edgeSet (P : GraphPath G)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).edgeSet = P.edgeSet := by
  classical
  simp [mapLe, edgeSet, _root_.SimpleGraph.Walk.edges_mapLe_eq_edges]

/-- Transfer a graph path to another graph on the same vertex type, given that
the target graph contains all of the path's edges. -/
def transfer (P : GraphPath G) (H : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ H.edgeSet) : GraphPath H where
  source := P.source
  target := P.target
  walk := P.walk.transfer H h
  isPath := by
    rw [_root_.SimpleGraph.Walk.isPath_def]
    simpa using P.isPath.support_nodup

@[simp] theorem transfer_vertexSet (P : GraphPath G)
    (H : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).vertexSet = P.vertexSet := by
  classical
  simp [transfer, vertexSet]

@[simp] theorem transfer_edgeSet (P : GraphPath G)
    (H : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).edgeSet = P.edgeSet := by
  classical
  simp [transfer, edgeSet]

/-- Lift a graph path that stays in a finite vertex set to the graph induced
on that set. -/
noncomputable def induce (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) : GraphPath (G.induce {v : V | v ∈ U}) where
  source := ⟨P.source, hU (GraphPath.source_mem_vertexSet P)⟩
  target := ⟨P.target, hU (GraphPath.target_mem_vertexSet P)⟩
  walk := P.walk.induce {v : V | v ∈ U} (by
    intro x hx
    exact hU (by simpa [GraphPath.vertexSet] using hx))
  isPath := by
    rw [_root_.SimpleGraph.Walk.isPath_def]
    rw [_root_.SimpleGraph.Walk.support_induce]
    have hmap :
        (List.map Subtype.val
          (P.walk.support.attachWith (Membership.mem {v : V | v ∈ U}) (by
            intro x hx
            exact hU (by simpa [GraphPath.vertexSet] using hx)))).Nodup := by
      simpa [List.map_attachWith] using P.isPath.support_nodup
    exact List.Nodup.of_map Subtype.val hmap

@[simp] theorem induce_source (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) :
    (P.induce U hU).source =
      ⟨P.source, hU (GraphPath.source_mem_vertexSet P)⟩ := rfl

@[simp] theorem induce_target (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) :
    (P.induce U hU).target =
      ⟨P.target, hU (GraphPath.target_mem_vertexSet P)⟩ := rfl

@[simp] theorem mem_induce_vertexSet (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) (v : {x : V // x ∈ U}) :
    v ∈ (P.induce U hU).vertexSet ↔ v.1 ∈ P.vertexSet := by
  classical
  constructor
  · intro hv
    have hv_support :
        v ∈ (P.induce U hU).walk.support := by
      have hv' : v ∈ (P.induce U hU).walk.support.toFinset := by
        simpa [GraphPath.vertexSet] using hv
      exact List.mem_toFinset.mp hv'
    change v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).support
      at hv_support
    rw [_root_.SimpleGraph.Walk.support_induce] at hv_support
    simpa [GraphPath.vertexSet] using hv_support
  · intro hv
    have hv_support : v.1 ∈ P.walk.support := by
      simpa [GraphPath.vertexSet] using hv
    let hWalk : ∀ x ∈ P.walk.support, x ∈ (↑U : Set V) := by
      intro x hx
      exact hU (by simpa [GraphPath.vertexSet] using hx)
    have hv_induce :
        v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk hWalk).support := by
      rw [_root_.SimpleGraph.Walk.support_induce]
      simpa using hv_support
    have hv_induce' : v ∈ (P.induce U hU).walk.support := by
      change v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).support
      simpa using hv_induce
    have hv_fin : v ∈ (P.induce U hU).walk.support.toFinset :=
      List.mem_toFinset.mpr hv_induce'
    simpa [GraphPath.vertexSet] using hv_fin

@[simp] theorem mem_induce_edgeSet (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) (e : Sym2 {x : V // x ∈ U}) :
    e ∈ (P.induce U hU).edgeSet ↔
      Sym2.map Subtype.val e ∈ P.edgeSet := by
  classical
  constructor
  · intro he
    have heWalk : e ∈ (P.induce U hU).walk.edges := by
      have heFin : e ∈ (P.induce U hU).walk.edges.toFinset := by
        simpa [GraphPath.edgeSet] using he
      exact (List.mem_toFinset.1 heFin)
    have hmap :
        Sym2.map Subtype.val e ∈
          ((P.induce U hU).walk.map
            (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges := by
      rw [_root_.SimpleGraph.Walk.edges_map]
      exact List.mem_map.2 ⟨e, heWalk, rfl⟩
    have hmap' : Sym2.map Subtype.val e ∈ P.walk.edges := by
      change Sym2.map Subtype.val e ∈
        ((_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).map
          (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges at hmap
      rwa [_root_.SimpleGraph.Walk.map_induce] at hmap
    simpa [GraphPath.edgeSet] using hmap'
  · intro he
    have heWalk : Sym2.map Subtype.val e ∈ P.walk.edges := by
      have heFin : Sym2.map Subtype.val e ∈ P.walk.edges.toFinset := by
        simpa [GraphPath.edgeSet] using he
      exact (List.mem_toFinset.1 heFin)
    have hmap :
        Sym2.map Subtype.val e ∈
          ((P.induce U hU).walk.map
            (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges := by
      change Sym2.map Subtype.val e ∈
        ((_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).map
          (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges
      rwa [_root_.SimpleGraph.Walk.map_induce]
    have hmapEdges :
        Sym2.map Subtype.val e ∈
          (P.induce U hU).walk.edges.map (Sym2.map Subtype.val) := by
      rw [_root_.SimpleGraph.Walk.edges_map] at hmap
      exact hmap
    rcases List.mem_map.1 hmapEdges with ⟨e', he', hproj⟩
    have heq : e' = e :=
      (Sym2.map.injective Subtype.val_injective) hproj
    have heFin : e ∈ (P.induce U hU).walk.edges := by
      simpa [heq] using he'
    exact List.mem_toFinset.mpr (by simpa [GraphPath.edgeSet] using heFin)

/-- A path is disjoint from a finite vertex set when none of its vertices lie in
the set. -/
def DisjointFromSet (P : GraphPath G) (U : Finset V) : Prop :=
  Disjoint P.vertexSet U

/-- A path is internally disjoint from `U` when every vertex it shares with `U`
is an endpoint of the path. -/
def InternallyDisjointFromSet (P : GraphPath G) (U : Finset V) : Prop :=
  ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ U → P.IsEndpoint v

/-- Cycle-erased concatenation preserves internal disjointness from `U` when
the glued vertex is outside `U`.

This variant does not require the two input paths to meet only at the glue
vertex: the cycle erasure uses only vertices from the concatenated walk, so
endpoint-cleanliness follows from endpoint-cleanliness of the two pieces and
the fact that the common glue cannot be a forbidden internal vertex. -/
theorem appendWithEqToPath_internallyDisjointFromSet
    (P Q : GraphPath G) (h : P.target = Q.source) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.InternallyDisjointFromSet U)
    (hglue : P.target ∉ U) :
    (P.appendWithEqToPath Q h).InternallyDisjointFromSet U := by
  intro v hv hvU
  have hvUnion :
      v ∈ P.vertexSet ∪ Q.vertexSet :=
    P.appendWithEqToPath_vertexSet_subset Q h hv
  rcases Finset.mem_union.1 hvUnion with hvP | hvQ
  · rcases hP hvP hvU with hsource | htarget
    · exact Or.inl (by simpa [appendWithEqToPath] using hsource)
    · exact False.elim (hglue (by simpa [htarget] using hvU))
  · rcases hQ hvQ hvU with hsource | htarget
    · exact False.elim (hglue (by simpa [h, hsource] using hvU))
    · exact Or.inr (by simpa [appendWithEqToPath] using htarget)

/-- A prefix of an internally-disjoint path is internally disjoint from the
same finite set. -/
theorem takeUntil_internallyDisjointFromSet (P : GraphPath G)
    {b : V} (hb : b ∈ P.vertexSet) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    (P.takeUntil hb).InternallyDisjointFromSet U := by
  intro v hvPrefix hvU
  have hvP : v ∈ P.vertexSet :=
    P.takeUntil_vertexSet_subset hb hvPrefix
  rcases hP hvP hvU with hsrc | htgt
  · exact Or.inl (by simp [hsrc])
  · have hbefore : P.Before P.target b := by
      simpa [htgt] using P.before_of_mem_takeUntil hb hvPrefix
    have htarget_before : P.Before b P.target :=
      P.before_target_of_mem hb
    have htarget_eq : P.target = b :=
      P.before_antisymm hbefore htarget_before
    exact Or.inr (by simp [htgt, htarget_eq])

/-- A suffix of an internally-disjoint path is internally disjoint from the
same finite set. -/
theorem dropUntil_internallyDisjointFromSet (P : GraphPath G)
    {b : V} (hb : b ∈ P.vertexSet) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    (P.dropUntil hb).InternallyDisjointFromSet U := by
  intro v hvSuffix hvU
  have hvP : v ∈ P.vertexSet :=
    P.dropUntil_vertexSet_subset hb hvSuffix
  rcases hP hvP hvU with hsrc | htgt
  · have hbefore : P.Before b P.source := by
      exact ⟨hb, by simpa [hsrc] using hvSuffix⟩
    have hsource_before : P.Before P.source b :=
      P.source_before_of_mem hb
    have hsource_eq : P.source = b :=
      P.before_antisymm hsource_before hbefore
    exact Or.inl (by simp [hsrc, hsource_eq])
  · exact Or.inr (by simp [htgt])

/-- The first-hit prefix is internally disjoint from the set it first hits. -/
theorem cleanPrefixToSet_internallyDisjointFromSet
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).InternallyDisjointFromSet U := by
  intro v hvPrefix hvU
  exact Or.inr (by
    dsimp [cleanPrefixToSet]
    exact P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set U hne hvPrefix hvU)

/-- The first-hit prefix meets the set it enters in exactly its target
vertex. -/
theorem cleanPrefixToSet_inter_eq_singleton_target
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    U ∩ (P.cleanPrefixToSet U hne).vertexSet =
      {(P.cleanPrefixToSet U hne).target} := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.1 hv with ⟨hvU, hvPrefix⟩
    have hvfirst :
        v = P.firstHitVertex U hne :=
      P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set U hne hvPrefix hvU
    simpa [cleanPrefixToSet] using hvfirst
  · intro hv
    have hvtarget : v = (P.cleanPrefixToSet U hne).target := by
      simpa using hv
    subst hvtarget
    exact Finset.mem_inter.2
      ⟨P.cleanPrefixToSet_target_mem U hne,
        GraphPath.target_mem_vertexSet (P.cleanPrefixToSet U hne)⟩

/-- The last-hit suffix is internally disjoint from the set it last leaves. -/
theorem cleanSuffixFromSet_internallyDisjointFromSet
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).InternallyDisjointFromSet U := by
  intro v hvSuffix hvU
  exact Or.inl (by
    dsimp [cleanSuffixFromSet]
    exact P.eq_lastHitVertex_of_mem_dropUntil_of_mem_set U hne hvSuffix hvU)

/-- The last-hit suffix meets the set it leaves in exactly its source vertex. -/
theorem cleanSuffixFromSet_inter_eq_singleton_source
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    U ∩ (P.cleanSuffixFromSet U hne).vertexSet =
      {(P.cleanSuffixFromSet U hne).source} := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.1 hv with ⟨hvU, hvSuffix⟩
    have hvlast :
        v = P.lastHitVertex U hne :=
      P.eq_lastHitVertex_of_mem_dropUntil_of_mem_set U hne hvSuffix hvU
    simpa [cleanSuffixFromSet] using hvlast
  · intro hv
    have hvsource : v = (P.cleanSuffixFromSet U hne).source := by
      simpa using hv
    subst hvsource
    exact Finset.mem_inter.2
      ⟨P.cleanSuffixFromSet_source_mem U hne,
        GraphPath.source_mem_vertexSet (P.cleanSuffixFromSet U hne)⟩

/-- Reversing a path preserves internal disjointness from a vertex set. -/
theorem reverse_internallyDisjointFromSet (P : GraphPath G) (U : Finset V) :
    P.reverse.InternallyDisjointFromSet U ↔ P.InternallyDisjointFromSet U := by
  constructor
  · intro h v hv hU
    have hend := h (by simpa using hv) hU
    rcases hend with hvtarget | hvsource
    · exact Or.inr hvtarget
    · exact Or.inl hvsource
  · intro h v hv hU
    have hend := h (by simpa using hv) hU
    rcases hend with hvsource | hvtarget
    · exact Or.inr hvsource
    · exact Or.inl hvtarget

/-- If a path is internally disjoint from `U` and starts outside `U`, then
any intersection with a path contained in `U` is forced to occur at its target.
-/
theorem eq_target_of_internallyDisjointFromSet_of_subset_of_source_not_mem
    (P Q : GraphPath G) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U)
    {v : V} (hvP : v ∈ P.vertexSet) (hvQ : v ∈ Q.vertexSet) :
    v = P.target := by
  rcases hP hvP (hQ hvQ) with hsrc | htgt
  · exact False.elim (hsource (by simpa [hsrc] using hQ hvQ))
  · exact htgt

/-- A vertex of degree exactly one in the ambient graph can appear on a simple
path only as one of the two endpoints of that path. -/
theorem isEndpoint_of_mem_vertexSet_of_degreeEquals_one
    (P : GraphPath G) {v : V}
    (hdeg : DegreeEquals G v 1) (hv : v ∈ P.vertexSet) :
    P.IsEndpoint v := by
  classical
  by_cases hsource : v = P.source
  · exact Or.inl hsource
  by_cases htarget : v = P.target
  · exact Or.inr htarget
  exfalso
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv
  rcases _root_.SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvSupport with
    ⟨n, hn, hnle⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hsource
    simpa [hn0] using hn.symm
  have hn_lt_length : n < P.walk.length := by
    by_contra hnot
    have hnlen : n = P.walk.length := by omega
    apply htarget
    simpa [hnlen] using hn.symm
  have hprev_adj :
      G.Adj v (P.walk.getVert (n - 1)) := by
    have hsub :
        P.walk.toSubgraph.Adj (P.walk.getVert (n - 1))
          (P.walk.getVert ((n - 1) + 1)) :=
      P.walk.toSubgraph_adj_getVert (by omega)
    have hsub' :
        P.walk.toSubgraph.Adj (P.walk.getVert (n - 1)) v := by
      simpa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero), hn] using hsub
    exact G.symm (P.walk.toSubgraph.adj_sub hsub')
  have hnext_adj :
      G.Adj v (P.walk.getVert (n + 1)) := by
    have hsub :
        P.walk.toSubgraph.Adj (P.walk.getVert n)
          (P.walk.getVert (n + 1)) :=
      P.walk.toSubgraph_adj_getVert hn_lt_length
    have hsub' :
        P.walk.toSubgraph.Adj v (P.walk.getVert (n + 1)) := by
      simpa [hn] using hsub
    exact P.walk.toSubgraph.adj_sub hsub'
  have hprev_ne_next :
      P.walk.getVert (n - 1) ≠ P.walk.getVert (n + 1) := by
    intro hsame
    have hidx := P.isPath.getVert_injOn
      (by exact (show n - 1 ≤ P.walk.length by omega))
      (by exact (show n + 1 ≤ P.walk.length by omega))
      hsame
    omega
  exact hprev_ne_next (DegreeEquals.one_adj_eq hdeg hprev_adj hnext_adj)

/-- Two paths are node-disjoint when their vertex sets are disjoint. -/
def NodeDisjoint (P Q : GraphPath G) : Prop :=
  Disjoint P.vertexSet Q.vertexSet

theorem nodeDisjoint_symm {P Q : GraphPath G}
    (h : P.NodeDisjoint Q) : Q.NodeDisjoint P :=
  h.symm

/-- If a path is contained in the union of two paths, and both of those paths
are node-disjoint from a fourth path, then the contained path is also
node-disjoint from the fourth path. -/
theorem nodeDisjoint_of_vertexSet_subset_union_left
    {P Q R W : GraphPath G}
    (hsub : R.vertexSet ⊆ P.vertexSet ∪ Q.vertexSet)
    (hP : P.NodeDisjoint W) (hQ : Q.NodeDisjoint W) :
    R.NodeDisjoint W := by
  rw [NodeDisjoint, Finset.disjoint_left]
  intro v hvR hvW
  rcases Finset.mem_union.1 (hsub hvR) with hvP | hvQ
  · exact Finset.disjoint_left.mp hP hvP hvW
  · exact Finset.disjoint_left.mp hQ hvQ hvW

/-- If two paths are each contained in a union of two paths, and all four
cross-pairs are node-disjoint, then the contained paths are node-disjoint. -/
theorem nodeDisjoint_of_vertexSet_subset_union_union
    {A B C D R W : GraphPath G}
    (hR : R.vertexSet ⊆ A.vertexSet ∪ B.vertexSet)
    (hW : W.vertexSet ⊆ C.vertexSet ∪ D.vertexSet)
    (hAC : A.NodeDisjoint C) (hAD : A.NodeDisjoint D)
    (hBC : B.NodeDisjoint C) (hBD : B.NodeDisjoint D) :
    R.NodeDisjoint W := by
  rw [NodeDisjoint, Finset.disjoint_left]
  intro v hvR hvW
  rcases Finset.mem_union.1 (hR hvR) with hvA | hvB
  · rcases Finset.mem_union.1 (hW hvW) with hvC | hvD
    · exact Finset.disjoint_left.mp hAC hvA hvC
    · exact Finset.disjoint_left.mp hAD hvA hvD
  · rcases Finset.mem_union.1 (hW hvW) with hvC | hvD
    · exact Finset.disjoint_left.mp hBC hvB hvC
    · exact Finset.disjoint_left.mp hBD hvB hvD

/-- Two paths are edge-disjoint when their edge sets are disjoint. -/
def EdgeDisjoint (P Q : GraphPath G) : Prop :=
  Disjoint P.edgeSet Q.edgeSet

theorem edgeDisjoint_symm {P Q : GraphPath G}
    (h : P.EdgeDisjoint Q) : Q.EdgeDisjoint P :=
  h.symm

/-- Two paths are internally disjoint when every common vertex is an endpoint
of both paths. -/
def InternallyDisjoint (P Q : GraphPath G) : Prop :=
  ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet →
    P.IsEndpoint v ∧ Q.IsEndpoint v

theorem internallyDisjoint_symm {P Q : GraphPath G}
    (h : P.InternallyDisjoint Q) : Q.InternallyDisjoint P := by
  intro v hvQ hvP
  exact (h hvP hvQ).symm

/-- A path connects `S` to `T` when its two endpoints lie one in each set.  The
orientation is irrelevant; a single-vertex path in `S ∩ T` also satisfies this
predicate. -/
def Connects (P : GraphPath G) (S T : Finset V) : Prop :=
  (P.source ∈ S ∧ P.target ∈ T) ∨ (P.source ∈ T ∧ P.target ∈ S)

/-- Orient a path connecting `S` and `T` so that it starts in `S` and ends in
`T`.  If it already has that orientation it is left unchanged; otherwise it is
reversed. -/
def orient (P : GraphPath G) {S T : Finset V} (_h : P.Connects S T) :
    GraphPath G :=
  if P.source ∈ S ∧ P.target ∈ T then P else P.reverse

@[simp] theorem orient_vertexSet (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).vertexSet = P.vertexSet := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · simp [orient, hst]

@[simp] theorem orient_edgeSet (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).edgeSet = P.edgeSet := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · simp [orient, hst]

theorem orient_source_mem (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).source ∈ S := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · rcases h with h | h
    · exact False.elim (hst h)
    · simpa [orient, hst, reverse] using h.2

theorem orient_target_mem (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).target ∈ T := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · rcases h with h | h
    · exact False.elim (hst h)
    · simpa [orient, hst, reverse] using h.1

/-- If a path connects `S` to some terminal set and, after that orientation, its
right endpoint lies in `T`, then the original unoriented path connects `S` to
`T`. -/
theorem connects_of_orient_target_mem (P : GraphPath G) {S U T : Finset V}
    (h : P.Connects S U) (htarget : (P.orient h).target ∈ T) :
    P.Connects S T := by
  classical
  by_cases hSU : P.source ∈ S ∧ P.target ∈ U
  · exact Or.inl ⟨hSU.1, by simpa [orient, hSU] using htarget⟩
  · rcases h with h | h
    · exact False.elim (hSU h)
    · exact Or.inr ⟨by simpa [orient, hSU, reverse] using htarget, h.2⟩

theorem orient_isEndpoint (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) {v : V} :
    (P.orient h).IsEndpoint v ↔ P.IsEndpoint v := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst, IsEndpoint]
  · simp [orient, hst, IsEndpoint, reverse, or_comm]

/-- Orient an unoriented segment so that it runs from `x` to `y`.

This is the singleton-endpoint specialization used in rerouting arguments:
the stored orientation of a transversal subpath is irrelevant, and the local
replacement chooses whichever orientation has the required endpoints. -/
def orientBetween (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) : GraphPath G :=
  P.orient h

@[simp] theorem orientBetween_vertexSet (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).vertexSet = P.vertexSet := by
  simp [orientBetween]

@[simp] theorem orientBetween_edgeSet (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).edgeSet = P.edgeSet := by
  simp [orientBetween]

@[simp] theorem orientBetween_source (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).source = x := by
  classical
  have hx : (P.orient h).source ∈ ({x} : Finset V) :=
    P.orient_source_mem h
  simpa [orientBetween] using hx

@[simp] theorem orientBetween_target (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).target = y := by
  classical
  have hy : (P.orient h).target ∈ ({y} : Finset V) :=
    P.orient_target_mem h
  simpa [orientBetween] using hy

/-- Given a path connecting `S` to `T`, orient it from `S` to `T`, truncate at
the first hit of `T`, and then discard the initial part before the last hit of
`S`.  The resulting path has the same orientation convention and has no
internal vertices in `S ∪ T`.

This is the formal terminal-clean version of the phrase “an `S`-`T` path” in
many graph-theory proofs of Menger's theorem. -/
noncomputable def cleanBetweenTerminalSets
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    GraphPath G := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  exact R.cleanSuffixFromSet S hS

theorem cleanBetweenTerminalSets_vertexSet_subset
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).vertexSet ⊆ P.vertexSet := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  intro v hv
  have hvR : v ∈ R.vertexSet :=
    R.cleanSuffixFromSet_vertexSet_subset S hS hv
  have hvO : v ∈ O.vertexSet :=
    O.cleanPrefixToSet_vertexSet_subset T hT hvR
  simpa [O] using hvO

theorem cleanBetweenTerminalSets_connects
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).Connects S T := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  exact Or.inl
    ⟨by
      simpa [cleanBetweenTerminalSets, O, hT, R, hS] using
        R.cleanSuffixFromSet_source_mem S hS,
     by
      simpa [cleanBetweenTerminalSets, O, hT, R, hS] using
        O.cleanPrefixToSet_target_mem T hT⟩

theorem cleanBetweenTerminalSets_source_mem
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).source ∈ S := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  simpa [cleanBetweenTerminalSets, O, hT, R, hS] using
    R.cleanSuffixFromSet_source_mem S hS

theorem cleanBetweenTerminalSets_target_mem
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).target ∈ T := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  simpa [cleanBetweenTerminalSets, O, hT, R, hS] using
    O.cleanPrefixToSet_target_mem T hT

/-- The terminal-clean segment has no internal vertex in either terminal set. -/
theorem cleanBetweenTerminalSets_internallyDisjointFromSet_union
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).InternallyDisjointFromSet (S ∪ T) := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  intro v hv hST
  have hvR : v ∈ R.vertexSet :=
    R.cleanSuffixFromSet_vertexSet_subset S hS (by
      simpa [cleanBetweenTerminalSets, O, hT, R, hS] using hv)
  have hSuffixClean :
      (R.cleanSuffixFromSet S hS).InternallyDisjointFromSet S :=
    R.cleanSuffixFromSet_internallyDisjointFromSet S hS
  have hPrefixClean :
      R.InternallyDisjointFromSet T := by
    simpa [R] using O.cleanPrefixToSet_internallyDisjointFromSet T hT
  rcases Finset.mem_union.1 hST with hvS | hvT
  · rcases hSuffixClean
        (by simpa [cleanBetweenTerminalSets, O, hT, R, hS] using hv) hvS with
      hsource | htarget
    · exact Or.inl hsource
    · exact Or.inr htarget
  · rcases hPrefixClean hvR hvT with
      hsource | htarget
    · have hsource_mem_suffix :
          R.source ∈ (R.cleanSuffixFromSet S hS).vertexSet := by
        simpa [hsource, cleanBetweenTerminalSets, O, hT, R, hS] using hv
      have hsource_eq :
          R.source = R.lastHitVertex S hS := by
        exact R.eq_lastHitVertex_of_mem_dropUntil_of_mem_set S hS
          (by simpa [cleanSuffixFromSet] using hsource_mem_suffix)
          (by
            simpa [R, O] using GraphPath.orient_source_mem P h)
      have hv_source : v = R.lastHitVertex S hS := hsource.trans hsource_eq
      exact Or.inl (by
        simpa [cleanBetweenTerminalSets, O, hT, R, hS] using hv_source)
    · exact Or.inr (by
        simpa [cleanBetweenTerminalSets, O, hT, R, hS] using htarget)

/-- Concatenate two graph paths whose endpoints match.

The proof that the appended walk is still a path is kept explicit; later
arguments usually derive it from disjointness hypotheses. -/
def appendWithEq (P Q : GraphPath G) (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    GraphPath G where
  source := P.source
  target := Q.target
  walk := P.walk.append (Q.walk.copy h.symm rfl)
  isPath := hpath

omit [DecidableEq V] in
@[simp] theorem appendWithEq_source (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).source = P.source := rfl

omit [DecidableEq V] in
@[simp] theorem appendWithEq_target (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).target = Q.target := rfl

theorem appendWithEq_vertexSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
  classical
  intro v hv
  simp [appendWithEq, vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] at hv ⊢
  exact hv

/-- The left constituent path is contained in a concatenation. -/
theorem left_vertexSet_subset_appendWithEq (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    P.vertexSet ⊆ (P.appendWithEq Q h hpath).vertexSet := by
  classical
  intro v hv
  simp [appendWithEq, vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] at hv ⊢
  exact Or.inl hv

/-- The right constituent path is contained in a concatenation. -/
theorem right_vertexSet_subset_appendWithEq (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    Q.vertexSet ⊆ (P.appendWithEq Q h hpath).vertexSet := by
  classical
  intro v hv
  simp [appendWithEq, vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] at hv ⊢
  exact Or.inr hv

private theorem appendWithEq_vertexIndex_left (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {v : V} (hv : v ∈ P.vertexSet) :
    (P.appendWithEq Q h hpath).vertexIndex v = P.vertexIndex v := by
  classical
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv
  change
    (P.walk.append (Q.walk.copy h.symm rfl)).support.idxOf v =
      P.walk.support.idxOf v
  rw [_root_.SimpleGraph.Walk.support_append,
    List.idxOf_append_of_mem hvSupport]

private theorem appendWithEq_vertexIndex_right (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {v : V} (hv : v ∈ Q.vertexSet) :
    (P.appendWithEq Q h hpath).vertexIndex v =
      P.walk.length + Q.vertexIndex v := by
  classical
  by_cases hvsource : v = Q.source
  · subst v
    calc
      (P.appendWithEq Q h hpath).vertexIndex Q.source =
          (P.appendWithEq Q h hpath).vertexIndex P.target :=
        congrArg (P.appendWithEq Q h hpath).vertexIndex h.symm
      _ = P.vertexIndex P.target :=
        appendWithEq_vertexIndex_left P Q h hpath
          (GraphPath.target_mem_vertexSet P)
      _ = P.walk.length := P.target_vertexIndex
      _ = P.walk.length + Q.vertexIndex Q.source := by simp
  · have hvSupport : v ∈ Q.walk.support := by
      simpa [vertexSet] using hv
    have hvTail : v ∈ Q.walk.support.tail := by
      rw [← _root_.SimpleGraph.Walk.cons_tail_support Q.walk] at hvSupport
      exact (List.mem_cons.mp hvSupport).resolve_left hvsource
    have hnodup :
        (P.walk.support ++
          (Q.walk.copy h.symm rfl).support.tail).Nodup := by
      simpa only [_root_.SimpleGraph.Walk.support_append] using
        hpath.support_nodup
    have hdisj :
        List.Disjoint P.walk.support
          (Q.walk.copy h.symm rfl).support.tail :=
      List.disjoint_of_nodup_append hnodup
    have hvCopyTail :
        v ∈ (Q.walk.copy h.symm rfl).support.tail := by
      simpa using hvTail
    have hvNotP : v ∉ P.walk.support := by
      intro hvP
      exact hdisj hvP hvCopyTail
    have hsourcev : Q.source ≠ v := Ne.symm hvsource
    have hidxQ :
        Q.walk.support.idxOf v = Q.walk.support.tail.idxOf v + 1 := by
      calc
        Q.walk.support.idxOf v =
            (Q.source :: Q.walk.support.tail).idxOf v := by
          rw [_root_.SimpleGraph.Walk.cons_tail_support Q.walk]
        _ = Nat.succ (Q.walk.support.tail.idxOf v) :=
          List.idxOf_cons_ne _ hsourcev
        _ = Q.walk.support.tail.idxOf v + 1 := by omega
    change
      (P.walk.append (Q.walk.copy h.symm rfl)).support.idxOf v =
        P.walk.length + Q.walk.support.idxOf v
    rw [_root_.SimpleGraph.Walk.support_append,
      List.idxOf_append_of_notMem hvNotP]
    simp only [_root_.SimpleGraph.Walk.support_copy]
    rw [P.walk.length_support, hidxQ]
    omega

/-- A `Before` relation in the left component is preserved by concatenation. -/
theorem before_appendWithEq_of_left (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {a b : V} (hab : P.Before a b) :
    (P.appendWithEq Q h hpath).Before a b := by
  classical
  have hab' := (P.before_iff_vertexIndex_le).1 hab
  refine ((P.appendWithEq Q h hpath).before_iff_vertexIndex_le).2
    ⟨P.left_vertexSet_subset_appendWithEq Q h hpath hab'.1,
      P.left_vertexSet_subset_appendWithEq Q h hpath hab'.2.1, ?_⟩
  rw [appendWithEq_vertexIndex_left P Q h hpath hab'.1,
    appendWithEq_vertexIndex_left P Q h hpath hab'.2.1]
  exact hab'.2.2

/-- A `Before` relation in the right component is preserved by concatenation;
the path proof rules out an earlier occurrence of every non-glue vertex. -/
theorem before_appendWithEq_of_right (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {a b : V} (hab : Q.Before a b) :
    (P.appendWithEq Q h hpath).Before a b := by
  classical
  have hab' := (Q.before_iff_vertexIndex_le).1 hab
  refine ((P.appendWithEq Q h hpath).before_iff_vertexIndex_le).2
    ⟨P.right_vertexSet_subset_appendWithEq Q h hpath hab'.1,
      P.right_vertexSet_subset_appendWithEq Q h hpath hab'.2.1, ?_⟩
  rw [appendWithEq_vertexIndex_right P Q h hpath hab'.1,
    appendWithEq_vertexIndex_right P Q h hpath hab'.2.1]
  exact Nat.add_le_add_left hab'.2.2 P.walk.length

/-- Every left-component vertex occurs before every right-component vertex.
This is non-strict at the shared glue endpoint. -/
theorem before_appendWithEq_of_mem_left_of_mem_right (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {a b : V} (ha : a ∈ P.vertexSet) (hb : b ∈ Q.vertexSet) :
    (P.appendWithEq Q h hpath).Before a b := by
  have haGlue :
      (P.appendWithEq Q h hpath).Before a P.target :=
    P.before_appendWithEq_of_left Q h hpath (P.before_target_of_mem ha)
  have hGlueB :
      (P.appendWithEq Q h hpath).Before Q.source b :=
    P.before_appendWithEq_of_right Q h hpath (Q.source_before_of_mem hb)
  exact (P.appendWithEq Q h hpath).before_trans haGlue (by simpa [h] using hGlueB)

/-- A concatenated path uses only edges from the two concatenated pieces. -/
theorem appendWithEq_edgeSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).edgeSet ⊆ P.edgeSet ∪ Q.edgeSet := by
  classical
  intro e he
  simp [appendWithEq, edgeSet, _root_.SimpleGraph.Walk.edges_append] at he ⊢
  exact he

/-- If two simple paths meet only at the endpoint where they are glued, then
their concatenation is again a simple path. -/
theorem appendWithEq_isPath_of_inter_subset_target (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.walk.append (Q.walk.copy h.symm rfl)).IsPath := by
  classical
  rw [_root_.SimpleGraph.Walk.isPath_def,
    _root_.SimpleGraph.Walk.support_append]
  refine List.Nodup.append P.isPath.support_nodup ?hQtail ?hdisj
  · have hQcopy :
        (Q.walk.copy h.symm rfl).support.Nodup := by
      simpa using Q.isPath.support_nodup
    exact List.Nodup.sublist (List.tail_sublist _) hQcopy
  · rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    have ha_fin : a ∈ P.vertexSet := by
      simpa [vertexSet] using ha
    have hb_support : a ∈ (Q.walk.copy h.symm rfl).support :=
      List.mem_of_mem_tail hb
    have hb_fin : a ∈ Q.vertexSet := by
      simpa [vertexSet] using hb_support
    have ha_target : a = P.target := hinter ha_fin hb_fin
    have hnot_target_tail :
        P.target ∉ (Q.walk.copy h.symm rfl).support.tail := by
      have hnot_source_tail : Q.source ∉ Q.walk.support.tail := by
        have hcons : (Q.source :: Q.walk.support.tail).Nodup := by
          rw [_root_.SimpleGraph.Walk.cons_tail_support Q.walk]
          exact Q.isPath.support_nodup
        exact (List.nodup_cons.mp hcons).1
      simpa [h] using hnot_source_tail
    exact hnot_target_tail (by simpa [ha_target] using hb)

/-- Concatenate two paths when their only common vertices lie at the glued
endpoint. -/
noncomputable def appendWithEqOfInterSubsetTarget
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    GraphPath G :=
  P.appendWithEq Q h (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

@[simp] theorem appendWithEqOfInterSubsetTarget_source
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfInterSubsetTarget_target
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).target = Q.target :=
  rfl

/-- Endpoint witness for a concatenation whose first path starts in `S` and
second path ends in `T`. -/
theorem appendWithEqOfInterSubsetTarget_connects
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- Concatenating two internally clean paths at a glue vertex outside the
forbidden set remains internally clean. -/
theorem appendWithEqOfInterSubsetTarget_internallyDisjointFromSet
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target)
    {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.InternallyDisjointFromSet U)
    (hglue : P.target ∉ U) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).InternallyDisjointFromSet U := by
  intro v hv hvU
  have hvUnion :
      v ∈ P.vertexSet ∪ Q.vertexSet :=
    P.appendWithEq_vertexSet_subset Q h
      (P.appendWithEq_isPath_of_inter_subset_target Q h hinter) hv
  rcases Finset.mem_union.1 hvUnion with hvP | hvQ
  · rcases hP hvP hvU with hsource | htarget
    · exact Or.inl (by simp [hsource])
    · exact False.elim (hglue (by simpa [htarget] using hvU))
  · rcases hQ hvQ hvU with hsource | htarget
    · exact False.elim (hglue (by simpa [h, hsource] using hvU))
    · exact Or.inr (by simp [htarget])

/-- The left constituent path is contained in a concatenation built using
`appendWithEqOfInterSubsetTarget`. -/
theorem left_vertexSet_subset_appendWithEqOfInterSubsetTarget
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    P.vertexSet ⊆
      (P.appendWithEqOfInterSubsetTarget Q h hinter).vertexSet := by
  exact P.left_vertexSet_subset_appendWithEq Q h
    (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

/-- The right constituent path is contained in a concatenation built using
`appendWithEqOfInterSubsetTarget`. -/
theorem right_vertexSet_subset_appendWithEqOfInterSubsetTarget
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    Q.vertexSet ⊆
      (P.appendWithEqOfInterSubsetTarget Q h hinter).vertexSet := by
  exact P.right_vertexSet_subset_appendWithEq Q h
    (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

/-- Append a suffix contained in a terminal region `U` to a path that starts
outside `U` and is internally disjoint from `U`. -/
noncomputable def appendWithEqOfInternallyDisjointFromSet
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      P.eq_target_of_internallyDisjointFromSet_of_subset_of_source_not_mem
        Q hP hQ hsource (v := v) hvP hvQ)

@[simp] theorem appendWithEqOfInternallyDisjointFromSet_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U) :
    (P.appendWithEqOfInternallyDisjointFromSet Q h hP hQ hsource).source =
      P.source :=
  by simp [appendWithEqOfInternallyDisjointFromSet]

@[simp] theorem appendWithEqOfInternallyDisjointFromSet_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U) :
    (P.appendWithEqOfInternallyDisjointFromSet Q h hP hQ hsource).target =
      Q.target :=
  by simp [appendWithEqOfInternallyDisjointFromSet]

theorem appendWithEqOfInternallyDisjointFromSet_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ U)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInternallyDisjointFromSet Q h hP hQ hsource_not).Connects S T :=
  Or.inl ⟨by simp [appendWithEqOfInternallyDisjointFromSet, hsource],
    by simp [appendWithEqOfInternallyDisjointFromSet, htarget]⟩

/-- Append a suffix contained in `U` to a path internally disjoint from `U`,
assuming only that the source of the first path is not on the appended suffix.
This is the form used in Menger splicing, where the source may itself be a
terminal vertex in `U` but is known not to lie on the particular suffix. -/
noncomputable def appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      by
        rcases hP hvP (hQ hvQ) with hsource | htarget
        · exact False.elim (hsource_not (by simpa [hsource] using hvQ))
        · exact htarget)

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
      Q h hP hQ hsource_not).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
      Q h hP hQ hsource_not).target = Q.target :=
  rfl

theorem appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
      Q h hP hQ hsource_not).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- Variant of
`appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix` allowing the
first path's source to lie on the appended suffix only in the degenerate case
where that source is also the glue vertex. -/
noncomputable def appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      by
        rcases hP hvP (hQ hvQ) with hsource | htarget
        · exact hsource.trans (hsource_only (by simpa [hsource] using hvQ))
        · exact htarget)

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
      Q h hP hQ hsource_only).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
      Q h hP hQ hsource_only).target = Q.target :=
  rfl

theorem appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
      Q h hP hQ hsource_only).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- Append a path internally disjoint from `U` to a prefix contained in `U`,
allowing the second path's target to lie on the prefix only in the degenerate
case where the second path starts and ends at the glued vertex.

This is the target-end symmetric form of
`appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget`. -/
noncomputable def appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      by
        rcases hQ hvQ (hP hvP) with hsource | htarget
        · exact hsource.trans h.symm
        · exact htarget.trans
            ((htarget_only (by simpa [htarget] using hvP)).trans h.symm))

@[simp] theorem appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source) :
    (P.appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
      Q h hP hQ htarget_only).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source) :
    (P.appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
      Q h hP hQ htarget_only).target = Q.target :=
  rfl

theorem appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
      Q h hP hQ htarget_only).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- If a path is internally disjoint from a terminal region `U`, then it is
disjoint from any path contained in `U` as soon as neither endpoint lies on that
contained path. -/
theorem nodeDisjoint_of_internallyDisjointFromSet_of_subset_of_endpoints_not_mem
    (P Q : GraphPath G) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ Q.vertexSet)
    (htarget : P.target ∉ Q.vertexSet) :
    P.NodeDisjoint Q := by
  rw [NodeDisjoint, Finset.disjoint_left]
  intro v hvP hvQ
  rcases hP hvP (hQ hvQ) with hsrc | htgt
  · exact hsource (by simpa [hsrc] using hvQ)
  · exact htarget (by simpa [htgt] using hvQ)

omit [DecidableEq V] in
theorem connects_comm (P : GraphPath G) (S T : Finset V) :
    P.Connects S T ↔ P.Connects T S := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Any two vertices on a graph path are connected by a subpath contained in
the original path.  The returned path is unoriented: it may run from `x` to
`y` or from `y` to `x`. -/
theorem exists_segment_connects_of_mem_vertexSet
    (P : GraphPath G) {x y : V}
    (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    ∃ Q : GraphPath G,
      Q.Connects ({x} : Finset V) ({y} : Finset V) ∧
        Q.vertexSet ⊆ P.vertexSet := by
  classical
  by_cases hxy : P.vertexIndex x ≤ P.vertexIndex y
  · let hbefore : P.Before x y :=
      (P.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    refine ⟨P.segmentOfBefore hbefore, ?_, ?_⟩
    · exact Or.inl ⟨by simp, by simp⟩
    · exact P.segmentOfBefore_vertexSet_subset hbefore
  · have hyx : P.vertexIndex y ≤ P.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : P.Before y x :=
      (P.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    refine ⟨P.segmentOfBefore hbefore, ?_, ?_⟩
    · exact Or.inr ⟨by simp, by simp⟩
    · exact P.segmentOfBefore_vertexSet_subset hbefore

end GraphPath

/-- A finite indexed family of node-disjoint paths connecting two vertex sets. -/
structure PathPacking {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  /-- The finite index type for the paths in the packing. -/
  Index : Type
  /-- The index type is finite. -/
  [indexFintype : Fintype Index]
  /-- The index type has decidable equality. -/
  [indexDecidableEq : DecidableEq Index]
  /-- The path assigned to each index. -/
  path : Index → GraphPath G
  /-- Every path connects the two specified vertex sets. -/
  connects : ∀ i : Index, (path i).Connects S T
  /-- Distinct indexed paths are vertex-disjoint. -/
  node_disjoint : Pairwise fun i j => GraphPath.NodeDisjoint (path i) (path j)

namespace PathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- The image of a finite set in a subtype determined by a larger finite set. -/
noncomputable def subtypeFinset (S U : Finset V) (hS : S ⊆ U) :
    Finset {v : V // v ∈ U} :=
  S.attach.map
    ⟨fun v => ⟨v.1, hS v.2⟩,
      by
        intro a b h
        have hval : a.1 = b.1 :=
          congrArg (fun x : {v : V // v ∈ U} => x.1) h
        exact Subtype.ext hval⟩

omit [DecidableEq V] in
@[simp] theorem mem_subtypeFinset {S U : Finset V} (hS : S ⊆ U)
    (v : {x : V // x ∈ U}) :
    v ∈ subtypeFinset S U hS ↔ v.1 ∈ S := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨x, hx, hxv⟩
    have hxval : x.1 = v.1 := congrArg Subtype.val hxv
    simpa [hxval] using x.2
  · intro hv
    exact Finset.mem_map.mpr
      ⟨⟨v.1, hv⟩, by simp, by
        apply Subtype.ext
        rfl⟩

instance (P : PathPacking G S T) : Fintype P.Index := P.indexFintype
instance (P : PathPacking G S T) : DecidableEq P.Index := P.indexDecidableEq

/-- The number of paths in a packing. -/
noncomputable def card (P : PathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- Reindex a path packing by an equivalent finite index type. -/
noncomputable def reindex {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) :
    PathPacking G S T where
  Index := ι
  path := fun i => P.path (e i)
  connects := fun i => P.connects (e i)
  node_disjoint := by
    intro i j hij
    exact P.node_disjoint (fun h => hij (e.injective h))

@[simp] theorem reindex_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) :
    (P.reindex e).card = P.card := by
  dsimp [reindex, card]
  exact Fintype.card_congr e

@[simp] theorem reindex_path_vertexSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) (i : ι) :
    ((P.reindex e).path i).vertexSet = (P.path (e i)).vertexSet := rfl

@[simp] theorem reindex_path_edgeSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) (i : ι) :
    ((P.reindex e).path i).edgeSet = (P.path (e i)).edgeSet := rfl

/-- The canonical equivalence from `Fin P.card` to the index type of a path
packing. -/
noncomputable def finIndexEquiv (P : PathPacking G S T) :
    Fin P.card ≃ P.Index := by
  simpa [card] using (Fintype.equivFin P.Index).symm

/-- Reindex a path packing by `Fin P.card`. -/
noncomputable def finReindex (P : PathPacking G S T) : PathPacking G S T :=
  P.reindex P.finIndexEquiv

@[simp] theorem finReindex_card (P : PathPacking G S T) :
    P.finReindex.card = P.card := by
  simp [finReindex]

/-- Restrict a path packing to a finite set of path indices. -/
noncomputable def restrictIndexSet (P : PathPacking G S T)
    (I : Finset P.Index) : PathPacking G S T where
  Index := {i : P.Index // i ∈ I}
  path := fun i => P.path i.1
  connects := fun i => P.connects i.1
  node_disjoint := by
    intro i j hij
    exact P.node_disjoint (fun h => hij (Subtype.ext h))

@[simp] theorem restrictIndexSet_card (P : PathPacking G S T)
    (I : Finset P.Index) :
    (P.restrictIndexSet I).card = I.card := by
  classical
  simp [restrictIndexSet, card]

@[simp] theorem restrictIndexSet_path_vertexSet
    (P : PathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).vertexSet = (P.path i.1).vertexSet := rfl

/-- Choose exactly `n` paths from a packing of size at least `n`. -/
theorem exists_indexSet_card_eq (P : PathPacking G S T)
    {n : ℕ} (hn : n ≤ P.card) :
    ∃ I : Finset P.Index, I.card = n ∧
      (P.restrictIndexSet I).card = n := by
  classical
  have hn_univ : n ≤ (Finset.univ : Finset P.Index).card := by
    simpa [card] using hn
  rcases Finset.exists_subset_card_eq hn_univ with ⟨I, _hI, hIcard⟩
  exact ⟨I, hIcard, by simp [hIcard]⟩

/-- Transfer every path in a packing to another graph on the same vertex type,
given edge-containment proofs for each path. -/
def transfer (P : PathPacking G S T) (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e, e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    PathPacking H S T where
  Index := P.Index
  path := fun i => (P.path i).transfer H (h i)
  connects := by
    intro i
    simpa [GraphPath.transfer, GraphPath.Connects] using P.connects i
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

/-- Every path in the packing has all vertices contained in `U`. -/
def StaysIn (P : PathPacking G S T) (U : Finset V) : Prop :=
  ∀ i : P.Index, (P.path i).vertexSet ⊆ U

/-- Lift a path packing that stays inside a finite vertex set to the induced
graph on that set.  The terminal sets are the corresponding subtype images. -/
noncomputable def induce (P : PathPacking G S T) (U : Finset V)
    (hP : P.StaysIn U) (hS : S ⊆ U) (hT : T ⊆ U) :
    PathPacking (G.induce {v : V | v ∈ U})
      (subtypeFinset S U hS) (subtypeFinset T U hT) where
  Index := P.Index
  path := fun i => (P.path i).induce U (hP i)
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨by
        rw [GraphPath.induce_source]
        exact (mem_subtypeFinset hS _).2 h.1,
        by
        rw [GraphPath.induce_target]
        exact (mem_subtypeFinset hT _).2 h.2⟩
    · exact Or.inr ⟨by
        rw [GraphPath.induce_source]
        exact (mem_subtypeFinset hT _).2 h.1,
        by
        rw [GraphPath.induce_target]
        exact (mem_subtypeFinset hS _).2 h.2⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hv_i hv_j
    have hvi : v.1 ∈ (P.path i).vertexSet := by
      have hv_support :
          v ∈ ((P.path i).induce U (hP i)).walk.support := by
        exact List.mem_toFinset.mp (by
          simpa [GraphPath.vertexSet] using hv_i)
      change
        v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V)
          (P.path i).walk _).support at hv_support
      rw [_root_.SimpleGraph.Walk.support_induce] at hv_support
      simpa [GraphPath.vertexSet] using hv_support
    have hvj : v.1 ∈ (P.path j).vertexSet := by
      have hv_support :
          v ∈ ((P.path j).induce U (hP j)).walk.support := by
        exact List.mem_toFinset.mp (by
          simpa [GraphPath.vertexSet] using hv_j)
      change
        v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V)
          (P.path j).walk _).support at hv_support
      rw [_root_.SimpleGraph.Walk.support_induce] at hv_support
      simpa [GraphPath.vertexSet] using hv_support
    exact Finset.disjoint_left.mp (P.node_disjoint hij) hvi hvj

/-- Every path in the packing is internally disjoint from `U`. -/
def InternallyDisjointFromSet (P : PathPacking G S T) (U : Finset V) : Prop :=
  ∀ i : P.Index, (P.path i).InternallyDisjointFromSet U

/-- The union of all vertices used by paths in the packing. -/
noncomputable def vertexSet (P : PathPacking G S T) : Finset V :=
  Finset.univ.biUnion fun i : P.Index => (P.path i).vertexSet

/-- Membership in the vertex set of a path packing is membership in one of its
indexed path vertex sets. -/
theorem mem_vertexSet (P : PathPacking G S T) {v : V} :
    v ∈ P.vertexSet ↔ ∃ i : P.Index, v ∈ (P.path i).vertexSet := by
  classical
  simp [vertexSet]

/-- The vertex set of each indexed path is contained in the packing vertex
set. -/
theorem path_vertexSet_subset_vertexSet (P : PathPacking G S T)
    (i : P.Index) :
    (P.path i).vertexSet ⊆ P.vertexSet := by
  intro v hv
  exact (P.mem_vertexSet).2 ⟨i, hv⟩

/-- Internal disjointness from `A` extends to `A ∪ B` when the whole packing is
disjoint from `B`. -/
theorem internallyDisjointFromSet_union_of_disjoint_vertexSet
    (P : PathPacking G S T) {A B : Finset V}
    (hA : P.InternallyDisjointFromSet A)
    (hB : Disjoint P.vertexSet B) :
    P.InternallyDisjointFromSet (A ∪ B) := by
  intro i v hv hvUnion
  rcases Finset.mem_union.mp hvUnion with hvA | hvB
  · exact hA i hv hvA
  · exact False.elim
      (Finset.disjoint_left.mp hB (P.path_vertexSet_subset_vertexSet i hv) hvB)

/-- If every path in a packing stays in `U`, then the whole packing vertex set is
contained in `U`. -/
theorem vertexSet_subset_of_staysIn {P : PathPacking G S T} {U : Finset V}
    (h : P.StaysIn U) :
    P.vertexSet ⊆ U := by
  classical
  intro v hv
  have hv' :
      v ∈ Finset.univ.biUnion fun i : P.Index => (P.path i).vertexSet := by
    simpa [vertexSet] using hv
  rcases Finset.mem_biUnion.mp hv' with ⟨i, _hi, hvi⟩
  exact h i hvi

/-- A bridge path from one indexed path of a packing to another, internally
disjoint from the whole packing.  This is the bridge object returned by
Chekuri--Chuzhoy Theorem 3.1. -/
structure BridgeBetween (P : PathPacking G S T) (i j : P.Index) where
  /-- The bridge path. -/
  path : GraphPath G
  /-- The bridge starts on path `i` and ends on path `j`, up to orientation. -/
  connects : path.Connects (P.path i).vertexSet (P.path j).vertexSet
  /-- Internal vertices of the bridge avoid every path in the packing. -/
  internallyDisjoint : path.InternallyDisjointFromSet P.vertexSet

namespace BridgeBetween

variable {P : PathPacking G S T} {i j : P.Index}

/-- Orient a bridge from the first indexed path to the second indexed path. -/
noncomputable def orientedPath (β : P.BridgeBetween i j) : GraphPath G :=
  β.path.orient β.connects

@[simp] theorem orientedPath_vertexSet (β : P.BridgeBetween i j) :
    β.orientedPath.vertexSet = β.path.vertexSet := by
  simp [orientedPath]

theorem orientedPath_source_mem_left (β : P.BridgeBetween i j) :
    β.orientedPath.source ∈ (P.path i).vertexSet :=
  GraphPath.orient_source_mem β.path β.connects

theorem orientedPath_target_mem_right (β : P.BridgeBetween i j) :
    β.orientedPath.target ∈ (P.path j).vertexSet :=
  GraphPath.orient_target_mem β.path β.connects

theorem orientedPath_internallyDisjoint (β : P.BridgeBetween i j) :
    β.orientedPath.InternallyDisjointFromSet P.vertexSet := by
  intro v hv hP
  exact (GraphPath.orient_isEndpoint β.path β.connects).2
    (β.internallyDisjoint (by simpa [orientedPath] using hv) hP)

end BridgeBetween

/-- A path whose endpoints lie on two indexed paths of a packing, and whose
internal vertices avoid the whole packing, is a bridge between those two
indexed paths.  This is the standard way that a clean transversal segment
creates an edge in the linkage auxiliary graph. -/
def BridgeBetween.of_orientedPath (P : PathPacking G S T)
    {i j : P.Index} (R : GraphPath G)
    (hsource : R.source ∈ (P.path i).vertexSet)
    (htarget : R.target ∈ (P.path j).vertexSet)
    (hinternal : R.InternallyDisjointFromSet P.vertexSet) :
    P.BridgeBetween i j where
  path := R
  connects := Or.inl ⟨hsource, htarget⟩
  internallyDisjoint := hinternal

/-- A packing has pairwise bridges if every pair of distinct indexed paths is
connected by a bridge internally disjoint from the entire packing. -/
def HasPairwiseBridges (P : PathPacking G S T) : Prop :=
  ∀ ⦃i j : P.Index⦄, i ≠ j → Nonempty (P.BridgeBetween i j)

/-- A localized version of pairwise bridges: each bridge is required to stay in
the finite region `U`. -/
def HasPairwiseBridgesIn (P : PathPacking G S T) (U : Finset V) : Prop :=
  ∀ ⦃i j : P.Index⦄, i ≠ j →
    ∃ β : P.BridgeBetween i j, β.path.vertexSet ⊆ U

/-- The union of all edges used by paths in the packing. -/
noncomputable def edgeSet (P : PathPacking G S T) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i : P.Index => (P.path i).edgeSet

/-- Membership in the edge set of a path packing is membership in one of its
indexed path edge sets. -/
theorem mem_edgeSet (P : PathPacking G S T) {e : Sym2 V} :
    e ∈ P.edgeSet ↔ ∃ i : P.Index, e ∈ (P.path i).edgeSet := by
  classical
  simp [edgeSet]

/-- The edge set of each indexed path is contained in the packing edge set. -/
theorem path_edgeSet_subset_edgeSet (P : PathPacking G S T) (i : P.Index) :
    (P.path i).edgeSet ⊆ P.edgeSet := by
  intro e he
  exact (P.mem_edgeSet).2 ⟨i, he⟩

/-- Every edge used by a path packing is an ambient graph edge. -/
theorem edgeSet_subset_edgeSet (P : PathPacking G S T) :
    ↑P.edgeSet ⊆ G.edgeSet := by
  classical
  intro e he
  have he' :
      e ∈ Finset.univ.biUnion fun i : P.Index => (P.path i).edgeSet := by
    simpa [edgeSet] using he
  rcases Finset.mem_biUnion.mp he' with ⟨i, _hi, hei⟩
  exact GraphPath.edgeSet_subset_edgeSet (P.path i) (by simpa using hei)

/-- The spanning subgraph consisting of exactly the path-packing edges. -/
noncomputable def spanningGraph (P : PathPacking G S T) : _root_.SimpleGraph V :=
  _root_.SimpleGraph.fromEdgeSet (↑P.edgeSet : Set (Sym2 V))

/-- The path-packing spanning graph is a subgraph of the ambient graph. -/
theorem spanningGraph_le (P : PathPacking G S T) :
    P.spanningGraph ≤ G := by
  intro u v huv
  rw [spanningGraph, _root_.SimpleGraph.fromEdgeSet_adj] at huv
  exact P.edgeSet_subset_edgeSet huv.1

/-- Adjacency in the graph spanned by a path packing comes from an edge of one
of the packed paths. -/
theorem spanningGraph_adj_iff_exists_path_edge (P : PathPacking G S T)
    {u v : V} :
    P.spanningGraph.Adj u v ↔
      (∃ i : P.Index, s(u, v) ∈ (P.path i).edgeSet) ∧ u ≠ v := by
  classical
  rw [spanningGraph, _root_.SimpleGraph.fromEdgeSet_adj]
  constructor
  · intro h
    constructor
    · have hedge : s(u, v) ∈ P.edgeSet := by
        simpa using h.1
      have hedge' :
          s(u, v) ∈ Finset.univ.biUnion fun i : P.Index =>
            (P.path i).edgeSet := by
        simpa [edgeSet] using hedge
      rcases Finset.mem_biUnion.mp hedge' with ⟨i, _hi, hpath⟩
      exact ⟨i, hpath⟩
    · exact h.2
  · rintro ⟨⟨i, hpath⟩, huv⟩
    constructor
    · have hedge :
          s(u, v) ∈ Finset.univ.biUnion fun i : P.Index =>
            (P.path i).edgeSet :=
        Finset.mem_biUnion.mpr ⟨i, by simp, hpath⟩
      simpa [edgeSet] using hedge
    · exact huv

/-- In the spanning graph of a node-disjoint packing, an edge incident with
one packed path stays on that same packed path. -/
theorem mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet
    (P : PathPacking G S T) {r : P.Index} {u v : V}
    (hu : u ∈ (P.path r).vertexSet) (huv : P.spanningGraph.Adj u v) :
    v ∈ (P.path r).vertexSet := by
  classical
  rcases (P.spanningGraph_adj_iff_exists_path_edge).1 huv with
    ⟨⟨i, he⟩, _hne⟩
  have heWalk : s(u, v) ∈ (P.path i).walk.edges := by
    simpa [GraphPath.edgeSet] using he
  have hu_i : u ∈ (P.path i).vertexSet := by
    simpa [GraphPath.vertexSet] using
      (P.path i).walk.fst_mem_support_of_mem_edges heWalk
  have hv_i : v ∈ (P.path i).vertexSet := by
    simpa [GraphPath.vertexSet] using
      (P.path i).walk.snd_mem_support_of_mem_edges heWalk
  by_cases hir : i = r
  · simpa [hir] using hv_i
  · exact False.elim
      (Finset.disjoint_left.mp (P.node_disjoint hir) hu_i hu)

/-- A walk in a packing's spanning graph that starts on one packed path never
leaves that path. -/
theorem spanningGraph_walk_support_subset_path
    (P : PathPacking G S T) (r : P.Index)
    {u v : V} (W : P.spanningGraph.Walk u v)
    (hu : u ∈ (P.path r).vertexSet) :
    ∀ x ∈ W.support, x ∈ (P.path r).vertexSet := by
  induction W with
  | nil =>
      intro x hx
      simp at hx
      subst x
      exact hu
  | @cons u v z huv W ih =>
      intro x hx
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih
          (P.mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet
            hu huv) x hx

/-- A graph path using only the edges of a node-disjoint packing and starting
on one packed path is wholly contained in that packed path. -/
theorem path_vertexSet_subset_of_edgeSet_subset_of_source_mem
    (P : PathPacking G S T) (Q : GraphPath G) (r : P.Index)
    (hQedge : Q.edgeSet ⊆ P.edgeSet)
    (hsource : Q.source ∈ (P.path r).vertexSet) :
    Q.vertexSet ⊆ (P.path r).vertexSet := by
  classical
  let Q' : GraphPath P.spanningGraph :=
    Q.transfer P.spanningGraph (by
      intro e he
      rw [spanningGraph, _root_.SimpleGraph.edgeSet_fromEdgeSet]
      constructor
      · apply hQedge
        simpa [GraphPath.edgeSet] using he
      · exact G.not_isDiag_of_mem_edgeSet
          (Q.walk.edges_subset_edgeSet he))
  intro x hx
  have hx' : x ∈ Q'.walk.support := by
    have hxQ' : x ∈ Q'.vertexSet := by
      simpa [Q'] using hx
    simpa [GraphPath.vertexSet] using hxQ'
  exact P.spanningGraph_walk_support_subset_path r Q'.walk
    (by simpa [Q'] using hsource) x hx'

/-- A path using only the edges of a node-disjoint packing and starting on one
packed path uses only the edges of that indexed path. -/
theorem path_edgeSet_subset_of_edgeSet_subset_of_source_mem
    (P : PathPacking G S T) (Q : GraphPath G) (r : P.Index)
    (hQedge : Q.edgeSet ⊆ P.edgeSet)
    (hsource : Q.source ∈ (P.path r).vertexSet) :
    Q.edgeSet ⊆ (P.path r).edgeSet := by
  classical
  have hQvertex :
      Q.vertexSet ⊆ (P.path r).vertexSet :=
    P.path_vertexSet_subset_of_edgeSet_subset_of_source_mem
      Q r hQedge hsource
  intro e heQ
  rcases P.mem_edgeSet.mp (hQedge heQ) with ⟨j, hej⟩
  by_cases hjr : j = r
  · simpa [hjr] using hej
  have heout : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  have hxQ : e.out.1 ∈ Q.vertexSet := by
    have heQ' : s(e.out.1, e.out.2) ∈ Q.edgeSet := by
      rw [heout]
      exact heQ
    exact
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q
        heQ').1
  have hxr : e.out.1 ∈ (P.path r).vertexSet :=
    hQvertex hxQ
  have hxj : e.out.1 ∈ (P.path j).vertexSet := by
    have hej' : s(e.out.1, e.out.2) ∈ (P.path j).edgeSet := by
      rw [heout]
      exact hej
    exact
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path j)
        hej').1
  exact False.elim
    (Finset.disjoint_left.mp (P.node_disjoint hjr) hxj hxr)

/-- A path packing can be viewed as a packing in the graph spanned by exactly
its own path edges. -/
noncomputable def inSpanningGraph (P : PathPacking G S T) :
    PathPacking P.spanningGraph S T :=
  P.transfer P.spanningGraph (by
    classical
    intro i e he
    rw [spanningGraph, _root_.SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · have hei_path : e ∈ (P.path i).edgeSet := by
        simpa [GraphPath.edgeSet] using he
      exact by
        simpa [edgeSet, hei_path] using
          (Finset.mem_biUnion.mpr ⟨i, by simp, hei_path⟩ :
            e ∈ (Finset.univ.biUnion fun i : P.Index => (P.path i).edgeSet))
    · exact G.not_isDiag_of_mem_edgeSet ((P.path i).walk.edges_subset_edgeSet he))

@[simp] theorem inSpanningGraph_card (P : PathPacking G S T) :
    P.inSpanningGraph.card = P.card := rfl

@[simp] theorem inSpanningGraph_path_vertexSet (P : PathPacking G S T)
    (i : P.Index) :
    (P.inSpanningGraph.path i).vertexSet = (P.path i).vertexSet := by
  simp [inSpanningGraph, transfer]

/-- Two path packings are mutually node-disjoint. -/
def MutuallyNodeDisjoint {S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking G S' T') : Prop :=
  ∀ i : P.Index, ∀ j : Q.Index,
    GraphPath.NodeDisjoint (P.path i) (Q.path j)

theorem mutuallyNodeDisjoint_symm {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyNodeDisjoint Q) :
    Q.MutuallyNodeDisjoint P := by
  intro j i
  exact GraphPath.nodeDisjoint_symm (h i j)

/-- Mutually node-disjoint path packings have disjoint total vertex sets. -/
theorem vertexSet_disjoint_of_mutuallyNodeDisjoint {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyNodeDisjoint Q) :
    Disjoint P.vertexSet Q.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  rcases (P.mem_vertexSet).1 hvP with ⟨i, hvi⟩
  rcases (Q.mem_vertexSet).1 hvQ with ⟨j, hvj⟩
  exact Finset.disjoint_left.mp (h i j) hvi hvj

/-- Two path packings are mutually edge-disjoint. -/
def MutuallyEdgeDisjoint {S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking G S' T') : Prop :=
  ∀ i : P.Index, ∀ j : Q.Index,
    GraphPath.EdgeDisjoint (P.path i) (Q.path j)

theorem mutuallyEdgeDisjoint_symm {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyEdgeDisjoint Q) :
    Q.MutuallyEdgeDisjoint P := by
  intro j i
  exact GraphPath.edgeDisjoint_symm (h i j)

/-- Mutually edge-disjoint path packings have disjoint total edge sets. -/
theorem edgeSet_disjoint_of_mutuallyEdgeDisjoint {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyEdgeDisjoint Q) :
    Disjoint P.edgeSet Q.edgeSet := by
  classical
  rw [Finset.disjoint_left]
  intro e heP heQ
  rcases (P.mem_edgeSet).1 heP with ⟨i, hei⟩
  rcases (Q.mem_edgeSet).1 heQ with ⟨j, hej⟩
  exact Finset.disjoint_left.mp (h i j) hei hej

/-- Orient every path in a packing from the first terminal set to the second
terminal set. -/
def orient (P : PathPacking G S T) : PathPacking G S T where
  Index := P.Index
  path := fun i => (P.path i).orient (P.connects i)
  connects := by
    intro i
    exact Or.inl ⟨GraphPath.orient_source_mem (P.path i) (P.connects i),
      GraphPath.orient_target_mem (P.path i) (P.connects i)⟩
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

@[simp] theorem orient_card (P : PathPacking G S T) :
    P.orient.card = P.card := rfl

@[simp] theorem orient_path_vertexSet (P : PathPacking G S T) (i : P.Index) :
    (P.orient.path i).vertexSet = (P.path i).vertexSet := by
  simp [orient]

@[simp] theorem orient_path_edgeSet (P : PathPacking G S T) (i : P.Index) :
    (P.orient.path i).edgeSet = (P.path i).edgeSet := by
  simp [orient]

@[simp] theorem orient_edgeSet (P : PathPacking G S T) :
    P.orient.edgeSet = P.edgeSet := by
  classical
  ext e
  rw [PathPacking.mem_edgeSet, PathPacking.mem_edgeSet]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa using hi⟩

/-- The left terminals actually used by an oriented path packing. -/
noncomputable def sourceSet (P : PathPacking G S T) : Finset V :=
  Finset.univ.image fun i : P.Index => (P.orient.path i).source

/-- The right terminals actually used by an oriented path packing. -/
noncomputable def targetSet (P : PathPacking G S T) : Finset V :=
  Finset.univ.image fun i : P.Index => (P.orient.path i).target

theorem sourceSet_subset_left (P : PathPacking G S T) :
    P.sourceSet ⊆ S := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact GraphPath.orient_source_mem (P.path i) (P.connects i)

theorem targetSet_subset_right (P : PathPacking G S T) :
    P.targetSet ⊆ T := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact GraphPath.orient_target_mem (P.path i) (P.connects i)

/-- Membership in the used source-terminal set is witnessed by an indexed
oriented path with that source. -/
theorem exists_orient_source_eq_of_mem_sourceSet
    (P : PathPacking G S T) {v : V} (hv : v ∈ P.sourceSet) :
    ∃ i : P.Index, (P.orient.path i).source = v := by
  classical
  rcases Finset.mem_image.mp hv with ⟨i, _hi, h⟩
  exact ⟨i, h⟩

/-- Membership in the used target-terminal set is witnessed by an indexed
oriented path with that target. -/
theorem exists_orient_target_eq_of_mem_targetSet
    (P : PathPacking G S T) {v : V} (hv : v ∈ P.targetSet) :
    ∃ i : P.Index, (P.orient.path i).target = v := by
  classical
  rcases Finset.mem_image.mp hv with ⟨i, _hi, h⟩
  exact ⟨i, h⟩

/-- An oriented path in a packing can contain a used source terminal only if
that terminal is its own source. -/
theorem eq_orient_source_of_mem_sourceSet_of_mem_orient_path_vertexSet
    (P : PathPacking G S T) (i : P.Index) {v : V}
    (hvS : v ∈ P.sourceSet)
    (hvpath : v ∈ (P.orient.path i).vertexSet) :
    v = (P.orient.path i).source := by
  classical
  rcases P.exists_orient_source_eq_of_mem_sourceSet hvS with ⟨j, hj⟩
  by_cases hji : j = i
  · simpa [hji] using hj.symm
  · have hvj : v ∈ (P.orient.path j).vertexSet := by
      simpa [hj] using GraphPath.source_mem_vertexSet (P.orient.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.orient.node_disjoint hji) hvj hvpath)

/-- An oriented path in a packing can contain a used target terminal only if
that terminal is its own target. -/
theorem eq_orient_target_of_mem_targetSet_of_mem_orient_path_vertexSet
    (P : PathPacking G S T) (i : P.Index) {v : V}
    (hvT : v ∈ P.targetSet)
    (hvpath : v ∈ (P.orient.path i).vertexSet) :
    v = (P.orient.path i).target := by
  classical
  rcases P.exists_orient_target_eq_of_mem_targetSet hvT with ⟨j, hj⟩
  by_cases hji : j = i
  · simpa [hji] using hj.symm
  · have hvj : v ∈ (P.orient.path j).vertexSet := by
      simpa [hj] using GraphPath.target_mem_vertexSet (P.orient.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.orient.node_disjoint hji) hvj hvpath)

@[simp] theorem sourceSet_card (P : PathPacking G S T) :
    P.sourceSet.card = P.card := by
  rw [sourceSet, Finset.card_image_of_injective]
  · simp [card]
  · intro i j hij
    by_contra hne
    have hdisj := P.orient.node_disjoint hne
    have hi :
        (P.orient.path i).source ∈ (P.orient.path i).vertexSet :=
      GraphPath.source_mem_vertexSet (P.orient.path i)
    have hj :
        (P.orient.path i).source ∈ (P.orient.path j).vertexSet := by
      simpa [hij] using GraphPath.source_mem_vertexSet (P.orient.path j)
    exact Finset.disjoint_left.mp hdisj hi hj

@[simp] theorem targetSet_card (P : PathPacking G S T) :
    P.targetSet.card = P.card := by
  rw [targetSet, Finset.card_image_of_injective]
  · simp [card]
  · intro i j hij
    by_contra hne
    have hdisj := P.orient.node_disjoint hne
    have hi :
        (P.orient.path i).target ∈ (P.orient.path i).vertexSet :=
      GraphPath.target_mem_vertexSet (P.orient.path i)
    have hj :
        (P.orient.path i).target ∈ (P.orient.path j).vertexSet := by
      simpa [hij] using GraphPath.target_mem_vertexSet (P.orient.path j)
    exact Finset.disjoint_left.mp hdisj hi hj

/-- If a path packing has as many paths as left terminals, its used source
terminal set is the whole left terminal set. -/
theorem sourceSet_eq_left_of_card_eq (P : PathPacking G S T)
    (hcard : P.card = S.card) :
    P.sourceSet = S := by
  exact Finset.eq_of_subset_of_card_le P.sourceSet_subset_left (by
    rw [sourceSet_card, hcard])

/-- If a path packing has as many paths as right terminals, its used target
terminal set is the whole right terminal set. -/
theorem targetSet_eq_right_of_card_eq (P : PathPacking G S T)
    (hcard : P.card = T.card) :
    P.targetSet = T := by
  exact Finset.eq_of_subset_of_card_le P.targetSet_subset_right (by
    rw [targetSet_card, hcard])

/-- Distinct paths in an oriented packing have distinct right endpoints. -/
theorem orient_target_injective (P : PathPacking G S T) :
    Function.Injective fun i : P.Index => (P.orient.path i).target := by
  intro i j hij
  by_contra hne
  have hdisj := P.orient.node_disjoint hne
  have hi :
      (P.orient.path i).target ∈ (P.orient.path i).vertexSet :=
    GraphPath.target_mem_vertexSet (P.orient.path i)
  have hj :
      (P.orient.path i).target ∈ (P.orient.path j).vertexSet := by
    simpa [hij] using GraphPath.target_mem_vertexSet (P.orient.path j)
  exact Finset.disjoint_left.mp hdisj hi hj

/-- Orienting a packing preserves the property that all paths stay in a finite
vertex set. -/
theorem orient_staysIn {P : PathPacking G S T} {U : Finset V}
    (hP : P.StaysIn U) :
    P.orient.StaysIn U := by
  intro i
  simpa [orient_path_vertexSet] using hP i

/-- Orienting a packing preserves internal disjointness from a vertex set. -/
theorem orient_internallyDisjointFromSet
    {P : PathPacking G S T} {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    P.orient.InternallyDisjointFromSet U := by
  intro i v hv hU
  exact (GraphPath.orient_isEndpoint (P.path i) (P.connects i)).2
    (hP i (by simpa [PathPacking.orient_path_vertexSet] using hv) hU)

/-- Orienting a packing preserves localized pairwise bridges. -/
theorem orient_hasPairwiseBridgesIn {P : PathPacking G S T} {U : Finset V}
    (h : P.HasPairwiseBridgesIn U) :
    P.orient.HasPairwiseBridgesIn U := by
  intro i j hij
  rcases h hij with ⟨β, hβU⟩
  let β' : P.orient.BridgeBetween i j := {
    path := β.path
    connects := by
      simpa [PathPacking.orient_path_vertexSet] using β.connects
    internallyDisjoint := by
      intro v hv hrows
      exact β.internallyDisjoint hv (by
        simpa [PathPacking.orient, PathPacking.vertexSet] using hrows)
  }
  exact ⟨β', by simpa [β'] using hβU⟩

/-- An oriented path of a packing always meets the right terminal set at its
target endpoint. -/
theorem orient_path_meets_right (P : PathPacking G S T) (i : P.Index) :
    ((P.orient.path i).vertexSet ∩ T).Nonempty := by
  exact ⟨(P.orient.path i).target, Finset.mem_inter.2
    ⟨GraphPath.target_mem_vertexSet (P.orient.path i),
      GraphPath.orient_target_mem (P.path i) (P.connects i)⟩⟩

/-- Clean a packing by replacing every oriented path with the prefix ending at
its first hit of the right terminal set.  The index set and left endpoints are
unchanged, while every resulting path is internally disjoint from the right
terminal set. -/
noncomputable def cleanToRight (P : PathPacking G S T) :
    PathPacking G S T where
  Index := P.Index
  path := fun i =>
    (P.orient.path i).cleanPrefixToSet T (P.orient_path_meets_right i)
  connects := by
    intro i
    exact Or.inl
      ⟨by
        simpa using GraphPath.orient_source_mem (P.path i) (P.connects i),
       by
        exact (P.orient.path i).cleanPrefixToSet_target_mem T
          (P.orient_path_meets_right i)⟩
  node_disjoint := by
    intro i j hij
    refine (P.orient.node_disjoint hij).mono ?_ ?_
    · exact (P.orient.path i).cleanPrefixToSet_vertexSet_subset T
        (P.orient_path_meets_right i)
    · exact (P.orient.path j).cleanPrefixToSet_vertexSet_subset T
        (P.orient_path_meets_right j)

@[simp] theorem cleanToRight_card (P : PathPacking G S T) :
    P.cleanToRight.card = P.card := rfl

theorem cleanToRight_path_vertexSet_subset
    (P : PathPacking G S T) (i : P.Index) :
    (P.cleanToRight.path i).vertexSet ⊆ (P.path i).vertexSet := by
  intro v hv
  have hv' :
      v ∈ (P.orient.path i).vertexSet :=
    (P.orient.path i).cleanPrefixToSet_vertexSet_subset T
      (P.orient_path_meets_right i) hv
  simpa [PathPacking.orient_path_vertexSet] using hv'

/-- Cleaning a packing makes every path internally disjoint from the right
terminal set. -/
theorem cleanToRight_internallyDisjointFromSet
    (P : PathPacking G S T) :
    P.cleanToRight.InternallyDisjointFromSet T := by
  intro i
  exact (P.orient.path i).cleanPrefixToSet_internallyDisjointFromSet T
    (P.orient_path_meets_right i)

@[simp] theorem cleanToRight_orient_path_source
    (P : PathPacking G S T) (i : P.Index) :
    (P.cleanToRight.orient.path i).source = (P.orient.path i).source := by
  classical
  have hst :
      (P.cleanToRight.path i).source ∈ S ∧
        (P.cleanToRight.path i).target ∈ T := by
    exact ⟨by
      simpa [cleanToRight] using
        GraphPath.orient_source_mem (P.path i) (P.connects i),
      by
        dsimp [cleanToRight]
        exact (P.orient.path i).cleanPrefixToSet_target_mem T
          (P.orient_path_meets_right i)⟩
  change ((P.cleanToRight.path i).orient (P.cleanToRight.connects i)).source =
    (P.orient.path i).source
  rw [GraphPath.orient, if_pos hst]
  rfl

@[simp] theorem cleanToRight_sourceSet
    (P : PathPacking G S T) :
    P.cleanToRight.sourceSet = P.sourceSet := by
  classical
  ext v
  rw [sourceSet, sourceSet]
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    cleanToRight_orient_path_source]
  rfl

/-- A packing is terminal-clean when no oriented path has an internal vertex
in either terminal set. -/
def TerminalClean (P : PathPacking G S T) : Prop :=
  P.InternallyDisjointFromSet (S ∪ T)

/-- Clean every path in a packing so that it has no internal vertices in
`S ∪ T`.  This preserves the index set and node-disjointness because each new
path is a subpath of the corresponding old one. -/
noncomputable def cleanToTerminals (P : PathPacking G S T) :
    PathPacking G S T where
  Index := P.Index
  path := fun i => (P.path i).cleanBetweenTerminalSets (P.connects i)
  connects := fun i => (P.path i).cleanBetweenTerminalSets_connects (P.connects i)
  node_disjoint := by
    intro i j hij
    refine (P.node_disjoint hij).mono ?_ ?_
    · exact (P.path i).cleanBetweenTerminalSets_vertexSet_subset (P.connects i)
    · exact (P.path j).cleanBetweenTerminalSets_vertexSet_subset (P.connects j)

@[simp] theorem cleanToTerminals_card (P : PathPacking G S T) :
    P.cleanToTerminals.card = P.card := rfl

theorem cleanToTerminals_path_vertexSet_subset
    (P : PathPacking G S T) (i : P.Index) :
    (P.cleanToTerminals.path i).vertexSet ⊆ (P.path i).vertexSet :=
  (P.path i).cleanBetweenTerminalSets_vertexSet_subset (P.connects i)

/-- Cleaning a packing at both terminal sets makes it terminal-clean. -/
theorem cleanToTerminals_terminalClean (P : PathPacking G S T) :
    P.cleanToTerminals.TerminalClean := by
  intro i
  exact (P.path i).cleanBetweenTerminalSets_internallyDisjointFromSet_union
    (P.connects i)

/-- Map every path in a packing to a supergraph on the same vertex type. -/
def mapLe (P : PathPacking G S T) {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    PathPacking H S T where
  Index := P.Index
  path := fun i => (P.path i).mapLe hGH
  connects := by
    intro i
    simpa [GraphPath.mapLe, GraphPath.Connects] using P.connects i
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

/-- View a path packing as connecting larger terminal sets.  A path packing
only requires each path to have one endpoint in each terminal set, so enlarging
the allowed terminal sets preserves the same indexed paths and all
node-disjointness information. -/
def widenTerminals {S' T' : Finset V} (P : PathPacking G S T)
    (hS : S ⊆ S') (hT : T ⊆ T') :
    PathPacking G S' T' where
  Index := P.Index
  path := P.path
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨hS h.1, hT h.2⟩
    · exact Or.inr ⟨hT h.1, hS h.2⟩
  node_disjoint := P.node_disjoint

@[simp] theorem widenTerminals_card {S' T' : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T') :
    (P.widenTerminals hS hT).card = P.card := rfl

@[simp] theorem widenTerminals_path_vertexSet {S' T' : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T')
    (i : (P.widenTerminals hS hT).Index) :
    ((P.widenTerminals hS hT).path i).vertexSet = (P.path i).vertexSet := rfl

@[simp] theorem widenTerminals_vertexSet {S' T' : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T') :
    (P.widenTerminals hS hT).vertexSet = P.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩

/-- Widening terminal sets preserves localized pairwise bridges. -/
theorem widenTerminals_hasPairwiseBridgesIn {S' T' U : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T')
    (h : P.HasPairwiseBridgesIn U) :
    (P.widenTerminals hS hT).HasPairwiseBridgesIn U := by
  intro i j hij
  rcases h hij with ⟨β, hβU⟩
  let β' : (P.widenTerminals hS hT).BridgeBetween i j := {
    path := β.path
    connects := by
      simpa [PathPacking.widenTerminals] using β.connects
    internallyDisjoint := by
      intro v hv hrows
      exact β.internallyDisjoint hv (by
        simpa [PathPacking.widenTerminals_vertexSet] using hrows)
  }
  exact ⟨β', by simpa [β'] using hβU⟩

@[simp] theorem mapLe_card (P : PathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).card = P.card := rfl

@[simp] theorem mapLe_vertexSet (P : PathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).vertexSet = P.vertexSet := by
  classical
  ext v
  simp [mapLe, vertexSet, GraphPath.mapLe_vertexSet]

@[simp] theorem mapLe_edgeSet (P : PathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).edgeSet = P.edgeSet := by
  classical
  ext e
  simp [mapLe, edgeSet, GraphPath.mapLe_edgeSet]

end PathPacking

/-- An oriented perfect path packing from `S` to `T`.

Unlike `PathPacking`, this structure records that each path starts in `S`, ends
in `T`, and that both endpoint maps are bijections.  This is the formal object
needed for the "every vertex of `B_i` to a distinct vertex of `A_{i+1}`"
phrases in the path-of-sets proof.
-/
structure PerfectPathPacking {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) extends PathPacking G S T where
  /-- Every path starts in the left endpoint set. -/
  source_mem : ∀ i : Index, (path i).source ∈ S
  /-- Every path ends in the right endpoint set. -/
  target_mem : ∀ i : Index, (path i).target ∈ T
  /-- Every left endpoint is used exactly once. -/
  source_bijective :
    Function.Bijective (fun i : Index => (⟨(path i).source, source_mem i⟩ : {v // v ∈ S}))
  /-- Every right endpoint is used exactly once. -/
  target_bijective :
    Function.Bijective (fun i : Index => (⟨(path i).target, target_mem i⟩ : {v // v ∈ T}))

namespace PerfectPathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

instance (P : PerfectPathPacking G S T) : Fintype P.Index := P.indexFintype
instance (P : PerfectPathPacking G S T) : DecidableEq P.Index := P.indexDecidableEq

/-- The number of paths in a perfect packing. -/
noncomputable def card (P : PerfectPathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- Reindex a perfect path packing by an equivalent finite index type. -/
noncomputable def reindex {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PerfectPathPacking G S T) (e : ι ≃ P.Index) :
    PerfectPathPacking G S T where
  toPathPacking := P.toPathPacking.reindex e
  source_mem := fun i => P.source_mem (e i)
  target_mem := fun i => P.target_mem (e i)
  source_bijective := by
    constructor
    · intro i j hij
      apply e.injective
      apply P.source_bijective.1
      exact hij
    · intro v
      rcases P.source_bijective.2 v with ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      change
        (⟨(P.path (e (e.symm j))).source,
          P.source_mem (e (e.symm j))⟩ : {x // x ∈ S}) = v
      simpa using hj
  target_bijective := by
    constructor
    · intro i j hij
      apply e.injective
      apply P.target_bijective.1
      exact hij
    · intro v
      rcases P.target_bijective.2 v with ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      change
        (⟨(P.path (e (e.symm j))).target,
          P.target_mem (e (e.symm j))⟩ : {x // x ∈ T}) = v
      simpa using hj

@[simp] theorem reindex_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PerfectPathPacking G S T) (e : ι ≃ P.Index) :
    (P.reindex e).card = P.card := by
  dsimp [reindex, card, PathPacking.reindex]
  exact Fintype.card_congr e

@[simp] theorem reindex_path_vertexSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PerfectPathPacking G S T) (e : ι ≃ P.Index) (i : ι) :
    ((P.reindex e).path i).vertexSet = (P.path (e i)).vertexSet := rfl

/-- The canonical equivalence from `Fin P.card` to the index type of a
perfect path packing. -/
noncomputable def finIndexEquiv (P : PerfectPathPacking G S T) :
    Fin P.card ≃ P.Index := by
  simpa [card] using (Fintype.equivFin P.Index).symm

/-- Reindex a perfect path packing by `Fin P.card`. -/
noncomputable def finReindex
    (P : PerfectPathPacking G S T) : PerfectPathPacking G S T :=
  P.reindex P.finIndexEquiv

@[simp] theorem finReindex_card (P : PerfectPathPacking G S T) :
    P.finReindex.card = P.card := by
  simp [finReindex]

/-- The identity perfect packing on a finite terminal set, consisting of one
length-zero path at each terminal. -/
noncomputable def refl (G : _root_.SimpleGraph V) (S : Finset V) :
    PerfectPathPacking G S S where
  toPathPacking := {
    Index := Fin S.card
    path := fun i => GraphPath.refl G ((S.equivFin.symm i).1)
    connects := by
      intro i
      exact Or.inl ⟨(S.equivFin.symm i).2, (S.equivFin.symm i).2⟩
    node_disjoint := by
      intro i j hij
      rw [GraphPath.NodeDisjoint, GraphPath.refl_vertexSet,
        GraphPath.refl_vertexSet, Finset.disjoint_singleton_left]
      intro h
      apply hij
      apply S.equivFin.symm.injective
      have hval :
          (S.equivFin.symm i).1 = (S.equivFin.symm j).1 := by
        simpa using h
      exact Subtype.ext hval
  }
  source_mem := fun i => (S.equivFin.symm i).2
  target_mem := fun i => (S.equivFin.symm i).2
  source_bijective := by
    constructor
    · intro i j h
      apply S.equivFin.symm.injective
      exact Subtype.ext (congrArg Subtype.val h)
    · intro v
      refine ⟨S.equivFin v, ?_⟩
      apply Subtype.ext
      simp
  target_bijective := by
    constructor
    · intro i j h
      apply S.equivFin.symm.injective
      exact Subtype.ext (congrArg Subtype.val h)
    · intro v
      refine ⟨S.equivFin v, ?_⟩
      apply Subtype.ext
      simp

@[simp] theorem refl_card (G : _root_.SimpleGraph V) (S : Finset V) :
    (PerfectPathPacking.refl G S).card = S.card := by
  classical
  change Fintype.card (Fin S.card) = S.card
  simp

@[simp] theorem toPathPacking_card (P : PerfectPathPacking G S T) :
    P.toPathPacking.card = P.card := rfl

/-- Transfer every path in a perfect packing to another graph on the same vertex
type, preserving the endpoint bijections. -/
def transfer (P : PerfectPathPacking G S T) (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e, e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    PerfectPathPacking H S T where
  toPathPacking := P.toPathPacking.transfer H h
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_bijective := by
    simpa [PathPacking.transfer, GraphPath.transfer] using P.source_bijective
  target_bijective := by
    simpa [PathPacking.transfer, GraphPath.transfer] using P.target_bijective

/-- A perfect packing has as many paths as left endpoints. -/
theorem card_eq_left_card (P : PerfectPathPacking G S T) :
    P.card = S.card := by
  classical
  dsimp [card]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective _ P.source_bijective)

/-- A perfect packing has as many paths as right endpoints. -/
theorem card_eq_right_card (P : PerfectPathPacking G S T) :
    P.card = T.card := by
  classical
  dsimp [card]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective _ P.target_bijective)

/-- The bijection from path indices to left endpoints. -/
noncomputable def sourceEquiv (P : PerfectPathPacking G S T) :
    P.Index ≃ {v // v ∈ S} :=
  Equiv.ofBijective _ P.source_bijective

/-- The bijection from path indices to right endpoints. -/
noncomputable def targetEquiv (P : PerfectPathPacking G S T) :
    P.Index ≃ {v // v ∈ T} :=
  Equiv.ofBijective _ P.target_bijective

/-- The unique path index whose source is a given left endpoint. -/
noncomputable def indexOfSource (P : PerfectPathPacking G S T)
    (v : {x // x ∈ S}) : P.Index :=
  (P.sourceEquiv).symm v

/-- The unique path index whose target is a given right endpoint. -/
noncomputable def indexOfTarget (P : PerfectPathPacking G S T)
    (v : {x // x ∈ T}) : P.Index :=
  (P.targetEquiv).symm v

@[simp] theorem source_indexOfSource (P : PerfectPathPacking G S T)
    (v : {x // x ∈ S}) :
    (⟨(P.path (P.indexOfSource v)).source,
      P.source_mem (P.indexOfSource v)⟩ : {x // x ∈ S}) = v := by
  exact (P.sourceEquiv).apply_symm_apply v

@[simp] theorem target_indexOfTarget (P : PerfectPathPacking G S T)
    (v : {x // x ∈ T}) :
    (⟨(P.path (P.indexOfTarget v)).target,
      P.target_mem (P.indexOfTarget v)⟩ : {x // x ∈ T}) = v := by
  exact (P.targetEquiv).apply_symm_apply v

@[simp] theorem indexOfSource_source (P : PerfectPathPacking G S T)
    (i : P.Index) :
    P.indexOfSource ⟨(P.path i).source, P.source_mem i⟩ = i := by
  exact (P.sourceEquiv).symm_apply_apply i

@[simp] theorem indexOfTarget_target (P : PerfectPathPacking G S T)
    (i : P.Index) :
    P.indexOfTarget ⟨(P.path i).target, P.target_mem i⟩ = i := by
  exact (P.targetEquiv).symm_apply_apply i

/-- Given perfect packings from `S` to `T` and from `T` to `U`, this is the
index of the second packing whose source matches the target of the first path. -/
noncomputable def indexOfSourceTarget {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (i : P.Index) : Q.Index :=
  Q.indexOfSource ⟨(P.path i).target, P.target_mem i⟩

@[simp] theorem source_indexOfSourceTarget {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (i : P.Index) :
    (Q.path (P.indexOfSourceTarget Q i)).source = (P.path i).target := by
  have h :=
    congrArg Subtype.val
      (source_indexOfSource Q ⟨(P.path i).target, P.target_mem i⟩)
  simpa [indexOfSourceTarget] using h

/-- A path in a perfect packing meets the source terminal set only at its own
source.  If it met another source terminal, it would meet the path whose source
is that terminal, contradicting node-disjointness. -/
theorem eq_source_of_mem_left_of_mem_path_vertexSet
    (P : PerfectPathPacking G S T) (i : P.Index)
    {v : V} (hvS : v ∈ S) (hvpath : v ∈ (P.path i).vertexSet) :
    v = (P.path i).source := by
  classical
  let j := P.indexOfSource ⟨v, hvS⟩
  have hsource_j : (P.path j).source = v := by
    have h :=
      congrArg Subtype.val (P.source_indexOfSource ⟨v, hvS⟩)
    simpa [j] using h
  by_cases hji : j = i
  · simpa [hji] using hsource_j.symm
  · have hvj : v ∈ (P.path j).vertexSet := by
      simpa [hsource_j] using GraphPath.source_mem_vertexSet (P.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hji)
        hvj hvpath)

/-- A path in a perfect packing meets the target terminal set only at its own
target. -/
theorem eq_target_of_mem_right_of_mem_path_vertexSet
    (P : PerfectPathPacking G S T) (i : P.Index)
    {v : V} (hvT : v ∈ T) (hvpath : v ∈ (P.path i).vertexSet) :
    v = (P.path i).target := by
  classical
  let j := P.indexOfTarget ⟨v, hvT⟩
  have htarget_j : (P.path j).target = v := by
    have h :=
      congrArg Subtype.val (P.target_indexOfTarget ⟨v, hvT⟩)
    simpa [j] using h
  by_cases hji : j = i
  · simpa [hji] using htarget_j.symm
  · have hvj : v ∈ (P.path j).vertexSet := by
      simpa [htarget_j] using GraphPath.target_mem_vertexSet (P.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hji)
        hvj hvpath)

/-- Map every path in a perfect packing to a supergraph on the same vertex type. -/
def mapLe (P : PerfectPathPacking G S T) {H : _root_.SimpleGraph V}
    (hGH : G ≤ H) :
    PerfectPathPacking H S T where
  toPathPacking := P.toPathPacking.mapLe hGH
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_bijective := by
    simpa [PathPacking.mapLe, GraphPath.mapLe] using P.source_bijective
  target_bijective := by
    simpa [PathPacking.mapLe, GraphPath.mapLe] using P.target_bijective

@[simp] theorem mapLe_card (P : PerfectPathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).card = P.card := rfl

@[simp] theorem mapLe_vertexSet (P : PerfectPathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).toPathPacking.vertexSet = P.toPathPacking.vertexSet := by
  simp [mapLe]

@[simp] theorem mapLe_edgeSet (P : PerfectPathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).toPathPacking.edgeSet = P.toPathPacking.edgeSet := by
  simp [mapLe]

/-- The disjoint union of two perfect path packings with disjoint terminal
sets and mutually disjoint paths.  The index type is the sum of the two input
index types. -/
noncomputable def disjointUnion
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    PerfectPathPacking G (S₁ ∪ S₂) (T₁ ∪ T₂) where
  toPathPacking := {
    Index := P₁.Index ⊕ P₂.Index
    path := fun i =>
      match i with
      | Sum.inl a => P₁.path a
      | Sum.inr b => P₂.path b
    connects := by
      intro i
      cases i with
      | inl a =>
          exact Or.inl
            ⟨Finset.mem_union_left _ (P₁.source_mem a),
              Finset.mem_union_left _ (P₁.target_mem a)⟩
      | inr b =>
          exact Or.inl
            ⟨Finset.mem_union_right _ (P₂.source_mem b),
              Finset.mem_union_right _ (P₂.target_mem b)⟩
    node_disjoint := by
      intro i j hij
      cases i with
      | inl a =>
          cases j with
          | inl b =>
              exact P₁.toPathPacking.node_disjoint
                (fun h => hij (by simp [h]))
          | inr b =>
              exact hnode a b
      | inr a =>
          cases j with
          | inl b =>
              exact GraphPath.nodeDisjoint_symm (hnode b a)
          | inr b =>
              exact P₂.toPathPacking.node_disjoint
                (fun h => hij (by simp [h]))
  }
  source_mem := by
    intro i
    cases i with
    | inl a => exact Finset.mem_union_left _ (P₁.source_mem a)
    | inr b => exact Finset.mem_union_right _ (P₂.source_mem b)
  target_mem := by
    intro i
    cases i with
    | inl a => exact Finset.mem_union_left _ (P₁.target_mem a)
    | inr b => exact Finset.mem_union_right _ (P₂.target_mem b)
  source_bijective := by
    classical
    constructor
    · intro i j hij
      cases i with
      | inl a =>
          cases j with
          | inl b =>
              apply congrArg Sum.inl
              apply P₁.source_bijective.1
              have hval : (P₁.path a).source = (P₁.path b).source :=
                congrArg (fun x : {v // v ∈ S₁ ∪ S₂} => x.1) hij
              exact Subtype.ext hval
          | inr b =>
              have hval :
                  (P₁.path a).source = (P₂.path b).source :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hS (P₁.source_mem a)
                  (by simpa [← hval] using P₂.source_mem b))
      | inr a =>
          cases j with
          | inl b =>
              have hval :
                  (P₂.path a).source = (P₁.path b).source :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hS (P₁.source_mem b)
                  (by simpa [hval] using P₂.source_mem a))
          | inr b =>
              apply congrArg Sum.inr
              apply P₂.source_bijective.1
              have hval : (P₂.path a).source = (P₂.path b).source :=
                congrArg (fun x : {v // v ∈ S₁ ∪ S₂} => x.1) hij
              exact Subtype.ext hval
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp hv with hv₁ | hv₂
      · rcases P₁.source_bijective.2 ⟨v, hv₁⟩ with ⟨i, hi⟩
        refine ⟨Sum.inl i, ?_⟩
        have hval : (P₁.path i).source = v :=
          congrArg (fun x : {v // v ∈ S₁} => x.1) hi
        exact Subtype.ext hval
      · rcases P₂.source_bijective.2 ⟨v, hv₂⟩ with ⟨i, hi⟩
        refine ⟨Sum.inr i, ?_⟩
        have hval : (P₂.path i).source = v :=
          congrArg (fun x : {v // v ∈ S₂} => x.1) hi
        exact Subtype.ext hval
  target_bijective := by
    classical
    constructor
    · intro i j hij
      cases i with
      | inl a =>
          cases j with
          | inl b =>
              apply congrArg Sum.inl
              apply P₁.target_bijective.1
              have hval : (P₁.path a).target = (P₁.path b).target :=
                congrArg (fun x : {v // v ∈ T₁ ∪ T₂} => x.1) hij
              exact Subtype.ext hval
          | inr b =>
              have hval :
                  (P₁.path a).target = (P₂.path b).target :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hT (P₁.target_mem a)
                  (by simpa [← hval] using P₂.target_mem b))
      | inr a =>
          cases j with
          | inl b =>
              have hval :
                  (P₂.path a).target = (P₁.path b).target :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hT (P₁.target_mem b)
                  (by simpa [hval] using P₂.target_mem a))
          | inr b =>
              apply congrArg Sum.inr
              apply P₂.target_bijective.1
              have hval : (P₂.path a).target = (P₂.path b).target :=
                congrArg (fun x : {v // v ∈ T₁ ∪ T₂} => x.1) hij
              exact Subtype.ext hval
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp hv with hv₁ | hv₂
      · rcases P₁.target_bijective.2 ⟨v, hv₁⟩ with ⟨i, hi⟩
        refine ⟨Sum.inl i, ?_⟩
        have hval : (P₁.path i).target = v :=
          congrArg (fun x : {v // v ∈ T₁} => x.1) hi
        exact Subtype.ext hval
      · rcases P₂.target_bijective.2 ⟨v, hv₂⟩ with ⟨i, hi⟩
        refine ⟨Sum.inr i, ?_⟩
        have hval : (P₂.path i).target = v :=
          congrArg (fun x : {v // v ∈ T₂} => x.1) hi
        exact Subtype.ext hval

@[simp] theorem disjointUnion_card
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    (P₁.disjointUnion P₂ hS hT hnode).card = P₁.card + P₂.card := by
  dsimp [disjointUnion, card, PathPacking.card]
  exact Fintype.card_sum

/-- Edges of a disjoint union packing come from one of the two input packings.
-/
theorem disjointUnion_edgeSet_subset_union
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.edgeSet ⊆
      P₁.toPathPacking.edgeSet ∪ P₂.toPathPacking.edgeSet := by
  classical
  intro e he
  rcases ((P₁.disjointUnion P₂ hS hT hnode).toPathPacking.mem_edgeSet).1 he with
    ⟨i, hei⟩
  cases i with
  | inl a =>
      exact Finset.mem_union_left _
        ((P₁.toPathPacking.mem_edgeSet).2
          ⟨a, by simpa [disjointUnion] using hei⟩)
  | inr b =>
      exact Finset.mem_union_right _
        ((P₂.toPathPacking.mem_edgeSet).2
          ⟨b, by simpa [disjointUnion] using hei⟩)

/-- A disjoint union stays in any vertex set containing every path of both
input packings. -/
theorem disjointUnion_staysIn
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    {U : Finset V}
    (hP₁ : P₁.toPathPacking.StaysIn U)
    (hP₂ : P₂.toPathPacking.StaysIn U) :
    (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.StaysIn U := by
  intro i
  cases i with
  | inl a =>
      simpa [disjointUnion] using hP₁ a
  | inr b =>
      simpa [disjointUnion] using hP₂ b

/-- A disjoint union is internally disjoint from a vertex set when each input
packing is. -/
theorem disjointUnion_internallyDisjointFromSet
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    {U : Finset V}
    (hP₁ : P₁.toPathPacking.InternallyDisjointFromSet U)
    (hP₂ : P₂.toPathPacking.InternallyDisjointFromSet U) :
    (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.InternallyDisjointFromSet U := by
  intro i
  cases i with
  | inl a =>
      simpa [disjointUnion] using hP₁ a
  | inr b =>
      simpa [disjointUnion] using hP₂ b

/-- Lift a perfect path packing that stays inside a finite vertex set to the
induced graph on that set. -/
noncomputable def induce (P : PerfectPathPacking G S T) (U : Finset V)
    (hP : P.toPathPacking.StaysIn U) (hS : S ⊆ U) (hT : T ⊆ U) :
    PerfectPathPacking (G.induce {v : V | v ∈ U})
      (PathPacking.subtypeFinset S U hS)
      (PathPacking.subtypeFinset T U hT) where
  toPathPacking := P.toPathPacking.induce U hP hS hT
  source_mem := by
    intro i
    change ((P.path i).induce U (hP i)).source ∈
      PathPacking.subtypeFinset S U hS
    rw [GraphPath.induce_source]
    exact (PathPacking.mem_subtypeFinset hS _).2 (P.source_mem i)
  target_mem := by
    intro i
    change ((P.path i).induce U (hP i)).target ∈
      PathPacking.subtypeFinset T U hT
    rw [GraphPath.induce_target]
    exact (PathPacking.mem_subtypeFinset hT _).2 (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij
      apply P.source_bijective.1
      apply Subtype.ext
      have hval :
          (((⟨((P.path i).induce U (hP i)).source,
              by
                rw [GraphPath.induce_source]
                exact (PathPacking.mem_subtypeFinset hS _).2
                  (P.source_mem i)⟩ :
              {v // v ∈ PathPacking.subtypeFinset S U hS}).1 :
              {v : V // v ∈ U}).1) =
            (((⟨((P.path j).induce U (hP j)).source,
              by
                rw [GraphPath.induce_source]
                exact (PathPacking.mem_subtypeFinset hS _).2
                  (P.source_mem j)⟩ :
              {v // v ∈ PathPacking.subtypeFinset S U hS}).1 :
              {v : V // v ∈ U}).1) :=
        congrArg
          (fun x : {v // v ∈ PathPacking.subtypeFinset S U hS} =>
            ((x.1 : {v : V // v ∈ U}).1)) hij
      simpa using hval
    · intro v
      have hvS : v.1.1 ∈ S :=
        (PathPacking.mem_subtypeFinset hS v.1).1 v.2
      rcases P.source_bijective.2 ⟨v.1.1, hvS⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have hval : (P.path i).source = v.1.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.induce] using hval
  target_bijective := by
    constructor
    · intro i j hij
      apply P.target_bijective.1
      apply Subtype.ext
      have hval :
          (((⟨((P.path i).induce U (hP i)).target,
              by
                rw [GraphPath.induce_target]
                exact (PathPacking.mem_subtypeFinset hT _).2
                  (P.target_mem i)⟩ :
              {v // v ∈ PathPacking.subtypeFinset T U hT}).1 :
              {v : V // v ∈ U}).1) =
            (((⟨((P.path j).induce U (hP j)).target,
              by
                rw [GraphPath.induce_target]
                exact (PathPacking.mem_subtypeFinset hT _).2
                  (P.target_mem j)⟩ :
              {v // v ∈ PathPacking.subtypeFinset T U hT}).1 :
              {v : V // v ∈ U}).1) :=
        congrArg
          (fun x : {v // v ∈ PathPacking.subtypeFinset T U hT} =>
            ((x.1 : {v : V // v ∈ U}).1)) hij
      simpa using hval
    · intro v
      have hvT : v.1.1 ∈ T :=
        (PathPacking.mem_subtypeFinset hT v.1).1 v.2
      rcases P.target_bijective.2 ⟨v.1.1, hvT⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have hval : (P.path i).target = v.1.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.induce] using hval

@[simp] theorem induce_card (P : PerfectPathPacking G S T) (U : Finset V)
    (hP : P.toPathPacking.StaysIn U) (hS : S ⊆ U) (hT : T ⊆ U) :
    (P.induce U hP hS hT).card = P.card := rfl

/-- Reinterpret a perfect path packing after replacing its terminal sets by
definitionally equal finite sets.  The path index type is preserved exactly,
which is useful when later proofs need to refer back to the original indexed
paths. -/
def copyTerminals {S' T' : Finset V} (P : PerfectPathPacking G S T)
    (hS : S = S') (hT : T = T') :
    PerfectPathPacking G S' T' where
  toPathPacking := {
    Index := P.Index
    path := P.path
    connects := by
      intro i
      rcases P.connects i with h | h
      · exact Or.inl ⟨by simpa [← hS] using h.1,
          by simpa [← hT] using h.2⟩
      · exact Or.inr ⟨by simpa [← hT] using h.1,
          by simpa [← hS] using h.2⟩
    node_disjoint := P.node_disjoint
  }
  source_mem := by
    intro i
    simpa [← hS] using P.source_mem i
  target_mem := by
    intro i
    simpa [← hT] using P.target_mem i
  source_bijective := by
    constructor
    · intro i j hij
      apply P.source_bijective.1
      have hsrc : (P.path i).source = (P.path j).source :=
        congrArg (fun x : {v // v ∈ S'} => x.1) hij
      exact Subtype.ext hsrc
    · rintro ⟨v, hv⟩
      have hvS : v ∈ S := by simpa [hS] using hv
      rcases P.source_bijective.2 ⟨v, hvS⟩ with ⟨i, hi⟩
      have hsrc : (P.path i).source = v :=
        congrArg (fun x : {v // v ∈ S} => x.1) hi
      exact ⟨i, Subtype.ext hsrc⟩
  target_bijective := by
    constructor
    · intro i j hij
      apply P.target_bijective.1
      have htgt : (P.path i).target = (P.path j).target :=
        congrArg (fun x : {v // v ∈ T'} => x.1) hij
      exact Subtype.ext htgt
    · rintro ⟨v, hv⟩
      have hvT : v ∈ T := by simpa [hT] using hv
      rcases P.target_bijective.2 ⟨v, hvT⟩ with ⟨i, hi⟩
      have htgt : (P.path i).target = v :=
        congrArg (fun x : {v // v ∈ T} => x.1) hi
      exact ⟨i, Subtype.ext htgt⟩

@[simp] theorem copyTerminals_card {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T') :
    (P.copyTerminals hS hT).card = P.card := rfl

@[simp] theorem copyTerminals_path_vertexSet {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T')
    (i : (P.copyTerminals hS hT).Index) :
    ((P.copyTerminals hS hT).path i).vertexSet = (P.path i).vertexSet := rfl

@[simp] theorem copyTerminals_vertexSet {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T') :
    (P.copyTerminals hS hT).toPathPacking.vertexSet =
      P.toPathPacking.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩

@[simp] theorem copyTerminals_edgeSet {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T') :
    (P.copyTerminals hS hT).toPathPacking.edgeSet =
      P.toPathPacking.edgeSet := by
  classical
  ext e
  rw [PathPacking.mem_edgeSet, PathPacking.mem_edgeSet]
  constructor
  · rintro ⟨i, he⟩
    exact ⟨i, he⟩
  · rintro ⟨i, he⟩
    exact ⟨i, he⟩

/-- Copying terminal-set equalities preserves containment of all path vertices
in a fixed set. -/
theorem copyTerminals_staysIn {S' T' U : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T')
    (hP : P.toPathPacking.StaysIn U) :
    (P.copyTerminals hS hT).toPathPacking.StaysIn U := by
  intro i v hv
  exact hP i (by simpa [copyTerminals] using hv)

/-- The sources of a chosen set of paths in a perfect packing. -/
noncomputable def sourceSet (P : PerfectPathPacking G S T)
    (I : Finset P.Index) : Finset V :=
  I.image fun i => (P.path i).source

/-- The targets of a chosen set of paths in a perfect packing. -/
noncomputable def targetSet (P : PerfectPathPacking G S T)
    (I : Finset P.Index) : Finset V :=
  I.image fun i => (P.path i).target

theorem sourceSet_subset_left (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    P.sourceSet I ⊆ S := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.source_mem i

theorem targetSet_subset_right (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    P.targetSet I ⊆ T := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.target_mem i

/-- Source endpoints are monotone with respect to the chosen index set. -/
theorem sourceSet_mono (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : I ⊆ J) :
    P.sourceSet I ⊆ P.sourceSet J := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hIJ hi, rfl⟩

/-- Target endpoints are monotone with respect to the chosen index set. -/
theorem targetSet_mono (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : I ⊆ J) :
    P.targetSet I ⊆ P.targetSet J := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hIJ hi, rfl⟩

/-- Disjoint index sets in a perfect packing have disjoint source endpoint
sets. -/
theorem sourceSet_disjoint (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : Disjoint I J) :
    Disjoint (P.sourceSet I) (P.sourceSet J) := by
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  rcases Finset.mem_image.mp hvI with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hvJ with ⟨j, hj, hsource⟩
  have hij : i = j := by
    apply P.source_bijective.1
    exact Subtype.ext hsource.symm
  exact Finset.disjoint_left.mp hIJ hi (by simpa [hij] using hj)

/-- Disjoint index sets in a perfect packing have disjoint target endpoint
sets. -/
theorem targetSet_disjoint (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : Disjoint I J) :
    Disjoint (P.targetSet I) (P.targetSet J) := by
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  rcases Finset.mem_image.mp hvI with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hvJ with ⟨j, hj, htarget⟩
  have hij : i = j := by
    apply P.target_bijective.1
    exact Subtype.ext htarget.symm
  exact Finset.disjoint_left.mp hIJ hi (by simpa [hij] using hj)

@[simp] theorem sourceSet_card (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    (P.sourceSet I).card = I.card := by
  classical
  rw [sourceSet, Finset.card_image_of_injective]
  intro i j hij
  apply P.source_bijective.1
  exact Subtype.ext hij

@[simp] theorem targetSet_card (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    (P.targetSet I).card = I.card := by
  classical
  rw [targetSet, Finset.card_image_of_injective]
  intro i j hij
  apply P.target_bijective.1
  exact Subtype.ext hij

/-- Restrict a perfect path packing to a finite set of its path indices.  The
new terminal sets are the corresponding source and target images. -/
noncomputable def restrictIndexSet (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    PerfectPathPacking G (P.sourceSet I) (P.targetSet I) where
  toPathPacking := {
    Index := {i : P.Index // i ∈ I}
    path := fun i => P.path i.1
    connects := by
      intro i
      exact Or.inl ⟨Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩,
        Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
    node_disjoint := by
      intro i j hij
      exact P.node_disjoint (fun h => hij (Subtype.ext h))
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
  source_bijective := by
    constructor
    · intro i j hij
      have hsrc : (P.path i.1).source = (P.path j.1).source :=
        congrArg (fun x : {v // v ∈ P.sourceSet I} => x.1) hij
      apply Subtype.ext
      apply P.source_bijective.1
      exact Subtype.ext hsrc
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨i, hi, hsource⟩
      exact ⟨⟨i, hi⟩, Subtype.ext hsource⟩
  target_bijective := by
    constructor
    · intro i j hij
      have htgt : (P.path i.1).target = (P.path j.1).target :=
        congrArg (fun x : {v // v ∈ P.targetSet I} => x.1) hij
      apply Subtype.ext
      apply P.target_bijective.1
      exact Subtype.ext htgt
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨i, hi, htarget⟩
      exact ⟨⟨i, hi⟩, Subtype.ext htarget⟩

@[simp] theorem restrictIndexSet_card (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    (P.restrictIndexSet I).card = I.card := by
  classical
  simp [restrictIndexSet, card]

@[simp] theorem restrictIndexSet_path_vertexSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).vertexSet = (P.path i.1).vertexSet := rfl

@[simp] theorem restrictIndexSet_path_edgeSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).edgeSet = (P.path i.1).edgeSet := rfl

theorem restrictIndexSet_vertexSet_subset
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.vertexSet ⊆
      P.toPathPacking.vertexSet := by
  classical
  intro v hv
  rcases ((P.restrictIndexSet I).toPathPacking.mem_vertexSet).1 hv with
    ⟨i, hvPath⟩
  exact (P.toPathPacking.mem_vertexSet).2 ⟨i.1, hvPath⟩

/-- A packing restricted to selected indices stays inside the vertex trace of
the original perfect packing. -/
theorem restrictIndexSet_staysIn_vertexSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.StaysIn P.toPathPacking.vertexSet := by
  intro i v hv
  exact P.toPathPacking.path_vertexSet_subset_vertexSet i.1 (by simpa using hv)

/-- Restricting a perfect packing to selected indices preserves internal
disjointness from a fixed vertex set. -/
theorem restrictIndexSet_internallyDisjointFromSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index) {U : Finset V}
    (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    (P.restrictIndexSet I).toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  exact hP i.1 (by simpa using hv) hvU

theorem restrictIndexSet_edgeSet_subset
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.edgeSet ⊆
      P.toPathPacking.edgeSet := by
  classical
  intro e he
  rcases ((P.restrictIndexSet I).toPathPacking.mem_edgeSet).1 he with
    ⟨i, hePath⟩
  exact (P.toPathPacking.mem_edgeSet).2 ⟨i.1, by simpa using hePath⟩

/-- The indices of paths whose source lies in a prescribed subset of the left
terminal set. -/
noncomputable def sourceIndexSetOfSubset
    (P : PerfectPathPacking G S T) (S' : Finset V) : Finset P.Index :=
  Finset.univ.filter fun i => (P.path i).source ∈ S'

@[simp] theorem mem_sourceIndexSetOfSubset
    (P : PerfectPathPacking G S T) (S' : Finset V) (i : P.Index) :
    i ∈ P.sourceIndexSetOfSubset S' ↔ (P.path i).source ∈ S' := by
  simp [sourceIndexSetOfSubset]

/-- Restricting by a source subset uses exactly that subset as the new source
terminal set. -/
theorem sourceSet_sourceIndexSetOfSubset
    (P : PerfectPathPacking G S T) {S' : Finset V} (hS : S' ⊆ S) :
    P.sourceSet (P.sourceIndexSetOfSubset S') = S' := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact (P.mem_sourceIndexSetOfSubset S' i).mp hi
  · intro hv
    rcases P.source_bijective.2 ⟨v, hS hv⟩ with ⟨i, hi⟩
    have hsource : (P.path i).source = v :=
      congrArg Subtype.val hi
    rw [sourceSet]
    exact Finset.mem_image.mpr
      ⟨i, by simpa [hsource] using hv, hsource⟩

/-- If a source subset is contained in the sources of `I`, then the indices
recovered from those sources are contained in `I`. -/
theorem sourceIndexSetOfSubset_subset_indexSet
    (P : PerfectPathPacking G S T) {S' : Finset V} {I : Finset P.Index}
    (hS : S' ⊆ P.sourceSet I) :
    P.sourceIndexSetOfSubset S' ⊆ I := by
  intro i hi
  have hsource_mem : (P.path i).source ∈ S' :=
    (P.mem_sourceIndexSetOfSubset S' i).mp hi
  rcases Finset.mem_image.mp (hS hsource_mem) with ⟨j, hj, hsource⟩
  have hij : i = j := by
    apply P.source_bijective.1
    exact Subtype.ext hsource.symm
  simpa [hij] using hj

@[simp] theorem sourceIndexSetOfSubset_card
    (P : PerfectPathPacking G S T) {S' : Finset V} (hS : S' ⊆ S) :
    (P.sourceIndexSetOfSubset S').card = S'.card := by
  have hcard := P.sourceSet_card (P.sourceIndexSetOfSubset S')
  rw [P.sourceSet_sourceIndexSetOfSubset hS] at hcard
  exact hcard.symm

/-- Restrict a perfect packing to the paths whose sources lie in a prescribed
subset of the left terminal set. -/
noncomputable def restrictSourceSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S) :
    PerfectPathPacking G S'
      (P.targetSet (P.sourceIndexSetOfSubset S')) :=
  (P.restrictIndexSet (P.sourceIndexSetOfSubset S')).copyTerminals
    (P.sourceSet_sourceIndexSetOfSubset hS) rfl

@[simp] theorem restrictSourceSet_card
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S) :
    (P.restrictSourceSet S' hS).card = S'.card := by
  simp [restrictSourceSet, sourceIndexSetOfSubset_card P hS]

@[simp] theorem restrictSourceSet_path_vertexSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S)
    (i : (P.restrictSourceSet S' hS).Index) :
    ((P.restrictSourceSet S' hS).path i).vertexSet = (P.path i.1).vertexSet := rfl

/-- A source-restricted perfect packing stays inside the vertex trace of the
original packing. -/
theorem restrictSourceSet_staysIn_vertexSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S) :
    (P.restrictSourceSet S' hS).toPathPacking.StaysIn P.toPathPacking.vertexSet := by
  intro i
  exact P.toPathPacking.path_vertexSet_subset_vertexSet i.1

/-- A source-restricted perfect packing stays in every set in which the
original packing stays. -/
theorem restrictSourceSet_staysIn
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S)
    {U : Finset V} (hP : P.toPathPacking.StaysIn U) :
    (P.restrictSourceSet S' hS).toPathPacking.StaysIn U := by
  intro i v hv
  exact hP i.1 (by simpa [restrictSourceSet, restrictIndexSet, copyTerminals] using hv)

/-- A source-restricted perfect packing preserves internal disjointness from any
finite vertex set. -/
theorem restrictSourceSet_internallyDisjointFromSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S)
    {U : Finset V} (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    (P.restrictSourceSet S' hS).toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  exact hP i.1
    (by simpa [restrictSourceSet, restrictIndexSet, copyTerminals] using hv)
    hvU

/-- Restricting both sides of mutually node-disjoint perfect packings
preserves mutual node-disjointness. -/
theorem restrictSourceSet_mutuallyNodeDisjoint
    {S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S T)
    (Q : PerfectPathPacking G S₂ T₂)
    (S₁' : Finset V) (hS₁ : S₁' ⊆ S)
    (S₂' : Finset V) (hS₂ : S₂' ⊆ S₂)
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    (P.restrictSourceSet S₁' hS₁).toPathPacking.MutuallyNodeDisjoint
      (Q.restrictSourceSet S₂' hS₂).toPathPacking := by
  intro i j
  exact h i.1 j.1

/-- The indices of paths whose target lies in a prescribed subset of the right
terminal set. -/
noncomputable def targetIndexSetOfSubset
    (P : PerfectPathPacking G S T) (T' : Finset V) : Finset P.Index :=
  Finset.univ.filter fun i => (P.path i).target ∈ T'

@[simp] theorem mem_targetIndexSetOfSubset
    (P : PerfectPathPacking G S T) (T' : Finset V) (i : P.Index) :
    i ∈ P.targetIndexSetOfSubset T' ↔ (P.path i).target ∈ T' := by
  simp [targetIndexSetOfSubset]

/-- Restricting by a target subset uses exactly that subset as the new target
terminal set. -/
theorem targetSet_targetIndexSetOfSubset
    (P : PerfectPathPacking G S T) {T' : Finset V} (hT : T' ⊆ T) :
    P.targetSet (P.targetIndexSetOfSubset T') = T' := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact (P.mem_targetIndexSetOfSubset T' i).mp hi
  · intro hv
    rcases P.target_bijective.2 ⟨v, hT hv⟩ with ⟨i, hi⟩
    have htarget : (P.path i).target = v :=
      congrArg Subtype.val hi
    rw [targetSet]
    exact Finset.mem_image.mpr
      ⟨i, by simpa [htarget] using hv, htarget⟩

/-- If a target subset is contained in the targets of `I`, then the indices
recovered from those targets are contained in `I`. -/
theorem targetIndexSetOfSubset_subset_indexSet
    (P : PerfectPathPacking G S T) {T' : Finset V} {I : Finset P.Index}
    (hT : T' ⊆ P.targetSet I) :
    P.targetIndexSetOfSubset T' ⊆ I := by
  intro i hi
  have htarget_mem : (P.path i).target ∈ T' :=
    (P.mem_targetIndexSetOfSubset T' i).mp hi
  rcases Finset.mem_image.mp (hT htarget_mem) with ⟨j, hj, htarget⟩
  have hij : i = j := by
    apply P.target_bijective.1
    exact Subtype.ext htarget.symm
  simpa [hij] using hj

@[simp] theorem targetIndexSetOfSubset_card
    (P : PerfectPathPacking G S T) {T' : Finset V} (hT : T' ⊆ T) :
    (P.targetIndexSetOfSubset T').card = T'.card := by
  have hcard := P.targetSet_card (P.targetIndexSetOfSubset T')
  rw [P.targetSet_targetIndexSetOfSubset hT] at hcard
  exact hcard.symm

/-- Restrict a perfect packing to the paths whose targets lie in a prescribed
subset of the right terminal set. -/
noncomputable def restrictTargetSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T) :
    PerfectPathPacking G
      (P.sourceSet (P.targetIndexSetOfSubset T')) T' :=
  (P.restrictIndexSet (P.targetIndexSetOfSubset T')).copyTerminals
    rfl (P.targetSet_targetIndexSetOfSubset hT)

@[simp] theorem restrictTargetSet_card
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T) :
    (P.restrictTargetSet T' hT).card = T'.card := by
  simp [restrictTargetSet, targetIndexSetOfSubset_card P hT]

@[simp] theorem restrictTargetSet_path_vertexSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T)
    (i : (P.restrictTargetSet T' hT).Index) :
    ((P.restrictTargetSet T' hT).path i).vertexSet = (P.path i.1).vertexSet := rfl

/-- A target-restricted perfect packing stays inside the vertex trace of the
original packing. -/
theorem restrictTargetSet_staysIn_vertexSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T) :
    (P.restrictTargetSet T' hT).toPathPacking.StaysIn P.toPathPacking.vertexSet := by
  intro i
  exact P.toPathPacking.path_vertexSet_subset_vertexSet i.1

/-- A target-restricted perfect packing stays in every set in which the
original packing stays. -/
theorem restrictTargetSet_staysIn
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T)
    {U : Finset V} (hP : P.toPathPacking.StaysIn U) :
    (P.restrictTargetSet T' hT).toPathPacking.StaysIn U := by
  intro i v hv
  exact hP i.1 (by simpa [restrictTargetSet, restrictIndexSet, copyTerminals] using hv)

/-- A target-restricted perfect packing preserves internal disjointness from any
finite vertex set. -/
theorem restrictTargetSet_internallyDisjointFromSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T)
    {U : Finset V} (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    (P.restrictTargetSet T' hT).toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  exact hP i.1
    (by simpa [restrictTargetSet, restrictIndexSet, copyTerminals] using hv)
    hvU

/-- The graph spanned by a restricted perfect packing is a subgraph of the
graph spanned by the original packing. -/
theorem restrictIndexSet_spanningGraph_le
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.spanningGraph ≤
      P.toPathPacking.spanningGraph := by
  intro u v huv
  rw [PathPacking.spanningGraph_adj_iff_exists_path_edge] at huv ⊢
  rcases huv with ⟨⟨i, hedge⟩, hne⟩
  exact ⟨⟨i.1, by simpa [restrictIndexSet] using hedge⟩, hne⟩

/-- Reverse every path in a perfect packing, swapping its two terminal sets. -/
noncomputable def reverse (P : PerfectPathPacking G S T) :
    PerfectPathPacking G T S where
  toPathPacking := {
    Index := P.Index
    path := fun i => (P.path i).reverse
    connects := by
      intro i
      exact Or.inl ⟨by simpa using P.target_mem i,
        by simpa using P.source_mem i⟩
    node_disjoint := by
      intro i j hij
      simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij
  }
  source_mem := by
    intro i
    simpa using P.target_mem i
  target_mem := by
    intro i
    simpa using P.source_mem i
  source_bijective := by
    simpa using P.target_bijective
  target_bijective := by
    simpa using P.source_bijective

@[simp] theorem reverse_card (P : PerfectPathPacking G S T) :
    P.reverse.card = P.card := rfl

@[simp] theorem reverse_path_vertexSet (P : PerfectPathPacking G S T)
    (i : P.reverse.Index) :
    (P.reverse.path i).vertexSet = (P.path i).vertexSet := by
  simp [reverse]

@[simp] theorem reverse_path_edgeSet (P : PerfectPathPacking G S T)
    (i : P.reverse.Index) :
    (P.reverse.path i).edgeSet = (P.path i).edgeSet := by
  simp [reverse]

/-- Reversing a perfect packing preserves containment of all path vertices in
a fixed finite set. -/
theorem reverse_staysIn {U : Finset V} (P : PerfectPathPacking G S T)
    (hP : P.toPathPacking.StaysIn U) :
    P.reverse.toPathPacking.StaysIn U := by
  intro i
  simpa using hP i

/-- Reversing a perfect packing preserves internal disjointness from a fixed
finite set. -/
theorem reverse_internallyDisjointFromSet {U : Finset V}
    (P : PerfectPathPacking G S T)
    (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    P.reverse.toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  have hrev :
      (P.path i).reverse.InternallyDisjointFromSet U :=
    (GraphPath.reverse_internallyDisjointFromSet (P.path i) U).2 (hP i)
  exact hrev (by simpa [reverse] using hv) hvU

/-- Choose exactly `n` paths from a perfect packing when `n` is at most its
cardinality. -/
theorem exists_indexSet_card_eq (P : PerfectPathPacking G S T)
    {n : ℕ} (hn : n ≤ P.card) :
    ∃ I : Finset P.Index, I.card = n ∧
      (P.restrictIndexSet I).card = n := by
  classical
  have hn_univ : n ≤ (Finset.univ : Finset P.Index).card := by
    simpa [card] using hn
  rcases Finset.exists_subset_card_eq hn_univ with ⟨I, _hI, hIcard⟩
  exact ⟨I, hIcard, by simp [hIcard]⟩

/-- A perfect path packing can be viewed inside the graph spanned by exactly
its own path edges. -/
noncomputable def inSpanningGraph (P : PerfectPathPacking G S T) :
    PerfectPathPacking P.toPathPacking.spanningGraph S T where
  toPathPacking := P.toPathPacking.inSpanningGraph
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_bijective := by
    simpa [PathPacking.inSpanningGraph, PathPacking.transfer, GraphPath.transfer]
      using P.source_bijective
  target_bijective := by
    simpa [PathPacking.inSpanningGraph, PathPacking.transfer, GraphPath.transfer]
      using P.target_bijective

@[simp] theorem inSpanningGraph_card (P : PerfectPathPacking G S T) :
    P.inSpanningGraph.card = P.card := rfl

@[simp] theorem inSpanningGraph_path_vertexSet (P : PerfectPathPacking G S T)
    (i : P.Index) :
    (P.inSpanningGraph.path i).vertexSet = (P.path i).vertexSet := by
  simp [inSpanningGraph, PathPacking.inSpanningGraph, PathPacking.transfer]

/-- If the first perfect packing is internally disjoint from a region, the
second stays in that region, and the first source terminals are outside it,
then every matching endpoint concatenation is a simple path. -/
theorem concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hvQ
  rcases hP i hvP hvA with hsource | htarget
  · exact False.elim
      (Finset.disjoint_left.mp hSdisj (P.source_mem i)
        (by simpa [hsource] using hvA))
  · exact htarget

/-- Under the same separation hypotheses as
`concat_isPath_of_first_internallyDisjointFromSet_second_staysIn`, distinct
matching endpoint concatenations remain node-disjoint. -/
theorem concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q j) hvjQ
      rcases hP i hviP hvA with hsource | htarget
      · exact Finset.disjoint_left.mp hSdisj (P.source_mem i)
          (by simpa [hsource] using hvA)
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem i
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q j)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q j) hvT hvjQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := htarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hqsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hviQ
      rcases hP j hvjP hvA with hsource | htarget
      · exact Finset.disjoint_left.mp hSdisj (P.source_mem j)
          (by simpa [hsource] using hvA)
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem j
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q i)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q i) hvT hviQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hqsource.symm
            _ = (P.path j).target := htarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- Variant of
`concat_isPath_of_first_internallyDisjointFromSet_second_staysIn` allowing a
left source terminal to lie in the region only when its path is trivial up to
the glued target. -/
theorem concat_isPath_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hvQ
  rcases hP i hvP hvA with hsource | htarget
  · exact hsource.trans
      (hsource_only i (P.indexOfSourceTarget Q i) (by simpa [hsource] using hvQ))
  · exact htarget

/-- Node-disjointness for the source-exception concatenation variant. -/
theorem concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q j) hvjQ
      rcases hP i hviP hvA with hsource | htarget
      · have hPi_trivial :
            (P.path i).source = (P.path i).target :=
          hsource_only i (P.indexOfSourceTarget Q j) (by simpa [hsource] using hvjQ)
        have hvT : v ∈ T := by
          simpa [hsource, hPi_trivial] using P.target_mem i
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q j)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q j) hvT hvjQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := by simp [hsource, hPi_trivial]
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hqsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem i
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q j)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q j) hvT hvjQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := htarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hqsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hviQ
      rcases hP j hvjP hvA with hsource | htarget
      · have hPj_trivial :
            (P.path j).source = (P.path j).target :=
          hsource_only j (P.indexOfSourceTarget Q i) (by simpa [hsource] using hviQ)
        have hvT : v ∈ T := by
          simpa [hsource, hPj_trivial] using P.target_mem j
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q i)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q i) hvT hviQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hqsource.symm
            _ = (P.path j).target := by simp [hsource, hPj_trivial]
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem j
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q i)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q i) hvT hviQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hqsource.symm
            _ = (P.path j).target := htarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- If the first perfect packing stays in a region, the second is internally
disjoint from that region, and the second target terminals are outside it, then
every matching endpoint concatenation is a simple path. -/
theorem concat_isPath_of_first_staysIn_second_internallyDisjointFromSet
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hP i hvP
  rcases hQ (P.indexOfSourceTarget Q i) hvQ hvA with hsource | htarget
  · exact hsource.trans (source_indexOfSourceTarget P Q i)
  · exact False.elim
      (Finset.disjoint_left.mp hUdisj
        (Q.target_mem (P.indexOfSourceTarget Q i))
        (by simpa [htarget] using hvA))

/-- Under the same separation hypotheses as
`concat_isPath_of_first_staysIn_second_internallyDisjointFromSet`, distinct
matching endpoint concatenations remain node-disjoint. -/
theorem concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hP i hviP
      rcases hQ (P.indexOfSourceTarget Q j) hvjQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q j] using P.target_mem j
        have hPtarget : v = (P.path i).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet i hvT hviP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := hPtarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · exact Finset.disjoint_left.mp hUdisj
          (Q.target_mem (P.indexOfSourceTarget Q j))
          (by simpa [htarget] using hvA)
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hP j hvjP
      rcases hQ (P.indexOfSourceTarget Q i) hviQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q i] using P.target_mem i
        have hPtarget : v = (P.path j).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet j hvT hvjP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hsource.symm
            _ = (P.path j).target := hPtarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · exact Finset.disjoint_left.mp hUdisj
          (Q.target_mem (P.indexOfSourceTarget Q i))
          (by simpa [htarget] using hvA)
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- Variant of
`concat_isPath_of_first_staysIn_second_internallyDisjointFromSet` allowing a
right target terminal to lie in the region only when the second path is
trivial from its source to that target. -/
theorem concat_isPath_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hP i hvP
  rcases hQ (P.indexOfSourceTarget Q i) hvQ hvA with hsource | htarget
  · exact hsource.trans (source_indexOfSourceTarget P Q i)
  · exact htarget.trans
      ((htarget_only i (P.indexOfSourceTarget Q i) (by simpa [htarget] using hvP)).trans
        (source_indexOfSourceTarget P Q i))

/-- Node-disjointness for the target-exception symmetric concatenation
variant. -/
theorem concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hP i hviP
      rcases hQ (P.indexOfSourceTarget Q j) hvjQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q j] using P.target_mem j
        have hPtarget : v = (P.path i).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet i hvT hviP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := hPtarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hQj_trivial :
            (Q.path (P.indexOfSourceTarget Q j)).target =
              (Q.path (P.indexOfSourceTarget Q j)).source :=
          htarget_only i (P.indexOfSourceTarget Q j) (by simpa [htarget] using hviP)
        have hvT : v ∈ T := by
          simpa [htarget, hQj_trivial, source_indexOfSourceTarget P Q j]
            using P.target_mem j
        have hPtarget : v = (P.path i).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet i hvT hviP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := hPtarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).target := htarget
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hQj_trivial
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hP j hvjP
      rcases hQ (P.indexOfSourceTarget Q i) hviQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q i] using P.target_mem i
        have hPtarget : v = (P.path j).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet j hvT hvjP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hsource.symm
            _ = (P.path j).target := hPtarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hQi_trivial :
            (Q.path (P.indexOfSourceTarget Q i)).target =
              (Q.path (P.indexOfSourceTarget Q i)).source :=
          htarget_only j (P.indexOfSourceTarget Q i) (by simpa [htarget] using hvjP)
        have hvT : v ∈ T := by
          simpa [htarget, hQi_trivial, source_indexOfSourceTarget P Q i]
            using P.target_mem i
        have hPtarget : v = (P.path j).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet j hvT hvjP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = (Q.path (P.indexOfSourceTarget Q i)).target := hQi_trivial.symm
            _ = v := htarget.symm
            _ = (P.path j).target := hPtarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- Concatenate two perfect path packings with matching middle terminal set.

The two proof arguments record the genuinely graph-theoretic obligations:
each concatenated walk is still a simple path, and different concatenated
paths remain node-disjoint. -/
noncomputable def concat {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j))) :
    PerfectPathPacking G S U where
  toPathPacking := {
    Index := P.Index
    path := fun i =>
      (P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
        (source_indexOfSourceTarget P Q i).symm (hpath i)
    connects := by
      intro i
      exact Or.inl ⟨P.source_mem i, Q.target_mem (P.indexOfSourceTarget Q i)⟩
    node_disjoint := hnode
  }
  source_mem := P.source_mem
  target_mem := fun i => Q.target_mem (P.indexOfSourceTarget Q i)
  source_bijective := by
    simpa [GraphPath.appendWithEq] using P.source_bijective
  target_bijective := by
    classical
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      have hq :
          P.indexOfSourceTarget Q i = P.indexOfSourceTarget Q j := by
        apply Q.target_bijective.1
        simpa [GraphPath.appendWithEq] using hij
      have htargets :
          (P.path i).target = (P.path j).target := by
        have hs :=
          congrArg (fun q => (Q.path q).source) hq
        exact (source_indexOfSourceTarget P Q i).symm.trans
          (hs.trans (source_indexOfSourceTarget P Q j))
      apply P.target_bijective.1
      exact Subtype.ext htargets
    · have hPU : P.card = U.card :=
        (P.card_eq_right_card.trans (Q.card_eq_left_card).symm).trans
          Q.card_eq_right_card
      rw [Fintype.card_coe]
      simpa [card] using hPU

/-- Concatenate two perfect packings using a region-separation certificate
instead of separately supplying path-simplicity and node-disjointness proofs. -/
noncomputable def concatOfFirstInternallyDisjointSecondStaysIn
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
      P Q hP hQ hSdisj
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn
      P Q hP hQ hSdisj hpath)

/-- Concatenate two perfect packings when the first is internally disjoint from
the region containing the second, allowing a first source to lie in that region
only when the corresponding first path is trivial up to its target. -/
noncomputable def concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
      P Q hP hQ hsource_only
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
      P Q hP hQ hsource_only hpath)

/-- Concatenate two perfect packings using the symmetric region-separation
certificate: the first packing stays in the region, the second is internally
disjoint from it, and the second target terminals are outside it. -/
noncomputable def concatOfFirstStaysInSecondInternallyDisjoint
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_staysIn_second_internallyDisjointFromSet
      P Q hP hQ hUdisj
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet
      P Q hP hQ hUdisj hpath)

/-- Concatenate two perfect packings when the second is internally disjoint
from the region containing the first, allowing a second target to lie in that
region only when that second path is trivial from source to target. -/
noncomputable def concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
      P Q hP hQ htarget_only
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
      P Q hP hQ htarget_only hpath)

@[simp] theorem concatOfFirstInternallyDisjointSecondStaysIn_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A) :
    (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).card =
      P.card := by
  rfl

@[simp] theorem concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target) :
    (P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).card = P.card := by
  rfl

@[simp] theorem concatOfFirstStaysInSecondInternallyDisjoint_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A) :
    (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).card =
      P.card := by
  rfl

@[simp] theorem concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source) :
    (P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).card = P.card := by
  rfl

@[simp] theorem concat_card {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j))) :
    (P.concat Q hpath hnode).card = P.card := rfl

/-- A concatenated path uses only vertices from the two paths that were glued. -/
theorem concat_path_vertexSet_subset {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (i : (P.concat Q hpath hnode).Index) :
    ((P.concat Q hpath hnode).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet :=
  GraphPath.appendWithEq_vertexSet_subset
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm (hpath i)

/-- A concatenated path uses only edges from the two paths that were glued. -/
theorem concat_path_edgeSet_subset {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (i : (P.concat Q hpath hnode).Index) :
    ((P.concat Q hpath hnode).path i).edgeSet ⊆
      (P.path i).edgeSet ∪
        (Q.path (P.indexOfSourceTarget Q i)).edgeSet :=
  GraphPath.appendWithEq_edgeSet_subset
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm (hpath i)

/-- A path in the region-separated concatenation uses only vertices from its
two input paths. -/
theorem concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (i : (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).Index) :
    ((P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysIn]
  exact P.concat_path_vertexSet_subset Q _ _ i

theorem concatOfFirstInternallyDisjointSecondStaysIn_path_edgeSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (i : (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).Index) :
    ((P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).path i).edgeSet ⊆
      (P.path i).edgeSet ∪
        (Q.path (P.indexOfSourceTarget Q i)).edgeSet := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysIn]
  exact P.concat_path_edgeSet_subset Q _ _ i

/-- A path in the source-exception region-separated concatenation uses only
vertices from its two input paths. -/
theorem concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target)
    (i : (P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).Index) :
    ((P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget]
  exact P.concat_path_vertexSet_subset Q _ _ i

/-- A path in the symmetric region-separated concatenation uses only vertices
from its two input paths. -/
theorem concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (i : (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).Index) :
    ((P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjoint]
  exact P.concat_path_vertexSet_subset Q _ _ i

theorem concatOfFirstStaysInSecondInternallyDisjoint_path_edgeSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (i : (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).Index) :
    ((P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).path i).edgeSet ⊆
      (P.path i).edgeSet ∪
        (Q.path (P.indexOfSourceTarget Q i)).edgeSet := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjoint]
  exact P.concat_path_edgeSet_subset Q _ _ i

/-- A path in the target-exception symmetric concatenation uses only vertices
from its two input paths. -/
theorem concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source)
    (i : (P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).Index) :
    ((P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource]
  exact P.concat_path_vertexSet_subset Q _ _ i

/-- If the two input perfect packings stay in prescribed vertex sets, then the
concatenated packing stays in their union. -/
theorem concat_staysIn_union {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    {A B : Finset V}
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.StaysIn B) :
    (P.concat Q hpath hnode).toPathPacking.StaysIn (A ∪ B) := by
  intro i v hv
  have hsubset := P.concat_path_vertexSet_subset Q hpath hnode i hv
  rcases Finset.mem_union.mp hsubset with hvP | hvQ
  · exact Finset.mem_union_left _ (hP i hvP)
  · exact Finset.mem_union_right _ (hQ (P.indexOfSourceTarget Q i) hvQ)

/-- If the left input packing is internally disjoint from a set, the right input
packing is disjoint from that set, and the glued terminal set avoids it, then
the concatenated packing is internally disjoint from that set. -/
theorem concat_internallyDisjointFromSet_left {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hTdisj : Disjoint T A)
    (hQdisj : Disjoint Q.toPathPacking.vertexSet A) :
    (P.concat Q hpath hnode).toPathPacking.InternallyDisjointFromSet A := by
  intro i v hv hA
  have hsplit := P.concat_path_vertexSet_subset Q hpath hnode i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · rcases hP i hvP hA with hsource | htarget
    · exact Or.inl (by simpa [concat, GraphPath.IsEndpoint] using hsource)
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj (P.target_mem i)
          (by simpa [htarget] using hA))
  · have hvQtotal :
        v ∈ Q.toPathPacking.vertexSet :=
      Q.toPathPacking.path_vertexSet_subset_vertexSet
        (P.indexOfSourceTarget Q i) hvQ
    exact False.elim
      (Finset.disjoint_left.mp hQdisj hvQtotal hA)

/-- If the right input packing is internally disjoint from a set, the left input
packing is disjoint from that set, and the glued terminal set avoids it, then
the concatenated packing is internally disjoint from that set. -/
theorem concat_internallyDisjointFromSet_right {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (hPdisj : Disjoint P.toPathPacking.vertexSet A)
    (hTdisj : Disjoint T A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A) :
    (P.concat Q hpath hnode).toPathPacking.InternallyDisjointFromSet A := by
  intro i v hv hA
  have hsplit := P.concat_path_vertexSet_subset Q hpath hnode i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · have hvPtotal :
        v ∈ P.toPathPacking.vertexSet :=
      P.toPathPacking.path_vertexSet_subset_vertexSet i hvP
    exact False.elim
      (Finset.disjoint_left.mp hPdisj hvPtotal hA)
  · rcases hQ (P.indexOfSourceTarget Q i) hvQ hA with hsource | htarget
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj
          (Q.source_mem (P.indexOfSourceTarget Q i))
          (by simpa [hsource] using hA))
    · exact Or.inr (by simpa [concat, GraphPath.IsEndpoint] using htarget)

/-- The region-separated concatenation stays in the union of the region used
by the first packing and the region used by the second packing. -/
theorem concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (hPstay : P.toPathPacking.StaysIn B) :
    (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).toPathPacking.StaysIn
      (B ∪ A) := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysIn]
  exact P.concat_staysIn_union Q _ _ hPstay hQ

/-- The source-exception region-separated concatenation stays in the union of
the region used by the first packing and the region used by the second
packing. -/
theorem concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target)
    (hPstay : P.toPathPacking.StaysIn B) :
    (P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).toPathPacking.StaysIn (B ∪ A) := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget]
  exact P.concat_staysIn_union Q _ _ hPstay hQ

/-- The symmetric region-separated concatenation stays in the union of the
region used by the first packing and the region used by the second packing. -/
theorem concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (hQstay : Q.toPathPacking.StaysIn B) :
    (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).toPathPacking.StaysIn
      (A ∪ B) := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjoint]
  exact P.concat_staysIn_union Q _ _ hP hQstay

/-- The target-exception symmetric concatenation stays in the union of the
region used by the first packing and the region used by the second packing. -/
theorem concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source)
    (hQstay : Q.toPathPacking.StaysIn B) :
    (P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).toPathPacking.StaysIn (A ∪ B) := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource]
  exact P.concat_staysIn_union Q _ _ hP hQstay

/-- A region-separated concatenation is internally disjoint from a third set
when both input packings are internally disjoint from that set and the glued
terminal set avoids it. -/
theorem concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
    {U A C : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (hPC : P.toPathPacking.InternallyDisjointFromSet C)
    (hQC : Q.toPathPacking.InternallyDisjointFromSet C)
    (hTdisj : Disjoint T C) :
    ((P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).toPathPacking).InternallyDisjointFromSet C := by
  intro i v hv hvC
  have hsplit :=
    P.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      Q hP hQ hSdisj i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · rcases hPC i hvP hvC with hsource | htarget
    · exact Or.inl (by
        simpa [concatOfFirstInternallyDisjointSecondStaysIn,
          GraphPath.IsEndpoint] using hsource)
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj (P.target_mem i)
          (by simpa [htarget] using hvC))
  · rcases hQC (P.indexOfSourceTarget Q i) hvQ hvC with hsource | htarget
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj
          (Q.source_mem (P.indexOfSourceTarget Q i))
          (by simpa [hsource] using hvC))
    · exact Or.inr (by
        simpa [concatOfFirstInternallyDisjointSecondStaysIn,
          GraphPath.IsEndpoint] using htarget)

/-- The symmetric region-separated concatenation is internally disjoint from a
third set when both input packings are internally disjoint from that set and the
glued terminal set avoids it. -/
theorem concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
    {U A C : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (hPC : P.toPathPacking.InternallyDisjointFromSet C)
    (hQC : Q.toPathPacking.InternallyDisjointFromSet C)
    (hTdisj : Disjoint T C) :
    ((P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).toPathPacking).InternallyDisjointFromSet C := by
  intro i v hv hvC
  have hsplit :=
    P.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
      Q hP hQ hUdisj i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · rcases hPC i hvP hvC with hsource | htarget
    · exact Or.inl (by
        simpa [concatOfFirstStaysInSecondInternallyDisjoint,
          GraphPath.IsEndpoint] using hsource)
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj (P.target_mem i)
          (by simpa [htarget] using hvC))
  · rcases hQC (P.indexOfSourceTarget Q i) hvQ hvC with hsource | htarget
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj
          (Q.source_mem (P.indexOfSourceTarget Q i))
          (by simpa [hsource] using hvC))
    · exact Or.inr (by
        simpa [concatOfFirstStaysInSecondInternallyDisjoint,
          GraphPath.IsEndpoint] using htarget)

end PerfectPathPacking

namespace PathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- An equal-size node-disjoint packing can be promoted to an oriented perfect
packing.  The node-disjointness and cardinality hypotheses imply that every
terminal on both sides is used exactly once. -/
noncomputable def toPerfectOfCardEq (P : PathPacking G S T)
    (hcardS : P.card = S.card) (hcardT : P.card = T.card) :
    PerfectPathPacking G S T where
  toPathPacking := P.orient
  source_mem := by
    intro i
    exact GraphPath.orient_source_mem (P.path i) (P.connects i)
  target_mem := by
    intro i
    exact GraphPath.orient_target_mem (P.path i) (P.connects i)
  source_bijective := by
    classical
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have hsrc :
          ((P.orient).path i).source = ((P.orient).path j).source :=
        congrArg Subtype.val hij
      have hi : ((P.orient).path i).source ∈ ((P.orient).path i).vertexSet :=
        GraphPath.source_mem_vertexSet ((P.orient).path i)
      have hj : ((P.orient).path i).source ∈ ((P.orient).path j).vertexSet := by
        simpa [hsrc] using GraphPath.source_mem_vertexSet ((P.orient).path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · rw [Fintype.card_coe]
      simpa [card] using hcardS
  target_bijective := by
    classical
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have htgt :
          ((P.orient).path i).target = ((P.orient).path j).target :=
        congrArg Subtype.val hij
      have hi : ((P.orient).path i).target ∈ ((P.orient).path i).vertexSet :=
        GraphPath.target_mem_vertexSet ((P.orient).path i)
      have hj : ((P.orient).path i).target ∈ ((P.orient).path j).vertexSet := by
        simpa [htgt] using GraphPath.target_mem_vertexSet ((P.orient).path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · rw [Fintype.card_coe]
      simpa [card] using hcardT

/-- Promote a path packing to a perfect packing on the terminal sets actually
used by its oriented paths. -/
noncomputable def toPerfectUsedTerminals (P : PathPacking G S T) :
    PerfectPathPacking G P.sourceSet P.targetSet where
  toPathPacking := {
    Index := P.Index
    path := fun i => P.orient.path i
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr ⟨i, by simp, rfl⟩,
          Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
    node_disjoint := P.orient.node_disjoint
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have hsrc :
          (P.orient.path i).source = (P.orient.path j).source :=
        congrArg Subtype.val hij
      have hi : (P.orient.path i).source ∈ (P.orient.path i).vertexSet :=
        GraphPath.source_mem_vertexSet (P.orient.path i)
      have hj : (P.orient.path i).source ∈ (P.orient.path j).vertexSet := by
        simpa [hsrc] using GraphPath.source_mem_vertexSet (P.orient.path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · intro v
      rcases Finset.mem_image.mp v.2 with ⟨i, _hi, hv⟩
      refine ⟨i, Subtype.ext ?_⟩
      exact hv
  target_bijective := by
    classical
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have htgt :
          (P.orient.path i).target = (P.orient.path j).target :=
        congrArg Subtype.val hij
      have hi : (P.orient.path i).target ∈ (P.orient.path i).vertexSet :=
        GraphPath.target_mem_vertexSet (P.orient.path i)
      have hj : (P.orient.path i).target ∈ (P.orient.path j).vertexSet := by
        simpa [htgt] using GraphPath.target_mem_vertexSet (P.orient.path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · intro v
      rcases Finset.mem_image.mp v.2 with ⟨i, _hi, hv⟩
      refine ⟨i, Subtype.ext ?_⟩
      exact hv

@[simp] theorem toPerfectUsedTerminals_card (P : PathPacking G S T) :
    P.toPerfectUsedTerminals.card = P.card := rfl

/-- Promoting a packing to a perfect packing on its used terminal sets
preserves vertex containment. -/
theorem toPerfectUsedTerminals_staysIn
    (P : PathPacking G S T) {U : Finset V} (hP : P.StaysIn U) :
    P.toPerfectUsedTerminals.toPathPacking.StaysIn U := by
  simpa [toPerfectUsedTerminals] using PathPacking.orient_staysIn hP

/-- Promoting a packing to a perfect packing on its used terminal sets
preserves internal disjointness from a vertex set. -/
theorem toPerfectUsedTerminals_internallyDisjointFromSet
    (P : PathPacking G S T) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    P.toPerfectUsedTerminals.toPathPacking.InternallyDisjointFromSet U := by
  simpa [toPerfectUsedTerminals] using
    PathPacking.orient_internallyDisjointFromSet hP

/-- Promoting a packing to a perfect packing on its used terminal sets
preserves localized pairwise bridges. -/
theorem toPerfectUsedTerminals_hasPairwiseBridgesIn
    (P : PathPacking G S T) {U : Finset V}
    (hP : P.HasPairwiseBridgesIn U) :
    P.toPerfectUsedTerminals.toPathPacking.HasPairwiseBridgesIn U := by
  intro i j hij
  rcases (PathPacking.orient_hasPairwiseBridgesIn hP) hij with ⟨β, hβU⟩
  let β' : P.toPerfectUsedTerminals.toPathPacking.BridgeBetween i j := {
    path := β.path
    connects := by
      simpa [toPerfectUsedTerminals] using β.connects
    internallyDisjoint := by
      intro v hv hrows
      exact β.internallyDisjoint hv (by
        simpa [toPerfectUsedTerminals, PathPacking.vertexSet] using hrows)
  }
  exact ⟨β', by simpa [β'] using hβU⟩

end PathPacking

/-- A finite indexed family of edge-disjoint paths connecting two vertex sets.

Unlike `PathPacking`, this structure does not require the paths to be
vertex-disjoint.  This matches the paper's edge-well-linkedness convention,
where paths may share endpoints and internal vertices but not edges. -/
structure EdgePathPacking {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  /-- The finite index type for the paths in the packing. -/
  Index : Type
  /-- The index type is finite. -/
  [indexFintype : Fintype Index]
  /-- The index type has decidable equality. -/
  [indexDecidableEq : DecidableEq Index]
  /-- The path assigned to each index. -/
  path : Index → GraphPath G
  /-- Every path connects the two specified vertex sets. -/
  connects : ∀ i : Index, (path i).Connects S T
  /-- Distinct indexed paths are edge-disjoint. -/
  edge_disjoint : Pairwise fun i j => GraphPath.EdgeDisjoint (path i) (path j)

namespace EdgePathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

instance (P : EdgePathPacking G S T) : Fintype P.Index := P.indexFintype
instance (P : EdgePathPacking G S T) : DecidableEq P.Index := P.indexDecidableEq

/-- The number of paths in an edge-disjoint packing. -/
noncomputable def card (P : EdgePathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- Every path in the edge-disjoint packing has all vertices contained in
`U`. -/
def StaysIn (P : EdgePathPacking G S T) (U : Finset V) : Prop :=
  ∀ i : P.Index, (P.path i).vertexSet ⊆ U

/-- Map every path in an edge-disjoint packing to a supergraph on the same
vertex type. -/
def mapLe (P : EdgePathPacking G S T) {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    EdgePathPacking H S T where
  Index := P.Index
  path := fun i => (P.path i).mapLe hGH
  connects := by
    intro i
    simpa [GraphPath.mapLe, GraphPath.Connects] using P.connects i
  edge_disjoint := by
    intro i j hij
    simpa [GraphPath.EdgeDisjoint] using P.edge_disjoint hij

end EdgePathPacking

/-- A finite vertex set is node-well-linked inside a finite region `C` of `G`
when every pair of disjoint subfamilies can be linked by the maximum possible
number of node-disjoint paths contained in `C`.

This is the paper's node-well-linkedness specialized to finite sets and with
the ambient cluster `C` made explicit. -/
def NodeWellLinkedIn {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C T : Finset V) : Prop :=
  T ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → Disjoint A B →
      ∃ P : PathPacking G A B,
        P.card = min A.card B.card ∧ P.StaysIn C

namespace NodeWellLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C T U : Finset V}

/-- Node-well-linkedness is inherited by smaller terminal sets. -/
theorem mono_terminals (h : NodeWellLinkedIn G C T) (hU : U ⊆ T) :
    NodeWellLinkedIn G C U := by
  constructor
  · exact subset_trans hU h.1
  · intro A B hA hB hdisj
    exact h.2 (subset_trans hA hU) (subset_trans hB hU) hdisj

/-- Node-well-linkedness is preserved when edges are added to the ambient
graph. -/
theorem mono_graph {G' : _root_.SimpleGraph V}
    (h : NodeWellLinkedIn G C T) (hGG' : G ≤ G') :
    NodeWellLinkedIn G' C T := by
  constructor
  · exact h.1
  · intro A B hA hB hdisj
    rcases h.2 hA hB hdisj with ⟨P, hcard, hstay⟩
    refine ⟨P.mapLe hGG', ?_, ?_⟩
    · simpa using hcard
    · intro i
      change ((P.path i).mapLe hGG').vertexSet ⊆ C
      simpa using hstay i

end NodeWellLinkedIn

/-- Edge-well-linkedness inside a finite region `C`.  Paths may share vertices
but must be pairwise edge-disjoint. -/
def EdgeWellLinkedIn {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C T : Finset V) : Prop :=
  T ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → Disjoint A B →
      ∃ P : EdgePathPacking G A B,
        P.card = min A.card B.card ∧ P.StaysIn C

namespace EdgeWellLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C T U : Finset V}

/-- Edge-well-linkedness is inherited by smaller terminal sets. -/
theorem mono_terminals (h : EdgeWellLinkedIn G C T) (hU : U ⊆ T) :
    EdgeWellLinkedIn G C U := by
  constructor
  · exact subset_trans hU h.1
  · intro A B hA hB hdisj
    exact h.2 (subset_trans hA hU) (subset_trans hB hU) hdisj

/-- Edge-well-linkedness is preserved when edges are added to the ambient
graph. -/
theorem mono_graph {G' : _root_.SimpleGraph V}
    (h : EdgeWellLinkedIn G C T) (hGG' : G ≤ G') :
    EdgeWellLinkedIn G' C T := by
  constructor
  · exact h.1
  · intro A B hA hB hdisj
    rcases h.2 hA hB hdisj with ⟨P, hcard, hstay⟩
    refine ⟨P.mapLe hGG', ?_, ?_⟩
    · simpa using hcard
    · intro i
      change ((P.path i).mapLe hGG').vertexSet ⊆ C
      simpa using hstay i

end EdgeWellLinkedIn

/-- Two finite vertex sets are linked inside `C` if all subfamilies can be
joined by the maximum possible number of node-disjoint paths contained in `C`. -/
def NodeLinkedIn {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C A B : Finset V) : Prop :=
  A ⊆ C ∧ B ⊆ C ∧ Disjoint A B ∧
    ∀ ⦃A' B' : Finset V⦄, A' ⊆ A → B' ⊆ B →
      ∃ P : PathPacking G A' B',
        P.card = min A'.card B'.card ∧ P.StaysIn C

namespace NodeLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C A B : Finset V}

/-- Node-linkedness is inherited by smaller terminal sets on both sides. -/
theorem mono_terminals {A₀ B₀ : Finset V} (h : NodeLinkedIn G C A B)
    (hA₀ : A₀ ⊆ A) (hB₀ : B₀ ⊆ B) :
    NodeLinkedIn G C A₀ B₀ := by
  refine ⟨subset_trans hA₀ h.1, subset_trans hB₀ h.2.1, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hvA hvB
    exact Finset.disjoint_left.mp h.2.2.1 (hA₀ hvA) (hB₀ hvB)
  · intro A' B' hA' hB'
    exact h.2.2.2 (subset_trans hA' hA₀) (subset_trans hB' hB₀)

/-- Node-linkedness is preserved when edges are added to the ambient graph. -/
theorem mono_graph {G' : _root_.SimpleGraph V}
    (h : NodeLinkedIn G C A B) (hGG' : G ≤ G') :
    NodeLinkedIn G' C A B := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro A' B' hA' hB'
  rcases h.2.2.2 hA' hB' with ⟨P, hcard, hstay⟩
  refine ⟨P.mapLe hGG', ?_, ?_⟩
  · simpa using hcard
  · intro i
    change ((P.path i).mapLe hGG').vertexSet ⊆ C
    simpa using hstay i

/-- A linked pair supplies a full-size path packing between the two full sets. -/
theorem exists_pathPacking (h : NodeLinkedIn G C A B) :
    ∃ P : PathPacking G A B,
      P.card = min A.card B.card ∧ P.StaysIn C :=
  h.2.2.2 subset_rfl subset_rfl

/-- If linked terminal sets have the same size, the full linkage can be
oriented and promoted to a perfect path packing. -/
theorem exists_perfectPathPacking_of_card_eq (h : NodeLinkedIn G C A B)
    (hcard : A.card = B.card) :
    ∃ P : PerfectPathPacking G A B,
      P.card = A.card ∧ P.toPathPacking.StaysIn C := by
  rcases h.exists_pathPacking with ⟨P, hPcard, hstay⟩
  have hPcardA : P.card = A.card := by
    simpa [hcard] using hPcard
  have hPcardB : P.card = B.card := hPcardA.trans hcard
  refine ⟨P.toPerfectOfCardEq hPcardA hPcardB, ?_, ?_⟩
  · simpa [PathPacking.toPerfectOfCardEq, PerfectPathPacking.card,
      PathPacking.card] using hPcardA
  · exact PathPacking.orient_staysIn hstay

end NodeLinkedIn

namespace NodeWellLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C T : Finset V}

/-- Disjoint subfamilies of one node-well-linked terminal set are node-linked
inside the same region. -/
theorem nodeLinkedIn_between_disjoint_subsets
    (h : NodeWellLinkedIn G C T) {A B : Finset V}
    (hA : A ⊆ T) (hB : B ⊆ T) (hdisj : Disjoint A B) :
    NodeLinkedIn G C A B := by
  refine ⟨subset_trans hA h.1, subset_trans hB h.1, hdisj, ?_⟩
  intro A' B' hA' hB'
  have hA'T : A' ⊆ T := subset_trans hA' hA
  have hB'T : B' ⊆ T := subset_trans hB' hB
  have hA'B' : Disjoint A' B' := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact Finset.disjoint_left.mp hdisj (hA' hvA) (hB' hvB)
  exact h.2 hA'T hB'T hA'B'

end NodeWellLinkedIn

end SimpleGraph

end Lax17Proofs
