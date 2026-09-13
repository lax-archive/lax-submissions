import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Contracting a family of disjoint paths

Section 4.1 of Chuzhoy--Tan repeatedly contracts the currently remaining
`P`-paths to single vertices.  This file provides a reusable simple-graph
model for that operation.  A vertex of the contracted graph is either one
selected path index or one original vertex outside all selected paths.
-/

namespace SimpleGraph


/-- Vertices of the graph obtained by contracting the paths indexed by `I`.

The left summand represents a contracted path.  The right summand represents an
original vertex outside all contracted paths. -/
abbrev ContractedPathVertex {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B) (I : Finset P.Index) : Type u :=
  {i : P.Index // i ∈ I} ⊕
    {v : V // ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet}

namespace ContractedPathVertex

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable (P : PerfectPathPacking G A B) (I : Finset P.Index)

/-- The contracted vertex corresponding to one selected path. -/
def ofPath (i : P.Index) (hi : i ∈ I) : ContractedPathVertex P I :=
  Sum.inl ⟨i, hi⟩

/-- The contracted vertex corresponding to an original vertex outside the
selected paths. -/
def ofVertex (v : V)
    (hv : ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet) :
    ContractedPathVertex P I :=
  Sum.inr ⟨v, hv⟩

end ContractedPathVertex

/-- The branch set in the original graph represented by a contracted-path
vertex. -/
noncomputable def contractedPathBranch {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    {P : PerfectPathPacking G A B} {I : Finset P.Index}
    (x : ContractedPathVertex P I) : Finset V :=
  match x with
  | Sum.inl i => (P.path i.1).vertexSet
  | Sum.inr v => {v.1}

/-- The simple graph obtained by contracting the paths indexed by `I`.

Two contracted vertices are adjacent when the original graph has an edge
between their branch sets.  Parallel edges from the paper are irrelevant for
the node-disjoint path arguments, so the formal model is simple. -/
noncomputable def contractedPathGraph {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) {A B : Finset V}
    (P : PerfectPathPacking G A B) (I : Finset P.Index) :
    _root_.SimpleGraph (ContractedPathVertex P I) where
  Adj x y :=
    x ≠ y ∧
      ∃ u ∈ contractedPathBranch x,
        ∃ v ∈ contractedPathBranch y, G.Adj u v
  symm := by
    intro x y hxy
    rcases hxy with ⟨hxy_ne, u, hu, v, hv, huv⟩
    exact ⟨hxy_ne.symm, v, hv, u, hu, G.symm huv⟩
  loopless := ⟨by
    intro x hxx
    exact hxx.1 rfl⟩

namespace contractedPathGraph

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {P : PerfectPathPacking G A B} {I : Finset P.Index}

@[simp] theorem adj_iff (x y : ContractedPathVertex P I) :
    (contractedPathGraph G P I).Adj x y ↔
      x ≠ y ∧
        ∃ u ∈ contractedPathBranch x,
          ∃ v ∈ contractedPathBranch y, G.Adj u v :=
  Iff.rfl

/-- Every branch set of the contracted graph is nonempty. -/
theorem branch_nonempty (x : ContractedPathVertex P I) :
    (contractedPathBranch x).Nonempty := by
  classical
  cases x with
  | inl i =>
      exact ⟨(P.path i.1).source, GraphPath.source_mem_vertexSet (P.path i.1)⟩
  | inr v =>
      exact ⟨v.1, by simp [contractedPathBranch]⟩

/-- Every branch set of the contracted graph is connected in the original
graph. -/
theorem branch_connected (x : ContractedPathVertex P I) :
    (G.induce {v : V | v ∈ contractedPathBranch x}).Connected := by
  classical
  cases x with
  | inl i =>
      simpa [contractedPathBranch] using
        GraphPath.connected_induce_vertexSet (P.path i.1)
  | inr v =>
      simpa [contractedPathBranch] using
        GraphPath.connected_induce_vertexSet (GraphPath.refl G v.1)

/-- Distinct contracted vertices have disjoint branch sets. -/
theorem branch_disjoint ⦃x y : ContractedPathVertex P I⦄
    (hxy : x ≠ y) :
    Disjoint (contractedPathBranch x) (contractedPathBranch y) := by
  classical
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          by_cases hij : i.1 = j.1
          · exfalso
            apply hxy
            cases i
            cases j
            simp_all
          · simpa [contractedPathBranch] using
              P.toPathPacking.node_disjoint hij
      | inr v =>
          rw [Finset.disjoint_left]
          intro z hz hvz
          have hzv : z = v.1 := by simpa [contractedPathBranch] using hvz
          exact v.2 i.1 i.2 (by simpa [hzv] using hz)
  | inr v =>
      cases y with
      | inl j =>
          rw [Finset.disjoint_left]
          intro z hzv hzj
          have hzv' : z = v.1 := by simpa [contractedPathBranch] using hzv
          exact v.2 j.1 j.2 (by simpa [hzv'] using hzj)
      | inr w =>
          rw [Finset.disjoint_left]
          intro z hzv hzw
          have hzv' : z = v.1 := by simpa [contractedPathBranch] using hzv
          have hzw' : z = w.1 := by simpa [contractedPathBranch] using hzw
          apply hxy
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hzv'.symm.trans hzw'

/-- The contracted-path graph is a minor of the original graph. -/
theorem isMinor :
    IsMinor (contractedPathGraph G P I) G := by
  exact IsMinor.of_branchSets contractedPathBranch
    branch_nonempty branch_connected
    (fun {u v} hxy => branch_disjoint (x := u) (y := v) hxy)
    (by
      intro x y hxy
      exact hxy.2)

end contractedPathGraph

/-- The union of the original branch sets represented by a finite set of
vertices of a contracted-path graph. -/
noncomputable def contractedPathBranchUnion {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    {P : PerfectPathPacking G A B} {I : Finset P.Index}
    (S : Finset (ContractedPathVertex P I)) : Finset V :=
  S.biUnion contractedPathBranch

namespace contractedPathBranchUnion

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {P : PerfectPathPacking G A B} {I : Finset P.Index}

theorem branch_subset {S : Finset (ContractedPathVertex P I)}
    {x : ContractedPathVertex P I} (hx : x ∈ S) :
    contractedPathBranch x ⊆ contractedPathBranchUnion S := by
  classical
  intro v hv
  exact Finset.mem_biUnion.2 ⟨x, hx, hv⟩

theorem mem_of_mem_branch {S : Finset (ContractedPathVertex P I)}
    {x : ContractedPathVertex P I} (hx : x ∈ S) {v : V}
    (hv : v ∈ contractedPathBranch x) :
    v ∈ contractedPathBranchUnion S :=
  branch_subset hx hv

/-- The branch-union operation preserves disjointness of vertex sets in the
contracted graph.  This is the basic lifting fact used to turn disjoint
contracted linkages into disjoint original paths. -/
theorem disjoint_of_disjoint {S T : Finset (ContractedPathVertex P I)}
    (hST : Disjoint S T) :
    Disjoint (contractedPathBranchUnion S) (contractedPathBranchUnion T) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvS hvT
  rcases Finset.mem_biUnion.1 hvS with ⟨x, hxS, hvx⟩
  rcases Finset.mem_biUnion.1 hvT with ⟨y, hyT, hvy⟩
  by_cases hxy : x = y
  · subst hxy
    exact Finset.disjoint_left.mp hST hxS hyT
  · exact Finset.disjoint_left.mp
      (contractedPathGraph.branch_disjoint (G := G) (P := P) (I := I) hxy)
      hvx hvy

end contractedPathBranchUnion

namespace ContractedPathVertex

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {P : PerfectPathPacking G A B} {I : Finset P.Index}

/-- The union of branch sets along a walk in the contracted graph is connected
in the original graph. -/
theorem walk_branchUnion_connected :
    {x y : ContractedPathVertex P I} →
      (W : (contractedPathGraph G P I).Walk x y) →
        (G.induce
          {v : V | v ∈ contractedPathBranchUnion W.support.toFinset}).Connected
  | x, _, _root_.SimpleGraph.Walk.nil' _ => by
      rw [show
        {v : V | v ∈ contractedPathBranchUnion
          ((_root_.SimpleGraph.Walk.nil : (contractedPathGraph G P I).Walk x x).support.toFinset)}
          = {v : V | v ∈ contractedPathBranch x} by
          ext v
          simp [contractedPathBranchUnion]]
      exact contractedPathGraph.branch_connected (G := G) (P := P) (I := I) x
  | x, z, _root_.SimpleGraph.Walk.cons' _ y _ hxy W => by
      classical
      have hbranch :
          (G.induce {v : V | v ∈ contractedPathBranch x}).Connected :=
        contractedPathGraph.branch_connected (G := G) (P := P) (I := I) x
      have htail :
          (G.induce
            {v : V | v ∈ contractedPathBranchUnion W.support.toFinset}).Connected :=
        walk_branchUnion_connected W
      rcases (contractedPathGraph.adj_iff (G := G) (P := P) (I := I) x y).1 hxy with
        ⟨_hne, u, hu, v, hv, huv⟩
      have hvTail :
          v ∈ contractedPathBranchUnion W.support.toFinset := by
        exact contractedPathBranchUnion.mem_of_mem_branch
          (S := W.support.toFinset) (x := y) (by simp) hv
      have hconn :
          (G.induce
            ({v : V | v ∈ contractedPathBranch x} ∪
              {v : V | v ∈ contractedPathBranchUnion W.support.toFinset})).Connected :=
        _root_.SimpleGraph.connected_induce_union
          hbranch.preconnected htail.preconnected hu hvTail huv
      rw [show
        {v : V | v ∈ contractedPathBranchUnion
          ((_root_.SimpleGraph.Walk.cons hxy W).support.toFinset)}
          =
        ({v : V | v ∈ contractedPathBranch x} ∪
          {v : V | v ∈ contractedPathBranchUnion W.support.toFinset}) by
          ext w
          simp [contractedPathBranchUnion, _root_.SimpleGraph.Walk.support_cons,
            Finset.mem_biUnion]]
      exact hconn

/-- The union of branch sets along a contracted graph path is connected in the
original graph. -/
theorem graphPath_branchUnion_connected
    (R : GraphPath (contractedPathGraph G P I)) :
    (G.induce
      {v : V | v ∈ contractedPathBranchUnion R.vertexSet}).Connected := by
  simpa [GraphPath.vertexSet] using
    (walk_branchUnion_connected (P := P) (I := I) R.walk)

/-- Lift a path in the contracted graph to an original graph path between
chosen vertices in the endpoint branch sets.  The chosen path stays inside the
union of branch sets visited by the contracted path. -/
noncomputable def liftGraphPath
    (R : GraphPath (contractedPathGraph G P I))
    {s t : V}
    (hs : s ∈ contractedPathBranch R.source)
    (ht : t ∈ contractedPathBranch R.target) : GraphPath G :=
  GraphPath.ofConnectedInduce
    (contractedPathBranchUnion R.vertexSet)
    (graphPath_branchUnion_connected (P := P) (I := I) R)
    s t
    (contractedPathBranchUnion.mem_of_mem_branch
      (S := R.vertexSet) (x := R.source) R.source_mem_vertexSet hs)
    (contractedPathBranchUnion.mem_of_mem_branch
      (S := R.vertexSet) (x := R.target) R.target_mem_vertexSet ht)

@[simp] theorem liftGraphPath_source
    (R : GraphPath (contractedPathGraph G P I))
    {s t : V}
    (hs : s ∈ contractedPathBranch R.source)
    (ht : t ∈ contractedPathBranch R.target) :
    (liftGraphPath (P := P) (I := I) R hs ht).source = s := rfl

@[simp] theorem liftGraphPath_target
    (R : GraphPath (contractedPathGraph G P I))
    {s t : V}
    (hs : s ∈ contractedPathBranch R.source)
    (ht : t ∈ contractedPathBranch R.target) :
    (liftGraphPath (P := P) (I := I) R hs ht).target = t := rfl

theorem liftGraphPath_vertexSet_subset_branchUnion
    (R : GraphPath (contractedPathGraph G P I))
    {s t : V}
    (hs : s ∈ contractedPathBranch R.source)
    (ht : t ∈ contractedPathBranch R.target) :
    (liftGraphPath (P := P) (I := I) R hs ht).vertexSet ⊆
      contractedPathBranchUnion R.vertexSet :=
  GraphPath.ofConnectedInduce_vertexSet_subset
    (contractedPathBranchUnion R.vertexSet)
    (graphPath_branchUnion_connected (P := P) (I := I) R)
    s t
    (contractedPathBranchUnion.mem_of_mem_branch
      (S := R.vertexSet) (x := R.source) R.source_mem_vertexSet hs)
    (contractedPathBranchUnion.mem_of_mem_branch
      (S := R.vertexSet) (x := R.target) R.target_mem_vertexSet ht)

end ContractedPathVertex

namespace ContractedPathVertex

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {P : PerfectPathPacking G A B} {I : Finset P.Index}

/-- A vertex of the original graph lies in at most one contracted path branch. -/
theorem path_index_unique_of_mem
    {x : V} {i j : P.Index} (_hi : i ∈ I) (_hj : j ∈ I)
    (hxi : x ∈ (P.path i).vertexSet) (hxj : x ∈ (P.path j).vertexSet) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hxi hxj

/-- Project an original vertex to the graph obtained by contracting the
selected `P`-paths.  Vertices on a selected path are sent to the corresponding
contracted path vertex; all other vertices remain as singleton vertices. -/
noncomputable def projection (x : V) : ContractedPathVertex P I :=
  if h : ∃ i : P.Index, i ∈ I ∧ x ∈ (P.path i).vertexSet then
    Sum.inl ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  else
    Sum.inr ⟨x, by
      intro i hi hxi
      exact h ⟨i, hi, hxi⟩⟩

/-- A projected vertex always has the original vertex in its branch set. -/
theorem mem_branch_projection (x : V) :
    x ∈ contractedPathBranch (P := P) (I := I) (projection (P := P) (I := I) x) := by
  classical
  unfold projection
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · simp [contractedPathBranch]

/-- Projection of a vertex known to lie on one of the contracted paths. -/
theorem projection_eq_of_mem_path
    {x : V} {i : P.Index} (hi : i ∈ I)
    (hxi : x ∈ (P.path i).vertexSet) :
    projection (P := P) (I := I) x =
      (Sum.inl ⟨i, hi⟩ : ContractedPathVertex P I) := by
  classical
  unfold projection
  have h : ∃ j : P.Index, j ∈ I ∧ x ∈ (P.path j).vertexSet := ⟨i, hi, hxi⟩
  simp only [dif_pos h]
  apply congrArg Sum.inl
  apply Subtype.ext
  exact path_index_unique_of_mem
    (P := P) (I := I) (Classical.choose_spec h).1 hi
    (Classical.choose_spec h).2 hxi

/-- Projection of a vertex outside all contracted paths. -/
theorem projection_eq_of_forall_not_mem
    {x : V} (hx : ∀ i : P.Index, i ∈ I → x ∉ (P.path i).vertexSet) :
    projection (P := P) (I := I) x =
      (Sum.inr ⟨x, hx⟩ : ContractedPathVertex P I) := by
  classical
  unfold projection
  have hnot : ¬ ∃ i : P.Index, i ∈ I ∧ x ∈ (P.path i).vertexSet := by
    rintro ⟨i, hi, hxi⟩
    exact hx i hi hxi
  simp only [dif_neg hnot]

/-- An original edge whose endpoints project to distinct contracted vertices
gives an edge in the contracted graph. -/
theorem projection_adj_of_adj_of_ne {x y : V}
    (hxy : G.Adj x y)
    (hne :
      projection (P := P) (I := I) x ≠ projection (P := P) (I := I) y) :
    (contractedPathGraph G P I).Adj
      (projection (P := P) (I := I) x)
      (projection (P := P) (I := I) y) := by
  exact ⟨hne, x, mem_branch_projection (P := P) (I := I) x,
    y, mem_branch_projection (P := P) (I := I) y, hxy⟩

namespace ProjectionWalk

/-- Project a walk in the original graph to the contracted graph, suppressing
steps whose two endpoints project to the same contracted vertex. -/
noncomputable def ofWalk : {x y : V} → (W : G.Walk x y) →
    (contractedPathGraph G P I).Walk
      (projection (P := P) (I := I) x)
      (projection (P := P) (I := I) y)
  | x, _, _root_.SimpleGraph.Walk.nil' _ =>
      _root_.SimpleGraph.Walk.nil
  | x, z, _root_.SimpleGraph.Walk.cons' _ y _ h W => by
      let ih := ofWalk W
      by_cases hsame :
        projection (P := P) (I := I) x = projection (P := P) (I := I) y
      · exact ih.copy hsame.symm rfl
      · exact _root_.SimpleGraph.Walk.cons
          (projection_adj_of_adj_of_ne (P := P) (I := I) h hsame) ih

/-- Every vertex of the projected walk is the projection of some vertex of the
original walk. -/
theorem support_subset_projection : {x y : V} → (W : G.Walk x y) →
    ∀ z ∈ (ofWalk (P := P) (I := I) W).support,
      ∃ v ∈ W.support, projection (P := P) (I := I) v = z
  | x, _, _root_.SimpleGraph.Walk.nil' _ => by
      intro z hz
      have hz' : z = projection (P := P) (I := I) x := by
        simpa [ofWalk] using hz
      exact ⟨x, by simp, hz'.symm⟩
  | x, _, _root_.SimpleGraph.Walk.cons' _ y _ h W => by
      intro z hz
      by_cases hsame :
        projection (P := P) (I := I) x = projection (P := P) (I := I) y
      · have hzTail : z ∈ (ofWalk (P := P) (I := I) W).support := by
          simpa [ofWalk, hsame] using hz
        rcases support_subset_projection W z hzTail with
          ⟨v, hv, hvz⟩
        exact ⟨v, by simp [hv], hvz⟩
      · have hzCons :
            z = projection (P := P) (I := I) x ∨
              z ∈ (ofWalk (P := P) (I := I) W).support := by
          simpa [ofWalk, hsame, _root_.SimpleGraph.Walk.support_cons] using hz
        rcases hzCons with hzHead | hzTail
        · exact ⟨x, by simp, hzHead.symm⟩
        · rcases support_subset_projection W z hzTail with
            ⟨v, hv, hvz⟩
          exact ⟨v, by simp [hv], hvz⟩

/-- Turn the projected walk into a simple graph path. -/
noncomputable def toGraphPath (R : GraphPath G) :
    GraphPath (contractedPathGraph G P I) where
  source := projection (P := P) (I := I) R.source
  target := projection (P := P) (I := I) R.target
  walk := (ofWalk R.walk).toPath.val
  isPath := (ofWalk R.walk).toPath.property

theorem toGraphPath_vertexSet_subset_projection (R : GraphPath G) :
    ∀ z ∈ (toGraphPath (P := P) (I := I) R).vertexSet,
      ∃ v ∈ R.vertexSet, projection (P := P) (I := I) v = z := by
  classical
  intro z hz
  have hzSupport :
      z ∈ ((ofWalk (P := P) (I := I) R.walk).toPath :
        (contractedPathGraph G P I).Walk
          (projection (P := P) (I := I) R.source)
          (projection (P := P) (I := I) R.target)).support := by
    simpa [toGraphPath, GraphPath.vertexSet] using hz
  have hzWalk :
      z ∈ (ofWalk (P := P) (I := I) R.walk).support :=
    _root_.SimpleGraph.Walk.support_toPath_subset
      (ofWalk (P := P) (I := I) R.walk) hzSupport
  rcases support_subset_projection (P := P) (I := I) R.walk z hzWalk with
    ⟨v, hv, hvz⟩
  exact ⟨v, by simpa [GraphPath.vertexSet] using hv, hvz⟩

end ProjectionWalk

/-- The set `S_i` in the paper: vertices representing the contracted paths. -/
noncomputable def pathTerminalSet :
    Finset (ContractedPathVertex P I) :=
  Finset.univ.image fun i : {i : P.Index // i ∈ I} =>
    (Sum.inl i : ContractedPathVertex P I)

/-- A finite original vertex set embedded into the contracted graph, assuming
it is disjoint from all contracted path branch sets. -/
noncomputable def vertexTerminalSet (U : Finset V)
    (hU : ∀ v ∈ U, ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet) :
    Finset (ContractedPathVertex P I) :=
  U.attach.image fun v =>
    (Sum.inr ⟨v.1, hU v.1 v.2⟩ : ContractedPathVertex P I)

@[simp] theorem mem_pathTerminalSet_of_mem (i : P.Index) (hi : i ∈ I) :
    (Sum.inl ⟨i, hi⟩ : ContractedPathVertex P I) ∈
      pathTerminalSet (P := P) (I := I) := by
  classical
  exact Finset.mem_image.mpr ⟨⟨i, hi⟩, by simp, rfl⟩

theorem mem_pathTerminalSet_iff (x : ContractedPathVertex P I) :
    x ∈ pathTerminalSet (P := P) (I := I) ↔
      ∃ (i : P.Index) (hi : i ∈ I),
        x = (Sum.inl ⟨i, hi⟩ : ContractedPathVertex P I) := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    exact ⟨i.1, i.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact mem_pathTerminalSet_of_mem (P := P) (I := I) i hi

theorem pathTerminalSet_card :
    (pathTerminalSet (P := P) (I := I)).card = I.card := by
  classical
  rw [pathTerminalSet, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact Sum.inl.inj h

theorem vertexTerminalSet_card (U : Finset V)
    (hU : ∀ v ∈ U, ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet) :
    (vertexTerminalSet (P := P) (I := I) U hU).card = U.card := by
  classical
  rw [vertexTerminalSet, Finset.card_image_of_injective]
  · simp
  · intro v w h
    have hsub :
        (⟨v.1, hU v.1 v.2⟩ :
          {v : V // ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet}) =
          ⟨w.1, hU w.1 w.2⟩ := Sum.inr.inj h
    have hvw : v.1 = w.1 :=
      congrArg
        (fun z : {v : V // ∀ i : P.Index, i ∈ I →
            v ∉ (P.path i).vertexSet} => z.1) hsub
    exact Subtype.ext hvw

theorem mem_vertexTerminalSet_iff (U : Finset V)
    (hU : ∀ v ∈ U, ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet)
    (x : ContractedPathVertex P I) :
    x ∈ vertexTerminalSet (P := P) (I := I) U hU ↔
      ∃ (v : V) (_hv : v ∈ U)
        (hout : ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet),
        x = (Sum.inr ⟨v, hout⟩ : ContractedPathVertex P I) := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨v, _hv, rfl⟩
    exact ⟨v.1, v.2, hU v.1 v.2, rfl⟩
  · rintro ⟨v, hv, hout, rfl⟩
    unfold vertexTerminalSet
    exact Finset.mem_image.mpr
      ⟨⟨v, hv⟩, by simp, by
        apply congrArg Sum.inr
        apply Subtype.ext
        rfl⟩

/-- Contracted path terminals and embedded original-vertex terminals are
disjoint: the former are represented by `Sum.inl`, the latter by `Sum.inr`. -/
theorem disjoint_pathTerminalSet_vertexTerminalSet (U : Finset V)
    (hU : ∀ v ∈ U, ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet) :
    Disjoint (pathTerminalSet (P := P) (I := I))
      (vertexTerminalSet (P := P) (I := I) U hU) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxPath hxVertex
  rcases Finset.mem_image.mp hxPath with ⟨i, _hi, rfl⟩
  rcases Finset.mem_image.mp hxVertex with ⟨v, _hv, h⟩
  cases h

/-- The contracted path vertices of a finite set of contracted-graph vertices. -/
noncomputable def pathVerticesIn
    (J : Finset (ContractedPathVertex P I)) :
    Finset {i : P.Index // i ∈ I} :=
  Finset.univ.filter fun i : {i : P.Index // i ∈ I} =>
    (Sum.inl i : ContractedPathVertex P I) ∈ J

/-- The original path indices represented by the contracted path vertices in
`J`. -/
noncomputable def pathIndicesIn
    (J : Finset (ContractedPathVertex P I)) : Finset P.Index :=
  (pathVerticesIn (P := P) (I := I) J).image Subtype.val

theorem mem_pathVerticesIn_iff
    (J : Finset (ContractedPathVertex P I))
    (i : {i : P.Index // i ∈ I}) :
    i ∈ pathVerticesIn (P := P) (I := I) J ↔
      (Sum.inl i : ContractedPathVertex P I) ∈ J := by
  classical
  simp [pathVerticesIn]

theorem mem_pathIndicesIn_iff
    (J : Finset (ContractedPathVertex P I)) (i : P.Index) :
    i ∈ pathIndicesIn (P := P) (I := I) J ↔
      ∃ hi : i ∈ I, (Sum.inl ⟨i, hi⟩ : ContractedPathVertex P I) ∈ J := by
  classical
  constructor
  · intro hiJ
    rcases Finset.mem_image.mp hiJ with ⟨j, hj, hji⟩
    subst hji
    exact ⟨j.2, (mem_pathVerticesIn_iff (P := P) (I := I) J j).1 hj⟩
  · rintro ⟨hi, hJ⟩
    exact Finset.mem_image.mpr
      ⟨⟨i, hi⟩,
        (mem_pathVerticesIn_iff (P := P) (I := I) J ⟨i, hi⟩).2 hJ,
        rfl⟩

theorem pathVerticesIn_card_le
    (J : Finset (ContractedPathVertex P I)) :
    (pathVerticesIn (P := P) (I := I) J).card ≤ J.card := by
  classical
  let f : {i : {i : P.Index // i ∈ I} //
      i ∈ pathVerticesIn (P := P) (I := I) J} →
      {x : ContractedPathVertex P I // x ∈ J} :=
    fun i => ⟨Sum.inl i.1,
      (mem_pathVerticesIn_iff (P := P) (I := I) J i.1).1 i.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have hsum : (Sum.inl i.1 : ContractedPathVertex P I) = Sum.inl j.1 :=
      congrArg Subtype.val hij
    exact Sum.inl.inj hsum
  have hcard :
      Fintype.card {i : {i : P.Index // i ∈ I} //
        i ∈ pathVerticesIn (P := P) (I := I) J} ≤
        Fintype.card {x : ContractedPathVertex P I // x ∈ J} :=
    Fintype.card_le_of_injective f hf
  simpa [Fintype.card_coe] using hcard

theorem pathIndicesIn_card_le
    (J : Finset (ContractedPathVertex P I)) :
    (pathIndicesIn (P := P) (I := I) J).card ≤ J.card := by
  classical
  rw [pathIndicesIn, Finset.card_image_of_injective]
  · exact pathVerticesIn_card_le (P := P) (I := I) J
  · intro i j hij
    exact Subtype.ext hij

theorem pathIndicesIn_subset
    (J : Finset (ContractedPathVertex P I)) :
    pathIndicesIn (P := P) (I := I) J ⊆ I := by
  classical
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, _hj, rfl⟩
  exact j.2

section OriginalVertices

variable [Fintype V]

/-- The original singleton vertices of a finite set of contracted-graph
vertices. -/
noncomputable def originalVerticesIn
    (J : Finset (ContractedPathVertex P I)) :
    Finset {v : V // ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet} :=
  Finset.univ.filter fun v =>
    (Sum.inr v : ContractedPathVertex P I) ∈ J

/-- The original vertices represented by singleton vertices in `J`. -/
noncomputable def originalVertexSetIn
    (J : Finset (ContractedPathVertex P I)) : Finset V :=
  (originalVerticesIn (P := P) (I := I) J).image Subtype.val

theorem mem_originalVerticesIn_iff
    (J : Finset (ContractedPathVertex P I))
    (v : {v : V // ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet}) :
    v ∈ originalVerticesIn (P := P) (I := I) J ↔
      (Sum.inr v : ContractedPathVertex P I) ∈ J := by
  classical
  simp [originalVerticesIn]

theorem mem_originalVertexSetIn_iff
    (J : Finset (ContractedPathVertex P I)) (v : V) :
    v ∈ originalVertexSetIn (P := P) (I := I) J ↔
      ∃ hv : ∀ i : P.Index, i ∈ I → v ∉ (P.path i).vertexSet,
        (Sum.inr ⟨v, hv⟩ : ContractedPathVertex P I) ∈ J := by
  classical
  constructor
  · intro hvJ
    rcases Finset.mem_image.mp hvJ with ⟨w, hw, hwv⟩
    subst hwv
    exact ⟨w.2, (mem_originalVerticesIn_iff (P := P) (I := I) J w).1 hw⟩
  · rintro ⟨hv, hJ⟩
    exact Finset.mem_image.mpr
      ⟨⟨v, hv⟩,
        (mem_originalVerticesIn_iff (P := P) (I := I) J ⟨v, hv⟩).2 hJ,
        rfl⟩

theorem originalVerticesIn_card_le
    (J : Finset (ContractedPathVertex P I)) :
    (originalVerticesIn (P := P) (I := I) J).card ≤ J.card := by
  classical
  let f : {v : {v : V // ∀ i : P.Index, i ∈ I →
        v ∉ (P.path i).vertexSet} //
      v ∈ originalVerticesIn (P := P) (I := I) J} →
      {x : ContractedPathVertex P I // x ∈ J} :=
    fun v => ⟨Sum.inr v.1,
      (mem_originalVerticesIn_iff (P := P) (I := I) J v.1).1 v.2⟩
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    have hsum : (Sum.inr v.1 : ContractedPathVertex P I) = Sum.inr w.1 :=
      congrArg Subtype.val hvw
    exact Sum.inr.inj hsum
  have hcard :
      Fintype.card {v : {v : V // ∀ i : P.Index, i ∈ I →
          v ∉ (P.path i).vertexSet} //
        v ∈ originalVerticesIn (P := P) (I := I) J} ≤
        Fintype.card {x : ContractedPathVertex P I // x ∈ J} :=
    Fintype.card_le_of_injective f hf
  simpa [Fintype.card_coe] using hcard

theorem originalVertexSetIn_card_le
    (J : Finset (ContractedPathVertex P I)) :
    (originalVertexSetIn (P := P) (I := I) J).card ≤ J.card := by
  classical
  rw [originalVertexSetIn, Finset.card_image_of_injective]
  · exact originalVerticesIn_card_le (P := P) (I := I) J
  · intro v w hvw
    exact Subtype.ext hvw

end OriginalVertices

end ContractedPathVertex

end SimpleGraph

end Lax17Proofs
