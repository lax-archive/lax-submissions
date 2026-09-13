import Lax17Proofs.Source.Section45PseudoGrid

namespace Lax17Proofs

/-!
# Exact slice supports for Observation 5.4

This module begins the formal proof of Chuzhoy--Tan, Observation 5.4
(`grid-minor-theorem.pdf`, Section 5.2).  A sliced linkage cannot span a graph
on the original ambient vertex type: vertices outside the slice would be
isolated counterexamples to `PerfectPathPacking.SpansVertices`.  We therefore
use the subtype consisting exactly of the vertices of the sliced rows and the
selected auxiliary paths.

The main theorem in this file is `sliceSupport_spansVertices`.  Its proof uses
the precise meaning of `PathInSlice`: an auxiliary vertex first lies on some
full row by global spanning, and localization then places that row intersection
inside the selected half-open row segment.
-/

namespace SimpleGraph
namespace Exponent8

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {M : ℕ}
variable {R : PerfectPathPacking G A B}

/-- Map a path in an induced graph back to the original vertex type. -/
noncomputable def liftInducedPath
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U})) :
    GraphPath K where
  source := P.source.1
  target := P.target.1
  walk :=
    P.walk.map
      (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom
  isPath := by
    exact
      _root_.SimpleGraph.Walk.map_isPath_of_injective
        Subtype.val_injective P.isPath

/-- Mapping an injectively relabelled list does not change the position of a
member. -/
theorem list_idxOf_map_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (l : List α) (a : α) (ha : a ∈ l) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        simp
      · have hfa : f x ≠ f a := by
          intro h
          exact hxa (hf h)
        have haTail : a ∈ xs := by
          rcases (by simpa using ha : a = x ∨ a ∈ xs) with hax | htail
          · exact False.elim (hxa hax.symm)
          · exact htail
        simp [hxa, hfa, ih haTail]

@[simp] theorem liftInducedPath_vertexIndex
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U}))
    (z : {v : V // v ∈ U}) (hz : z ∈ P.vertexSet) :
    (liftInducedPath P).vertexIndex z.1 = P.vertexIndex z := by
  classical
  simp only [liftInducedPath, GraphPath.vertexIndex]
  let f :=
    (_root_.SimpleGraph.Embedding.induce
      (G := K) (↑U : Set V)).toHom
  have hs :
      (P.walk.map f).support = P.walk.support.map f :=
    _root_.SimpleGraph.Walk.support_map f P.walk
  dsimp [f] at hs
  rw [hs]
  exact
    list_idxOf_map_of_injective
      (fun x : {v : V // v ∈ U} =>
        (_root_.SimpleGraph.Embedding.induce
          (G := K) (↑U : Set V)).toHom x)
      Subtype.val_injective P.walk.support z
      (by
        change z ∈ P.walk.support.toFinset at hz
        exact List.mem_toFinset.mp hz)

@[simp] theorem liftInducedPath_source
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U})) :
    (liftInducedPath P).source = P.source.1 := rfl

@[simp] theorem liftInducedPath_target
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U})) :
    (liftInducedPath P).target = P.target.1 := rfl

theorem mem_liftInducedPath_vertexSet
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U})) {v : V} :
    v ∈ (liftInducedPath P).vertexSet ↔
      ∃ hv : v ∈ U, (⟨v, hv⟩ : {x : V // x ∈ U}) ∈ P.vertexSet := by
  classical
  constructor
  · intro hv
    have hvSupport :
        v ∈ (liftInducedPath P).walk.support := by
      exact List.mem_toFinset.mp (by
        simpa [GraphPath.vertexSet] using hv)
    change
      v ∈
        (P.walk.map
          (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).support
      at hvSupport
    rw [_root_.SimpleGraph.Walk.support_map] at hvSupport
    rcases List.mem_map.mp hvSupport with ⟨z, hz, hzv⟩
    subst v
    refine ⟨z.2, ?_⟩
    exact List.mem_toFinset.mpr hz
  · rintro ⟨hvU, hv⟩
    have hvList : (⟨v, hvU⟩ : {x : V // x ∈ U}) ∈ P.walk.support := by
      exact List.mem_toFinset.mp hv
    have :
        v ∈ List.map Subtype.val P.walk.support :=
      List.mem_map.mpr ⟨⟨v, hvU⟩, hvList, rfl⟩
    apply List.mem_toFinset.mpr
    change
      v ∈
        (P.walk.map
          (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).support
    rw [_root_.SimpleGraph.Walk.support_map]
    exact this

/-- Lifting a path from an induced graph preserves the order of all vertices
on that path. -/
theorem liftInducedPath_before
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U}))
    {x y : {v : V // v ∈ U}} (hxy : P.Before x y) :
    (liftInducedPath P).Before x.1 y.1 := by
  have hdata := (P.before_iff_vertexIndex_le).1 hxy
  apply (liftInducedPath P).before_iff_vertexIndex_le.2
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_liftInducedPath_vertexSet P).2 ⟨x.2, hdata.1⟩
  · exact (mem_liftInducedPath_vertexSet P).2 ⟨y.2, hdata.2.1⟩
  · simpa only [
        liftInducedPath_vertexIndex P x hdata.1,
        liftInducedPath_vertexIndex P y hdata.2.1] using hdata.2.2

/-- Inducing a path onto a finite support and then forgetting the subtype
preserves the original path order. -/
theorem induce_before_val
    {K : _root_.SimpleGraph V} (P : GraphPath K)
    (U : Finset V) (hU : P.vertexSet ⊆ U)
    {x y : {v : V // v ∈ U}}
    (hxy : (P.induce U hU).Before x y) :
    P.Before x.1 y.1 := by
  have hxy' := liftInducedPath_before (P.induce U hU) hxy
  have hpath : liftInducedPath (P.induce U hU) = P := by
    cases P
    simp [liftInducedPath, GraphPath.induce]
    exact _root_.SimpleGraph.Walk.map_induce _ _
  simpa [hpath] using hxy'

@[simp] theorem mapLe_vertexIndex_local
    {K L : _root_.SimpleGraph V} (P : GraphPath K)
    (hKL : K ≤ L) (v : V) :
    (P.mapLe hKL).vertexIndex v = P.vertexIndex v := by
  classical
  simp [GraphPath.vertexIndex, GraphPath.mapLe,
    _root_.SimpleGraph.Walk.support_mapLe_eq_support]

theorem mapLe_before_iff_local
    {K L : _root_.SimpleGraph V} (P : GraphPath K)
    (hKL : K ≤ L) {x y : V} :
    (P.mapLe hKL).Before x y ↔ P.Before x y := by
  rw [(P.mapLe hKL).before_iff_vertexIndex_le,
    P.before_iff_vertexIndex_le, mapLe_vertexIndex_local,
    mapLe_vertexIndex_local]
  simp only [GraphPath.mapLe_vertexSet]

@[simp] theorem transfer_vertexIndex_local
    {K : _root_.SimpleGraph V} (P : GraphPath K)
    (L : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ L.edgeSet)
    (v : V) :
    (P.transfer L h).vertexIndex v = P.vertexIndex v := by
  classical
  simp [GraphPath.vertexIndex, GraphPath.transfer,
    _root_.SimpleGraph.Walk.support_transfer]

theorem transfer_before_iff_local
    {K : _root_.SimpleGraph V} (P : GraphPath K)
    (L : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ L.edgeSet)
    {x y : V} :
    (P.transfer L h).Before x y ↔ P.Before x y := by
  rw [(P.transfer L h).before_iff_vertexIndex_le,
    P.before_iff_vertexIndex_le, transfer_vertexIndex_local,
    transfer_vertexIndex_local]
  simp only [GraphPath.transfer_vertexSet]

theorem pathPacking_inSpanningGraph_before_iff_local
    {K : _root_.SimpleGraph V} {C D : Finset V}
    (P : PathPacking K C D) (i : P.Index) {x y : V} :
    (P.inSpanningGraph.path i).Before x y ↔
      (P.path i).Before x y := by
  change
    ((P.path i).transfer P.spanningGraph _).Before x y ↔
      (P.path i).Before x y
  exact transfer_before_iff_local (P.path i) P.spanningGraph _

/-- An infix of a duplicate-free list has the same relative order as the
ambient list. -/
theorem list_idxOf_le_of_infix
    {α : Type*} [DecidableEq α] {small large : List α}
    (hlarge : large.Nodup) (hsmall : small <:+: large)
    {x y : α} (hx : x ∈ small) (hy : y ∈ small)
    (hxy : small.idxOf x ≤ small.idxOf y) :
    large.idxOf x ≤ large.idxOf y := by
  rcases hsmall with ⟨pre, post, hdecomp⟩
  have hnodup : (pre ++ small ++ post).Nodup := by
    simpa [hdecomp] using hlarge
  have hdisjoint : List.Disjoint pre (small ++ post) :=
    List.disjoint_of_nodup_append (by
      simpa [List.append_assoc] using hnodup)
  have hxpre : x ∉ pre := by
    intro hx'
    exact hdisjoint hx' (by simp [hx])
  have hypre : y ∉ pre := by
    intro hy'
    exact hdisjoint hy' (by simp [hy])
  have hxidx :
      (pre ++ small ++ post).idxOf x =
        pre.length + small.idxOf x := by
    rw [List.append_assoc]
    rw [List.idxOf_append_of_notMem hxpre,
      List.idxOf_append_of_mem hx]
  have hyidx :
      (pre ++ small ++ post).idxOf y =
        pre.length + small.idxOf y := by
    rw [List.append_assoc]
    rw [List.idxOf_append_of_notMem hypre,
      List.idxOf_append_of_mem hy]
  rw [← hdecomp, hxidx, hyidx]
  omega

/-- A contiguous subwalk of a simple path preserves its oriented vertex
order in the ambient path. -/
theorem before_of_walk_isSubwalk
    {K : _root_.SimpleGraph V} (P Q : GraphPath K)
    (hsub : Q.walk.IsSubwalk P.walk)
    {x y : V} (hxy : Q.Before x y) :
    P.Before x y := by
  have hdata := (Q.before_iff_vertexIndex_le).1 hxy
  apply P.before_iff_vertexIndex_le.2
  refine ⟨?_, ?_, ?_⟩
  · have hsubset := hsub.support_subset
    exact by
      simpa [GraphPath.vertexSet] using
        hsubset (by simpa [GraphPath.vertexSet] using hdata.1)
  · have hsubset := hsub.support_subset
    exact by
      simpa [GraphPath.vertexSet] using
        hsubset (by simpa [GraphPath.vertexSet] using hdata.2.1)
  · apply list_idxOf_le_of_infix P.isPath.support_nodup
      (_root_.SimpleGraph.Walk.isSubwalk_iff_support_isInfix.1 hsub)
    · simpa [GraphPath.vertexSet] using hdata.1
    · simpa [GraphPath.vertexSet] using hdata.2.1
    · simpa [GraphPath.vertexIndex] using hdata.2.2

theorem liftInducedPath_vertexSet_subset
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U})) :
    (liftInducedPath P).vertexSet ⊆ U := by
  intro v hv
  exact (mem_liftInducedPath_vertexSet P).1 hv |>.choose

/-- Lift a perfect packing in an induced graph back to its original terminal
sets and vertex type. -/
noncomputable def liftInducedPerfect
    {K : _root_.SimpleGraph V} {U A₀ B₀ : Finset V}
    (hA : A₀ ⊆ U) (hB : B₀ ⊆ U)
    (P : PerfectPathPacking (K.induce {v : V | v ∈ U})
      (PathPacking.subtypeFinset A₀ U hA)
      (PathPacking.subtypeFinset B₀ U hB)) :
    PerfectPathPacking K A₀ B₀ where
  toPathPacking := {
    Index := P.Index
    path := fun p => liftInducedPath (P.path p)
    connects := by
      intro p
      rcases P.connects p with hp | hp
      · exact Or.inl
          ⟨(PathPacking.mem_subtypeFinset hA _).1 hp.1,
            (PathPacking.mem_subtypeFinset hB _).1 hp.2⟩
      · exact Or.inr
          ⟨(PathPacking.mem_subtypeFinset hB _).1 hp.1,
            (PathPacking.mem_subtypeFinset hA _).1 hp.2⟩
    node_disjoint := by
      intro p q hpq
      rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro v hvp hvq
      rcases (mem_liftInducedPath_vertexSet (P.path p)).1 hvp with
        ⟨hvU, hvp'⟩
      have hvq' :
          (⟨v, hvU⟩ : {x : V // x ∈ U}) ∈ (P.path q).vertexSet := by
        rcases (mem_liftInducedPath_vertexSet (P.path q)).1 hvq with
          ⟨_hvU', h⟩
        simpa using h
      exact Finset.disjoint_left.mp (P.node_disjoint hpq) hvp' hvq'
  }
  source_mem := by
    intro p
    exact
      (PathPacking.mem_subtypeFinset hA _).1 (P.source_mem p)
  target_mem := by
    intro p
    exact
      (PathPacking.mem_subtypeFinset hB _).1 (P.target_mem p)
  source_bijective := by
    constructor
    · intro p q hpq
      apply P.source_bijective.1
      apply Subtype.ext
      apply Subtype.ext
      simpa [liftInducedPath] using congrArg Subtype.val hpq
    · rintro ⟨v, hvA⟩
      let vU : {x : V // x ∈ U} := ⟨v, hA hvA⟩
      have hvSub :
          vU ∈ PathPacking.subtypeFinset A₀ U hA :=
        (PathPacking.mem_subtypeFinset hA vU).2 hvA
      rcases P.source_bijective.2 ⟨vU, hvSub⟩ with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z => z.1.1) hp
  target_bijective := by
    constructor
    · intro p q hpq
      apply P.target_bijective.1
      apply Subtype.ext
      apply Subtype.ext
      simpa [liftInducedPath] using congrArg Subtype.val hpq
    · rintro ⟨v, hvB⟩
      let vU : {x : V // x ∈ U} := ⟨v, hB hvB⟩
      have hvSub :
          vU ∈ PathPacking.subtypeFinset B₀ U hB :=
        (PathPacking.mem_subtypeFinset hB vU).2 hvB
      rcases P.target_bijective.2 ⟨vU, hvSub⟩ with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z => z.1.1) hp

@[simp] theorem liftInducedPerfect_path_vertexSet
    {K : _root_.SimpleGraph V} {U A₀ B₀ : Finset V}
    (hA : A₀ ⊆ U) (hB : B₀ ⊆ U)
    (P : PerfectPathPacking (K.induce {v : V | v ∈ U})
      (PathPacking.subtypeFinset A₀ U hA)
      (PathPacking.subtypeFinset B₀ U hB))
    (p : P.Index) :
    ((liftInducedPerfect hA hB P).path p).vertexSet =
      (liftInducedPath (P.path p)).vertexSet := rfl

namespace PathSlicing

/-- The left endpoints of the half-open row paths in one slice. -/
noncomputable def sliceLeftBoundary
    (sigma : PathSlicing R M) (i : Fin M) : Finset V :=
  Finset.univ.image fun r : R.Index => (sigma.sliceRowPath i r).source

/-- The right endpoints of the half-open row paths in one slice.

For a nontrivial closed segment this is the predecessor of the right cut,
because `sliceRowPath` removes that right cut. -/
noncomputable def sliceRightBoundary
    (sigma : PathSlicing R M) (i : Fin M) : Finset V :=
  Finset.univ.image fun r : R.Index => (sigma.sliceRowPath i r).target

/-- The sliced rows, now oriented as a perfect linkage between their actual
left and right endpoint sets. -/
noncomputable def sliceRowPerfectPacking
    (sigma : PathSlicing R M) (i : Fin M) :
    PerfectPathPacking G (sliceLeftBoundary sigma i)
      (sliceRightBoundary sigma i) where
  toPathPacking := {
    Index := R.Index
    path := sigma.sliceRowPath i
    connects := by
      intro r
      exact Or.inl
        ⟨Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩,
          Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩
    node_disjoint := by
      intro r s hrs
      exact (sigma.sliceRowPacking i).node_disjoint hrs
  }
  source_mem := by
    intro r
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  target_mem := by
    intro r
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  source_bijective := by
    constructor
    · intro r s hrs
      apply sigma.sliceRowPath_source_injective i
      exact congrArg Subtype.val hrs
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨r, _hr, rfl⟩
      exact ⟨r, rfl⟩
  target_bijective := by
    constructor
    · intro r s hrs
      apply sigma.sliceRowPath_target_injective i
      exact congrArg Subtype.val hrs
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨r, _hr, rfl⟩
      exact ⟨r, rfl⟩

@[simp] theorem sliceRowPerfectPacking_path
    (sigma : PathSlicing R M) (i : Fin M)
    (r : (sliceRowPerfectPacking sigma i).Index) :
    (sliceRowPerfectPacking sigma i).path r = sigma.sliceRowPath i r := rfl

@[simp] theorem sliceRowPerfectPacking_card
    (sigma : PathSlicing R M) (i : Fin M) :
    (sliceRowPerfectPacking sigma i).card = R.card := rfl

/-- The selected auxiliary subfamily used to form one exact slice support. -/
noncomputable def sliceAux
    (Q : PathPacking G S T) (Qset : Finset Q.Index) :
    PathPacking G S T :=
  Q.restrictIndexSet Qset

/-- The union graph of all sliced rows and the selected auxiliary paths. -/
noncomputable def sliceRawGraph
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    _root_.SimpleGraph V :=
  (sliceRowPerfectPacking sigma i).toPathPacking.spanningGraph ⊔
    (sliceAux Q Qset).spanningGraph

theorem sliceRawGraph_le
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    sliceRawGraph sigma Q i Qset ≤ G :=
  sup_le
    (sliceRowPerfectPacking sigma i).toPathPacking.spanningGraph_le
    (sliceAux Q Qset).spanningGraph_le

/-- Exactly the vertices used by the sliced rows or selected auxiliary paths. -/
noncomputable def sliceSupportVertexSetFor
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) : Finset V :=
  (sliceRowPerfectPacking sigma i).toPathPacking.vertexSet ∪
    (sliceAux Q Qset).vertexSet

/-- The ambient vertex type of an exact slice support. -/
abbrev SliceSupportVertex
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :=
  {v : V // v ∈ sliceSupportVertexSetFor sigma Q i Qset}

/-- The exact support graph on the subtype of vertices actually used in the
slice. -/
noncomputable def sliceSupportGraph
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    _root_.SimpleGraph (SliceSupportVertex sigma Q i Qset) :=
  (sliceRawGraph sigma Q i Qset).induce
    {v : V | v ∈ sliceSupportVertexSetFor sigma Q i Qset}

theorem sliceRows_stayIn_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    (sliceRowPerfectPacking sigma i).toPathPacking.StaysIn
      (sliceSupportVertexSetFor sigma Q i Qset) := by
  intro r v hv
  apply Finset.mem_union_left
  exact
    (sliceRowPerfectPacking sigma i).toPathPacking
      |>.path_vertexSet_subset_vertexSet r hv

theorem sliceLeftBoundary_subset_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    sliceLeftBoundary sigma i ⊆
      sliceSupportVertexSetFor sigma Q i Qset := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨r, _hr, rfl⟩
  apply Finset.mem_union_left
  exact
    (sliceRowPerfectPacking sigma i).toPathPacking
      |>.path_vertexSet_subset_vertexSet r
        (GraphPath.source_mem_vertexSet _)

theorem sliceRightBoundary_subset_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    sliceRightBoundary sigma i ⊆
      sliceSupportVertexSetFor sigma Q i Qset := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨r, _hr, rfl⟩
  apply Finset.mem_union_left
  exact
    (sliceRowPerfectPacking sigma i).toPathPacking
      |>.path_vertexSet_subset_vertexSet r
        (GraphPath.target_mem_vertexSet _)

/-- The sliced rows transferred to the raw union graph. -/
noncomputable def sliceRowsInRawGraph
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    PerfectPathPacking (sliceRawGraph sigma Q i Qset)
      (sliceLeftBoundary sigma i) (sliceRightBoundary sigma i) :=
  (sliceRowPerfectPacking sigma i).inSpanningGraph.mapLe le_sup_left

/-- Viewing the sliced rows in the union graph does not change their vertices. -/
theorem sliceRowsInRawGraph_stayIn_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    (sliceRowsInRawGraph sigma Q i Qset).toPathPacking.StaysIn
      (sliceSupportVertexSetFor sigma Q i Qset) := by
  intro r
  simpa [sliceRowsInRawGraph, PerfectPathPacking.mapLe,
    PathPacking.mapLe] using
    sliceRows_stayIn_support sigma Q i Qset r

/-- The perfect sliced-row linkage in the exact support subtype. -/
noncomputable def sliceRowsInSupport
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset)) :=
  (sliceRowsInRawGraph sigma Q i Qset).induce
    (sliceSupportVertexSetFor sigma Q i Qset)
    (sliceRowsInRawGraph_stayIn_support sigma Q i Qset)
    (sliceLeftBoundary_subset_support sigma Q i Qset)
    (sliceRightBoundary_subset_support sigma Q i Qset)

/-- A localized auxiliary-row intersection lies in the actual half-open sliced
row path. -/
theorem mem_sliceRowPath_of_mem_pathsInSlice
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    {i : Fin M} {q : Q.Index} (hq : q ∈ sigma.pathsInSlice Q i)
    {r : R.Index} {v : V}
    (hvQ : v ∈ (Q.path q).vertexSet)
    (hvR : v ∈ (R.path r).vertexSet) :
    v ∈ (sigma.sliceRowPath i r).vertexSet := by
  exact sigma.mem_sliceRowPath_of_sliceInterior i r
    ((sigma.mem_pathsInSlice Q i q).1 hq hvQ hvR)

/-- Observation 5.4, spanning part: on the exact support subtype, every vertex
lies on one of the canonical sliced rows. -/
theorem sliceSupport_spansVertices
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i) :
    (sliceRowsInSupport sigma Q i Qset).SpansVertices := by
  classical
  intro z
  apply
    (sliceRowsInSupport sigma Q i Qset).toPathPacking.mem_vertexSet.2
  rcases Finset.mem_union.mp z.2 with hzRow | hzAux
  · rcases
        (sliceRowPerfectPacking sigma i).toPathPacking.mem_vertexSet.1 hzRow with
      ⟨r, hzr⟩
    refine ⟨r, ?_⟩
    exact
      (GraphPath.mem_induce_vertexSet
        ((sliceRowsInRawGraph sigma Q i Qset).path r)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRowsInRawGraph_stayIn_support sigma Q i Qset r) z).2 (by
          simpa [sliceRowsInRawGraph, PerfectPathPacking.mapLe,
            PathPacking.mapLe] using hzr)
  · rcases (sliceAux Q Qset).mem_vertexSet.1 hzAux with ⟨q, hzq⟩
    rcases R.toPathPacking.mem_vertexSet.1 (hspan z.1) with ⟨r, hzr⟩
    have hzSlice :
        z.1 ∈ (sigma.sliceRowPath i r).vertexSet :=
      mem_sliceRowPath_of_mem_pathsInSlice sigma Q
        (hQset q.2) (by simpa [sliceAux] using hzq) hzr
    refine ⟨r, ?_⟩
    exact
      (GraphPath.mem_induce_vertexSet
        ((sliceRowsInRawGraph sigma Q i Qset).path r)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRowsInRawGraph_stayIn_support sigma Q i Qset r) z).2 (by
          simpa [sliceRowsInRawGraph, PerfectPathPacking.mapLe,
            PathPacking.mapLe] using hzSlice)

end PathSlicing
end Exponent8
end SimpleGraph

end Lax17Proofs
