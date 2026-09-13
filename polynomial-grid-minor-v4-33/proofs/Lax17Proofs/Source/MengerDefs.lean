import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Definitions for finite vertex-Menger

This file contains only the proof-facing language for finite vertex-Menger:
`(S,T)`-separators and finite families of pairwise vertex-disjoint `S`-to-`T`
paths.  The theorem itself is stated in `MengerContract.lean` and proved in
`Menger.lean`.
-/

namespace SimpleGraph


/-- An oriented endpoint-clean `S`-to-`T` path starts in `S`, ends in `T`,
has no vertex of `S` except its source, and has no vertex of `T` except its
target.

This is the convention used in the self-contained finite Menger proof.  It
handles non-disjoint terminal sets: if a nontrivial path starts in `S ∩ T`,
the right-clean condition forces the first right terminal to be the same
vertex, so the cleaned subpath is trivial. -/
structure GraphPath.EndpointClean {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} (P : GraphPath G) (S T : Finset V) : Prop where
  source_mem : P.source ∈ S
  target_mem : P.target ∈ T
  left_eq_source :
    ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ S → v = P.source
  right_eq_target :
    ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ T → v = P.target

namespace GraphPath

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T X : Finset V} {P : GraphPath G}

theorem EndpointClean.connects (hP : P.EndpointClean S T) :
    P.Connects S T :=
  Or.inl ⟨hP.source_mem, hP.target_mem⟩

theorem EndpointClean.vertexSet_inter_left_subset_singleton
    (hP : P.EndpointClean S T) :
    P.vertexSet ∩ S ⊆ {P.source} := by
  intro v hv
  exact Finset.mem_singleton.2 (hP.left_eq_source
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)

theorem EndpointClean.vertexSet_inter_right_subset_singleton
    (hP : P.EndpointClean S T) :
    P.vertexSet ∩ T ⊆ {P.target} := by
  intro v hv
  exact Finset.mem_singleton.2 (hP.right_eq_target
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)

theorem EndpointClean.vertexSet_inter_right_eq_singleton
    (hP : P.EndpointClean S T) :
    P.vertexSet ∩ T = {P.target} := by
  apply Finset.Subset.antisymm hP.vertexSet_inter_right_subset_singleton
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  exact Finset.mem_inter.2 ⟨GraphPath.target_mem_vertexSet P, hP.target_mem⟩

theorem EndpointClean.internallyDisjointFromRight
    (hP : P.EndpointClean S T) :
    P.InternallyDisjointFromSet T := by
  intro v hv hvT
  exact Or.inr (hP.right_eq_target hv hvT)

theorem EndpointClean.internallyDisjointFromLeft
    (hP : P.EndpointClean S T) :
    P.InternallyDisjointFromSet S := by
  intro v hv hvS
  exact Or.inl (hP.left_eq_source hv hvS)

theorem EndpointClean.right_mem_eq_target
    (hP : P.EndpointClean S T) {v : V}
    (hv : v ∈ P.vertexSet) (hvT : v ∈ T) :
    v = P.target :=
  hP.right_eq_target hv hvT

theorem EndpointClean.left_mem_eq_source
    (hP : P.EndpointClean S T) {v : V}
    (hv : v ∈ P.vertexSet) (hvS : v ∈ S) :
    v = P.source :=
  hP.left_eq_source hv hvS

theorem EndpointClean.source_eq_target_of_source_mem_right
    (hP : P.EndpointClean S T) (hsource : P.source ∈ T) :
    P.source = P.target :=
  hP.right_eq_target (GraphPath.source_mem_vertexSet P) hsource

theorem EndpointClean.source_only_at_target_on_right_subset
    (hP : P.EndpointClean S T) {Q : GraphPath G}
    (hQ : Q.vertexSet ⊆ T) :
    P.source ∈ Q.vertexSet → P.source = P.target := by
  intro hsourceQ
  exact hP.source_eq_target_of_source_mem_right (hQ hsourceQ)

noncomputable def appendWithEqOfEndpointCleanRightSubset
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    GraphPath G :=
  P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
    Q h hP.internallyDisjointFromRight hQ
    (hP.source_only_at_target_on_right_subset hQ)

@[simp] theorem appendWithEqOfEndpointCleanRightSubset_source
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQ h).source = P.source := by
  simp [appendWithEqOfEndpointCleanRightSubset]

@[simp] theorem appendWithEqOfEndpointCleanRightSubset_target
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQ h).target = Q.target := by
  simp [appendWithEqOfEndpointCleanRightSubset]

theorem appendWithEqOfEndpointCleanRightSubset_vertexSet_subset
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQ h).vertexSet ⊆
      P.vertexSet ∪ Q.vertexSet :=
by
  exact GraphPath.appendWithEq_vertexSet_subset P Q h _

theorem appendWithEqOfEndpointCleanRightSubset_endpointClean
    {U : Finset V} (P Q : GraphPath G) (hP : P.EndpointClean S U)
    (hTU : T ⊆ U) (hQsub : Q.vertexSet ⊆ U)
    (hQtarget : Q.target ∈ T)
    (hQleft : ∀ ⦃v : V⦄, v ∈ Q.vertexSet → v ∈ S → v = P.target)
    (hQright : ∀ ⦃v : V⦄, v ∈ Q.vertexSet → v ∈ T → v = Q.target)
    (hPtarget : P.target ∈ T → P.target = Q.target)
    (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQsub h).EndpointClean S T := by
  classical
  let A := P.appendWithEqOfEndpointCleanRightSubset Q hP hQsub h
  have hsub :
      A.vertexSet ⊆ P.vertexSet ∪ Q.vertexSet :=
    P.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset Q hP hQsub h
  refine
    { source_mem := ?_
      target_mem := ?_
      left_eq_source := ?_
      right_eq_target := ?_ }
  · simpa [A] using hP.source_mem
  · simpa [A] using hQtarget
  · intro v hv hvS
    rcases Finset.mem_union.1 (hsub hv) with hvP | hvQ
    · simpa [A] using hP.left_eq_source hvP hvS
    · have hv_target : v = P.target := hQleft hvQ hvS
      have htarget_source : P.target = P.source := by
        exact (hP.left_eq_source (GraphPath.target_mem_vertexSet P)
          (by simpa [hv_target] using hvS))
      simpa [A] using hv_target.trans htarget_source
  · intro v hv hvT
    rcases Finset.mem_union.1 (hsub hv) with hvP | hvQ
    · have hv_target : v = P.target := hP.right_eq_target hvP (hTU hvT)
      simpa [A] using hv_target.trans (hPtarget (by simpa [hv_target] using hvT))
    · simpa [A] using hQright hvQ hvT

theorem nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
    {U : Finset V} (P Q W : GraphPath G)
    (hPclean : P.EndpointClean S U) (hWclean : W.EndpointClean S U)
    (hQsub : Q.vertexSet ⊆ U) (h : P.target = Q.source)
    (hPW : P.NodeDisjoint W)
    (hWtarget : W.target ∉ Q.vertexSet) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hPclean hQsub h).NodeDisjoint W := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvA hvW
  have hvA' :=
    P.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset Q hPclean hQsub h hvA
  rcases Finset.mem_union.1 hvA' with hvP | hvQ
  · exact Finset.disjoint_left.mp hPW hvP hvW
  · have hvU : v ∈ U := hQsub hvQ
    have hv_target : v = W.target := hWclean.right_eq_target hvW hvU
    exact hWtarget (by simpa [hv_target] using hvQ)

theorem nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_right
    {U : Finset V} (P Q W : GraphPath G)
    (hPclean : P.EndpointClean S U) (hWclean : W.EndpointClean S U)
    (hQsub : Q.vertexSet ⊆ U) (h : P.target = Q.source)
    (hWP : W.NodeDisjoint P)
    (hWtarget : W.target ∉ Q.vertexSet) :
    W.NodeDisjoint
      (P.appendWithEqOfEndpointCleanRightSubset Q hPclean hQsub h) :=
  (nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
    P Q W hPclean hWclean hQsub h hWP.symm hWtarget).symm

theorem nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_append
    {U : Finset V} (P Q R W : GraphPath G)
    (hPclean : P.EndpointClean S U) (hRclean : R.EndpointClean S U)
    (hQsub : Q.vertexSet ⊆ U) (hWsub : W.vertexSet ⊆ U)
    (hPQ : P.target = Q.source) (hRW : R.target = W.source)
    (hPR : P.NodeDisjoint R)
    (hRtargetQ : R.target ∉ Q.vertexSet)
    (hPtargetW : P.target ∉ W.vertexSet)
    (hQW : Disjoint Q.vertexSet W.vertexSet) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hPclean hQsub hPQ).NodeDisjoint
      (R.appendWithEqOfEndpointCleanRightSubset W hRclean hWsub hRW) := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvA hvB
  have hvA' :=
    P.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset Q hPclean hQsub hPQ hvA
  have hvB' :=
    R.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset W hRclean hWsub hRW hvB
  rcases Finset.mem_union.1 hvA' with hvP | hvQ
  · rcases Finset.mem_union.1 hvB' with hvR | hvW
    · exact Finset.disjoint_left.mp hPR hvP hvR
    · have hvU : v ∈ U := hWsub hvW
      have hv_target : v = P.target := hPclean.right_eq_target hvP hvU
      exact hPtargetW (by simpa [hv_target] using hvW)
  · rcases Finset.mem_union.1 hvB' with hvR | hvW
    · have hvU : v ∈ U := hQsub hvQ
      have hv_target : v = R.target := hRclean.right_eq_target hvR hvU
      exact hRtargetQ (by simpa [hv_target] using hvQ)
    · exact Finset.disjoint_left.mp hQW hvQ hvW

/-- The standard terminal-cleaning operation produces an oriented
endpoint-clean path. -/
theorem cleanBetweenTerminalSets_endpointClean
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).EndpointClean S T := by
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
  refine
    { source_mem := ?_
      target_mem := ?_
      left_eq_source := ?_
      right_eq_target := ?_ }
  · simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using
      R.cleanSuffixFromSet_source_mem S hS
  · simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using
      O.cleanPrefixToSet_target_mem T hT
  · intro v hv hvS
    have hvSuffix :
        v ∈ (R.cleanSuffixFromSet S hS).vertexSet := by
      simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using hv
    have hvlast :
        v = R.lastHitVertex S hS :=
      R.eq_lastHitVertex_of_mem_dropUntil_of_mem_set S hS
        (by simpa [GraphPath.cleanSuffixFromSet] using hvSuffix) hvS
    simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using hvlast
  · intro v hv hvT
    have hvSuffix :
        v ∈ (R.cleanSuffixFromSet S hS).vertexSet := by
      simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using hv
    have hvR : v ∈ R.vertexSet :=
      R.cleanSuffixFromSet_vertexSet_subset S hS hvSuffix
    have hvfirst :
        v = O.firstHitVertex T hT :=
      O.eq_firstHitVertex_of_mem_takeUntil_of_mem_set T hT
        (by simpa [R, GraphPath.cleanPrefixToSet] using hvR) hvT
    simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using hvfirst

/-- The prefix and suffix of a simple path at the same cut vertex meet only at
that cut vertex. -/
theorem eq_of_mem_takeUntil_and_mem_dropUntil
    (P : GraphPath G) {x v : V} (hx : x ∈ P.vertexSet)
    (hvPrefix : v ∈ (P.takeUntil hx).vertexSet)
    (hvSuffix : v ∈ (P.dropUntil hx).vertexSet) :
    v = x := by
  have hvBeforeX : P.Before v x :=
    P.before_of_mem_takeUntil hx hvPrefix
  have hxBeforeV : P.Before x v :=
    ⟨hx, hvSuffix⟩
  exact P.before_antisymm hvBeforeX hxBeforeV

/-- If the cut vertex is not the original target, the prefix ending at that
vertex is a proper subpath on vertices. -/
theorem takeUntil_vertexSet_ssubset_of_ne_target
    (P : GraphPath G) {x : V} (hx : x ∈ P.vertexSet)
    (hne : x ≠ P.target) :
    (P.takeUntil hx).vertexSet ⊂ P.vertexSet := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · exact P.takeUntil_vertexSet_subset hx
  · intro heq
    have htargetPrefix :
        P.target ∈ (P.takeUntil hx).vertexSet := by
      rw [heq]
      exact GraphPath.target_mem_vertexSet P
    have htargetSuffix :
        P.target ∈ (P.dropUntil hx).vertexSet :=
      GraphPath.target_mem_vertexSet (P.dropUntil hx)
    exact hne ((P.eq_of_mem_takeUntil_and_mem_dropUntil hx
      htargetPrefix htargetSuffix).symm)

/-- On the suffix starting at the last vertex of a set, any later vertex that
still lies in the set is the suffix source. -/
theorem eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvSuffix :
      v ∈ (P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)).vertexSet)
    (hvU : v ∈ U) :
    v = (P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)).source := by
  dsimp
  exact P.eq_lastHitVertex_of_mem_dropUntil_of_mem_set U hne hvSuffix hvU

theorem EndpointClean.dropUntil_left_eq_source
    (hP : P.EndpointClean S T) {x v : V} (hx : x ∈ P.vertexSet)
    (hv : v ∈ (P.dropUntil hx).vertexSet) (hvS : v ∈ S) :
    v = (P.dropUntil hx).source := by
  have hvOld : v ∈ P.vertexSet := P.dropUntil_vertexSet_subset hx hv
  have hv_source : v = P.source := hP.left_eq_source hvOld hvS
  have hsource_suffix : P.source ∈ (P.dropUntil hx).vertexSet := by
    simpa [hv_source] using hv
  have hsource_x :
      P.source = x :=
    P.eq_of_mem_takeUntil_and_mem_dropUntil hx
      (by
        simpa using GraphPath.source_mem_vertexSet (P.takeUntil hx))
      hsource_suffix
  simpa using hv_source.trans hsource_x

theorem EndpointClean.dropUntil_right_eq_target
    (hP : P.EndpointClean S T) {x v : V} (hx : x ∈ P.vertexSet)
    (hv : v ∈ (P.dropUntil hx).vertexSet) (hvT : v ∈ T) :
    v = (P.dropUntil hx).target := by
  have hvOld : v ∈ P.vertexSet := P.dropUntil_vertexSet_subset hx hv
  simpa using hP.right_eq_target hvOld hvT

end GraphPath

/-- A finite indexed family of pairwise vertex-disjoint oriented endpoint-clean
`S`-to-`T` paths.  This is the proof-facing path-system object for Diestel's
augmentation proof of finite Menger.

The public theorem still uses `PathPacking`; an endpoint-clean system converts
to a `PathPacking` by forgetting the orientation-cleaning data. -/
structure EndpointCleanPathPacking {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  path : Index → GraphPath G
  endpoint_clean : ∀ i, (path i).EndpointClean S T
  node_disjoint : Pairwise fun i j => GraphPath.NodeDisjoint (path i) (path j)

namespace EndpointCleanPathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

instance (P : EndpointCleanPathPacking G S T) : Fintype P.Index :=
  P.indexFintype

instance (P : EndpointCleanPathPacking G S T) : DecidableEq P.Index :=
  P.indexDecidableEq

/-- The number of paths in an endpoint-clean path system. -/
noncomputable def card (P : EndpointCleanPathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- The union of the vertices used by all paths in the system. -/
noncomputable def vertexSet (P : EndpointCleanPathPacking G S T) : Finset V :=
  Finset.univ.biUnion fun i : P.Index => (P.path i).vertexSet

theorem mem_vertexSet (P : EndpointCleanPathPacking G S T) {v : V} :
    v ∈ P.vertexSet ↔ ∃ i : P.Index, v ∈ (P.path i).vertexSet := by
  classical
  simp [vertexSet]

theorem path_vertexSet_subset_vertexSet
    (P : EndpointCleanPathPacking G S T) (i : P.Index) :
    (P.path i).vertexSet ⊆ P.vertexSet := by
  classical
  intro v hv
  exact (P.mem_vertexSet).2 ⟨i, hv⟩

theorem exists_index_of_mem_vertexSet
    (P : EndpointCleanPathPacking G S T) {v : V}
    (hv : v ∈ P.vertexSet) :
    ∃ i : P.Index, v ∈ (P.path i).vertexSet :=
  (P.mem_vertexSet).1 hv

/-- The empty endpoint-clean path system. -/
def empty (G : _root_.SimpleGraph V) (S T : Finset V) :
    EndpointCleanPathPacking G S T where
  Index := Empty
  path := fun i => nomatch i
  endpoint_clean := by
    intro i
    cases i
  node_disjoint := by
    intro i
    cases i

@[simp] theorem empty_card :
    (empty G S T).card = 0 := by
  simp [empty, card]

/-- Adjoin one endpoint-clean path that is vertex-disjoint from the old
system. -/
noncomputable def cons (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    EndpointCleanPathPacking G S T where
  Index := Option P.Index
  path := fun i =>
    match i with
    | none => R
    | some j => P.path j
  endpoint_clean := by
    intro i
    cases i with
    | none => exact hR
    | some j => exact P.endpoint_clean j
  node_disjoint := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact False.elim (hij rfl)
        | some j =>
            rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
            intro v hvR hvj
            exact Finset.disjoint_left.mp hdisj hvR
              (P.path_vertexSet_subset_vertexSet j hvj)
    | some i =>
        cases j with
        | none =>
            rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
            intro v hvi hvR
            exact Finset.disjoint_left.mp hdisj hvR
              (P.path_vertexSet_subset_vertexSet i hvi)
        | some j =>
            exact P.node_disjoint (by
              intro hij'
              apply hij
              simp [hij'])

@[simp] theorem cons_card (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    (P.cons R hR hdisj).card = P.card + 1 := by
  change Fintype.card (Option P.Index) = Fintype.card P.Index + 1
  exact Fintype.card_option

/-- Rebuild a path system on the same index type from a new path assignment.
This is a small constructor used by splicing arguments. -/
noncomputable def withSameIndex {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j)) :
    EndpointCleanPathPacking G S T' where
  Index := P.Index
  path := f
  endpoint_clean := hclean
  node_disjoint := hnode

@[simp] theorem withSameIndex_card {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j)) :
    (P.withSameIndex f hclean hnode).card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

/-!
The next constructor is the formal splice used in Diestel's Menger proof.
It starts with a path system whose paths are endpoint-clean for a larger
right-terminal set `U`.  Two selected paths have right endpoints in `U \ T`;
we append tails contained in `U` that end in the smaller terminal set `T`.
All other paths are required to already end in `T` and to have endpoints
outside the appended tails.  Endpoint-cleanliness relative to `U` then gives
the disjointness of the spliced family.
-/

noncomputable def spliceTwo {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    EndpointCleanPathPacking G S T := by
  classical
  let A₀ : GraphPath G :=
    (P.path i₀).appendWithEqOfEndpointCleanRightSubset
      tail₀ (P.endpoint_clean i₀) htail₀U hjoin₀
  let A₁ : GraphPath G :=
    (P.path i₁).appendWithEqOfEndpointCleanRightSubset
      tail₁ (P.endpoint_clean i₁) htail₁U hjoin₁
  let f : P.Index → GraphPath G := fun i =>
    if hi₀ : i = i₀ then A₀ else if hi₁ : i = i₁ then A₁ else P.path i
  refine P.withSameIndex f ?_ ?_
  · intro i
    by_cases hi₀ : i = i₀
    · subst i
      simpa [f, A₀] using
        GraphPath.appendWithEqOfEndpointCleanRightSubset_endpointClean
          (P.path i₀) tail₀ (P.endpoint_clean i₀) hTU htail₀U htail₀T
          htail₀Left htail₀Right hjoin₀Target hjoin₀
    · by_cases hi₁ : i = i₁
      · subst i
        simpa [f, hi₀, A₁] using
          GraphPath.appendWithEqOfEndpointCleanRightSubset_endpointClean
            (P.path i₁) tail₁ (P.endpoint_clean i₁) hTU htail₁U htail₁T
            htail₁Left htail₁Right hjoin₁Target hjoin₁
      · refine
          { source_mem := ?_
            target_mem := ?_
            left_eq_source := ?_
            right_eq_target := ?_ }
        · have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using (P.endpoint_clean i).source_mem
        · have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using hotherTargetT i hi₀ hi₁
        · intro v hv hvS
          have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using
            (P.endpoint_clean i).left_eq_source (by simpa [hf] using hv) hvS
        · intro v hv hvT
          have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using
            (P.endpoint_clean i).right_eq_target (by simpa [hf] using hv) (hTU hvT)
  · intro i j hij
    by_cases hi₀ : i = i₀
    · subst i
      by_cases hj₀ : j = i₀
      · exact False.elim (hij hj₀.symm)
      · by_cases hj₁ : j = i₁
        · subst j
          simpa [f, A₀, A₁, hj₀, hidx.symm] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_append
              (P.path i₀) tail₀ (P.path i₁) tail₁
              (P.endpoint_clean i₀) (P.endpoint_clean i₁)
              htail₀U htail₁U hjoin₀ hjoin₁
              (P.node_disjoint hidx) hi₁TargetNotTail₀
              hi₀TargetNotTail₁ htails
        · simpa [f, A₀, hj₀, hj₁] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
              (P.path i₀) tail₀ (P.path j)
              (P.endpoint_clean i₀) (P.endpoint_clean j)
              htail₀U hjoin₀
              (P.node_disjoint (by
                intro h
                exact hj₀ h.symm))
              (hotherTargetNotTail₀ j hj₀ hj₁)
    · by_cases hi₁ : i = i₁
      · subst i
        by_cases hj₀ : j = i₀
        · subst j
          simpa [f, A₀, A₁, hi₀, hidx] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_append
              (P.path i₁) tail₁ (P.path i₀) tail₀
              (P.endpoint_clean i₁) (P.endpoint_clean i₀)
              htail₁U htail₀U hjoin₁ hjoin₀
              (P.node_disjoint hidx.symm) hi₀TargetNotTail₁
              hi₁TargetNotTail₀ htails.symm
        · by_cases hj₁ : j = i₁
          · exact False.elim (hij hj₁.symm)
          · simpa [f, A₁, hi₀, hj₀, hj₁] using
              GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
                (P.path i₁) tail₁ (P.path j)
                (P.endpoint_clean i₁) (P.endpoint_clean j)
                htail₁U hjoin₁
                (P.node_disjoint (by
                  intro h
                  exact hj₁ h.symm))
                (hotherTargetNotTail₁ j hj₀ hj₁)
      · by_cases hj₀ : j = i₀
        · subst j
          simpa [f, A₀, hi₀, hi₁] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_right
              (P.path i₀) tail₀ (P.path i)
              (P.endpoint_clean i₀) (P.endpoint_clean i)
              htail₀U hjoin₀
              (P.node_disjoint (by
                intro h
                exact hi₀ h))
              (hotherTargetNotTail₀ i hi₀ hi₁)
        · by_cases hj₁ : j = i₁
          · subst j
            simpa [f, A₁, hi₀, hi₁, hidx.symm] using
              GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_right
                (P.path i₁) tail₁ (P.path i)
                (P.endpoint_clean i₁) (P.endpoint_clean i)
                htail₁U hjoin₁
                (P.node_disjoint (by
                  intro h
                  exact hi₁ h))
                (hotherTargetNotTail₁ i hi₀ hi₁)
          · simpa [f, hi₀, hi₁, hj₀, hj₁] using P.node_disjoint hij

@[simp] theorem spliceTwo_card {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    (P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

theorem spliceTwo_target_left {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    ((P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).path i₀).target = tail₀.target := by
  classical
  simp [spliceTwo, withSameIndex]

theorem spliceTwo_target_right {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    ((P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).path i₁).target = tail₁.target := by
  classical
  simp [spliceTwo, withSameIndex, hidx.symm]

theorem spliceTwo_target_other {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ j : P.Index) (hidx : i₀ ≠ i₁)
    (hj₀ : j ≠ i₀) (hj₁ : j ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    ((P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).path j).target = (P.path j).target := by
  classical
  simp [spliceTwo, withSameIndex, hj₀, hj₁]

/-- Replace one path by a new endpoint-clean path contained in the old path,
possibly after changing the right terminal set.  The endpoint-clean hypotheses
for the unchanged paths are explicit because Diestel's proof enlarges the
target set in a way that must be verified geometrically. -/
noncomputable def replacePath {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    EndpointCleanPathPacking G S T' where
  Index := P.Index
  path := fun i => if i = i₀ then Q else P.path i
  endpoint_clean := by
    intro i
    by_cases hi : i = i₀
    · simpa [hi]
    · simpa [hi] using hold i hi
  node_disjoint := by
    intro i j hij
    by_cases hi : i = i₀
    · by_cases hj : j = i₀
      · exact False.elim (hij (hi.trans hj.symm))
      · rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro v hvQ hvj
        exact Finset.disjoint_left.mp
          (P.node_disjoint (by
            intro h
            exact hj h.symm))
          (hsub (by simpa [hi] using hvQ))
          (by simpa [hj] using hvj)
    · by_cases hj : j = i₀
      · rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro v hvi hvQ
        exact Finset.disjoint_left.mp
          (P.node_disjoint (by
            intro h
            exact hi h))
          (by simpa [hi] using hvi)
          (hsub (by simpa [hj] using hvQ))
      · simpa [hi, hj] using P.node_disjoint hij

@[simp] theorem replacePath_card {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    (P.replacePath i₀ Q hQ hold hsub).card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

theorem replacePath_vertexSet_subset {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    (P.replacePath i₀ Q hQ hold hsub).vertexSet ⊆ P.vertexSet := by
  classical
  intro v hv
  rcases ((P.replacePath i₀ Q hQ hold hsub).mem_vertexSet).1 hv with
    ⟨i, hvi⟩
  by_cases hi : i = i₀
  · have hviQ : v ∈ Q.vertexSet := by
      change v ∈ (if i = i₀ then Q else P.path i).vertexSet at hvi
      simpa [hi] using hvi
    exact (P.mem_vertexSet).2 ⟨i₀, hsub hviQ⟩
  · have hviOld : v ∈ (P.path i).vertexSet := by
      change v ∈ (if i = i₀ then Q else P.path i).vertexSet at hvi
      simpa [hi] using hvi
    exact (P.mem_vertexSet).2 ⟨i, hviOld⟩

theorem replacePath_vertexSet_ssubset {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet)
    (hproper : Q.vertexSet ⊂ (P.path i₀).vertexSet) :
    (P.replacePath i₀ Q hQ hold hsub).vertexSet ⊂ P.vertexSet := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · exact P.replacePath_vertexSet_subset i₀ Q hQ hold hsub
  · intro heq
    have hnotSubset : ¬ (P.path i₀).vertexSet ⊆ Q.vertexSet := by
      intro hrev
      exact (Finset.ssubset_iff_subset_ne.mp hproper).2
        (Finset.Subset.antisymm hsub hrev)
    rw [Finset.not_subset] at hnotSubset
    rcases hnotSubset with ⟨y, hyOld, hyQ⟩
    have hyP : y ∈ P.vertexSet := (P.mem_vertexSet).2 ⟨i₀, hyOld⟩
    have hyNew :
        y ∈ (P.replacePath i₀ Q hQ hold hsub).vertexSet := by
      rw [heq]
      exact hyP
    rcases ((P.replacePath i₀ Q hQ hold hsub).mem_vertexSet).1 hyNew with
      ⟨j, hyj⟩
    by_cases hj : j = i₀
    · have hyQ' : y ∈ Q.vertexSet := by
        change y ∈ (if j = i₀ then Q else P.path j).vertexSet at hyj
        simpa [hj] using hyj
      exact hyQ hyQ'
    · have hyOldj : y ∈ (P.path j).vertexSet := by
        change y ∈ (if j = i₀ then Q else P.path j).vertexSet at hyj
        simpa [hj] using hyj
      exact Finset.disjoint_left.mp
        (P.node_disjoint (by
          intro h
          exact hj h.symm))
        hyOld hyOldj

/-- The set of left endpoints used by an endpoint-clean path system. -/
noncomputable def sourceSet (P : EndpointCleanPathPacking G S T) : Finset V :=
  Finset.univ.image fun i : P.Index => (P.path i).source

/-- The set of right endpoints used by an endpoint-clean path system. -/
noncomputable def targetSet (P : EndpointCleanPathPacking G S T) : Finset V :=
  Finset.univ.image fun i : P.Index => (P.path i).target

@[simp] theorem withSameIndex_sourceSet_eq {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j))
    (hsource : ∀ i, (f i).source = (P.path i).source) :
    (P.withSameIndex f hclean hnode).sourceSet = P.sourceSet := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    exact Finset.mem_image.2
      ⟨i, by simp, by simpa [sourceSet, withSameIndex, hsource i] using hiv⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    exact Finset.mem_image.2
      ⟨i, by simp, by simpa [sourceSet, withSameIndex, hsource i] using hiv⟩

theorem mem_targetSet_withSameIndex_iff {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j))
    {v : V} :
    v ∈ (P.withSameIndex f hclean hnode).targetSet ↔
      ∃ i : P.Index, v = (f i).target := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    exact ⟨i, hiv.symm⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.2 ⟨i, by simp, rfl⟩

@[simp] theorem withSameIndex_targetSet_eq {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j))
    (htarget : ∀ i, (f i).target = (P.path i).target) :
    (P.withSameIndex f hclean hnode).targetSet = P.targetSet := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    exact Finset.mem_image.2
      ⟨i, by simp, by simpa [targetSet, withSameIndex, htarget i] using hiv⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    exact Finset.mem_image.2
      ⟨i, by simp, by simpa [targetSet, withSameIndex, htarget i] using hiv⟩

theorem target_mem_targetSet_withSameIndex {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j))
    (i : P.Index) :
    (f i).target ∈ (P.withSameIndex f hclean hnode).targetSet := by
  classical
  exact Finset.mem_image.2 ⟨i, by simp, rfl⟩

theorem spliceTwo_sourceSet_eq {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    (P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).sourceSet = P.sourceSet := by
  classical
  unfold spliceTwo
  apply withSameIndex_sourceSet_eq
  intro i
  by_cases hi₀ : i = i₀
  · subst i
    simp
  · by_cases hi₁ : i = i₁
    · subst i
      simp [hidx.symm]
    · simp [hi₀, hi₁]

theorem mem_targetSet_spliceTwo_iff {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) {v : V} :
    v ∈ (P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).targetSet ↔
      v = tail₀.target ∨ v = tail₁.target ∨
        ∃ j : P.Index, j ≠ i₀ ∧ j ≠ i₁ ∧ v = (P.path j).target := by
  classical
  unfold spliceTwo
  rw [mem_targetSet_withSameIndex_iff]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hj₀ : j = i₀
    · subst j
      exact Or.inl (by simpa [withSameIndex] using hj)
    · by_cases hj₁ : j = i₁
      · subst j
        exact Or.inr (Or.inl (by simpa [withSameIndex, hidx.symm] using hj))
      · exact Or.inr (Or.inr ⟨j, hj₀, hj₁, by
          simpa [withSameIndex, hj₀, hj₁] using hj⟩)
  · intro hv
    rcases hv with rfl | rfl | ⟨j, hj₀, hj₁, rfl⟩
    · exact ⟨i₀, by simp⟩
    · exact ⟨i₁, by simp [hidx.symm]⟩
    · exact ⟨j, by simp [hj₀, hj₁]⟩

@[simp] theorem replacePath_sourceSet_eq_of_source_eq {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet)
    (hsource : Q.source = (P.path i₀).source) :
    (P.replacePath i₀ Q hQ hold hsub).sourceSet = P.sourceSet := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    by_cases hi : i = i₀
    · subst i
      have holdv : (P.path i₀).source = v := hsource.symm.trans (by
        simpa [replacePath] using hiv)
      exact Finset.mem_image.2
        ⟨i₀, by simp, holdv⟩
    · have hivOld : (P.path i).source = v := by
        change (if i = i₀ then Q else P.path i).source = v at hiv
        simpa [hi] using hiv
      exact Finset.mem_image.2 ⟨i, by simp, hivOld⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    by_cases hi : i = i₀
    · subst i
      have hqv : Q.source = v := hsource.trans hiv
      exact Finset.mem_image.2
        ⟨i₀, by simp, by simpa [replacePath] using hqv⟩
    · have hivNew : (if i = i₀ then Q else P.path i).source = v := by
        simpa [hi] using hiv
      exact Finset.mem_image.2 ⟨i, by simp, hivNew⟩

theorem mem_targetSet_replacePath_iff {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) {v : V} :
    v ∈ (P.replacePath i₀ Q hQ hold hsub).targetSet ↔
      v = Q.target ∨ ∃ i : P.Index, i ≠ i₀ ∧ v = (P.path i).target := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    by_cases hi : i = i₀
    · subst i
      exact Or.inl (by simpa [replacePath] using hiv.symm)
    · have hivOld : (P.path i).target = v := by
        change (if i = i₀ then Q else P.path i).target = v at hiv
        simpa [hi] using hiv
      exact Or.inr ⟨i, hi, hivOld.symm⟩
  · intro hv
    rcases hv with rfl | ⟨i, hi, rfl⟩
    · exact Finset.mem_image.2
        ⟨i₀, by simp, by simp [replacePath]⟩
    · exact Finset.mem_image.2
        ⟨i, by simp, by simp [replacePath, hi]⟩

theorem target_mem_right_of_mem_replacePath_targetSet_ne {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) {v : V}
    (hv : v ∈ (P.replacePath i₀ Q hQ hold hsub).targetSet)
    (hne : v ≠ Q.target) :
    v ∈ T := by
  classical
  rw [P.mem_targetSet_replacePath_iff i₀ Q hQ hold hsub] at hv
  rcases hv with hv | ⟨j, _hj, hvj⟩
  · exact False.elim (hne hv)
  · rw [hvj]
    exact (P.endpoint_clean j).target_mem

theorem replacePath_new_target_mem_targetSet {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    Q.target ∈ (P.replacePath i₀ Q hQ hold hsub).targetSet := by
  classical
  rw [P.mem_targetSet_replacePath_iff i₀ Q hQ hold hsub]
  exact Or.inl rfl

theorem replacePath_old_target_mem_targetSet {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ j : P.Index)
    (hj : j ≠ i₀)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    (P.path j).target ∈ (P.replacePath i₀ Q hQ hold hsub).targetSet := by
  classical
  rw [P.mem_targetSet_replacePath_iff i₀ Q hQ hold hsub]
  exact Or.inr ⟨j, hj, rfl⟩

/-- `Q` exceeds `P` when it strictly extends both the left endpoint set and
the right endpoint set. -/
def Exceeds (P Q : EndpointCleanPathPacking G S T) : Prop :=
  P.sourceSet ⊂ Q.sourceSet ∧ P.targetSet ⊂ Q.targetSet

@[simp] theorem cons_sourceSet (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    (P.cons R hR hdisj).sourceSet = insert R.source P.sourceSet := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    cases i with
    | none =>
        exact Finset.mem_insert.2 (Or.inl hiv.symm)
    | some i =>
        exact Finset.mem_insert.2 (Or.inr
          (Finset.mem_image.2 ⟨i, by simp, hiv⟩))
  · intro hv
    rcases Finset.mem_insert.1 hv with rfl | hvP
    · exact Finset.mem_image.2 ⟨none, by simp, rfl⟩
    · rcases Finset.mem_image.mp hvP with ⟨i, _hi, hiv⟩
      exact Finset.mem_image.2 ⟨some i, by simp, hiv⟩

@[simp] theorem cons_targetSet (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    (P.cons R hR hdisj).targetSet = insert R.target P.targetSet := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    cases i with
    | none =>
        exact Finset.mem_insert.2 (Or.inl hiv.symm)
    | some i =>
        exact Finset.mem_insert.2 (Or.inr
          (Finset.mem_image.2 ⟨i, by simp, hiv⟩))
  · intro hv
    rcases Finset.mem_insert.1 hv with rfl | hvP
    · exact Finset.mem_image.2 ⟨none, by simp, rfl⟩
    · rcases Finset.mem_image.mp hvP with ⟨i, _hi, hiv⟩
      exact Finset.mem_image.2 ⟨some i, by simp, hiv⟩

theorem cons_source_not_mem_sourceSet (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (_hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    R.source ∉ P.sourceSet := by
  classical
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hsource⟩
  have hP : R.source ∈ P.vertexSet :=
    P.path_vertexSet_subset_vertexSet i (by
      simpa [hsource] using GraphPath.source_mem_vertexSet (P.path i))
  exact Finset.disjoint_left.mp hdisj
    (GraphPath.source_mem_vertexSet R) hP

theorem cons_target_not_mem_targetSet (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (_hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    R.target ∉ P.targetSet := by
  classical
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, htarget⟩
  have hP : R.target ∈ P.vertexSet :=
    P.path_vertexSet_subset_vertexSet i (by
      simpa [htarget] using GraphPath.target_mem_vertexSet (P.path i))
  exact Finset.disjoint_left.mp hdisj
    (GraphPath.target_mem_vertexSet R) hP

theorem exceeds_cons (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    P.Exceeds (P.cons R hR hdisj) := by
  classical
  constructor
  · rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro v hv
      simp [hv]
    · intro heq
      exact P.cons_source_not_mem_sourceSet R hR hdisj (by
        rw [heq]
        simp)
  · rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro v hv
      simp [hv]
    · intro heq
      exact P.cons_target_not_mem_targetSet R hR hdisj (by
        rw [heq]
        simp)

theorem sourceSet_subset_left (P : EndpointCleanPathPacking G S T) :
    P.sourceSet ⊆ S := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact (P.endpoint_clean i).source_mem

theorem targetSet_subset_right (P : EndpointCleanPathPacking G S T) :
    P.targetSet ⊆ T := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact (P.endpoint_clean i).target_mem

theorem source_mem_sourceSet (P : EndpointCleanPathPacking G S T)
    (i : P.Index) :
    (P.path i).source ∈ P.sourceSet := by
  classical
  exact Finset.mem_image.2 ⟨i, by simp, rfl⟩

theorem target_mem_targetSet (P : EndpointCleanPathPacking G S T)
    (i : P.Index) :
    (P.path i).target ∈ P.targetSet := by
  classical
  exact Finset.mem_image.2 ⟨i, by simp, rfl⟩

theorem exists_index_source_eq_of_mem_sourceSet
    (P : EndpointCleanPathPacking G S T) {v : V}
    (hv : v ∈ P.sourceSet) :
    ∃ i : P.Index, (P.path i).source = v := by
  classical
  rcases Finset.mem_image.mp hv with ⟨i, _hi, hi⟩
  exact ⟨i, hi⟩

theorem exists_index_target_eq_of_mem_targetSet
    (P : EndpointCleanPathPacking G S T) {v : V}
    (hv : v ∈ P.targetSet) :
    ∃ i : P.Index, (P.path i).target = v := by
  classical
  rcases Finset.mem_image.mp hv with ⟨i, _hi, hi⟩
  exact ⟨i, hi⟩

theorem source_injective (P : EndpointCleanPathPacking G S T) :
    Function.Injective fun i : P.Index => (P.path i).source := by
  intro i j hij
  by_contra hne
  have hdisj := P.node_disjoint hne
  have hi : (P.path i).source ∈ (P.path i).vertexSet :=
    GraphPath.source_mem_vertexSet (P.path i)
  have hj : (P.path i).source ∈ (P.path j).vertexSet := by
    simp [hij]
  exact Finset.disjoint_left.mp hdisj hi hj

theorem target_injective (P : EndpointCleanPathPacking G S T) :
    Function.Injective fun i : P.Index => (P.path i).target := by
  intro i j hij
  by_contra hne
  have hdisj := P.node_disjoint hne
  have hi : (P.path i).target ∈ (P.path i).vertexSet :=
    GraphPath.target_mem_vertexSet (P.path i)
  have hj : (P.path i).target ∈ (P.path j).vertexSet := by
    simp [hij]
  exact Finset.disjoint_left.mp hdisj hi hj

theorem target_notMem_path_of_ne (P : EndpointCleanPathPacking G S T)
    {i j : P.Index} (hij : i ≠ j) :
    (P.path i).target ∉ (P.path j).vertexSet := by
  intro hmem
  exact Finset.disjoint_left.mp (P.node_disjoint hij)
    (GraphPath.target_mem_vertexSet (P.path i)) hmem

theorem source_notMem_path_of_ne (P : EndpointCleanPathPacking G S T)
    {i j : P.Index} (hij : i ≠ j) :
    (P.path i).source ∉ (P.path j).vertexSet := by
  intro hmem
  exact Finset.disjoint_left.mp (P.node_disjoint hij)
    (GraphPath.source_mem_vertexSet (P.path i)) hmem

theorem target_notMem_vertexSet_of_target_not_mem_targetSet
    (P : EndpointCleanPathPacking G S T) {v : V}
    (hv : v ∉ P.targetSet) :
    ∀ i : P.Index, (P.path i).target ≠ v := by
  intro i hi
  exact hv (by
    rw [← hi]
    exact P.target_mem_targetSet i)

@[simp] theorem sourceSet_card (P : EndpointCleanPathPacking G S T) :
    P.sourceSet.card = P.card := by
  classical
  rw [sourceSet, card, Finset.card_image_of_injective Finset.univ]
  · simp
  intro i j hij
  by_contra hne
  have hdisj := P.node_disjoint hne
  have hi : (P.path i).source ∈ (P.path i).vertexSet :=
    GraphPath.source_mem_vertexSet (P.path i)
  have hj : (P.path i).source ∈ (P.path j).vertexSet := by
    simp [hij]
  exact Finset.disjoint_left.mp hdisj hi hj

@[simp] theorem targetSet_card (P : EndpointCleanPathPacking G S T) :
    P.targetSet.card = P.card := by
  classical
  rw [targetSet, card, Finset.card_image_of_injective Finset.univ]
  · simp
  intro i j hij
  by_contra hne
  have hdisj := P.node_disjoint hne
  have hi : (P.path i).target ∈ (P.path i).vertexSet :=
    GraphPath.target_mem_vertexSet (P.path i)
  have hj : (P.path i).target ∈ (P.path j).vertexSet := by
    simp [hij]
  exact Finset.disjoint_left.mp hdisj hi hj

theorem Exceeds.sourceSet_subset {P Q : EndpointCleanPathPacking G S T}
    (h : P.Exceeds Q) :
    P.sourceSet ⊆ Q.sourceSet :=
  (Finset.ssubset_iff_subset_ne.mp h.1).1

theorem Exceeds.targetSet_subset {P Q : EndpointCleanPathPacking G S T}
    (h : P.Exceeds Q) :
    P.targetSet ⊆ Q.targetSet :=
  (Finset.ssubset_iff_subset_ne.mp h.2).1

theorem exceeds_of_subset_card_add_one
    {P Q : EndpointCleanPathPacking G S T}
    (hsource : P.sourceSet ⊆ Q.sourceSet)
    (htarget : P.targetSet ⊆ Q.targetSet)
    (hcard : Q.card = P.card + 1) :
    P.Exceeds Q := by
  constructor
  · rw [Finset.ssubset_iff_subset_ne]
    constructor
    · exact hsource
    · intro heq
      have hcards : P.sourceSet.card = Q.sourceSet.card := congrArg Finset.card heq
      rw [sourceSet_card, sourceSet_card, hcard] at hcards
      omega
  · rw [Finset.ssubset_iff_subset_ne]
    constructor
    · exact htarget
    · intro heq
      have hcards : P.targetSet.card = Q.targetSet.card := congrArg Finset.card heq
      rw [targetSet_card, targetSet_card, hcard] at hcards
      omega

/-- If `Q` exceeds `P` and has exactly one more path, then it has exactly one
new right endpoint. -/
theorem Exceeds.targetSet_sdiff_card_eq_one
    {P Q : EndpointCleanPathPacking G S T} (h : P.Exceeds Q)
    (hcard : Q.card = P.card + 1) :
    (Q.targetSet \ P.targetSet).card = 1 := by
  rw [Finset.card_sdiff_of_subset h.targetSet_subset]
  rw [targetSet_card, targetSet_card, hcard]
  omega

/-- If `Q` exceeds `P` and has exactly one more path, then it has exactly one
new left endpoint. -/
theorem Exceeds.sourceSet_sdiff_card_eq_one
    {P Q : EndpointCleanPathPacking G S T} (h : P.Exceeds Q)
    (hcard : Q.card = P.card + 1) :
    (Q.sourceSet \ P.sourceSet).card = 1 := by
  rw [Finset.card_sdiff_of_subset h.sourceSet_subset]
  rw [sourceSet_card, sourceSet_card, hcard]
  omega

theorem Exceeds.exists_unique_new_target
    {P Q : EndpointCleanPathPacking G S T} (h : P.Exceeds Q)
    (hcard : Q.card = P.card + 1) :
    ∃ y : V, y ∈ Q.targetSet \ P.targetSet ∧
      ∀ z : V, z ∈ Q.targetSet \ P.targetSet → z = y := by
  classical
  rcases Finset.card_eq_one.mp
      (h.targetSet_sdiff_card_eq_one hcard) with ⟨y, hy⟩
  refine ⟨y, ?_, ?_⟩
  · rw [hy]
    simp
  · intro z hz
    rw [hy] at hz
    simpa using hz

theorem Exceeds.exists_unique_new_source
    {P Q : EndpointCleanPathPacking G S T} (h : P.Exceeds Q)
    (hcard : Q.card = P.card + 1) :
    ∃ y : V, y ∈ Q.sourceSet \ P.sourceSet ∧
      ∀ z : V, z ∈ Q.sourceSet \ P.sourceSet → z = y := by
  classical
  rcases Finset.card_eq_one.mp
      (h.sourceSet_sdiff_card_eq_one hcard) with ⟨y, hy⟩
  refine ⟨y, ?_, ?_⟩
  · rw [hy]
    simp
  · intro z hz
    rw [hy] at hz
    simpa using hz

theorem Exceeds.exists_target_index_of_old_target
    {P Q : EndpointCleanPathPacking G S T} (h : P.Exceeds Q)
    {x : V} (hx : x ∈ P.targetSet) :
    ∃ i : Q.Index, (Q.path i).target = x := by
  exact Q.exists_index_target_eq_of_mem_targetSet (h.targetSet_subset hx)

theorem Exceeds.exists_new_target_index
    {P Q : EndpointCleanPathPacking G S T} (h : P.Exceeds Q)
    (hcard : Q.card = P.card + 1) :
    ∃ y : V, ∃ i : Q.Index,
      y ∈ Q.targetSet \ P.targetSet ∧
      (Q.path i).target = y ∧
      ∀ z : V, z ∈ Q.targetSet \ P.targetSet → z = y := by
  classical
  rcases h.exists_unique_new_target hcard with ⟨y, hy, hyuniq⟩
  rcases Q.exists_index_target_eq_of_mem_targetSet
      (Finset.mem_sdiff.mp hy).1 with ⟨i, hi⟩
  exact ⟨y, i, hy, hi, hyuniq⟩

theorem Exceeds.target_mem_old_or_eq_unique_new
    {P Q : EndpointCleanPathPacking G S T} (_h : P.Exceeds Q)
    {y : V}
    (hyuniq : ∀ z : V, z ∈ Q.targetSet \ P.targetSet → z = y)
    (i : Q.Index) :
    (Q.path i).target ∈ P.targetSet ∨ (Q.path i).target = y := by
  classical
  by_cases hold : (Q.path i).target ∈ P.targetSet
  · exact Or.inl hold
  · right
    apply hyuniq
    exact Finset.mem_sdiff.2 ⟨Q.target_mem_targetSet i, hold⟩

theorem Exceeds.target_ne_of_ne_index
    {P Q : EndpointCleanPathPacking G S T} (_h : P.Exceeds Q)
    {i j : Q.Index} (hij : i ≠ j) :
    (Q.path i).target ≠ (Q.path j).target := by
  intro htarget
  exact hij (Q.target_injective htarget)

theorem Exceeds.target_mem_old_of_ne_new_target_index
    {P Q : EndpointCleanPathPacking G S T} (h : P.Exceeds Q)
    {y : V} {iy j : Q.Index}
    (hyuniq : ∀ z : V, z ∈ Q.targetSet \ P.targetSet → z = y)
    (hiy : (Q.path iy).target = y) (hj : j ≠ iy) :
    (Q.path j).target ∈ P.targetSet := by
  rcases h.target_mem_old_or_eq_unique_new hyuniq j with hold | hnew
  · exact hold
  · have htargets : (Q.path j).target = (Q.path iy).target := by
      simpa [hiy] using hnew
    exact False.elim (hj (Q.target_injective htargets))

theorem Exceeds.target_mem_right_of_ne_indices_replacePath
    {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Qrep : GraphPath G) (hQrep : Qrep.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Qrep.vertexSet ⊆ (P.path i₀).vertexSet)
    {Qbig : EndpointCleanPathPacking G S T'}
    (h : (P.replacePath i₀ Qrep hQrep hold hsub).Exceeds Qbig)
    {x y : V} {ix iy j : Qbig.Index}
    (hix : (Qbig.path ix).target = x)
    (hx : x = Qrep.target)
    (hyuniq :
      ∀ z : V,
        z ∈ Qbig.targetSet \
          (P.replacePath i₀ Qrep hQrep hold hsub).targetSet →
          z = y)
    (hiy : (Qbig.path iy).target = y)
    (hjx : j ≠ ix) (hjy : j ≠ iy) :
    (Qbig.path j).target ∈ T := by
  classical
  have holdTarget :
      (Qbig.path j).target ∈
        (P.replacePath i₀ Qrep hQrep hold hsub).targetSet :=
    h.target_mem_old_of_ne_new_target_index hyuniq hiy hjy
  have hneRep : (Qbig.path j).target ≠ Qrep.target := by
    intro htarget
    have htargets : (Qbig.path j).target = (Qbig.path ix).target := by
      calc
        (Qbig.path j).target = Qrep.target := htarget
        _ = x := hx.symm
        _ = (Qbig.path ix).target := hix.symm
    exact hjx (Qbig.target_injective htargets)
  exact P.target_mem_right_of_mem_replacePath_targetSet_ne
    i₀ Qrep hQrep hold hsub holdTarget hneRep

theorem Exceeds.old_target_index_ne_new_target_index
    {P Q : EndpointCleanPathPacking G S T} (_h : P.Exceeds Q)
    {x y : V} {ix iy : Q.Index}
    (hx_old : x ∈ P.targetSet)
    (hy_new : y ∈ Q.targetSet \ P.targetSet)
    (hix : (Q.path ix).target = x)
    (hiy : (Q.path iy).target = y) :
    ix ≠ iy := by
  intro hidx
  have hxy : x = y := by
    calc
      x = (Q.path ix).target := hix.symm
      _ = (Q.path iy).target := by rw [hidx]
      _ = y := hiy
  exact (Finset.mem_sdiff.mp hy_new).2 (by simpa [hxy] using hx_old)

/-- Forget endpoint-clean data and keep the underlying disjoint path packing. -/
def toPathPacking (P : EndpointCleanPathPacking G S T) :
    PathPacking G S T where
  Index := P.Index
  path := P.path
  connects := fun i => (P.endpoint_clean i).connects
  node_disjoint := P.node_disjoint

@[simp] theorem toPathPacking_card (P : EndpointCleanPathPacking G S T) :
    P.toPathPacking.card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

/-- Transfer an endpoint-clean packing to another graph on the same vertices
when every edge of every packed path belongs to the new graph. -/
def transfer (P : EndpointCleanPathPacking G S T)
    (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e,
      e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    EndpointCleanPathPacking H S T where
  Index := P.Index
  path := fun i => (P.path i).transfer H (h i)
  endpoint_clean := by
    intro i
    have hclean := P.endpoint_clean i
    exact
      { source_mem := hclean.source_mem
        target_mem := hclean.target_mem
        left_eq_source := by
          intro v hv hvS
          exact hclean.left_eq_source (by simpa using hv) hvS
        right_eq_target := by
          intro v hv hvT
          exact hclean.right_eq_target (by simpa using hv) hvT }
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

@[simp] theorem transfer_card (P : EndpointCleanPathPacking G S T)
    (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e,
      e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).card = P.card := rfl

@[simp] theorem transfer_path_vertexSet
    (P : EndpointCleanPathPacking G S T)
    (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e,
      e ∈ (P.path i).walk.edges → e ∈ H.edgeSet)
    (i : (P.transfer H h).Index) :
    ((P.transfer H h).path i).vertexSet =
      (P.path i).vertexSet := by
  exact GraphPath.transfer_vertexSet (P.path i) H (h i)

@[simp] theorem transfer_path_edgeSet
    (P : EndpointCleanPathPacking G S T)
    (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e,
      e ∈ (P.path i).walk.edges → e ∈ H.edgeSet)
    (i : (P.transfer H h).Index) :
    ((P.transfer H h).path i).edgeSet =
      (P.path i).edgeSet := by
  exact GraphPath.transfer_edgeSet (P.path i) H (h i)

@[simp] theorem transfer_sourceSet (P : EndpointCleanPathPacking G S T)
    (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e,
      e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).sourceSet = P.sourceSet := by
  classical
  rfl

@[simp] theorem transfer_targetSet (P : EndpointCleanPathPacking G S T)
    (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e,
      e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).targetSet = P.targetSet := by
  classical
  rfl

@[simp] theorem transfer_toPathPacking_edgeSet
    (P : EndpointCleanPathPacking G S T)
    (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e,
      e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).toPathPacking.edgeSet =
      P.toPathPacking.edgeSet := by
  classical
  ext e
  simp [EndpointCleanPathPacking.transfer,
    EndpointCleanPathPacking.toPathPacking,
    PathPacking.edgeSet]

/-- Restrict an endpoint-clean packing to a finite set of path indices. -/
noncomputable def restrictIndexSet (P : EndpointCleanPathPacking G S T)
    (I : Finset P.Index) : EndpointCleanPathPacking G S T where
  Index := {i : P.Index // i ∈ I}
  path := fun i => P.path i.1
  endpoint_clean := fun i => P.endpoint_clean i.1
  node_disjoint := by
    intro i j hij
    exact P.node_disjoint (fun h => hij (Subtype.ext h))

@[simp] theorem restrictIndexSet_card
    (P : EndpointCleanPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).card = I.card := by
  classical
  simp [restrictIndexSet, EndpointCleanPathPacking.card]

@[simp] theorem restrictIndexSet_path_vertexSet
    (P : EndpointCleanPathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).vertexSet =
      (P.path i.1).vertexSet := rfl

@[simp] theorem restrictIndexSet_path_edgeSet
    (P : EndpointCleanPathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).edgeSet =
      (P.path i.1).edgeSet := rfl

/-- Indices of the paths whose oriented source belongs to `U`. -/
noncomputable def sourceIndexSet
    (P : EndpointCleanPathPacking G S T) (U : Finset V) :
    Finset P.Index :=
  Finset.univ.filter fun i => (P.path i).source ∈ U

/-- Restrict a packing to the paths originating in `U`. -/
noncomputable def restrictSources
    (P : EndpointCleanPathPacking G S T) (U : Finset V) :
    EndpointCleanPathPacking G S T :=
  P.restrictIndexSet (P.sourceIndexSet U)

theorem sourceIndexSet_card_eq
    (P : EndpointCleanPathPacking G S T) (U : Finset V)
    (hU : U ⊆ P.sourceSet) :
    (P.sourceIndexSet U).card = U.card := by
  classical
  let f : P.Index ↪ V :=
    ⟨fun i => (P.path i).source, P.source_injective⟩
  have hmap :
      (P.sourceIndexSet U).map f = U := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_map.mp hv with ⟨i, hi, hiv⟩
      have hiU : (P.path i).source ∈ U := by
        simpa [sourceIndexSet] using hi
      have heq : (P.path i).source = v := by
        simpa [f] using hiv
      simpa [heq] using hiU
    · intro hvU
      rcases P.exists_index_source_eq_of_mem_sourceSet (hU hvU) with
        ⟨i, hi⟩
      exact Finset.mem_map.mpr
        ⟨i, by simp [sourceIndexSet, hi, hvU], by
          simpa [f] using hi⟩
  calc
    (P.sourceIndexSet U).card =
        ((P.sourceIndexSet U).map f).card := by
          rw [Finset.card_map]
    _ = U.card := congrArg Finset.card hmap

@[simp] theorem restrictSources_card
    (P : EndpointCleanPathPacking G S T) (U : Finset V)
    (hU : U ⊆ P.sourceSet) :
    (P.restrictSources U).card = U.card := by
  simp [restrictSources, P.sourceIndexSet_card_eq U hU]

theorem restrictSources_sourceSet_eq
    (P : EndpointCleanPathPacking G S T) (U : Finset V)
    (hU : U ⊆ P.sourceSet) :
    (P.restrictSources U).sourceSet = U := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hiv⟩
    have hiU : (P.path i.1).source ∈ U := by
      exact (Finset.mem_filter.mp i.2).2
    have heq : (P.path i.1).source = v := by
      simpa [restrictSources] using hiv
    simpa [heq] using hiU
  · intro hvU
    rcases P.exists_index_source_eq_of_mem_sourceSet (hU hvU) with
      ⟨i, hi⟩
    exact Finset.mem_image.mpr
      ⟨⟨i, by simp [sourceIndexSet, hi, hvU]⟩, by simp, by
        exact hi⟩

end EndpointCleanPathPacking

namespace PathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- Clean every path of a path packing to the oriented endpoint-clean subpath
between its terminal sets. -/
noncomputable def toEndpointClean (P : PathPacking G S T) :
    EndpointCleanPathPacking G S T where
  Index := P.Index
  path := fun i => (P.path i).cleanBetweenTerminalSets (P.connects i)
  endpoint_clean := fun i =>
    (P.path i).cleanBetweenTerminalSets_endpointClean (P.connects i)
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvi hvj
    exact Finset.disjoint_left.mp (P.node_disjoint hij)
      ((P.path i).cleanBetweenTerminalSets_vertexSet_subset (P.connects i) hvi)
      ((P.path j).cleanBetweenTerminalSets_vertexSet_subset (P.connects j) hvj)

@[simp] theorem toEndpointClean_card (P : PathPacking G S T) :
    P.toEndpointClean.card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

end PathPacking

namespace PerfectPathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- Regard a perfect packing between smaller terminal sets as an
endpoint-clean packing between larger terminal sets, provided every terminal
in the larger sets has degree one. -/
noncomputable def toEndpointCleanInOfTerminalDegreeOne
    {S₀ T₀ S T : Finset V}
    (P : PerfectPathPacking G S₀ T₀)
    (hS₀ : S₀ ⊆ S) (hT₀ : T₀ ⊆ T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    EndpointCleanPathPacking G S T where
  Index := P.Index
  path := P.path
  endpoint_clean := by
    intro i
    refine
      { source_mem := hS₀ (P.source_mem i)
        target_mem := hT₀ (P.target_mem i)
        left_eq_source := ?_
        right_eq_target := ?_ }
    · intro v hv hvS
      rcases (P.path i).isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          (hSdeg v hvS) hv with hsource | htarget
      · exact hsource
      · exact False.elim
          (Finset.disjoint_left.mp hST hvS
            (by simpa [htarget] using hT₀ (P.target_mem i)))
    · intro v hv hvT
      rcases (P.path i).isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          (hTdeg v hvT) hv with hsource | htarget
      · exact False.elim
          (Finset.disjoint_left.mp hST
            (by simpa [hsource] using hS₀ (P.source_mem i)) hvT)
      · exact htarget
  node_disjoint := P.toPathPacking.node_disjoint

@[simp] theorem toEndpointCleanInOfTerminalDegreeOne_card
    {S₀ T₀ S T : Finset V}
    (P : PerfectPathPacking G S₀ T₀)
    (hS₀ : S₀ ⊆ S) (hT₀ : T₀ ⊆ T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    (P.toEndpointCleanInOfTerminalDegreeOne
      hS₀ hT₀ hST hSdeg hTdeg).card = P.card := rfl

@[simp] theorem toEndpointCleanInOfTerminalDegreeOne_sourceSet
    {S₀ T₀ S T : Finset V}
    (P : PerfectPathPacking G S₀ T₀)
    (hS₀ : S₀ ⊆ S) (hT₀ : T₀ ⊆ T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    (P.toEndpointCleanInOfTerminalDegreeOne
      hS₀ hT₀ hST hSdeg hTdeg).sourceSet = S₀ := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hvi⟩
    simpa [toEndpointCleanInOfTerminalDegreeOne] using
      (hvi ▸ P.source_mem i)
  · intro hv
    rcases P.source_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
    exact Finset.mem_image.mpr
      ⟨i, by simp, congrArg Subtype.val hi⟩

@[simp] theorem toEndpointCleanInOfTerminalDegreeOne_targetSet
    {S₀ T₀ S T : Finset V}
    (P : PerfectPathPacking G S₀ T₀)
    (hS₀ : S₀ ⊆ S) (hT₀ : T₀ ⊆ T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    (P.toEndpointCleanInOfTerminalDegreeOne
      hS₀ hT₀ hST hSdeg hTdeg).targetSet = T₀ := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hvi⟩
    simpa [toEndpointCleanInOfTerminalDegreeOne] using
      (hvi ▸ P.target_mem i)
  · intro hv
    rcases P.target_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
    exact Finset.mem_image.mpr
      ⟨i, by simp, congrArg Subtype.val hi⟩

/-- A perfect packing whose terminal vertices all have degree one is already
endpoint-clean.  This is the proof-facing form of the standard pendant-copy
normalization used in flow and gammoid arguments. -/
noncomputable def toEndpointCleanOfTerminalDegreeOne
    (P : PerfectPathPacking G S T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    EndpointCleanPathPacking G S T where
  Index := P.Index
  path := P.path
  endpoint_clean := by
    intro i
    refine
      { source_mem := P.source_mem i
        target_mem := P.target_mem i
        left_eq_source := ?_
        right_eq_target := ?_ }
    · intro v hv hvS
      rcases (P.path i).isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          (hSdeg v hvS) hv with hsource | htarget
      · exact hsource
      · exact False.elim
          (Finset.disjoint_left.mp hST hvS
            (by simpa [htarget] using P.target_mem i))
    · intro v hv hvT
      rcases (P.path i).isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          (hTdeg v hvT) hv with hsource | htarget
      · exact False.elim
          (Finset.disjoint_left.mp hST
            (by simpa [hsource] using P.source_mem i) hvT)
      · exact htarget
  node_disjoint := P.toPathPacking.node_disjoint

@[simp] theorem toEndpointCleanOfTerminalDegreeOne_card
    (P : PerfectPathPacking G S T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    (P.toEndpointCleanOfTerminalDegreeOne hST hSdeg hTdeg).card =
      P.card := rfl

@[simp] theorem toEndpointCleanOfTerminalDegreeOne_sourceSet
    (P : PerfectPathPacking G S T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    (P.toEndpointCleanOfTerminalDegreeOne hST hSdeg hTdeg).sourceSet = S := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hvi⟩
    simpa [toEndpointCleanOfTerminalDegreeOne] using
      (hvi ▸ P.source_mem i)
  · intro hv
    rcases P.source_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
    exact Finset.mem_image.mpr
      ⟨i, by simp, by
        exact congrArg Subtype.val hi⟩

@[simp] theorem toEndpointCleanOfTerminalDegreeOne_targetSet
    (P : PerfectPathPacking G S T)
    (hST : Disjoint S T)
    (hSdeg : ∀ v ∈ S, DegreeEquals G v 1)
    (hTdeg : ∀ v ∈ T, DegreeEquals G v 1) :
    (P.toEndpointCleanOfTerminalDegreeOne hST hSdeg hTdeg).targetSet = T := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, hvi⟩
    simpa [toEndpointCleanOfTerminalDegreeOne] using
      (hvi ▸ P.target_mem i)
  · intro hv
    rcases P.target_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
    exact Finset.mem_image.mpr
      ⟨i, by simp, by
        exact congrArg Subtype.val hi⟩

end PerfectPathPacking

/-- A finite vertex set `X` is an `(S,T)`-separator if every path connecting
`S` and `T` contains a vertex of `X`.

This is not a balanced-separator notion: it is the ordinary separator used in
Menger's theorem.  We allow `X` to meet `S` or `T`, so the terminal sets
themselves are always separators. -/
def STSeparator {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T X : Finset V) : Prop :=
  ∀ P : GraphPath G, P.Connects S T → ∃ v ∈ P.vertexSet, v ∈ X

/-- There are at least `k` pairwise vertex-disjoint paths connecting `S` to
`T`.  The paths are represented by the existing finite indexed `PathPacking`
structure. -/
def HasDisjointSTPaths {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) (k : ℕ) : Prop :=
  ∃ P : PathPacking G S T, k ≤ P.card

namespace STSeparator

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T X Y : Finset V}

/-- Enlarging a separator preserves the separator property. -/
theorem mono (hX : STSeparator G S T X) (hXY : X ⊆ Y) :
    STSeparator G S T Y := by
  intro P hP
  rcases hX P hP with ⟨v, hvP, hvX⟩
  exact ⟨v, hvP, hXY hvX⟩

/-- The left terminal set separates `S` from `T`. -/
theorem left :
    STSeparator G S T S := by
  intro P hP
  rcases hP with hP | hP
  · exact ⟨P.source, GraphPath.source_mem_vertexSet P, hP.1⟩
  · exact ⟨P.target, GraphPath.target_mem_vertexSet P, hP.2⟩

/-- The right terminal set separates `S` from `T`. -/
theorem right :
    STSeparator G S T T := by
  intro P hP
  rcases hP with hP | hP
  · exact ⟨P.target, GraphPath.target_mem_vertexSet P, hP.2⟩
  · exact ⟨P.source, GraphPath.source_mem_vertexSet P, hP.1⟩

/-- Every `(S,T)`-separator contains `S ∩ T`: a vertex in the intersection is
itself a trivial `S`-to-`T` path. -/
theorem inter_subset (hX : STSeparator G S T X) :
    S ∩ T ⊆ X := by
  intro v hv
  rcases hX (GraphPath.refl G v)
      (Or.inl ⟨(Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩) with
    ⟨w, hwPath, hwX⟩
  have hw : w = v := by
    simpa [GraphPath.refl_vertexSet] using hwPath
  simpa [hw] using hwX

end STSeparator

namespace HasDisjointSTPaths

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- The empty path family witnesses the existence of zero disjoint paths. -/
theorem zero :
    HasDisjointSTPaths G S T 0 :=
  ⟨{
    Index := Empty
    path := fun i => nomatch i
    connects := by
      intro i
      cases i
    node_disjoint := by
      intro i
      cases i
  }, by simp [PathPacking.card]⟩

/-- Any `k` vertices in `S ∩ T` give `k` disjoint trivial `S`-to-`T` paths. -/
theorem of_le_inter_card {k : ℕ} (h : k ≤ (S ∩ T).card) :
    HasDisjointSTPaths G S T k := by
  classical
  rcases Finset.exists_subset_card_eq h with ⟨I, hI, hIcard⟩
  let P₀ := (PerfectPathPacking.refl G I).toPathPacking
  have hIS : I ⊆ S := by
    intro v hv
    exact (Finset.mem_inter.mp (hI hv)).1
  have hIT : I ⊆ T := by
    intro v hv
    exact (Finset.mem_inter.mp (hI hv)).2
  refine ⟨P₀.widenTerminals hIS hIT, ?_⟩
  rw [PathPacking.widenTerminals_card, PerfectPathPacking.toPathPacking_card,
    PerfectPathPacking.refl_card, hIcard]

end HasDisjointSTPaths

end SimpleGraph

end Lax17Proofs
