import Lax17Proofs.Source.ChekuriChuzhoyPendantTerminals
import Lax17Proofs.Source.TreeOfSets

namespace Lax17Proofs

universe u v w

/-!
# Transport out of the Chekuri--Chuzhoy pendant extension

The Section 4 tree-of-sets construction is applied after replacing the
well-linked terminals by fresh degree-one leaves.  This file proves the
graph-theoretic transport needed after that construction: an old-ended simple
path cannot use a pendant leaf, so old-copy clusters, interfaces, and connector
packings project back to the original graph without changing their sizes or
disjointness properties.
-/

namespace SimpleGraph


open scoped Classical

namespace ChekuriChuzhoyPendantVertex

variable {V : Type u} [Fintype V] [DecidableEq V] {X : Finset V}
variable {G : _root_.SimpleGraph V}

/-- The finite old-copy region of the pendant extension. -/
noncomputable def oldRegion :
    Finset (ChekuriChuzhoyPendantVertex V X) :=
  oldImage (X := X) (Finset.univ : Finset V)

@[simp] theorem mem_oldRegion_old (x : V) :
    old (X := X) x ∈ oldRegion (V := V) (X := X) := by
  simp [oldRegion]

@[simp] theorem not_mem_oldRegion_leaf (x : {x : V // x ∈ X}) :
    leaf x ∉ oldRegion (V := V) (X := X) := by
  simp [oldRegion, oldImage]

theorem mem_oldRegion_iff_isOld
    (z : ChekuriChuzhoyPendantVertex V X) :
    z ∈ oldRegion (V := V) (X := X) ↔ IsOld z := by
  cases z <;> simp [IsOld]

/-- Avoiding the full pendant terminal set is equivalent to being old-only,
in the direction needed for output clusters. -/
theorem subset_oldRegion_of_disjoint_leaves
    {A : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hA : Disjoint A (leaves (V := V) (X := X))) :
    A ⊆ oldRegion (V := V) (X := X) := by
  intro z hz
  cases z with
  | old x => exact mem_oldRegion_old x
  | leaf x =>
      exact False.elim
        (Finset.disjoint_left.mp hA hz (mem_leaves (V := V) (X := X)))

/-- Project an arbitrary finite set by retaining its old-copy vertices. -/
noncomputable def projectOldSet
    (A : Finset (ChekuriChuzhoyPendantVertex V X)) : Finset V :=
  Finset.univ.filter fun x => old (X := X) x ∈ A

@[simp] theorem mem_projectOldSet
    {A : Finset (ChekuriChuzhoyPendantVertex V X)} {x : V} :
    x ∈ projectOldSet (X := X) A ↔ old (X := X) x ∈ A := by
  simp [projectOldSet]

theorem oldImage_projectOldSet_eq
    {A : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hA : A ⊆ oldRegion (V := V) (X := X)) :
    oldImage (X := X) (projectOldSet (X := X) A) = A := by
  ext z
  cases z with
  | old x => simp
  | leaf x =>
      constructor
      · intro hz
        simpa [oldImage] using hz
      · intro hz
        exact False.elim (not_mem_oldRegion_leaf x (hA hz))

@[simp] theorem projectOldSet_oldImage (A : Finset V) :
    projectOldSet (X := X) (oldImage (X := X) A) = A := by
  ext x
  simp

theorem projectOldSet_subset
    {A B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hAB : A ⊆ B) :
    projectOldSet (X := X) A ⊆ projectOldSet (X := X) B := by
  intro x hx
  exact mem_projectOldSet.mpr (hAB (mem_projectOldSet.mp hx))

theorem projectOldSet_disjoint
    {A B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hAB : Disjoint A B) :
    Disjoint (projectOldSet (X := X) A) (projectOldSet (X := X) B) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  exact Finset.disjoint_left.mp hAB
    (mem_projectOldSet.mp hxA) (mem_projectOldSet.mp hxB)

theorem projectOldSet_card
    {A : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hA : A ⊆ oldRegion (V := V) (X := X)) :
    (projectOldSet (X := X) A).card = A.card := by
  rw [← oldImage_card (X := X) (projectOldSet (X := X) A),
    oldImage_projectOldSet_eq hA]

/-- A simple path whose two endpoints are old vertices contains no pendant
leaf.  This is the endpoint-stripping fact used by every record transport
below. -/
theorem GraphPath.vertexSet_subset_oldRegion_of_isOld_endpoints
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (hsource : IsOld P.source) (htarget : IsOld P.target) :
    P.vertexSet ⊆ oldRegion (V := V) (X := X) := by
  intro z hz
  cases z with
  | old x => exact mem_oldRegion_old x
  | leaf x =>
      have hend : P.IsEndpoint (leaf x) :=
        P.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          (leaf_degree_one (G := G) x) hz
      rcases hend with hs | ht
      · rw [← hs] at hsource
        exact False.elim hsource
      · rw [← ht] at htarget
        exact False.elim htarget

/-- An old-ended path stays in the old-copy region. -/
theorem GraphPath.vertexSet_subset_oldRegion
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    {a b : V} (hsource : P.source = old (X := X) a)
    (htarget : P.target = old (X := X) b) :
    P.vertexSet ⊆ oldRegion (V := V) (X := X) := by
  apply GraphPath.vertexSet_subset_oldRegion_of_isOld_endpoints P
  · simpa [hsource, IsOld]
  · simpa [htarget, IsOld]

/-- Forget the old constructor on a vertex certified to lie in `oldRegion`. -/
def oldRegionValue
    (z : {z : ChekuriChuzhoyPendantVertex V X //
      z ∈ oldRegion (V := V) (X := X)}) : V :=
  oldValue (X := X) ⟨z.1, (mem_oldRegion_iff_isOld z.1).mp z.2⟩

@[simp] theorem oldRegionValue_old (x : V) :
    oldRegionValue (X := X) ⟨old (X := X) x, mem_oldRegion_old x⟩ = x := rfl

theorem old_oldRegionValue
    (z : {z : ChekuriChuzhoyPendantVertex V X //
      z ∈ oldRegion (V := V) (X := X)}) :
    old (X := X) (oldRegionValue (X := X) z) = z.1 := by
  rcases exists_old_of_isOld ((mem_oldRegion_iff_isOld z.1).mp z.2) with
    ⟨x, hx⟩
  have hz : z = ⟨old (X := X) x, mem_oldRegion_old x⟩ := Subtype.ext hx
  rw [hz]
  rfl

/-- The old-copy region projects homomorphically to the original graph. -/
def oldRegionProjectionHom (G : _root_.SimpleGraph V) :
    (graph (X := X) G).induce
      {z : ChekuriChuzhoyPendantVertex V X |
        z ∈ oldRegion (V := V) (X := X)} →g G where
  toFun := oldRegionValue (X := X)
  map_rel' := by
    intro a b hab
    have hab' : (graph (X := X) G).Adj a.1 b.1 := by simpa using hab
    rw [← old_oldRegionValue (X := X) a,
      ← old_oldRegionValue (X := X) b] at hab'
    exact adj_old_old_iff.mp hab'

theorem oldRegionProjectionHom_injective (G : _root_.SimpleGraph V) :
    Function.Injective (oldRegionProjectionHom (X := X) G) := by
  intro a b hab
  apply Subtype.ext
  rw [← old_oldRegionValue (X := X) a,
    ← old_oldRegionValue (X := X) b]
  exact congrArg (old (X := X)) hab

/-- Project a path known to stay in the old-copy region back to `G`. -/
noncomputable def GraphPath.projectOld
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (X := X)) :
    Lax17Proofs.SimpleGraph.GraphPath G :=
  GraphPath.mapHomInjective
    (P.induce (oldRegion (V := V) (X := X)) hP)
    (oldRegionProjectionHom (X := X) G)
    (oldRegionProjectionHom_injective (X := X) G)

@[simp] theorem GraphPath.projectOld_source
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (X := X)) :
    (GraphPath.projectOld P hP).source =
      oldRegionValue (X := X)
        ⟨P.source, hP P.source_mem_vertexSet⟩ := rfl

@[simp] theorem GraphPath.projectOld_target
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (X := X)) :
    (GraphPath.projectOld P hP).target =
      oldRegionValue (X := X)
        ⟨P.target, hP P.target_mem_vertexSet⟩ := rfl

theorem GraphPath.mem_projectOld_vertexSet_iff
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (X := X)) (x : V) :
    x ∈ (GraphPath.projectOld P hP).vertexSet ↔
      old (X := X) x ∈ P.vertexSet := by
  classical
  rw [GraphPath.projectOld, GraphPath.mapHomInjective_vertexSet]
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, hzx⟩
    have hzP : z.1 ∈ P.vertexSet :=
      (GraphPath.mem_induce_vertexSet P _ hP z).mp hz
    have hval : old (X := X) x = z.1 := by
      rw [← old_oldRegionValue (X := X) z]
      exact congrArg (old (X := X)) hzx.symm
    simpa [hval] using hzP
  · intro hx
    let z : {z : ChekuriChuzhoyPendantVertex V X //
        z ∈ oldRegion (V := V) (X := X)} :=
      ⟨old (X := X) x, mem_oldRegion_old x⟩
    exact Finset.mem_image.mpr
      ⟨z, (GraphPath.mem_induce_vertexSet P _ hP z).mpr hx, by
        change oldRegionValue (X := X) z = x
        apply old_injective (V := V) (X := X)
        rw [old_oldRegionValue (X := X)]⟩

/-- The old neighbor of a pendant source occurs on every nontrivial path
starting at that leaf. -/
theorem GraphPath.old_neighbor_mem_of_source_leaf
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (x : {x : V // x ∈ X}) (hsource : P.source = leaf x)
    (hne : P.source ≠ P.target) :
    old (X := X) x.1 ∈ P.vertexSet := by
  have hrev_ne : P.reverse.source ≠ P.reverse.target := by
    simpa using hne.symm
  have hmem := P.reverse.penultimate_mem_vertexSet hrev_ne
  have hadj : (graph (X := X) G).Adj (leaf x) P.reverse.penultimate := by
    have h := (P.reverse.penultimate_adj_target hrev_ne).symm
    simpa [hsource] using h
  have hvalue : P.reverse.penultimate = old (X := X) x.1 :=
    (adj_leaf_iff (G := G) x).mp hadj
  simpa [hvalue] using hmem

/-- The old neighbor of a pendant target occurs on every nontrivial path
ending at that leaf. -/
theorem GraphPath.old_neighbor_mem_of_target_leaf
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (x : {x : V // x ∈ X}) (htarget : P.target = leaf x)
    (hne : P.source ≠ P.target) :
    old (X := X) x.1 ∈ P.vertexSet := by
  have hmem := P.penultimate_mem_vertexSet hne
  have hadj : (graph (X := X) G).Adj (leaf x) P.penultimate := by
    have h := (P.penultimate_adj_target hne).symm
    simpa [htarget] using h
  have hvalue : P.penultimate = old (X := X) x.1 :=
    (adj_leaf_iff (G := G) x).mp hadj
  simpa [hvalue] using hmem

/-- Strip the two pendant endpoint edges from a leaf-to-leaf path and project
the intervening old-copy path back to `G`.

The projected path is oriented from the base of the source leaf to the base of
the target leaf, and every one of its vertices lifts to a vertex of the input
path. -/
theorem GraphPath.exists_projected_of_leaf_endpoints
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (a b : {x : V // x ∈ X})
    (hsource : P.source = leaf a) (htarget : P.target = leaf b)
    (hne : P.source ≠ P.target) :
    ∃ Q : Lax17Proofs.SimpleGraph.GraphPath G,
      Q.source = a.1 ∧ Q.target = b.1 ∧
        ∀ x ∈ Q.vertexSet, old (X := X) x ∈ P.vertexSet := by
  have ha : old (X := X) a.1 ∈ P.vertexSet :=
    GraphPath.old_neighbor_mem_of_source_leaf P a hsource hne
  have hb : old (X := X) b.1 ∈ P.vertexSet :=
    GraphPath.old_neighbor_mem_of_target_leaf P b htarget hne
  rcases P.exists_segment_connects_of_mem_vertexSet ha hb with
    ⟨R, hconnects, hRsub⟩
  let R' := R.orient hconnects
  have hRsource : R'.source = old (X := X) a.1 := by
    simpa [R'] using GraphPath.orient_source_mem R hconnects
  have hRtarget : R'.target = old (X := X) b.1 := by
    simpa [R'] using GraphPath.orient_target_mem R hconnects
  have hRold : R'.vertexSet ⊆ oldRegion (V := V) (X := X) :=
    GraphPath.vertexSet_subset_oldRegion R' hRsource hRtarget
  let Q := GraphPath.projectOld R' hRold
  refine ⟨Q, ?_, ?_, ?_⟩
  · change oldRegionValue (X := X)
      ⟨R'.source, hRold R'.source_mem_vertexSet⟩ = a.1
    apply old_injective (V := V) (X := X)
    rw [old_oldRegionValue (X := X)]
    exact hRsource
  · change oldRegionValue (X := X)
      ⟨R'.target, hRold R'.target_mem_vertexSet⟩ = b.1
    apply old_injective (V := V) (X := X)
    rw [old_oldRegionValue (X := X)]
    exact hRtarget
  · intro x hx
    have hxR : old (X := X) x ∈ R'.vertexSet :=
      (GraphPath.mem_projectOld_vertexSet_iff R' hRold x).mp hx
    have hxR0 : old (X := X) x ∈ R.vertexSet := by
      simpa [R'] using hxR
    exact hRsub hxR0

/-- Strip only the pendant source edge from a leaf-to-old path and project
the remaining old-copy segment back to the original graph. -/
theorem GraphPath.exists_projected_of_source_leaf_target_old
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph (X := X) G))
    (a : {x : V // x ∈ X}) (b : V)
    (hsource : P.source = leaf a)
    (htarget : P.target = old (X := X) b) :
    ∃ Q : Lax17Proofs.SimpleGraph.GraphPath G,
      Q.source = a.1 ∧ Q.target = b ∧
        ∀ x ∈ Q.vertexSet, old (X := X) x ∈ P.vertexSet := by
  have hne : P.source ≠ P.target := by
    rw [hsource, htarget]
    intro h
    cases h
  have ha : old (X := X) a.1 ∈ P.vertexSet :=
    GraphPath.old_neighbor_mem_of_source_leaf P a hsource hne
  have hb : old (X := X) b ∈ P.vertexSet := by
    simpa [htarget] using GraphPath.target_mem_vertexSet P
  rcases P.exists_segment_connects_of_mem_vertexSet ha hb with
    ⟨R, hconnects, hRsub⟩
  let R' := R.orient hconnects
  have hRsource : R'.source = old (X := X) a.1 := by
    simpa [R'] using GraphPath.orient_source_mem R hconnects
  have hRtarget : R'.target = old (X := X) b := by
    simpa [R'] using GraphPath.orient_target_mem R hconnects
  have hRold : R'.vertexSet ⊆ oldRegion (V := V) (X := X) :=
    GraphPath.vertexSet_subset_oldRegion R' hRsource hRtarget
  let Q := GraphPath.projectOld R' hRold
  refine ⟨Q, ?_, ?_, ?_⟩
  · change oldRegionValue (X := X)
      ⟨R'.source, hRold R'.source_mem_vertexSet⟩ = a.1
    apply old_injective (V := V) (X := X)
    rw [old_oldRegionValue (X := X)]
    exact hRsource
  · change oldRegionValue (X := X)
      ⟨R'.target, hRold R'.target_mem_vertexSet⟩ = b
    apply old_injective (V := V) (X := X)
    rw [old_oldRegionValue (X := X)]
    exact hRtarget
  · intro x hx
    have hxR : old (X := X) x ∈ R'.vertexSet :=
      (GraphPath.mem_projectOld_vertexSet_iff R' hRold x).mp hx
    exact hRsub (by simpa [R'] using hxR)

/-- Project a perfect packing whose sources are pendant copies and whose
targets are old vertices.  The index type is unchanged, and every projected
path is a segment of the corresponding pendant path.

This is the formal inverse to `prependLeafSourcesPerfectPathPacking` used
after the artificial-source application of Lemma 2.19. -/
noncomputable def PerfectPathPacking.projectSourceLeaves
    {U : Finset V} (hU : U ⊆ X)
    {B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G)
      (leavesOf (X := X) U hU) B)
    (hB : B ⊆ oldRegion (V := V) (X := X)) :
    PerfectPathPacking G U (projectOldSet (X := X) B) := by
  let sourceBase : P.Index → {x : V // x ∈ U} :=
    fun i => leavesOfValue U hU (P.source_mem i)
  let targetBase : P.Index → V :=
    fun i => oldRegionValue (X := X)
      ⟨(P.path i).target, hB (P.target_mem i)⟩
  have hsource :
      ∀ i, (P.path i).source =
        leaf
          (⟨(sourceBase i).1, hU (sourceBase i).2⟩ :
            {x : V // x ∈ X}) := by
    intro i
    exact leavesOfValue_spec U hU (P.source_mem i)
  have htarget :
      ∀ i, (P.path i).target =
        old (X := X) (targetBase i) := by
    intro i
    exact (old_oldRegionValue (X := X)
      ⟨(P.path i).target, hB (P.target_mem i)⟩).symm
  let projected : ∀ i : P.Index, Lax17Proofs.SimpleGraph.GraphPath G :=
    fun i => Classical.choose
      (GraphPath.exists_projected_of_source_leaf_target_old
        (P.path i)
        (⟨(sourceBase i).1, hU (sourceBase i).2⟩ :
          {x : V // x ∈ X})
        (targetBase i) (hsource i) (htarget i))
  have hprojected :
      ∀ i,
        (projected i).source = (sourceBase i).1 ∧
          (projected i).target = targetBase i ∧
            ∀ x ∈ (projected i).vertexSet,
              old (X := X) x ∈ (P.path i).vertexSet := by
    intro i
    exact Classical.choose_spec
      (GraphPath.exists_projected_of_source_leaf_target_old
        (P.path i)
        (⟨(sourceBase i).1, hU (sourceBase i).2⟩ :
          {x : V // x ∈ X})
        (targetBase i) (hsource i) (htarget i))
  exact {
    toPathPacking := {
      Index := P.Index
      path := projected
      connects := by
        intro i
        exact Or.inl
          ⟨by simpa [hprojected i |>.1] using (sourceBase i).2,
            by
              apply mem_projectOldSet.mpr
              rw [hprojected i |>.2.1, ← htarget i]
              exact P.target_mem i⟩
      node_disjoint := by
        intro i j hij
        rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro x hxi hxj
        exact Finset.disjoint_left.mp (P.node_disjoint hij)
          (hprojected i |>.2.2 x hxi)
          (hprojected j |>.2.2 x hxj) }
    source_mem := by
      intro i
      simpa [hprojected i |>.1] using (sourceBase i).2
    target_mem := by
      intro i
      apply mem_projectOldSet.mpr
      rw [hprojected i |>.2.1, ← htarget i]
      exact P.target_mem i
    source_bijective := by
      constructor
      · intro i j hij
        apply P.source_bijective.1
        apply Subtype.ext
        have hbase :
            (sourceBase i).1 = (sourceBase j).1 := by
          have := congrArg Subtype.val hij
          simpa [hprojected i |>.1, hprojected j |>.1] using this
        calc
          (P.path i).source =
              leaf
                (⟨(sourceBase i).1, hU (sourceBase i).2⟩ :
                  {x : V // x ∈ X}) := hsource i
          _ = leaf
                (⟨(sourceBase j).1, hU (sourceBase j).2⟩ :
                  {x : V // x ∈ X}) := by
                    exact congrArg leaf (Subtype.ext hbase)
          _ = (P.path j).source := (hsource j).symm
      · intro x
        let z : ChekuriChuzhoyPendantVertex V X :=
          leaf (⟨x.1, hU x.2⟩ : {x : V // x ∈ X})
        have hz :
            z ∈ leavesOf (X := X) U hU := by
          exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
        rcases P.source_bijective.2 ⟨z, hz⟩ with ⟨i, hi⟩
        refine ⟨i, Subtype.ext ?_⟩
        have hleaf :
            leaf
                (⟨(sourceBase i).1, hU (sourceBase i).2⟩ :
                  {x : V // x ∈ X}) =
              leaf (⟨x.1, hU x.2⟩ : {x : V // x ∈ X}) := by
          calc
            _ = (P.path i).source := (hsource i).symm
            _ = z := congrArg Subtype.val hi
            _ = _ := rfl
        have hbase : (sourceBase i).1 = x.1 := by
          injection hleaf with hsub
          exact congrArg
            (fun q : {x : V // x ∈ X} => q.1) hsub
        simpa [hprojected i |>.1] using hbase
    target_bijective := by
      constructor
      · intro i j hij
        apply P.target_bijective.1
        apply Subtype.ext
        have hbase : targetBase i = targetBase j := by
          have := congrArg Subtype.val hij
          simpa [hprojected i |>.2.1, hprojected j |>.2.1] using this
        calc
          (P.path i).target = old (X := X) (targetBase i) := htarget i
          _ = old (X := X) (targetBase j) := congrArg (old (X := X)) hbase
          _ = (P.path j).target := (htarget j).symm
      · intro x
        have hxB : old (X := X) x.1 ∈ B := mem_projectOldSet.mp x.2
        rcases P.target_bijective.2
            ⟨old (X := X) x.1, hxB⟩ with ⟨i, hi⟩
        refine ⟨i, Subtype.ext ?_⟩
        apply old_injective (V := V) (X := X)
        calc
          old (X := X) (projected i).target =
              old (X := X) (targetBase i) :=
                congrArg (old (X := X)) (hprojected i |>.2.1)
          _ = (P.path i).target := (htarget i).symm
          _ = old (X := X) x.1 := congrArg Subtype.val hi }

theorem PerfectPathPacking.projectSourceLeaves_path_lifts
    {U : Finset V} (hU : U ⊆ X)
    {B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G)
      (leavesOf (X := X) U hU) B)
    (hB : B ⊆ oldRegion (V := V) (X := X))
    (i : (PerfectPathPacking.projectSourceLeaves hU P hB).Index) :
    ∀ x ∈
        (PerfectPathPacking.projectSourceLeaves hU P hB).path i |>.vertexSet,
      old (X := X) x ∈ (P.path i).vertexSet := by
  classical
  exact
    (Classical.choose_spec
      (GraphPath.exists_projected_of_source_leaf_target_old
        (P.path i)
        (⟨(leavesOfValue U hU (P.source_mem i)).1,
          hU (leavesOfValue U hU (P.source_mem i)).2⟩ :
          {x : V // x ∈ X})
        (oldRegionValue (X := X)
          ⟨(P.path i).target, hB (P.target_mem i)⟩)
        (leavesOfValue_spec U hU (P.source_mem i))
        ((old_oldRegionValue (X := X)
          ⟨(P.path i).target, hB (P.target_mem i)⟩).symm))).2.2

theorem PerfectPathPacking.projectSourceLeaves_target_lifts
    {U : Finset V} (hU : U ⊆ X)
    {B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G)
      (leavesOf (X := X) U hU) B)
    (hB : B ⊆ oldRegion (V := V) (X := X))
    (i : (PerfectPathPacking.projectSourceLeaves hU P hB).Index) :
    old (X := X)
        ((PerfectPathPacking.projectSourceLeaves hU P hB).path i).target =
      (P.path i).target := by
  classical
  have htarget :
      ((PerfectPathPacking.projectSourceLeaves hU P hB).path i).target =
        oldRegionValue (X := X)
          ⟨(P.path i).target, hB (P.target_mem i)⟩ :=
    (Classical.choose_spec
      (GraphPath.exists_projected_of_source_leaf_target_old
        (P.path i)
        (⟨(leavesOfValue U hU (P.source_mem i)).1,
          hU (leavesOfValue U hU (P.source_mem i)).2⟩ :
          {x : V // x ∈ X})
        (oldRegionValue (X := X)
          ⟨(P.path i).target, hB (P.target_mem i)⟩)
        (leavesOfValue_spec U hU (P.source_mem i))
        ((old_oldRegionValue (X := X)
          ⟨(P.path i).target, hB (P.target_mem i)⟩).symm))).2.1
  rw [htarget, old_oldRegionValue (X := X)]

/-- Project a perfect packing between two finite subsets of pendant leaves.
The endpoint sets are converted with `baseSet`, and every projected path is a
segment of its pendant counterpart. -/
noncomputable def PerfectPathPacking.projectLeafEndpoints
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G) S T)
    (hS : S ⊆ leaves (V := V) (X := X))
    (hT : T ⊆ leaves (V := V) (X := X))
    (hST : Disjoint S T) :
    PerfectPathPacking G (baseSet S hS) (baseSet T hT) := by
  let sourceValue : P.Index → {x : V // x ∈ X} :=
    fun i => leafValue (hS (P.source_mem i))
  let targetValue : P.Index → {x : V // x ∈ X} :=
    fun i => leafValue (hT (P.target_mem i))
  have hsource :
      ∀ i, (P.path i).source = leaf (sourceValue i) := by
    intro i
    exact leafValue_spec (hS (P.source_mem i))
  have htarget :
      ∀ i, (P.path i).target = leaf (targetValue i) := by
    intro i
    exact leafValue_spec (hT (P.target_mem i))
  have hne : ∀ i, (P.path i).source ≠ (P.path i).target := by
    intro i heq
    have hst : (P.path i).source ∈ S := P.source_mem i
    have htt : (P.path i).target ∈ T := P.target_mem i
    exact Finset.disjoint_left.mp
      hST hst (by simpa [heq] using htt)
  let projected : ∀ i : P.Index, Lax17Proofs.SimpleGraph.GraphPath G :=
    fun i => Classical.choose
      (GraphPath.exists_projected_of_leaf_endpoints
        (P.path i) (sourceValue i) (targetValue i)
        (hsource i) (htarget i) (hne i))
  have hprojected :
      ∀ i,
        (projected i).source = (sourceValue i).1 ∧
          (projected i).target = (targetValue i).1 ∧
            ∀ x ∈ (projected i).vertexSet,
              old (X := X) x ∈ (P.path i).vertexSet := by
    intro i
    exact Classical.choose_spec
      (GraphPath.exists_projected_of_leaf_endpoints
        (P.path i) (sourceValue i) (targetValue i)
        (hsource i) (htarget i) (hne i))
  exact {
    toPathPacking := {
      Index := P.Index
      path := projected
      connects := by
        intro i
        exact Or.inl
          ⟨by
              apply Finset.mem_image.mpr
              refine ⟨⟨(P.path i).source, P.source_mem i⟩, by simp, ?_⟩
              simpa [sourceValue, hprojected i |>.1],
            by
              apply Finset.mem_image.mpr
              refine ⟨⟨(P.path i).target, P.target_mem i⟩, by simp, ?_⟩
              simpa [targetValue, hprojected i |>.2.1]⟩
      node_disjoint := by
        intro i j hij
        rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro x hxi hxj
        exact Finset.disjoint_left.mp (P.node_disjoint hij)
          (hprojected i |>.2.2 x hxi)
          (hprojected j |>.2.2 x hxj) }
    source_mem := by
      intro i
      apply Finset.mem_image.mpr
      refine ⟨⟨(P.path i).source, P.source_mem i⟩, by simp, ?_⟩
      simpa [sourceValue, hprojected i |>.1]
    target_mem := by
      intro i
      apply Finset.mem_image.mpr
      refine ⟨⟨(P.path i).target, P.target_mem i⟩, by simp, ?_⟩
      simpa [targetValue, hprojected i |>.2.1]
    source_bijective := by
      constructor
      · intro i j hij
        apply P.source_bijective.1
        apply Subtype.ext
        have hbase : (sourceValue i).1 = (sourceValue j).1 := by
          have := congrArg Subtype.val hij
          simpa [hprojected i |>.1, hprojected j |>.1] using this
        calc
          (P.path i).source = leaf (sourceValue i) := hsource i
          _ = leaf (sourceValue j) := by
            exact congrArg leaf (Subtype.ext hbase)
          _ = (P.path j).source := (hsource j).symm
      · intro x
        rcases Finset.mem_image.mp x.2 with ⟨z, _hz, hzx⟩
        rcases P.source_bijective.2
            ⟨z.1, z.2⟩ with ⟨i, hi⟩
        refine ⟨i, Subtype.ext ?_⟩
        have hzspec :
            z.1 = leaf (leafValue (hS z.2)) :=
          leafValue_spec (hS z.2)
        have hvalue :
            sourceValue i = leafValue (hS z.2) := by
          apply Subtype.ext
          have hsEq :
              (P.path i).source = z.1 := congrArg Subtype.val hi
          have :
              leaf (sourceValue i) =
                leaf (leafValue (hS z.2)) := by
            calc
              _ = (P.path i).source := (hsource i).symm
              _ = z.1 := hsEq
              _ = _ := hzspec
          injection this with hvalue
          exact congrArg Subtype.val hvalue
        calc
          (projected i).source = (sourceValue i).1 :=
            hprojected i |>.1
          _ = (leafValue (hS z.2)).1 := congrArg Subtype.val hvalue
          _ = x.1 := hzx
    target_bijective := by
      constructor
      · intro i j hij
        apply P.target_bijective.1
        apply Subtype.ext
        have hbase : (targetValue i).1 = (targetValue j).1 := by
          have := congrArg Subtype.val hij
          simpa [hprojected i |>.2.1, hprojected j |>.2.1] using this
        calc
          (P.path i).target = leaf (targetValue i) := htarget i
          _ = leaf (targetValue j) := by
            exact congrArg leaf (Subtype.ext hbase)
          _ = (P.path j).target := (htarget j).symm
      · intro x
        rcases Finset.mem_image.mp x.2 with ⟨z, _hz, hzx⟩
        rcases P.target_bijective.2
            ⟨z.1, z.2⟩ with ⟨i, hi⟩
        refine ⟨i, Subtype.ext ?_⟩
        have hzspec :
            z.1 = leaf (leafValue (hT z.2)) :=
          leafValue_spec (hT z.2)
        have hvalue :
            targetValue i = leafValue (hT z.2) := by
          apply Subtype.ext
          have htEq :
              (P.path i).target = z.1 := congrArg Subtype.val hi
          have :
              leaf (targetValue i) =
                leaf (leafValue (hT z.2)) := by
            calc
              _ = (P.path i).target := (htarget i).symm
              _ = z.1 := htEq
              _ = _ := hzspec
          injection this with hvalue
          exact congrArg Subtype.val hvalue
        calc
          (projected i).target = (targetValue i).1 :=
            hprojected i |>.2.1
          _ = (leafValue (hT z.2)).1 := congrArg Subtype.val hvalue
          _ = x.1 := hzx }

theorem PerfectPathPacking.projectLeafEndpoints_path_lifts
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G) S T)
    (hS : S ⊆ leaves (V := V) (X := X))
    (hT : T ⊆ leaves (V := V) (X := X))
    (hST : Disjoint S T)
    (i : (PerfectPathPacking.projectLeafEndpoints P hS hT hST).Index) :
    ∀ x ∈
        (PerfectPathPacking.projectLeafEndpoints P hS hT hST).path i |>.vertexSet,
      old (X := X) x ∈ (P.path i).vertexSet := by
  classical
  exact
    (Classical.choose_spec
      (GraphPath.exists_projected_of_leaf_endpoints
        (P.path i)
        (leafValue (hS (P.source_mem i)))
        (leafValue (hT (P.target_mem i)))
        (leafValue_spec (hS (P.source_mem i)))
        (leafValue_spec (hT (P.target_mem i)))
        (by
          intro heq
          exact Finset.disjoint_left.mp
            hST
            (P.source_mem i) (by simpa [heq] using P.target_mem i)))).2.2

/-- Project an old-copy path packing back to `G`. -/
noncomputable def PathPacking.projectOld
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PathPacking (graph (X := X) G) S T)
    (hP : P.StaysIn (oldRegion (V := V) (X := X))) :
    PathPacking G (projectOldSet (X := X) S) (projectOldSet (X := X) T) where
  Index := P.Index
  path := fun i => GraphPath.projectOld (P.path i) (hP i)
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨mem_projectOldSet.mpr (by
        rw [GraphPath.projectOld_source, old_oldRegionValue (X := X)]
        exact h.1),
        mem_projectOldSet.mpr (by
          rw [GraphPath.projectOld_target, old_oldRegionValue (X := X)]
          exact h.2)⟩
    · exact Or.inr ⟨mem_projectOldSet.mpr (by
        rw [GraphPath.projectOld_source, old_oldRegionValue (X := X)]
        exact h.1),
        mem_projectOldSet.mpr (by
          rw [GraphPath.projectOld_target, old_oldRegionValue (X := X)]
          exact h.2)⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxi hxj
    exact Finset.disjoint_left.mp (P.node_disjoint hij)
      ((GraphPath.mem_projectOld_vertexSet_iff (P.path i) (hP i) x).mp hxi)
      ((GraphPath.mem_projectOld_vertexSet_iff (P.path j) (hP j) x).mp hxj)

@[simp] theorem PathPacking.projectOld_card
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PathPacking (graph (X := X) G) S T)
    (hP : P.StaysIn (oldRegion (V := V) (X := X))) :
    (PathPacking.projectOld P hP).card = P.card := rfl

theorem PathPacking.projectOld_staysIn
    {S T C : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PathPacking (graph (X := X) G) S T)
    (hP : P.StaysIn C) (hC : C ⊆ oldRegion (V := V) (X := X)) :
    (PathPacking.projectOld P (fun i => subset_trans (hP i) hC)).StaysIn
      (projectOldSet (X := X) C) := by
  intro i x hx
  exact mem_projectOldSet.mpr
    ((GraphPath.mem_projectOld_vertexSet_iff _ _ x).mp hx |> hP i)

/-- Project an old-copy perfect path packing back to `G`, preserving its index
type and endpoint bijections. -/
noncomputable def PerfectPathPacking.projectOld
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G) S T)
    (hP : P.toPathPacking.StaysIn (oldRegion (V := V) (X := X))) :
    PerfectPathPacking G
      (projectOldSet (X := X) S) (projectOldSet (X := X) T) where
  toPathPacking := PathPacking.projectOld P.toPathPacking hP
  source_mem := by
    intro i
    apply mem_projectOldSet.mpr
    change old (X := X)
      (GraphPath.projectOld (P.path i) (hP i)).source ∈ S
    rw [GraphPath.projectOld_source, old_oldRegionValue (X := X)]
    exact P.source_mem i
  target_mem := by
    intro i
    apply mem_projectOldSet.mpr
    change old (X := X)
      (GraphPath.projectOld (P.path i) (hP i)).target ∈ T
    rw [GraphPath.projectOld_target, old_oldRegionValue (X := X)]
    exact P.target_mem i
  source_bijective := by
    constructor
    · intro i j hij
      apply P.source_bijective.1
      apply Subtype.ext
      have hvalue :
          (GraphPath.projectOld (P.path i) (hP i)).source =
            (GraphPath.projectOld (P.path j) (hP j)).source :=
        congrArg Subtype.val hij
      have hold := congrArg (old (X := X)) hvalue
      simpa [GraphPath.projectOld_source, old_oldRegionValue] using hold
    · intro x
      have hxS : old (X := X) x.1 ∈ S := mem_projectOldSet.mp x.2
      rcases P.source_bijective.2 ⟨old (X := X) x.1, hxS⟩ with ⟨i, hi⟩
      refine ⟨i, Subtype.ext ?_⟩
      apply old_injective (V := V) (X := X)
      change old (X := X)
        (GraphPath.projectOld (P.path i) (hP i)).source = old (X := X) x.1
      rw [GraphPath.projectOld_source, old_oldRegionValue (X := X)]
      exact congrArg Subtype.val hi
  target_bijective := by
    constructor
    · intro i j hij
      apply P.target_bijective.1
      apply Subtype.ext
      have hvalue :
          (GraphPath.projectOld (P.path i) (hP i)).target =
            (GraphPath.projectOld (P.path j) (hP j)).target :=
        congrArg Subtype.val hij
      have hold := congrArg (old (X := X)) hvalue
      simpa [GraphPath.projectOld_target, old_oldRegionValue] using hold
    · intro x
      have hxT : old (X := X) x.1 ∈ T := mem_projectOldSet.mp x.2
      rcases P.target_bijective.2 ⟨old (X := X) x.1, hxT⟩ with ⟨i, hi⟩
      refine ⟨i, Subtype.ext ?_⟩
      apply old_injective (V := V) (X := X)
      change old (X := X)
        (GraphPath.projectOld (P.path i) (hP i)).target = old (X := X) x.1
      rw [GraphPath.projectOld_target, old_oldRegionValue (X := X)]
      exact congrArg Subtype.val hi

@[simp] theorem PerfectPathPacking.projectOld_card
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G) S T)
    (hP : P.toPathPacking.StaysIn (oldRegion (V := V) (X := X))) :
    (PerfectPathPacking.projectOld P hP).card = P.card := rfl

theorem PerfectPathPacking.projectOld_staysIn
    {S T C : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G) S T)
    (hP : P.toPathPacking.StaysIn C)
    (hC : C ⊆ oldRegion (V := V) (X := X)) :
    (PerfectPathPacking.projectOld P
      (fun i => subset_trans (hP i) hC)).toPathPacking.StaysIn
        (projectOldSet (X := X) C) :=
  PathPacking.projectOld_staysIn P.toPathPacking hP hC

/-- Internal disjointness is reflected by old-copy projection. -/
theorem PerfectPathPacking.projectOld_internallyDisjointFromSet
    {S T C : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G) S T)
    (hP : P.toPathPacking.StaysIn (oldRegion (V := V) (X := X)))
    (hInt : P.toPathPacking.InternallyDisjointFromSet C) :
    PathPacking.InternallyDisjointFromSet
      (PerfectPathPacking.projectOld P hP).toPathPacking
      (projectOldSet (X := X) C) := by
  intro i x hxPath hxC
  have hxPathOld : old (X := X) x ∈ (P.path i).vertexSet :=
    (GraphPath.mem_projectOld_vertexSet_iff (P.path i) (hP i) x).mp hxPath
  have hxCOld : old (X := X) x ∈ C := mem_projectOldSet.mp hxC
  rcases hInt i hxPathOld hxCOld with hs | ht
  · apply Or.inl
    apply old_injective (V := V) (X := X)
    change old (X := X) x =
      old (X := X) (GraphPath.projectOld (P.path i) (hP i)).source
    rw [GraphPath.projectOld_source, old_oldRegionValue (X := X)]
    exact hs
  · apply Or.inr
    apply old_injective (V := V) (X := X)
    change old (X := X) x =
      old (X := X) (GraphPath.projectOld (P.path i) (hP i)).target
    rw [GraphPath.projectOld_target, old_oldRegionValue (X := X)]
    exact ht

/-- Mutual node-disjointness of two old-copy perfect packings survives
projection. -/
theorem PerfectPathPacking.projectOld_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : PerfectPathPacking (graph (X := X) G) S₁ T₁)
    (Q : PerfectPathPacking (graph (X := X) G) S₂ T₂)
    (hP : P.toPathPacking.StaysIn (oldRegion (V := V) (X := X)))
    (hQ : Q.toPathPacking.StaysIn (oldRegion (V := V) (X := X)))
    (hPQ : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    (PerfectPathPacking.projectOld P hP).toPathPacking.MutuallyNodeDisjoint
      (PerfectPathPacking.projectOld Q hQ).toPathPacking := by
  intro i j
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro x hxP hxQ
  exact Finset.disjoint_left.mp (hPQ i j)
    ((GraphPath.mem_projectOld_vertexSet_iff (P.path i) (hP i) x).mp hxP)
    ((GraphPath.mem_projectOld_vertexSet_iff (Q.path j) (hQ j) x).mp hxQ)

/-- The subgraph induced by an old-only finite set is isomorphic to the
subgraph of `G` induced by its projection. -/
noncomputable def projectOldInducedIso
    (G : _root_.SimpleGraph V)
    (A : Finset (ChekuriChuzhoyPendantVertex V X))
    (hA : A ⊆ oldRegion (V := V) (X := X)) :
    (graph (X := X) G).induce
        {z : ChekuriChuzhoyPendantVertex V X | z ∈ A} ≃g
      G.induce {x : V | x ∈ projectOldSet (X := X) A} where
  toFun := fun z =>
    ⟨oldRegionValue (X := X) ⟨z.1, hA z.2⟩, by
      apply mem_projectOldSet.mpr
      rw [old_oldRegionValue (X := X)]
      exact z.2⟩
  invFun := fun x =>
    ⟨old (X := X) x.1, mem_projectOldSet.mp x.2⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact old_oldRegionValue (X := X) ⟨z.1, hA z.2⟩
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  map_rel_iff' := by
    intro a b
    change G.Adj
        (oldRegionValue (X := X) ⟨a.1, hA a.2⟩)
        (oldRegionValue (X := X) ⟨b.1, hA b.2⟩) ↔
      (graph (X := X) G).Adj a.1 b.1
    rw [← adj_old_old_iff]
    have ha := old_oldRegionValue (X := X) ⟨a.1, hA a.2⟩
    have hb := old_oldRegionValue (X := X) ⟨b.1, hA b.2⟩
    rw [ha, hb]

theorem isCluster_projectOld
    (A : Finset (ChekuriChuzhoyPendantVertex V X))
    (hA : A ⊆ oldRegion (V := V) (X := X))
    (hcluster : IsCluster (graph (X := X) G) A) :
    IsCluster G (projectOldSet (X := X) A) := by
  exact ((projectOldInducedIso (X := X) G A hA).connected_iff).mp hcluster

variable {m w : ℕ}

/-- Every connector of a tree-of-sets system with old-only clusters is itself
entirely contained in the old-copy region. -/
theorem TreeOfSetsSystem.connector_staysIn_oldRegion
    (T : TreeOfSetsSystem (graph (X := X) G) m w)
    (hcluster : ∀ i, T.cluster i ⊆ oldRegion (V := V) (X := X))
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    (T.connector i j hij).toPathPacking.StaysIn
      (oldRegion (V := V) (X := X)) := by
  intro a
  apply GraphPath.vertexSet_subset_oldRegion_of_isOld_endpoints
  · apply (mem_oldRegion_iff_isOld _).mp
    exact hcluster i
      (T.interface_subset_cluster i j hij ((T.connector i j hij).source_mem a))
  · apply (mem_oldRegion_iff_isOld _).mp
    exact hcluster j
      (T.interface_subset_cluster j i (T.metaTree.symm hij)
        ((T.connector i j hij).target_mem a))

/-- Transport an ordinary tree-of-sets system whose clusters avoid all
pendant leaves back to the original graph. -/
noncomputable def TreeOfSetsSystem.projectOld
    (T : TreeOfSetsSystem (graph (X := X) G) m w)
    (hcluster : ∀ i, T.cluster i ⊆ oldRegion (V := V) (X := X)) :
    TreeOfSetsSystem G m w where
  clusterCount_pos := T.clusterCount_pos
  width_pos := T.width_pos
  metaTree := T.metaTree
  meta_isTree := T.meta_isTree
  meta_maxDegree_three := T.meta_maxDegree_three
  cluster := fun i => projectOldSet (X := X) (T.cluster i)
  cluster_connected := by
    intro i
    exact isCluster_projectOld (T.cluster i) (hcluster i) (T.cluster_connected i)
  cluster_disjoint := by
    intro i j hij
    exact projectOldSet_disjoint (T.cluster_disjoint hij)
  interface := fun i j hij => projectOldSet (X := X) (T.interface i j hij)
  interface_subset_cluster := by
    intro i j hij
    exact projectOldSet_subset (T.interface_subset_cluster i j hij)
  interface_card := by
    intro i j hij
    rw [projectOldSet_card
      (subset_trans (T.interface_subset_cluster i j hij) (hcluster i))]
    exact T.interface_card i j hij
  interface_disjoint := by
    intro i j k hij hik hjk
    exact projectOldSet_disjoint (T.interface_disjoint hij hik hjk)
  connector := fun i j hij =>
    PerfectPathPacking.projectOld (T.connector i j hij)
      (TreeOfSetsSystem.connector_staysIn_oldRegion T hcluster i j hij)
  connector_card := by
    intro i j hij
    simpa using T.connector_card i j hij
  connector_internally_disjoint_clusters := by
    intro i j hij r a
    exact PerfectPathPacking.projectOld_internallyDisjointFromSet
      (T.connector i j hij)
      (TreeOfSetsSystem.connector_staysIn_oldRegion T hcluster i j hij)
      (T.connector_internally_disjoint_cluster i j hij r) a
  connector_mutually_nodeDisjoint := by
    intro i j hij p q hpq hedge
    exact PerfectPathPacking.projectOld_mutuallyNodeDisjoint
      (T.connector i j hij) (T.connector p q hpq)
      (TreeOfSetsSystem.connector_staysIn_oldRegion T hcluster i j hij)
      (TreeOfSetsSystem.connector_staysIn_oldRegion T hcluster p q hpq)
      (T.connector_mutually_nodeDisjoint i j hij p q hpq hedge)

theorem oldImage_subset_of_subset_projectOldSet
    {A : Finset V} {C : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hAC : A ⊆ projectOldSet (X := X) C) :
    oldImage (X := X) A ⊆ C := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
  exact mem_projectOldSet.mp (hAC hx)

theorem oldImage_disjoint
    {A B : Finset V} (hAB : Disjoint A B) :
    Disjoint (oldImage (X := X) A) (oldImage (X := X) B) := by
  rw [Finset.disjoint_left]
  intro z hzA hzB
  rcases Finset.mem_image.mp hzA with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hzB with ⟨b, hb, hab⟩
  have hab' : a = b := old_injective (V := V) (X := X) hab.symm
  exact Finset.disjoint_left.mp hAB ha (by simpa [hab'] using hb)

/-- Reinterpret a path packing after replacing its two terminal sets by equal
finite sets. -/
def PathPacking.copyTerminals
    {W : Type*} [DecidableEq W] {H : _root_.SimpleGraph W}
    {S T S' T' : Finset W} (P : PathPacking H S T)
    (hS : S = S') (hT : T = T') : PathPacking H S' T' where
  Index := P.Index
  path := P.path
  connects := by
    intro i
    simpa [← hS, ← hT] using P.connects i
  node_disjoint := P.node_disjoint

@[simp] theorem PathPacking.copyTerminals_card
    {W : Type*} [DecidableEq W] {H : _root_.SimpleGraph W}
    {S T S' T' : Finset W} (P : PathPacking H S T)
    (hS : S = S') (hT : T = T') :
    (PathPacking.copyTerminals P hS hT).card = P.card := rfl

theorem PathPacking.copyTerminals_staysIn
    {W : Type*} [DecidableEq W] {H : _root_.SimpleGraph W}
    {S T S' T' U : Finset W} (P : PathPacking H S T)
    (hS : S = S') (hT : T = T') (hP : P.StaysIn U) :
    (PathPacking.copyTerminals P hS hT).StaysIn U := hP

/-- Node-well-linkedness inside an old-only region projects to the original
graph. -/
theorem nodeWellLinkedIn_projectOld
    {C T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hC : C ⊆ oldRegion (V := V) (X := X))
    (hlinked : NodeWellLinkedIn (graph (X := X) G) C T) :
    NodeWellLinkedIn G
      (projectOldSet (X := X) C) (projectOldSet (X := X) T) := by
  constructor
  · exact projectOldSet_subset hlinked.1
  · intro A B hA hB hAB
    have hAold : oldImage (X := X) A ⊆ T :=
      oldImage_subset_of_subset_projectOldSet hA
    have hBold : oldImage (X := X) B ⊆ T :=
      oldImage_subset_of_subset_projectOldSet hB
    have hdisj : Disjoint (oldImage (X := X) A) (oldImage (X := X) B) :=
      oldImage_disjoint hAB
    rcases hlinked.2 hAold hBold hdisj with ⟨P, hcard, hstay⟩
    let R := PathPacking.projectOld P (fun i => subset_trans (hstay i) hC)
    let Q : PathPacking G A B := PathPacking.copyTerminals R
      (projectOldSet_oldImage (X := X) A)
      (projectOldSet_oldImage (X := X) B)
    refine ⟨Q, ?_, ?_⟩
    · change R.card = min A.card B.card
      have hcard' : P.card = min A.card B.card := by simpa using hcard
      exact (PathPacking.projectOld_card P _).trans hcard'
    · change R.StaysIn (projectOldSet (X := X) C)
      exact PathPacking.projectOld_staysIn P hstay hC

/-- Node-linkedness of two terminal sets inside an old-only region projects to
the original graph. -/
theorem nodeLinkedIn_projectOld
    {C A B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hC : C ⊆ oldRegion (V := V) (X := X))
    (hlinked : NodeLinkedIn (graph (X := X) G) C A B) :
    NodeLinkedIn G (projectOldSet (X := X) C)
      (projectOldSet (X := X) A) (projectOldSet (X := X) B) := by
  refine ⟨projectOldSet_subset hlinked.1,
    projectOldSet_subset hlinked.2.1,
    projectOldSet_disjoint hlinked.2.2.1, ?_⟩
  intro A' B' hA' hB'
  have hAold : oldImage (X := X) A' ⊆ A :=
    oldImage_subset_of_subset_projectOldSet hA'
  have hBold : oldImage (X := X) B' ⊆ B :=
    oldImage_subset_of_subset_projectOldSet hB'
  rcases hlinked.2.2.2 hAold hBold with ⟨P, hcard, hstay⟩
  let R := PathPacking.projectOld P (fun i => subset_trans (hstay i) hC)
  let Q : PathPacking G A' B' := PathPacking.copyTerminals R
    (projectOldSet_oldImage (X := X) A')
    (projectOldSet_oldImage (X := X) B')
  refine ⟨Q, ?_, ?_⟩
  · change R.card = min A'.card B'.card
    have hcard' : P.card = min A'.card B'.card := by simpa using hcard
    exact (PathPacking.projectOld_card P _).trans hcard'
  · change R.StaysIn (projectOldSet (X := X) C)
    exact PathPacking.projectOld_staysIn P hstay hC

/-- Transport the full strong tree-of-sets record out of the pendant
extension.  Positivity, the meta-tree, widths, connector indices, and all
strong linkage properties are preserved. -/
noncomputable def StrongTreeOfSetsSystem.projectOld
    (T : StrongTreeOfSetsSystem (graph (X := X) G) m w)
    (hcluster : ∀ i, T.cluster i ⊆ oldRegion (V := V) (X := X)) :
    StrongTreeOfSetsSystem G m w where
  toTreeOfSetsSystem :=
    TreeOfSetsSystem.projectOld T.toTreeOfSetsSystem hcluster
  interface_nodeWellLinked := by
    intro i j hij
    exact nodeWellLinkedIn_projectOld (hcluster i)
      (T.interface_nodeWellLinked i j hij)
  interface_pair_nodeLinked := by
    intro i j k hij hik hjk
    exact nodeLinkedIn_projectOld (hcluster i)
      (T.interface_pair_nodeLinked hij hik hjk)

/-- Natural terminal-free form of ordinary tree-of-sets transport. -/
noncomputable def TreeOfSetsSystem.projectOldOfDisjointLeaves
    (T : TreeOfSetsSystem (graph (X := X) G) m w)
    (hterminalFree :
      ∀ i, Disjoint (T.cluster i) (leaves (V := V) (X := X))) :
    TreeOfSetsSystem G m w :=
  TreeOfSetsSystem.projectOld T fun i =>
    subset_oldRegion_of_disjoint_leaves (hterminalFree i)

/-- A terminal-free strong tree-of-sets system in the pendant extension
projects wholesale to a strong tree-of-sets system in the original graph. -/
noncomputable def StrongTreeOfSetsSystem.projectOldOfDisjointLeaves
    (T : StrongTreeOfSetsSystem (graph (X := X) G) m w)
    (hterminalFree :
      ∀ i, Disjoint (T.cluster i) (leaves (V := V) (X := X))) :
    StrongTreeOfSetsSystem G m w :=
  StrongTreeOfSetsSystem.projectOld T fun i =>
    subset_oldRegion_of_disjoint_leaves (hterminalFree i)

end ChekuriChuzhoyPendantVertex
end SimpleGraph

end Lax17Proofs
