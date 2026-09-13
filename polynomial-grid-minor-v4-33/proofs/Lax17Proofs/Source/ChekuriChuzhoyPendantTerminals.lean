import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Pendant normalization for one terminal set

This module packages the standard normalization used in Chekuri--Chuzhoy:
replace every terminal `x ∈ X` by a fresh degree-one vertex adjacent only to
`x`.  The construction is independent of the larger four-terminal
normalization in `TreewidthSparsifierSection2` and is intended for reuse when
normalizing a single node-well-linked terminal set.
-/

namespace SimpleGraph


/-- The vertices of the pendant extension of `G` at `X`: an old copy of every
vertex and one fresh leaf for every member of `X`. -/
inductive ChekuriChuzhoyPendantVertex (V : Type u) (X : Finset V) where
  | old : V → ChekuriChuzhoyPendantVertex V X
  | leaf : {x : V // x ∈ X} → ChekuriChuzhoyPendantVertex V X
deriving DecidableEq

namespace ChekuriChuzhoyPendantVertex

variable {V : Type u} [DecidableEq V] {X : Finset V}

instance [Fintype V] : Fintype (ChekuriChuzhoyPendantVertex V X) where
  elems :=
    (Finset.univ.image (old (X := X))) ∪
      (X.attach.image (leaf (V := V) (X := X)))
  complete := by
    intro z
    cases z with
    | old x => simp
    | leaf x => simp

/-- A directed presentation of the old edges and pendant edges.  `fromRel`
supplies symmetry and removes loops. -/
def rel (G : _root_.SimpleGraph V) :
    ChekuriChuzhoyPendantVertex V X →
      ChekuriChuzhoyPendantVertex V X → Prop
  | old x, old y => G.Adj x y
  | leaf x, old y => x.1 = y
  | _, _ => False

/-- Add one fresh pendant leaf adjacent to each vertex of `X`. -/
def graph (G : _root_.SimpleGraph V) :
    _root_.SimpleGraph (ChekuriChuzhoyPendantVertex V X) :=
  _root_.SimpleGraph.fromRel (rel (X := X) G)

/-- The old-copy image of a finite vertex set. -/
noncomputable def oldImage (A : Finset V) :
    Finset (ChekuriChuzhoyPendantVertex V X) :=
  A.image (old (X := X))

/-- The set of all fresh pendant terminals. -/
noncomputable def leaves : Finset (ChekuriChuzhoyPendantVertex V X) :=
  X.attach.image (leaf (V := V) (X := X))

@[simp] theorem leaves_card :
    (leaves (V := V) (X := X)).card = X.card := by
  classical
  rw [leaves, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    cases hxy
    rfl

@[simp] theorem oldImage_card (A : Finset V) :
    (oldImage (X := X) A).card = A.card := by
  classical
  rw [oldImage, Finset.card_image_of_injective]
  intro x y hxy
  cases hxy
  rfl

@[simp] theorem mem_oldImage {A : Finset V} {x : V} :
    old (X := X) x ∈ oldImage (X := X) A ↔ x ∈ A := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    cases hxy
    exact hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

@[simp] theorem mem_leaves {x : {x : V // x ∈ X}} :
    leaf x ∈ leaves (V := V) (X := X) := by
  classical
  exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

theorem exists_leafValue
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leaves (V := V) (X := X)) :
    ∃ x : {x : V // x ∈ X}, z = leaf x := by
  classical
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hxz⟩
  exact ⟨x, hxz.symm⟩

/-- Recover the base terminal represented by a member of `leaves`. -/
noncomputable def leafValue
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leaves (V := V) (X := X)) : {x : V // x ∈ X} :=
  Classical.choose (exists_leafValue hz)

theorem leafValue_spec
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leaves (V := V) (X := X)) :
    z = leaf (leafValue hz) :=
  Classical.choose_spec (exists_leafValue hz)

/-- Project a finite subset of fresh leaves to its original terminals. -/
noncomputable def baseSet
    (A : Finset (ChekuriChuzhoyPendantVertex V X))
    (hA : A ⊆ leaves (V := V) (X := X)) : Finset V :=
  A.attach.image fun z => (leafValue (hA z.2)).1

theorem baseSet_subset
    (A : Finset (ChekuriChuzhoyPendantVertex V X))
    (hA : A ⊆ leaves (V := V) (X := X)) :
    baseSet A hA ⊆ X := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨z, _hz, rfl⟩
  exact (leafValue (hA z.2)).2

@[simp] theorem baseSet_card
    (A : Finset (ChekuriChuzhoyPendantVertex V X))
    (hA : A ⊆ leaves (V := V) (X := X)) :
    (baseSet A hA).card = A.card := by
  classical
  rw [baseSet, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Subtype.ext
    have hvalue : leafValue (hA a.2) = leafValue (hA b.2) :=
      Subtype.ext hab
    calc
      a.1 = leaf (leafValue (hA a.2)) := leafValue_spec (hA a.2)
      _ = leaf (leafValue (hA b.2)) := congrArg leaf hvalue
      _ = b.1 := (leafValue_spec (hA b.2)).symm

theorem baseSet_disjoint
    {A B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hA : A ⊆ leaves (V := V) (X := X))
    (hB : B ⊆ leaves (V := V) (X := X))
    (hAB : Disjoint A B) :
    Disjoint (baseSet A hA) (baseSet B hB) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxA hxB
  rcases Finset.mem_image.mp hxA with ⟨a, _ha, hax⟩
  rcases Finset.mem_image.mp hxB with ⟨b, _hb, hbx⟩
  have hvalue : leafValue (hA a.2) = leafValue (hB b.2) := by
    apply Subtype.ext
    exact hax.trans hbx.symm
  have hab : a.1 = b.1 := by
    calc
      a.1 = leaf (leafValue (hA a.2)) := leafValue_spec (hA a.2)
      _ = leaf (leafValue (hB b.2)) := congrArg leaf hvalue
      _ = b.1 := (leafValue_spec (hB b.2)).symm
  exact Finset.disjoint_left.mp hAB a.2 (by simpa [hab] using b.2)

@[simp] theorem graph_adj {G : _root_.SimpleGraph V}
    {a b : ChekuriChuzhoyPendantVertex V X} :
    (graph (X := X) G).Adj a b ↔
      a ≠ b ∧ (rel (X := X) G a b ∨ rel (X := X) G b a) :=
  Iff.rfl

@[simp] theorem adj_old_old_iff {G : _root_.SimpleGraph V} {x y : V} :
    (graph (X := X) G).Adj (old x) (old y) ↔ G.Adj x y := by
  rw [graph_adj]
  constructor
  · rintro ⟨_hne, hxy | hyx⟩
    · exact hxy
    · exact hyx.symm
  · intro hxy
    exact ⟨by
      intro h
      cases h
      exact hxy.ne rfl,
      Or.inl hxy⟩

@[simp] theorem adj_leaf_iff {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ X})
    {y : ChekuriChuzhoyPendantVertex V X} :
    (graph (X := X) G).Adj (leaf x) y ↔ y = old x.1 := by
  constructor
  · intro hy
    rw [graph_adj] at hy
    rcases hy with ⟨_hne, hrel | hrel⟩
    · cases y <;> simp [rel] at hrel
      simpa using congrArg (old (X := X)) hrel.symm
    · cases y <;> simp [rel] at hrel
  · rintro rfl
    rw [graph_adj]
    constructor
    · intro h
      cases h
    · exact Or.inl rfl

@[simp] theorem adj_old_leaf_iff {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ X}) {y : V} :
    (graph (X := X) G).Adj (old y) (leaf x) ↔ y = x.1 := by
  rw [(graph (X := X) G).adj_comm, adj_leaf_iff]
  simp

/-- The old-copy inclusion is an injective graph homomorphism. -/
def oldHom (G : _root_.SimpleGraph V) : G →g graph (X := X) G where
  toFun := old (X := X)
  map_rel' := by
    intro x y hxy
    exact adj_old_old_iff.mpr hxy

theorem old_injective : Function.Injective (old (V := V) (X := X)) := by
  intro x y hxy
  cases hxy
  rfl

namespace GraphPath

/-- Map a bundled path along an injective graph homomorphism. -/
def mapHomInjective {W : Type*} [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (f : G →g H)
    (hf : Function.Injective f) : Lax17Proofs.SimpleGraph.GraphPath H where
  source := f P.source
  target := f P.target
  walk := P.walk.map f
  isPath := _root_.SimpleGraph.Walk.map_isPath_of_injective
    (f := f) hf P.isPath

@[simp] theorem mapHomInjective_vertexSet {W : Type*} [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (f : G →g H)
    (hf : Function.Injective f) :
    (mapHomInjective P f hf).vertexSet =
      P.vertexSet.image (fun x => f x) := by
  classical
  ext y
  simp [mapHomInjective, Lax17Proofs.SimpleGraph.GraphPath.vertexSet,
    _root_.SimpleGraph.Walk.support_map]

/-- The one-edge bundled path associated with an adjacency. -/
noncomputable def ofAdj {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) : Lax17Proofs.SimpleGraph.GraphPath G :=
  Lax17Proofs.SimpleGraph.GraphPath.ofWalk
    (_root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil)

@[simp] theorem ofAdj_source {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) : (ofAdj huv).source = u := rfl

@[simp] theorem ofAdj_target {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) : (ofAdj huv).target = v := rfl

theorem ofAdj_vertexSet_subset_pair {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) :
    (ofAdj huv).vertexSet ⊆ ({u, v} : Finset V) := by
  classical
  intro x hx
  have hxWalk :
      x ∈ ((_root_.SimpleGraph.Walk.cons huv
        _root_.SimpleGraph.Walk.nil).support.toFinset) :=
    Lax17Proofs.SimpleGraph.GraphPath.ofWalk_vertexSet_subset
      (_root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil) hx
  simpa [ofAdj] using hxWalk

theorem ofAdj_internallyDisjointFromSet
    {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (U : Finset V) :
    (ofAdj huv).InternallyDisjointFromSet U := by
  classical
  intro x hx _hxU
  have hxPair := ofAdj_vertexSet_subset_pair huv hx
  simp at hxPair
  rcases hxPair with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end GraphPath

/-- The leaf copy of a subset `U ⊆ X`. -/
noncomputable def leavesOf (U : Finset V) (hU : U ⊆ X) :
    Finset (ChekuriChuzhoyPendantVertex V X) :=
  U.attach.image fun x => leaf ⟨x.1, hU x.2⟩

@[simp] theorem leavesOf_card (U : Finset V) (hU : U ⊆ X) :
    (leavesOf (X := X) U hU).card = U.card := by
  classical
  rw [leavesOf, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    apply Subtype.ext
    injection hxy with hsub
    exact congrArg (fun q : {x : V // x ∈ X} => q.1) hsub

theorem leavesOf_subset_leaves (U : Finset V) (hU : U ⊆ X) :
    leavesOf (X := X) U hU ⊆ leaves (V := V) (X := X) := by
  classical
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
  exact mem_leaves

theorem exists_leavesOfValue
    (U : Finset V) (hU : U ⊆ X)
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leavesOf (X := X) U hU) :
    ∃ x : {x : V // x ∈ U},
      z = leaf (⟨x.1, hU x.2⟩ : {x : V // x ∈ X}) := by
  classical
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hzx⟩
  exact ⟨x, hzx.symm⟩

/-- Recover the original terminal represented by a member of `leavesOf U`. -/
noncomputable def leavesOfValue
    (U : Finset V) (hU : U ⊆ X)
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leavesOf (X := X) U hU) : {x : V // x ∈ U} :=
  Classical.choose (exists_leavesOfValue U hU hz)

theorem leavesOfValue_spec
    (U : Finset V) (hU : U ⊆ X)
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leavesOf (X := X) U hU) :
    z = leaf
      (⟨(leavesOfValue U hU hz).1, hU (leavesOfValue U hU hz).2⟩ :
        {x : V // x ∈ X}) :=
  Classical.choose_spec (exists_leavesOfValue U hU hz)

theorem leavesOf_baseSet_subset
    (A : Finset (ChekuriChuzhoyPendantVertex V X))
    (hA : A ⊆ leaves (V := V) (X := X))
    (U : Finset V) (hU : U ⊆ baseSet A hA) :
    leavesOf (X := X) U (subset_trans hU (baseSet_subset A hA)) ⊆ A := by
  classical
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨u, _hu, hzu⟩
  have huBase : u.1 ∈ baseSet A hA := hU u.2
  rcases Finset.mem_image.mp huBase with ⟨a, _ha, hau⟩
  have hvalue :
      (⟨u.1, (baseSet_subset A hA) (hU u.2)⟩ : {x : V // x ∈ X}) =
        leafValue (hA a.2) := by
    apply Subtype.ext
    exact hau.symm
  have hza : z = a.1 := by
    calc
      z = leaf ⟨u.1, (subset_trans hU (baseSet_subset A hA)) u.2⟩ := hzu.symm
      _ = leaf (leafValue (hA a.2)) := congrArg leaf hvalue
      _ = a.1 := (leafValue_spec (hA a.2)).symm
  simpa [hza] using a.2

theorem baseSet_subset_of_subset_leavesOf
    (A : Finset (ChekuriChuzhoyPendantVertex V X))
    (hA : A ⊆ leaves (V := V) (X := X))
    (U : Finset V) (hU : U ⊆ X)
    (hAU : A ⊆ leavesOf (X := X) U hU) :
    baseSet A hA ⊆ U := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨z, _hz, hzx⟩
  rcases Finset.mem_image.mp (hAU z.2) with ⟨u, _hu, hzu⟩
  have hzLeaf :
      z.1 = leaf (leafValue (hA z.2)) :=
    leafValue_spec (hA z.2)
  have hvalues :
      leafValue (hA z.2) =
        (⟨u.1, hU u.2⟩ : {x : V // x ∈ X}) := by
    apply Subtype.ext
    have := hzLeaf.symm.trans hzu.symm
    injection this with hsub
    exact congrArg Subtype.val hsub
  have hxU : x = u.1 := by
    exact hzx.symm.trans (congrArg Subtype.val hvalues)
  simpa [hxU] using u.2

theorem leavesOf_disjoint_oldImage (U A : Finset V) (hU : U ⊆ X) :
    Disjoint (leavesOf (X := X) U hU) (oldImage (X := X) A) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzLeaf hzOld
  rcases Finset.mem_image.mp hzLeaf with ⟨x, _hx, hzx⟩
  rcases Finset.mem_image.mp hzOld with ⟨y, _hy, hzy⟩
  rw [← hzx] at hzy
  cases hzy

/-- Map a perfect packing into the old-copy induced subgraph. -/
noncomputable def oldPerfectPathPacking
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B) :
    PerfectPathPacking (graph (X := X) G)
      (oldImage (X := X) A) (oldImage (X := X) B) where
  toPathPacking := {
    Index := P.Index
    path := fun i => GraphPath.mapHomInjective (P.path i)
      (oldHom (X := X) G) (old_injective (V := V) (X := X))
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr ⟨(P.path i).source, P.source_mem i, rfl⟩,
          Finset.mem_image.mpr ⟨(P.path i).target, P.target_mem i, rfl⟩⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      rw [GraphPath.mapHomInjective_vertexSet] at hzi hzj
      rcases Finset.mem_image.mp hzi with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hzj with ⟨y, hy, hyx⟩
      have hxy : x = y := old_injective (V := V) (X := X) hyx.symm
      exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij)
        hx (by simpa [hxy] using hy)
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨(P.path i).source, P.source_mem i, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨(P.path i).target, P.target_mem i, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      apply P.source_bijective.1
      apply Subtype.ext
      exact old_injective (V := V) (X := X) (congrArg Subtype.val hij)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      rcases P.source_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
      refine ⟨i, Subtype.ext ?_⟩
      have hsrc : (P.path i).source = v := congrArg Subtype.val hi
      exact (congrArg (old (X := X)) hsrc).trans hvx
  target_bijective := by
    classical
    constructor
    · intro i j hij
      apply P.target_bijective.1
      apply Subtype.ext
      exact old_injective (V := V) (X := X) (congrArg Subtype.val hij)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      rcases P.target_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
      refine ⟨i, Subtype.ext ?_⟩
      have htgt : (P.path i).target = v := congrArg Subtype.val hi
      exact (congrArg (old (X := X)) htgt).trans hvx

theorem oldPerfectPathPacking_staysIn
    [Fintype V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B) :
    (oldPerfectPathPacking (X := X) P).toPathPacking.StaysIn
      (oldImage (X := X) (Finset.univ : Finset V)) := by
  classical
  intro i z hz
  change z ∈ (GraphPath.mapHomInjective (P.path i)
    (oldHom (X := X) G) (old_injective (V := V) (X := X))).vertexSet at hz
  rw [GraphPath.mapHomInjective_vertexSet] at hz
  rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
  exact mem_oldImage.mpr (by simp)

/-- The canonical one-edge perfect packing from leaf copies of `U` to the old
copy of `U`. -/
noncomputable def leafToOldPacking
    {G : _root_.SimpleGraph V} (U : Finset V) (hU : U ⊆ X) :
    PerfectPathPacking (graph (X := X) G)
      (leavesOf (X := X) U hU) (oldImage (X := X) U) where
  toPathPacking := {
    Index := Fin U.card
    path := fun i => GraphPath.ofAdj
      ((adj_leaf_iff (G := G) (⟨(U.equivFin.symm i).1,
        hU (U.equivFin.symm i).2⟩ : {x : V // x ∈ X})).2 rfl)
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr ⟨U.equivFin.symm i, by simp, rfl⟩,
          Finset.mem_image.mpr
            ⟨(U.equivFin.symm i).1, (U.equivFin.symm i).2, rfl⟩⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      have hi := GraphPath.ofAdj_vertexSet_subset_pair
        ((adj_leaf_iff (G := G) (⟨(U.equivFin.symm i).1,
          hU (U.equivFin.symm i).2⟩ : {x : V // x ∈ X})).2 rfl) hzi
      have hj := GraphPath.ofAdj_vertexSet_subset_pair
        ((adj_leaf_iff (G := G) (⟨(U.equivFin.symm j).1,
          hU (U.equivFin.symm j).2⟩ : {x : V // x ∈ X})).2 rfl) hzj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with h | h
      · have hv : U.equivFin.symm i = U.equivFin.symm j := by
          apply Subtype.ext
          injection h with hsub
          exact congrArg (fun q : {x : V // x ∈ X} => q.1) hsub
        exact hij (U.equivFin.symm.injective hv)
      · cases h
      · cases h
      · have hv : U.equivFin.symm i = U.equivFin.symm j := by
          apply Subtype.ext
          exact old_injective (V := V) (X := X) h
        exact hij (U.equivFin.symm.injective hv)
  }
  source_mem := by intro i; exact Finset.mem_image.mpr ⟨U.equivFin.symm i, by simp, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨(U.equivFin.symm i).1, (U.equivFin.symm i).2, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      have hleaf := congrArg Subtype.val hij
      change
        leaf (⟨(U.equivFin.symm i).1, hU (U.equivFin.symm i).2⟩ :
          {x : V // x ∈ X}) =
        leaf (⟨(U.equivFin.symm j).1, hU (U.equivFin.symm j).2⟩ :
          {x : V // x ∈ X}) at hleaf
      have hv : U.equivFin.symm i = U.equivFin.symm j := by
        apply Subtype.ext
        injection hleaf with hsub
        exact congrArg (fun q : {x : V // x ∈ X} => q.1) hsub
      exact U.equivFin.symm.injective hv
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, _hv, hvx⟩
      refine ⟨U.equivFin v, Subtype.ext ?_⟩
      simpa using hvx
  target_bijective := by
    classical
    constructor
    · intro i j hij
      have hold := congrArg Subtype.val hij
      exact U.equivFin.symm.injective
        (Subtype.ext (old_injective (V := V) (X := X) hold))
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      refine ⟨U.equivFin ⟨v, hv⟩, Subtype.ext ?_⟩
      simpa using hvx

theorem leafToOldPacking_internallyDisjoint
    {G : _root_.SimpleGraph V} (U : Finset V) (hU : U ⊆ X)
    (R : Finset (ChekuriChuzhoyPendantVertex V X)) :
    (leafToOldPacking (G := G) U hU).toPathPacking.InternallyDisjointFromSet R := by
  intro i
  exact GraphPath.ofAdj_internallyDisjointFromSet _ R

theorem leafToOldPacking_staysIn [Fintype V]
    {G : _root_.SimpleGraph V} (U : Finset V) (hU : U ⊆ X) :
    (leafToOldPacking (G := G) U hU).toPathPacking.StaysIn
      (leavesOf (X := X) U hU ∪ oldImage (X := X) (Finset.univ : Finset V)) := by
  classical
  intro i z hz
  have hpair := GraphPath.ofAdj_vertexSet_subset_pair
    ((adj_leaf_iff (G := G) (⟨(U.equivFin.symm i).1,
      hU (U.equivFin.symm i).2⟩ : {x : V // x ∈ X})).2 rfl) hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
  rcases hpair with rfl | rfl
  · exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨U.equivFin.symm i, by simp, rfl⟩)
  · exact Finset.mem_union_right _ (mem_oldImage.mpr (by simp))

/-- Add a fresh pendant source to every path of a perfect packing.

This is the artificial-source normalization used in Appendix A.3 of
Chekuri--Chuzhoy.  Unlike `augmentPerfectPathPacking`, the targets remain old
vertices; this is the form used by Lemma 2.19, where all destinations are
subsequently joined to one artificial sink. -/
noncomputable def prependLeafSourcesPerfectPathPacking [Fintype V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (hA : A ⊆ X) (P : PerfectPathPacking G A B) :
    PerfectPathPacking (graph (X := X) G)
      (leavesOf (X := X) A hA) (oldImage (X := X) B) := by
  let oldRegion := oldImage (X := X) (Finset.univ : Finset V)
  let L := leafToOldPacking (G := G) A hA
  let O := oldPerfectPathPacking (X := X) P
  have hLint : L.toPathPacking.InternallyDisjointFromSet oldRegion := by
    simpa [L, oldRegion] using
      (leafToOldPacking_internallyDisjoint (G := G) A hA oldRegion)
  have hOstay : O.toPathPacking.StaysIn oldRegion := by
    simpa [O, oldRegion] using oldPerfectPathPacking_staysIn (X := X) P
  have hLdisj : Disjoint (leavesOf (X := X) A hA) oldRegion := by
    simpa [oldRegion] using
      leavesOf_disjoint_oldImage (X := X) A (Finset.univ : Finset V) hA
  exact L.concatOfFirstInternallyDisjointSecondStaysIn
    O hLint hOstay hLdisj

@[simp] theorem prependLeafSourcesPerfectPathPacking_card [Fintype V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (hA : A ⊆ X) (P : PerfectPathPacking G A B) :
    (prependLeafSourcesPerfectPathPacking (X := X) hA P).card = P.card := by
  rw [PerfectPathPacking.card_eq_left_card,
    leavesOf_card, P.card_eq_left_card]

theorem prependLeafSourcesPerfectPathPacking_staysIn [Fintype V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (hA : A ⊆ X) (P : PerfectPathPacking G A B) :
    (prependLeafSourcesPerfectPathPacking (X := X) hA P).toPathPacking.StaysIn
      (leavesOf (X := X) A hA ∪
        oldImage (X := X) (Finset.univ : Finset V)) := by
  let oldRegion := oldImage (X := X) (Finset.univ : Finset V)
  let L := leafToOldPacking (G := G) A hA
  let O := oldPerfectPathPacking (X := X) P
  have hLint : L.toPathPacking.InternallyDisjointFromSet oldRegion := by
    simpa [L, oldRegion] using
      (leafToOldPacking_internallyDisjoint (G := G) A hA oldRegion)
  have hOstay : O.toPathPacking.StaysIn oldRegion := by
    simpa [O, oldRegion] using oldPerfectPathPacking_staysIn (X := X) P
  have hLdisj : Disjoint (leavesOf (X := X) A hA) oldRegion := by
    simpa [oldRegion] using
      leavesOf_disjoint_oldImage (X := X) A (Finset.univ : Finset V) hA
  have hLstay :
      L.toPathPacking.StaysIn
        (leavesOf (X := X) A hA ∪ oldRegion) := by
    simpa [L, oldRegion] using
      leafToOldPacking_staysIn (G := G) A hA
  simpa [prependLeafSourcesPerfectPathPacking, L, O, oldRegion] using
    PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
      L O hLint hOstay hLdisj hLstay

/-- Region-sensitive form of the preceding containment theorem. -/
theorem prependLeafSourcesPerfectPathPacking_staysIn_region [Fintype V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : A ⊆ X) (P : PerfectPathPacking G A B)
    (hP : P.toPathPacking.StaysIn C) :
    (prependLeafSourcesPerfectPathPacking (X := X) hA P).toPathPacking.StaysIn
      (leavesOf (X := X) A hA ∪ oldImage (X := X) C) := by
  classical
  let oldC := oldImage (X := X) C
  let L := leafToOldPacking (G := G) A hA
  let O := oldPerfectPathPacking (X := X) P
  have hAC : A ⊆ C := by
    intro x hx
    rcases P.source_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    have hs : (P.path i).source = x := congrArg Subtype.val hi
    exact hP i (by
      rw [← hs]
      exact GraphPath.source_mem_vertexSet (P.path i))
  have hLstay :
      L.toPathPacking.StaysIn
        (leavesOf (X := X) A hA ∪ oldC) := by
    intro i z hz
    have hpair := GraphPath.ofAdj_vertexSet_subset_pair
      ((adj_leaf_iff (G := G) (⟨(A.equivFin.symm i).1,
        hA (A.equivFin.symm i).2⟩ : {x : V // x ∈ X})).2 rfl) hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨A.equivFin.symm i, by simp, rfl⟩)
    · exact Finset.mem_union_right _
        (mem_oldImage.mpr (hAC (A.equivFin.symm i).2))
  have hOstay : O.toPathPacking.StaysIn oldC := by
    intro i z hz
    change z ∈
      (GraphPath.mapHomInjective (P.path i)
        (oldHom (X := X) G) (old_injective (V := V) (X := X))).vertexSet at hz
    rw [GraphPath.mapHomInjective_vertexSet] at hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact mem_oldImage.mpr (hP i hx)
  have hLint : L.toPathPacking.InternallyDisjointFromSet oldC :=
    leafToOldPacking_internallyDisjoint (G := G) A hA oldC
  have hLdisj : Disjoint (leavesOf (X := X) A hA) oldC :=
    leavesOf_disjoint_oldImage (X := X) A C hA
  intro i z hz
  have hsplit :=
    PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      L O hLint hOstay hLdisj i (by
        simpa [prependLeafSourcesPerfectPathPacking, L, O] using hz)
  rcases Finset.mem_union.mp hsplit with hzL | hzO
  · exact hLstay i hzL
  · exact Finset.mem_union_right _ (hOstay _ hzO)

/-- Removing the artificial pendant source does not create any new old
vertex: every old vertex used by a prepended path already belongs to the
support of the original packing. -/
theorem prependLeafSourcesPerfectPathPacking_old_vertex_mem_originalVertexSet
    [Fintype V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (hA : A ⊆ X) (P : PerfectPathPacking G A B)
    (i : (prependLeafSourcesPerfectPathPacking (X := X) hA P).Index)
    {x : V}
    (hx :
      old (X := X) x ∈
        ((prependLeafSourcesPerfectPathPacking (X := X) hA P).path i).vertexSet) :
    x ∈ P.toPathPacking.vertexSet := by
  classical
  let oldRegion := oldImage (X := X) (Finset.univ : Finset V)
  let L := leafToOldPacking (G := G) A hA
  let O := oldPerfectPathPacking (X := X) P
  have hLint : L.toPathPacking.InternallyDisjointFromSet oldRegion := by
    simpa [L, oldRegion] using
      (leafToOldPacking_internallyDisjoint (G := G) A hA oldRegion)
  have hOstay : O.toPathPacking.StaysIn oldRegion := by
    simpa [O, oldRegion] using oldPerfectPathPacking_staysIn (X := X) P
  have hLdisj : Disjoint (leavesOf (X := X) A hA) oldRegion := by
    simpa [oldRegion] using
      leavesOf_disjoint_oldImage (X := X) A (Finset.univ : Finset V) hA
  have hsplit :=
    PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      L O hLint hOstay hLdisj i (by
        simpa [prependLeafSourcesPerfectPathPacking, L, O] using hx)
  rcases Finset.mem_union.mp hsplit with hxL | hxO
  · have hxEndpoint :=
      leafToOldPacking_internallyDisjoint
        (G := G) A hA oldRegion i hxL
          (mem_oldImage.mpr (by simp))
    rcases hxEndpoint with hxSource | hxTarget
    · change old (X := X) x =
        leaf
          (⟨(A.equivFin.symm i).1, hA (A.equivFin.symm i).2⟩ :
            {x : V // x ∈ X}) at hxSource
      cases hxSource
    · let j := L.indexOfSourceTarget O i
      have hxOsource :
          old (X := X) x = (O.path j).source := by
        exact hxTarget.trans (L.source_indexOfSourceTarget O i).symm
      have hxOpath :
          old (X := X) x ∈ (O.path j).vertexSet := by
        rw [hxOsource]
        exact GraphPath.source_mem_vertexSet (O.path j)
      change old (X := X) x ∈
        (GraphPath.mapHomInjective (P.path j)
          (oldHom (X := X) G)
          (old_injective (V := V) (X := X))).vertexSet at hxOpath
      rw [GraphPath.mapHomInjective_vertexSet] at hxOpath
      rcases Finset.mem_image.mp hxOpath with ⟨y, hy, hyx⟩
      have hxy : x = y :=
        old_injective (V := V) (X := X) hyx.symm
      exact P.toPathPacking.path_vertexSet_subset_vertexSet j
        (by simpa [hxy] using hy)
  · change old (X := X) x ∈
      (GraphPath.mapHomInjective
        (P.path (L.indexOfSourceTarget O i))
        (oldHom (X := X) G)
        (old_injective (V := V) (X := X))).vertexSet at hxO
    rw [GraphPath.mapHomInjective_vertexSet] at hxO
    rcases Finset.mem_image.mp hxO with ⟨y, hy, hyx⟩
    have hxy : x = y :=
      old_injective (V := V) (X := X) hyx.symm
    exact P.toPathPacking.path_vertexSet_subset_vertexSet
      (L.indexOfSourceTarget O i) (by simpa [hxy] using hy)

/-- The artificial-source lift is endpoint-clean with respect to an old-copy
target region whenever the original paths meet that region only at their
targets and their sources lie outside it. -/
theorem prependLeafSourcesPerfectPathPacking_internallyDisjoint_oldImage
    [Fintype V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : A ⊆ X) (P : PerfectPathPacking G A B)
    (hP : P.toPathPacking.InternallyDisjointFromSet C)
    (hAC : Disjoint A C) :
    (prependLeafSourcesPerfectPathPacking (X := X) hA P).toPathPacking
      |>.InternallyDisjointFromSet (oldImage (X := X) C) := by
  classical
  let oldRegion := oldImage (X := X) (Finset.univ : Finset V)
  let L := leafToOldPacking (G := G) A hA
  let O := oldPerfectPathPacking (X := X) P
  have hLint : L.toPathPacking.InternallyDisjointFromSet oldRegion := by
    simpa [L, oldRegion] using
      (leafToOldPacking_internallyDisjoint (G := G) A hA oldRegion)
  have hOstay : O.toPathPacking.StaysIn oldRegion := by
    simpa [O, oldRegion] using oldPerfectPathPacking_staysIn (X := X) P
  have hLdisj : Disjoint (leavesOf (X := X) A hA) oldRegion := by
    simpa [oldRegion] using
      leavesOf_disjoint_oldImage (X := X) A (Finset.univ : Finset V) hA
  have hLtarget :
      L.toPathPacking.InternallyDisjointFromSet (oldImage (X := X) C) :=
    leafToOldPacking_internallyDisjoint
      (G := G) A hA (oldImage (X := X) C)
  have hOtarget :
      O.toPathPacking.InternallyDisjointFromSet (oldImage (X := X) C) := by
    intro i z hz hzC
    cases z with
    | leaf z => simpa [oldImage] using hzC
    | old x =>
        change old (X := X) x ∈
          (GraphPath.mapHomInjective (P.path i)
            (oldHom (X := X) G)
            (old_injective (V := V) (X := X))).vertexSet at hz
        rw [GraphPath.mapHomInjective_vertexSet] at hz
        rcases Finset.mem_image.mp hz with ⟨y, hy, hyx⟩
        have hxy : x = y :=
          old_injective (V := V) (X := X) hyx.symm
        have hxC : x ∈ C := mem_oldImage.mp hzC
        rcases hP i (by simpa [hxy] using hy) hxC with hs | ht
        · exact Or.inl (by
            change old (X := X) x =
              old (X := X) (P.path i).source
            exact congrArg (old (X := X)) hs)
        · exact Or.inr (by
            change old (X := X) x =
              old (X := X) (P.path i).target
            exact congrArg (old (X := X)) ht)
  have hGlue :
      Disjoint (oldImage (X := X) A) (oldImage (X := X) C) := by
    rw [Finset.disjoint_left]
    intro z hzA hzC
    rcases Finset.mem_image.mp hzA with ⟨a, ha, rfl⟩
    exact Finset.disjoint_left.mp hAC ha (mem_oldImage.mp hzC)
  simpa [prependLeafSourcesPerfectPathPacking, L, O] using
    PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
      L O hLint hOstay hLdisj hLtarget hOtarget hGlue

/-- The reverse one-edge packing, from old vertices to their leaf copies. -/
noncomputable def oldToLeafPacking
    {G : _root_.SimpleGraph V} (U : Finset V) (hU : U ⊆ X) :
    PerfectPathPacking (graph (X := X) G)
      (oldImage (X := X) U) (leavesOf (X := X) U hU) :=
  (leafToOldPacking (G := G) U hU).reverse

theorem oldToLeafPacking_internallyDisjoint
    {G : _root_.SimpleGraph V} (U : Finset V) (hU : U ⊆ X)
    (R : Finset (ChekuriChuzhoyPendantVertex V X)) :
    (oldToLeafPacking (G := G) U hU).toPathPacking.InternallyDisjointFromSet R := by
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    (leafToOldPacking (G := G) U hU)
    (leafToOldPacking_internallyDisjoint (G := G) U hU R)

theorem oldToLeafPacking_staysIn [Fintype V]
    {G : _root_.SimpleGraph V} (U : Finset V) (hU : U ⊆ X) :
    (oldToLeafPacking (G := G) U hU).toPathPacking.StaysIn
      (leavesOf (X := X) U hU ∪ oldImage (X := X) (Finset.univ : Finset V)) := by
  exact PerfectPathPacking.reverse_staysIn
    (leafToOldPacking (G := G) U hU)
    (leafToOldPacking_staysIn (G := G) U hU)

/-- Add pendant endpoints to both ends of a perfect packing. -/
noncomputable def augmentPerfectPathPacking [Fintype V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ X) (hAB : Disjoint A B)
    (P : PerfectPathPacking G A B) :
    PerfectPathPacking (graph (X := X) G)
      (leavesOf (X := X) A hA) (leavesOf (X := X) B hB) := by
  let oldRegion := oldImage (X := X) (Finset.univ : Finset V)
  let L := leafToOldPacking (G := G) A hA
  let O := oldPerfectPathPacking (X := X) P
  let R := oldToLeafPacking (G := G) B hB
  have hLint : L.toPathPacking.InternallyDisjointFromSet oldRegion := by
    simpa [L, oldRegion] using
      (leafToOldPacking_internallyDisjoint (G := G) A hA oldRegion)
  have hOstay : O.toPathPacking.StaysIn oldRegion := by
    simpa [O, oldRegion] using oldPerfectPathPacking_staysIn (X := X) P
  have hLdisj : Disjoint (leavesOf (X := X) A hA) oldRegion := by
    simpa [oldRegion] using
      leavesOf_disjoint_oldImage (X := X) A (Finset.univ : Finset V) hA
  let Prefix := L.concatOfFirstInternallyDisjointSecondStaysIn
    O hLint hOstay hLdisj
  let prefixRegion := leavesOf (X := X) A hA ∪ oldRegion
  have hLstay : L.toPathPacking.StaysIn prefixRegion := by
    simpa [L, prefixRegion, oldRegion] using leafToOldPacking_staysIn (G := G) A hA
  have hPrefixStay : Prefix.toPathPacking.StaysIn prefixRegion := by
    have h :=
      PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        L O hLint hOstay hLdisj hLstay
    intro i z hz
    have hz' := h i hz
    rcases Finset.mem_union.mp hz' with hzPrefix | hzOld
    · exact hzPrefix
    · exact Finset.mem_union_right _ hzOld
  have hRint : R.toPathPacking.InternallyDisjointFromSet prefixRegion := by
    simpa [R] using
      (oldToLeafPacking_internallyDisjoint (G := G) B hB prefixRegion)
  have hRdisj : Disjoint (leavesOf (X := X) B hB) prefixRegion := by
    rw [Finset.disjoint_left]
    intro z hzB hzPrefix
    rcases Finset.mem_union.mp hzPrefix with hzA | hzOld
    · rcases Finset.mem_image.mp hzB with ⟨b, _hb, hzb⟩
      rcases Finset.mem_image.mp hzA with ⟨a, _ha, hza⟩
      have hba : b.1 = a.1 := by
        rw [← hzb] at hza
        injection hza with hsub
        exact (congrArg (fun q : {x : V // x ∈ X} => q.1) hsub).symm
      have hbBase : b.1 ∈ B := b.2
      have haBase : a.1 ∈ A := a.2
      exact Finset.disjoint_left.mp
        hAB haBase (by simpa [hba] using hbBase)
    · exact Finset.disjoint_left.mp
        (leavesOf_disjoint_oldImage (X := X) B (Finset.univ : Finset V) hB)
        hzB hzOld
  exact Prefix.concatOfFirstStaysInSecondInternallyDisjoint
    R hPrefixStay hRint hRdisj

/-- The augmented packing stays in the two pendant endpoint sets together
with the old-copy image of any region containing the original paths. -/
theorem augmentPerfectPathPacking_staysIn [Fintype V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ X) (hAB : Disjoint A B)
    (P : PerfectPathPacking G A B)
    (hP : P.toPathPacking.StaysIn C)
    (hAC : A ⊆ C) (hBC : B ⊆ C) :
    (augmentPerfectPathPacking (X := X) hA hB hAB P).toPathPacking.StaysIn
      (leavesOf (X := X) A hA ∪
        (oldImage (X := X) C ∪ leavesOf (X := X) B hB)) := by
  classical
  let oldC := oldImage (X := X) C
  let L := leafToOldPacking (G := G) A hA
  let O := oldPerfectPathPacking (X := X) P
  let R := oldToLeafPacking (G := G) B hB
  have hLstay :
      L.toPathPacking.StaysIn
        (leavesOf (X := X) A hA ∪ oldC) := by
    intro i z hz
    have hpair := GraphPath.ofAdj_vertexSet_subset_pair
      ((adj_leaf_iff (G := G) (⟨(A.equivFin.symm i).1,
        hA (A.equivFin.symm i).2⟩ : {x : V // x ∈ X})).2 rfl) hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨A.equivFin.symm i, by simp, rfl⟩)
    · exact Finset.mem_union_right _
        (mem_oldImage.mpr (hAC (A.equivFin.symm i).2))
  have hOstay : O.toPathPacking.StaysIn oldC := by
    intro i z hz
    change z ∈
      (GraphPath.mapHomInjective (P.path i)
        (oldHom (X := X) G) (old_injective (V := V) (X := X))).vertexSet at hz
    rw [GraphPath.mapHomInjective_vertexSet] at hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact mem_oldImage.mpr (hP i hx)
  have hLint : L.toPathPacking.InternallyDisjointFromSet oldC := by
    exact leafToOldPacking_internallyDisjoint (G := G) A hA oldC
  have hLdisj : Disjoint (leavesOf (X := X) A hA) oldC := by
    exact leavesOf_disjoint_oldImage (X := X) A C hA
  let Prefix :=
    L.concatOfFirstInternallyDisjointSecondStaysIn
      O hLint hOstay hLdisj
  have hPrefixStay :
      Prefix.toPathPacking.StaysIn
        (leavesOf (X := X) A hA ∪ oldC) := by
    intro i z hz
    have hsplit :=
      PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
        L O hLint hOstay hLdisj i hz
    rcases Finset.mem_union.mp hsplit with hzL | hzO
    · exact hLstay i hzL
    · exact Finset.mem_union_right _ (hOstay _ hzO)
  have hRstay :
      R.toPathPacking.StaysIn
        (oldC ∪ leavesOf (X := X) B hB) := by
    intro i z hz
    have hpair := GraphPath.ofAdj_vertexSet_subset_pair
      ((adj_leaf_iff (G := G) (⟨(B.equivFin.symm i).1,
        hB (B.equivFin.symm i).2⟩ : {x : V // x ∈ X})).2 rfl) (by
          simpa [R, oldToLeafPacking, GraphPath.reverse_vertexSet] using hz)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with rfl | rfl
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨B.equivFin.symm i, by simp, rfl⟩)
    · exact Finset.mem_union_left _
        (mem_oldImage.mpr (hBC (B.equivFin.symm i).2))
  have hRint :
      R.toPathPacking.InternallyDisjointFromSet
        (leavesOf (X := X) A hA ∪ oldC) :=
    oldToLeafPacking_internallyDisjoint
      (G := G) B hB (leavesOf (X := X) A hA ∪ oldC)
  have hRdisj :
      Disjoint (leavesOf (X := X) B hB)
        (leavesOf (X := X) A hA ∪ oldC) := by
    rw [Finset.disjoint_left]
    intro z hzB hz
    rcases Finset.mem_union.mp hz with hzA | hzOld
    · rcases Finset.mem_image.mp hzB with ⟨b, _hb, hzb⟩
      rcases Finset.mem_image.mp hzA with ⟨a, _ha, hza⟩
      have hba : b.1 = a.1 := by
        rw [← hzb] at hza
        injection hza with hsub
        exact congrArg (fun q : {x : V // x ∈ X} => q.1) hsub |>.symm
      exact Finset.disjoint_left.mp hAB a.2 (by simpa [hba] using b.2)
    · exact Finset.disjoint_left.mp
        (leavesOf_disjoint_oldImage (X := X) B C hB) hzB hzOld
  have h :=
    PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
      Prefix R hPrefixStay hRint hRdisj hRstay
  intro i z hz
  rcases Finset.mem_union.mp (h i hz) with hzPrefix | hzR
  · rcases Finset.mem_union.mp hzPrefix with hzA | hzOld
    · exact Finset.mem_union_left _ hzA
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hzOld)
  · rcases Finset.mem_union.mp hzR with hzOld | hzB
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hzOld)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hzB)

/-- Augmenting two mutually node-disjoint perfect packings at pairwise
disjoint endpoint classes preserves mutual node-disjointness. -/
theorem augmentPerfectPathPacking_mutuallyNodeDisjoint [Fintype V]
    {G : _root_.SimpleGraph V}
    {A₁ B₁ A₂ B₂ : Finset V}
    (hA₁ : A₁ ⊆ X) (hB₁ : B₁ ⊆ X)
    (hA₂ : A₂ ⊆ X) (hB₂ : B₂ ⊆ X)
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hclasses : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    (P₁ : PerfectPathPacking G A₁ B₁)
    (P₂ : PerfectPathPacking G A₂ B₂)
    (hP :
      P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    (augmentPerfectPathPacking (X := X) hA₁ hB₁ hAB₁ P₁).toPathPacking
      |>.MutuallyNodeDisjoint
        (augmentPerfectPathPacking (X := X) hA₂ hB₂ hAB₂ P₂).toPathPacking := by
  classical
  let U₁ := P₁.toPathPacking.vertexSet
  let U₂ := P₂.toPathPacking.vertexSet
  have hP₁stay : P₁.toPathPacking.StaysIn U₁ := by
    intro i x hx
    exact P₁.toPathPacking.mem_vertexSet.mpr ⟨i, hx⟩
  have hP₂stay : P₂.toPathPacking.StaysIn U₂ := by
    intro i x hx
    exact P₂.toPathPacking.mem_vertexSet.mpr ⟨i, hx⟩
  have hA₁U₁ : A₁ ⊆ U₁ := by
    intro x hx
    rcases P₁.source_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    have hs : (P₁.path i).source = x := congrArg Subtype.val hi
    exact P₁.toPathPacking.mem_vertexSet.mpr ⟨i, by
      rw [← hs]
      exact GraphPath.source_mem_vertexSet (P₁.path i)⟩
  have hB₁U₁ : B₁ ⊆ U₁ := by
    intro x hx
    rcases P₁.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    have ht : (P₁.path i).target = x := congrArg Subtype.val hi
    exact P₁.toPathPacking.mem_vertexSet.mpr ⟨i, by
      rw [← ht]
      exact GraphPath.target_mem_vertexSet (P₁.path i)⟩
  have hA₂U₂ : A₂ ⊆ U₂ := by
    intro x hx
    rcases P₂.source_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    have hs : (P₂.path i).source = x := congrArg Subtype.val hi
    exact P₂.toPathPacking.mem_vertexSet.mpr ⟨i, by
      rw [← hs]
      exact GraphPath.source_mem_vertexSet (P₂.path i)⟩
  have hB₂U₂ : B₂ ⊆ U₂ := by
    intro x hx
    rcases P₂.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    have ht : (P₂.path i).target = x := congrArg Subtype.val hi
    exact P₂.toPathPacking.mem_vertexSet.mpr ⟨i, by
      rw [← ht]
      exact GraphPath.target_mem_vertexSet (P₂.path i)⟩
  have hR₁stay :=
    augmentPerfectPathPacking_staysIn
      hA₁ hB₁ hAB₁ P₁ hP₁stay hA₁U₁ hB₁U₁
  have hR₂stay :=
    augmentPerfectPathPacking_staysIn
      hA₂ hB₂ hAB₂ P₂ hP₂stay hA₂U₂ hB₂U₂
  intro i j
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro z hz₁ hz₂
  have hz₁' := hR₁stay i hz₁
  have hz₂' := hR₂stay j hz₂
  cases z with
  | old x =>
      have hxU₁ : x ∈ U₁ := by
        rcases Finset.mem_union.mp hz₁' with hleaf | hrest
        · simpa [leavesOf] using hleaf
        · rcases Finset.mem_union.mp hrest with hold | hleaf
          · exact mem_oldImage.mp hold
          · simpa [leavesOf] using hleaf
      have hxU₂ : x ∈ U₂ := by
        rcases Finset.mem_union.mp hz₂' with hleaf | hrest
        · simpa [leavesOf] using hleaf
        · rcases Finset.mem_union.mp hrest with hold | hleaf
          · exact mem_oldImage.mp hold
          · simpa [leavesOf] using hleaf
      rcases P₁.toPathPacking.mem_vertexSet.mp hxU₁ with ⟨a, ha⟩
      rcases P₂.toPathPacking.mem_vertexSet.mp hxU₂ with ⟨b, hb⟩
      exact Finset.disjoint_left.mp (hP a b) ha hb
  | leaf x =>
      have hx₁ : x.1 ∈ A₁ ∪ B₁ := by
        rcases Finset.mem_union.mp hz₁' with hA | hrest
        · rcases Finset.mem_image.mp hA with ⟨a, _ha, hax⟩
          injection hax with hsub
          have hbase :
              a.1 = x.1 := congrArg Subtype.val hsub
          exact Finset.mem_union_left _
            (by simpa [← hbase] using a.2)
        · rcases Finset.mem_union.mp hrest with hold | hB
          · simpa [oldImage] using hold
          · rcases Finset.mem_image.mp hB with ⟨b, _hb, hbx⟩
            injection hbx with hsub
            have hbase :
                b.1 = x.1 := congrArg Subtype.val hsub
            exact Finset.mem_union_right _
              (by simpa [← hbase] using b.2)
      have hx₂ : x.1 ∈ A₂ ∪ B₂ := by
        rcases Finset.mem_union.mp hz₂' with hA | hrest
        · rcases Finset.mem_image.mp hA with ⟨a, _ha, hax⟩
          injection hax with hsub
          have hbase :
              a.1 = x.1 := congrArg Subtype.val hsub
          exact Finset.mem_union_left _
            (by simpa [← hbase] using a.2)
        · rcases Finset.mem_union.mp hrest with hold | hB
          · simpa [oldImage] using hold
          · rcases Finset.mem_image.mp hB with ⟨b, _hb, hbx⟩
            injection hbx with hsub
            have hbase :
                b.1 = x.1 := congrArg Subtype.val hsub
            exact Finset.mem_union_right _
              (by simpa [← hbase] using b.2)
      exact Finset.disjoint_left.mp hclasses hx₁ hx₂

/-- Every fresh terminal has exactly one neighbor, its original vertex. -/
theorem leaf_degree_one {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ X}) :
    DegreeEquals (graph (X := X) G) (leaf x) 1 := by
  classical
  refine degreeEquals_one_of_unique_neighbor
    ((adj_leaf_iff (G := G) x).2 rfl) ?_
  intro y hy
  exact (adj_leaf_iff (G := G) x).1 hy

/-- Every member of the fresh terminal set has degree exactly one. -/
theorem terminal_degree_one {G : _root_.SimpleGraph V}
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leaves (V := V) (X := X)) :
    DegreeEquals (graph (X := X) G) z 1 := by
  rcases exists_leafValue hz with ⟨x, rfl⟩
  exact leaf_degree_one x

/-- At an old vertex, the extension adds at most its own pendant leaf. -/
theorem old_degreeAtMost_succ {G : _root_.SimpleGraph V} {Delta : ℕ}
    (hG : MaxDegreeAtMost G Delta) (x : V) :
    DegreeAtMost (graph (X := X) G) (old x) (Delta + 1) := by
  classical
  rcases hG x with ⟨N, hN, hcard⟩
  by_cases hx : x ∈ X
  · let lx : ChekuriChuzhoyPendantVertex V X := leaf ⟨x, hx⟩
    refine ⟨N.image (old (X := X)) ∪ {lx}, ?_, ?_⟩
    · intro y
      constructor
      · intro hy
        rcases Finset.mem_union.mp hy with hyOld | hyLeaf
        · rcases Finset.mem_image.mp hyOld with ⟨z, hz, rfl⟩
          exact adj_old_old_iff.mpr ((hN z).1 hz)
        · have hylx : y = lx := by simpa using hyLeaf
          subst y
          exact (adj_old_leaf_iff (G := G) (x := ⟨x, hx⟩)).2 rfl
      · intro hy
        cases y with
        | old z =>
            exact Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨z, (hN z).2 (adj_old_old_iff.mp hy), rfl⟩)
        | leaf z =>
            have hzx : x = z.1 := (adj_old_leaf_iff (G := G) z).1 hy
            have hzsub : z = ⟨x, hx⟩ := Subtype.ext hzx.symm
            exact Finset.mem_union_right _ (by simp [lx, hzsub])
    · refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_image_of_injective]
      simp only [Finset.card_singleton]
      omega
      exact old_injective (V := V) (X := X)
  · refine ⟨N.image (old (X := X)), ?_, ?_⟩
    · intro y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
        exact adj_old_old_iff.mpr ((hN z).1 hz)
      · intro hy
        cases y with
        | old z =>
            exact Finset.mem_image.mpr
              ⟨z, (hN z).2 (adj_old_old_iff.mp hy), rfl⟩
        | leaf z =>
            have hzx : x = z.1 := (adj_old_leaf_iff (G := G) z).1 hy
            exact False.elim (hx (hzx ▸ z.2))
    · rw [Finset.card_image_of_injective]
      exact hcard.trans (Nat.le_add_right Delta 1)
      exact old_injective (V := V) (X := X)

/-- Pendant normalization increases maximum degree by at most one. -/
theorem maxDegreeAtMost_succ {G : _root_.SimpleGraph V} {Delta : ℕ}
    (hG : MaxDegreeAtMost G Delta) :
    MaxDegreeAtMost (graph (X := X) G) (Delta + 1) := by
  intro z
  cases z with
  | old x => exact old_degreeAtMost_succ hG x
  | leaf x =>
      exact DegreeAtMost.mono (by
        rcases leaf_degree_one (G := G) x with ⟨N, hN, hcard⟩
        exact ⟨N, hN, hcard.le⟩) (by omega)

/-- A node-linked pair lifts to its two pendant copies.  The linkage stays in
the old region together with the two endpoint-leaf sets. -/
theorem nodeLinkedIn_leavesOf [Fintype V]
    {G : _root_.SimpleGraph V} {C A B : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ X)
    (h : NodeLinkedIn G C A B) :
    NodeLinkedIn (graph (X := X) G)
      (leavesOf (X := X) A hA ∪
        (oldImage (X := X) C ∪ leavesOf (X := X) B hB))
      (leavesOf (X := X) A hA)
      (leavesOf (X := X) B hB) := by
  classical
  let LA := leavesOf (X := X) A hA
  let LB := leavesOf (X := X) B hB
  let oldC := oldImage (X := X) C
  have hLAsub :
      LA ⊆ LA ∪ (oldC ∪ LB) := Finset.subset_union_left
  have hLBsub :
      LB ⊆ LA ∪ (oldC ∪ LB) :=
    fun _ hz => Finset.mem_union_right _ (Finset.mem_union_right _ hz)
  have hLALB : Disjoint LA LB := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    rcases Finset.mem_image.mp hzA with ⟨a, _ha, hza⟩
    rcases Finset.mem_image.mp hzB with ⟨b, _hb, hzb⟩
    have hab : a.1 = b.1 := by
      rw [← hza] at hzb
      injection hzb with hsub
      exact (congrArg (fun q : {x : V // x ∈ X} => q.1) hsub).symm
    exact Finset.disjoint_left.mp h.2.2.1 a.2 (by simpa [hab] using b.2)
  refine ⟨hLAsub, hLBsub, hLALB, ?_⟩
  intro A' B' hA' hB'
  have hA'leaves :
      A' ⊆ leaves (V := V) (X := X) :=
    hA'.trans (leavesOf_subset_leaves A hA)
  have hB'leaves :
      B' ⊆ leaves (V := V) (X := X) :=
    hB'.trans (leavesOf_subset_leaves B hB)
  let A0 := baseSet A' hA'leaves
  let B0 := baseSet B' hB'leaves
  have hA0A : A0 ⊆ A := by
    simpa [A0, LA] using
      baseSet_subset_of_subset_leavesOf
        A' hA'leaves A hA hA'
  have hB0B : B0 ⊆ B := by
    simpa [B0, LB] using
      baseSet_subset_of_subset_leavesOf
        B' hB'leaves B hB hB'
  rcases h.2.2.2 hA0A hB0B with ⟨P, hPcard, hPstay⟩
  have hSourceA0 : P.sourceSet ⊆ A0 := P.sourceSet_subset_left
  have hTargetB0 : P.targetSet ⊆ B0 := P.targetSet_subset_right
  have hSourceX :
      P.sourceSet ⊆ X :=
    hSourceA0.trans (hA0A.trans hA)
  have hTargetX :
      P.targetSet ⊆ X :=
    hTargetB0.trans (hB0B.trans hB)
  have hSourceTarget :
      Disjoint P.sourceSet P.targetSet := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    exact Finset.disjoint_left.mp h.2.2.1
      (hA0A (hSourceA0 hxS)) (hB0B (hTargetB0 hxT))
  let Q := P.toPerfectUsedTerminals
  let R := augmentPerfectPathPacking (X := X)
    hSourceX hTargetX hSourceTarget Q
  have hRA :
      leavesOf (X := X) P.sourceSet hSourceX ⊆ A' :=
    leavesOf_baseSet_subset A' hA'leaves
      P.sourceSet hSourceA0
  have hRB :
      leavesOf (X := X) P.targetSet hTargetX ⊆ B' :=
    leavesOf_baseSet_subset B' hB'leaves
      P.targetSet hTargetB0
  let W := R.toPathPacking.widenTerminals hRA hRB
  refine ⟨W, ?_, ?_⟩
  · calc
      W.card = R.card := rfl
      _ = (leavesOf (X := X) P.sourceSet hSourceX).card :=
        R.card_eq_left_card
      _ = P.sourceSet.card := leavesOf_card P.sourceSet hSourceX
      _ = P.card := P.sourceSet_card
      _ = min A'.card B'.card := by
        simpa [A0, B0] using hPcard
  · have hQstay :
        Q.toPathPacking.StaysIn C :=
      PathPacking.toPerfectUsedTerminals_staysIn P hPstay
    have hSourceC :
        P.sourceSet ⊆ C :=
      hSourceA0.trans (hA0A.trans h.1)
    have hTargetC :
        P.targetSet ⊆ C :=
      hTargetB0.trans (hB0B.trans h.2.1)
    have hRstay :=
      augmentPerfectPathPacking_staysIn
        hSourceX hTargetX hSourceTarget Q
        hQstay hSourceC hTargetC
    intro i z hz
    rcases Finset.mem_union.mp (hRstay i hz) with hzSource | hzRest
    · exact Finset.mem_union_left _ (hA' (hRA hzSource))
    · rcases Finset.mem_union.mp hzRest with hzOld | hzTarget
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hzOld)
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _ (hB' (hRB hzTarget)))

/-- Node-well-linkedness of `X` lifts to node-well-linkedness of the fresh
degree-one terminal set in the pendant extension. -/
theorem nodeWellLinkedIn_leaves [Fintype V]
    {G : _root_.SimpleGraph V}
    (hX : NodeWellLinkedIn G (Finset.univ : Finset V) X) :
    NodeWellLinkedIn (graph (X := X) G)
      (Finset.univ : Finset (ChekuriChuzhoyPendantVertex V X))
      (leaves (V := V) (X := X)) := by
  classical
  constructor
  · simp
  · intro A B hA hB hAB
    let A0 := baseSet A hA
    let B0 := baseSet B hB
    have hA0X : A0 ⊆ X := by
      simpa [A0] using baseSet_subset A hA
    have hB0X : B0 ⊆ X := by
      simpa [B0] using baseSet_subset B hB
    have hA0B0 : Disjoint A0 B0 := by
      simpa [A0, B0] using baseSet_disjoint hA hB hAB
    rcases hX.2 hA0X hB0X hA0B0 with ⟨P, hPcard, _hPstay⟩
    have hSourceA0 : P.sourceSet ⊆ A0 := P.sourceSet_subset_left
    have hTargetB0 : P.targetSet ⊆ B0 := P.targetSet_subset_right
    have hSourceX : P.sourceSet ⊆ X := subset_trans hSourceA0 hA0X
    have hTargetX : P.targetSet ⊆ X := subset_trans hTargetB0 hB0X
    have hSourceTarget : Disjoint P.sourceSet P.targetSet := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      exact Finset.disjoint_left.mp hA0B0 (hSourceA0 hxS) (hTargetB0 hxT)
    let Q := P.toPerfectUsedTerminals
    let R := augmentPerfectPathPacking (X := X)
      hSourceX hTargetX hSourceTarget Q
    have hRA : leavesOf (X := X) P.sourceSet hSourceX ⊆ A :=
      leavesOf_baseSet_subset A hA P.sourceSet hSourceA0
    have hRB : leavesOf (X := X) P.targetSet hTargetX ⊆ B :=
      leavesOf_baseSet_subset B hB P.targetSet hTargetB0
    let W := R.toPathPacking.widenTerminals hRA hRB
    refine ⟨W, ?_, ?_⟩
    · calc
        W.card = R.card := rfl
        _ = (leavesOf (X := X) P.sourceSet hSourceX).card :=
          R.card_eq_left_card
        _ = P.sourceSet.card := leavesOf_card P.sourceSet hSourceX
        _ = P.card := P.sourceSet_card
        _ = min A.card B.card := by simpa [A0, B0] using hPcard
    · intro i z _hz
      simp

/-- Predicate cutting out the old-copy vertices. -/
def IsOld : ChekuriChuzhoyPendantVertex V X → Prop
  | old _ => True
  | leaf _ => False

/-- Forget the old-copy constructor. -/
def oldValue : {z : ChekuriChuzhoyPendantVertex V X // IsOld z} → V
  | ⟨old x, _⟩ => x

@[simp] theorem oldValue_old (x : V) :
    oldValue (X := X) ⟨old x, trivial⟩ = x := rfl

theorem exists_old_of_isOld
    {z : ChekuriChuzhoyPendantVertex V X} (hz : IsOld z) :
    ∃ x : V, z = old x := by
  cases z with
  | old x => exact ⟨x, rfl⟩
  | leaf x => exact False.elim hz

/-- The old-copy induced subgraph is exactly the original graph, expressed as
an adjacency-reflecting projection. -/
def oldProjectionHom (G : _root_.SimpleGraph V) :
    (graph (X := X) G).induce
      {z : ChekuriChuzhoyPendantVertex V X | IsOld z} →g G where
  toFun := oldValue (X := X)
  map_rel' := by
    intro a b hab
    rcases exists_old_of_isOld a.2 with ⟨x, hx⟩
    rcases exists_old_of_isOld b.2 with ⟨y, hy⟩
    have ha : a = ⟨old x, trivial⟩ := Subtype.ext hx
    have hb : b = ⟨old y, trivial⟩ := Subtype.ext hy
    subst a
    subst b
    exact adj_old_old_iff.mp hab

end ChekuriChuzhoyPendantVertex
end SimpleGraph

end Lax17Proofs
