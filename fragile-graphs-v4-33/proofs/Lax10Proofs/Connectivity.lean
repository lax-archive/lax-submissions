import Lax10Proofs.Coloring

/-!
# Connectivity and low-order separators

This file packages the separator information extracted from
$¬ ThreeConnected G$.
-/

namespace Lax10Proofs

universe u

variable {V : Type u}

/-- Deleted-vertex homomorphism induced by a graph isomorphism. -/
noncomputable def isoDeleteHom {W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (T : Finset W) :
    deleteVertices G (T.map e.symm.toEquiv.toEmbedding) →g deleteVertices H T := by
  classical
  refine ⟨?f, ?map⟩
  · intro x
    refine ⟨e x.1, ?_⟩
    intro hxT
    exact x.2 (by
      refine Finset.mem_map.mpr ⟨e x.1, hxT, ?_⟩
      simp [RelIso.symm_apply_apply])
  · intro x y hxy
    exact (show (deleteVertices H T).Adj _ _ from by
      simpa [deleteVertices] using (e.toHom.map_rel hxy))

/-- 3-connectivity is invariant under graph isomorphism. -/
theorem ThreeConnected.iso {W : Type*} [Finite V] [Finite W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (hG : ThreeConnected G) : ThreeConnected H := by
  classical
  constructor
  · rw [← Nat.card_congr e.toEquiv]
    exact hG.1
  · intro T hT hsep
    rcases hsep with ⟨x, y, hxy⟩
    let S : Finset V := T.map e.symm.toEquiv.toEmbedding
    have hSsmall : S.card ≤ 2 := by
      have hcard : S.card = T.card := Finset.card_map _
      exact hcard.trans_le hT
    have hxS : e.symm x.1 ∉ S := by
      intro hxmem
      rcases Finset.mem_map.mp hxmem with ⟨t, ht, htEq⟩
      have htx : t = x.1 := by
        apply_fun e at htEq
        simpa [RelIso.apply_symm_apply] using htEq
      exact x.2 (htx ▸ ht)
    have hyS : e.symm y.1 ∉ S := by
      intro hymem
      rcases Finset.mem_map.mp hymem with ⟨t, ht, htEq⟩
      have hty : t = y.1 := by
        apply_fun e at htEq
        simpa [RelIso.apply_symm_apply] using htEq
      exact y.2 (hty ▸ ht)
    have hGsep : IsVertexSeparator G S := by
      refine ⟨⟨e.symm x.1, hxS⟩, ⟨e.symm y.1, hyS⟩, ?_⟩
      intro hreach
      have hreachH := SimpleGraph.Reachable.map (isoDeleteHom e T) hreach
      exact hxy (by simpa [isoDeleteHom, S, RelIso.apply_symm_apply] using hreachH)
    exact hG.2 S hSsmall hGsep

/--
The coerced graph of a subgraph mapped along a graph embedding is isomorphic to
the original coerced subgraph.
-/
noncomputable def subgraphMapIso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (K : G.Subgraph) :
    K.coe ≃g (K.map f.toHom).coe := by
  classical
  let L := K.map f.toHom
  let toFun : K.verts → L.verts := fun x => by
    refine ⟨f x.1, ?_⟩
    rw [SimpleGraph.Subgraph.map_verts]
    exact ⟨x.1, x.2, rfl⟩
  let invFun : L.verts → K.verts := fun y => by
    let h : ∃ x ∈ K.verts, f.toHom x = y.1 := by
      have hy : y.1 ∈ f.toHom '' K.verts := by
        have hy2 : y.1 ∈ (K.map f.toHom).verts := y.2
        simp only [SimpleGraph.Subgraph.map_verts] at hy2
        exact hy2
      exact hy
    exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  have left_inv : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    dsimp [invFun, toFun]
    apply f.injective
    exact (Classical.choose_spec
      (show ∃ y ∈ K.verts, f.toHom y = f x.1 from ⟨x.1, x.2, rfl⟩)).2
  have right_inv : Function.RightInverse invFun toFun := by
    intro y
    apply Subtype.ext
    dsimp [invFun, toFun]
    exact (Classical.choose_spec
      (show ∃ x ∈ K.verts, f.toHom x = y.1 from by
        have hy : y.1 ∈ f.toHom '' K.verts := by
          have hy2 : y.1 ∈ (K.map f.toHom).verts := y.2
          simp only [SimpleGraph.Subgraph.map_verts] at hy2
          exact hy2
        exact hy)).2
  let e : K.verts ≃ L.verts := ⟨toFun, invFun, left_inv, right_inv⟩
  refine RelIso.mk e ?_
  intro a b
  change L.coe.Adj (e a) (e b) ↔ K.coe.Adj a b
  constructor
  · intro hab
    rw [SimpleGraph.Subgraph.coe_adj] at hab
    rw [SimpleGraph.Subgraph.map_adj] at hab
    rcases hab with ⟨a', b', ha'b', hfa, hfb⟩
    rw [SimpleGraph.Subgraph.coe_adj]
    have ha : a' = a.1 := f.injective (by simpa [e, toFun] using hfa)
    have hb : b' = b.1 := f.injective (by simpa [e, toFun] using hfb)
    subst a'
    subst b'
    simpa using ha'b'
  · intro hab
    rw [SimpleGraph.Subgraph.coe_adj] at hab
    rw [SimpleGraph.Subgraph.coe_adj]
    rw [SimpleGraph.Subgraph.map_adj]
    exact ⟨a.1, b.1, hab, by simp [e, toFun], by simp [e, toFun]⟩

/-- Induced subgraphs of an $m$-fragile graph are $m$-fragile. -/
theorem mfragile_induced [Finite V] {m : Nat} {G : SimpleGraph V}
    (hfrag : MFragile m G) (A : Set V) :
    MFragile m (G.induce A) := by
  classical
  intro H hH
  let f := SimpleGraph.Embedding.induce (G := G) A
  let K : G.Subgraph := H.map f.toHom
  have hK : ThreeConnected K.coe :=
    ThreeConnected.iso (subgraphMapIso f H) hH
  obtain ⟨cK⟩ := hfrag K hK
  exact ⟨KColoring.pullback (subgraphMapIso f H).toHom cK⟩

/--
A separated cover of the vertex set.  The intended separator is $A ∩ B$;
there are no edges between the two exclusive sides.
-/
structure SeparatedCover (G : SimpleGraph V) where
  A : Set V
  B : Set V
  separator : Finset V
  cover : A ∪ B = Set.univ
  no_edge : ∀ ⦃x y : V⦄, x ∈ A → x ∉ B → y ∈ B → y ∉ A → ¬ G.Adj x y
  left_nonempty : (A \ B).Nonempty
  right_nonempty : (B \ A).Nonempty
  inter_subset_separator : A ∩ B ⊆ (separator : Set V)
  separator_subset_inter : (separator : Set V) ⊆ A ∩ B
  separator_small : separator.card ≤ 2

namespace SeparatedCover

protected def symm {G : SimpleGraph V} (C : SeparatedCover G) : SeparatedCover G where
  A := C.B
  B := C.A
  separator := C.separator
  cover := by
    rw [Set.union_comm]
    exact C.cover
  no_edge := by
    intro x y hxB hxA yA yB hxy
    exact C.no_edge yA yB hxB hxA hxy.symm
  left_nonempty := C.right_nonempty
  right_nonempty := C.left_nonempty
  inter_subset_separator := by
    intro x hx
    exact C.inter_subset_separator ⟨hx.2, hx.1⟩
  separator_subset_inter := by
    intro x hx
    exact ⟨(C.separator_subset_inter hx).2, (C.separator_subset_inter hx).1⟩
  separator_small := C.separator_small

theorem left_mem_A {G : SimpleGraph V} (C : SeparatedCover G) :
    C.left_nonempty.some ∈ C.A :=
  C.left_nonempty.some_mem.1

theorem left_notMem_B {G : SimpleGraph V} (C : SeparatedCover G) :
    C.left_nonempty.some ∉ C.B :=
  C.left_nonempty.some_mem.2

theorem right_mem_B {G : SimpleGraph V} (C : SeparatedCover G) :
    C.right_nonempty.some ∈ C.B :=
  C.right_nonempty.some_mem.1

theorem right_notMem_A {G : SimpleGraph V} (C : SeparatedCover G) :
    C.right_nonempty.some ∉ C.A :=
  C.right_nonempty.some_mem.2

end SeparatedCover

/-- Vertices reachable from $root$ after deleting $S$, before adding $S$ back. -/
def deletedReachCore (G : SimpleGraph V) (S : Finset V) (root : {v : V // v ∉ S}) :
    Set V :=
  {v | ∃ hv : v ∉ S, (deleteVertices G S).Reachable root ⟨v, hv⟩}

/-- One side of the separated cover, with the separator included. -/
def deletedReachSide (G : SimpleGraph V) (S : Finset V) (root : {v : V // v ∉ S}) :
    Set V :=
  {v | v ∈ S ∨ v ∈ deletedReachCore G S root}

/-- The other side of the separated cover, with the separator included. -/
def deletedOtherSide (G : SimpleGraph V) (S : Finset V) (root : {v : V // v ∉ S}) :
    Set V :=
  {v | v ∈ S ∨ v ∉ deletedReachCore G S root}

private lemma deleted_cover (G : SimpleGraph V) (S : Finset V) (root : {v : V // v ∉ S}) :
    deletedReachSide G S root ∪ deletedOtherSide G S root = Set.univ := by
  ext v
  by_cases hv : v ∈ deletedReachSide G S root
  · simp [deletedOtherSide, hv]
  · have hvS : v ∉ S := by
      intro hvS
      exact hv (Or.inl hvS)
    have hvCore : v ∉ deletedReachCore G S root := by
      intro hvCore
      exact hv (Or.inr hvCore)
    simp [deletedReachSide, deletedOtherSide, hvS, hvCore]

private lemma deleted_no_edge (G : SimpleGraph V) (S : Finset V)
    (root : {v : V // v ∉ S}) :
    ∀ ⦃x y : V⦄,
      x ∈ deletedReachSide G S root → x ∉ deletedOtherSide G S root →
      y ∈ deletedOtherSide G S root → y ∉ deletedReachSide G S root →
      ¬ G.Adj x y := by
  intro x y hxA _hyNotB hyB hyNotA hxy
  have hxCore : x ∈ deletedReachCore G S root := by
    rcases hxA with hxS | hxCore
    · exact False.elim (_hyNotB (Or.inl hxS))
    · exact hxCore
  rcases hxCore with ⟨hxS, hxreach⟩
  have hyS : y ∉ S := by
    intro hys
    exact hyNotA (Or.inl hys)
  have hyReach : (deleteVertices G S).Reachable root ⟨y, hyS⟩ :=
    hxreach.trans (SimpleGraph.Adj.reachable (show (deleteVertices G S).Adj ⟨x, hxS⟩ ⟨y, hyS⟩ from hxy))
  exact hyNotA (Or.inr ⟨hyS, hyReach⟩)

private lemma deleted_left_nonempty (G : SimpleGraph V) (S : Finset V)
    (root : {v : V // v ∉ S}) :
    (deletedReachSide G S root \ deletedOtherSide G S root).Nonempty := by
  refine ⟨root, ?_⟩
  constructor
  · exact Or.inr ⟨root.2, SimpleGraph.Reachable.rfl⟩
  · simp [deletedOtherSide, deletedReachCore, root.2]

private lemma deleted_right_nonempty (G : SimpleGraph V) (S : Finset V)
    {root other : {v : V // v ∉ S}}
    (hnot : ¬ (deleteVertices G S).Reachable root other) :
    (deletedOtherSide G S root \ deletedReachSide G S root).Nonempty := by
  refine ⟨other, ?_⟩
  have hother_not : other.1 ∉ deletedReachCore G S root := by
    rintro ⟨hS, hreach⟩
    exact hnot (by
      simpa using hreach)
  constructor
  · exact Or.inr hother_not
  · intro hA
    rcases hA with hS | hCore
    · exact other.2 hS
    · exact hother_not hCore

private lemma deleted_separator_subset (G : SimpleGraph V) (S : Finset V)
    (root : {v : V // v ∉ S}) :
    deletedReachSide G S root ∩ deletedOtherSide G S root ⊆ (S : Set V) := by
  intro v hv
  rcases hv.1 with hvS | hvCore
  · exact hvS
  rcases hv.2 with hvS | hvNotCore
  · exact hvS
  · exact False.elim (hvNotCore hvCore)

private lemma deleted_separator_superset (G : SimpleGraph V) (S : Finset V)
    (root : {v : V // v ∉ S}) :
    (S : Set V) ⊆ deletedReachSide G S root ∩ deletedOtherSide G S root := by
  intro v hv
  exact ⟨Or.inl hv, Or.inl hv⟩

/--
If a graph has at least 4 vertices and is not 3-connected, then it has a
low-order separated cover.
-/
theorem not_three_connected_decomp [Finite V] (G : SimpleGraph V)
    (hcard : 4 ≤ Nat.card V) (hnot : ¬ ThreeConnected G) :
    Nonempty (SeparatedCover G) := by
  classical
  have hsep_exists : ∃ S : Finset V, S.card ≤ 2 ∧ IsVertexSeparator G S := by
    by_contra hnone
    apply hnot
    constructor
    · exact hcard
    · intro S hS hsep
      exact hnone ⟨S, hS, hsep⟩
  rcases hsep_exists with ⟨S, hSsmall, x, y, hxy⟩
  exact ⟨{
    A := deletedReachSide G S x
    B := deletedOtherSide G S x
    separator := S
    cover := deleted_cover G S x
    no_edge := deleted_no_edge G S x
    left_nonempty := deleted_left_nonempty G S x
    right_nonempty := deleted_right_nonempty G S hxy
    inter_subset_separator := deleted_separator_subset G S x
    separator_subset_inter := deleted_separator_superset G S x
    separator_small := hSsmall
  }⟩

/-- Deleted-vertex homomorphism from $G$ to the coerced top subgraph. -/
noncomputable def topDeleteHom [DecidableEq V] (G : SimpleGraph V)
    (T : Finset (⊤ : G.Subgraph).verts) :
    deleteVertices G (T.image (Function.Embedding.subtype _)) →g
      deleteVertices (⊤ : G.Subgraph).coe T := by
  classical
  refine ⟨?f, ?map⟩
  · intro a
    refine ⟨⟨a.1, by simp [SimpleGraph.Subgraph.verts_top]⟩, ?_⟩
    intro ht
    exact a.2 (by
      refine Finset.mem_image.mpr
        ⟨⟨a.1, by simp [SimpleGraph.Subgraph.verts_top]⟩, ht, rfl⟩)
  · intro a b hab
    exact (show (deleteVertices (⊤ : G.Subgraph).coe T).Adj
        ⟨⟨a.1, by simp [SimpleGraph.Subgraph.verts_top]⟩, by
          intro ht
          exact a.2 (by
            refine Finset.mem_image.mpr
              ⟨⟨a.1, by simp [SimpleGraph.Subgraph.verts_top]⟩, ht, rfl⟩)⟩
        ⟨⟨b.1, by simp [SimpleGraph.Subgraph.verts_top]⟩, by
          intro ht
          exact b.2 (by
            refine Finset.mem_image.mpr
              ⟨⟨b.1, by simp [SimpleGraph.Subgraph.verts_top]⟩, ht, rfl⟩)⟩ from by
      have hab' : G.Adj a.1 b.1 := SimpleGraph.induce_adj.mp hab
      simpa [deleteVertices, SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.top_adj] using hab')

private lemma not_mem_image_subtype_of_not_mem [DecidableEq V] {G : SimpleGraph V}
    {T : Finset (⊤ : G.Subgraph).verts} {x : (⊤ : G.Subgraph).verts}
    (hx : x ∉ T) : x.1 ∉ T.image (Function.Embedding.subtype _) := by
  classical
  intro hxmem
  rcases Finset.mem_image.mp hxmem with ⟨t, ht, htval⟩
  have htx : t = x := Subtype.ext htval
  exact hx (htx ▸ ht)

/-- If $G$ is 3-connected, then the coerced top subgraph is 3-connected. -/
theorem threeConnected_topCoe [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (hG : ThreeConnected G) :
    ThreeConnected (⊤ : G.Subgraph).coe := by
  classical
  constructor
  · rw [SimpleGraph.Subgraph.verts_top]
    rw [Nat.card_congr (Equiv.Set.univ V)]
    exact hG.1
  · intro T hT hsep
    rcases hsep with ⟨x, y, hxy⟩
    let S : Finset V := T.image (Function.Embedding.subtype _)
    have hSsmall : S.card ≤ 2 := by
      have hcard : S.card = T.card := by
        exact Finset.card_image_of_injective T (Function.Embedding.subtype _).injective
      exact hcard.trans_le hT
    have hxS : x.1.1 ∉ S := by
      exact not_mem_image_subtype_of_not_mem x.2
    have hyS : y.1.1 ∉ S := by
      exact not_mem_image_subtype_of_not_mem y.2
    have hGsep : IsVertexSeparator G S := by
      refine ⟨⟨x.1.1, hxS⟩, ⟨y.1.1, hyS⟩, ?_⟩
      intro hreach
      have hreachTop :=
        SimpleGraph.Reachable.map (topDeleteHom G T) hreach
      have hxmap : (topDeleteHom G T) ⟨x.1.1, hxS⟩ = x := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      have hymap : (topDeleteHom G T) ⟨y.1.1, hyS⟩ = y := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [hxmap, hymap] at hreachTop
      exact hxy hreachTop
    exact hG.2 S hSsmall hGsep

end Lax10Proofs
