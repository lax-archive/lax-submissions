import Lax17Proofs.Source.ReedTreeDecomposition

namespace Lax17Proofs

universe u v w

/-!
# Gluing region decompositions

This file supplies the recursive gluing step for `RegionDecomposition`.  The
center bag contains the adhesion of the two sides, and is joined to the root
bag of each child decomposition.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace ReedTreeDecomposition.RegionDecomposition

variable {G : _root_.SimpleGraph V} {C C₁ C₂ : Finset V}

private abbrev glueCenter {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    ((Unit ⊕ D₁.Node) ⊕ D₂.Node) :=
  Sum.inl (Sum.inl ())

private abbrev glueLeft {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₁.Node → ((Unit ⊕ D₁.Node) ⊕ D₂.Node) :=
  fun i => Sum.inl (Sum.inr i)

private abbrev glueRight {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₂.Node → ((Unit ⊕ D₁.Node) ⊕ D₂.Node) :=
  Sum.inr

private def glueLeftHom {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₁.tree →g attachTree D₁ D₂ where
  toFun := glueLeft D₁ D₂
  map_rel' := by
    intro i j hij
    simp [attachTree, ReedTreeDecomposition.joinTrees, hij]

private def glueRightHom {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₂.tree →g attachTree D₁ D₂ where
  toFun := glueRight D₁ D₂
  map_rel' := by
    intro i j hij
    simp [attachTree, ReedTreeDecomposition.joinTrees, hij]

private def glueLeftRootToCenter {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    (attachTree D₁ D₂).Walk (glueLeft D₁ D₂ D₁.root) (glueCenter D₁ D₂) :=
  .cons (by
    simp only [attachTree, ReedTreeDecomposition.joinTrees,
      _root_.SimpleGraph.sup_adj, _root_.SimpleGraph.sum_adj, false_or]
    exact Or.inl ((_root_.SimpleGraph.edge_adj (Sum.inl ()) (Sum.inr D₁.root)
      (Sum.inr D₁.root) (Sum.inl ())).2
      ⟨Or.inr ⟨rfl, rfl⟩, by simp⟩)) .nil

private def glueCenterToRightRoot {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    (attachTree D₁ D₂).Walk (glueCenter D₁ D₂) (glueRight D₁ D₂ D₂.root) :=
  .cons (by
    simp only [attachTree, ReedTreeDecomposition.joinTrees,
      _root_.SimpleGraph.sup_adj, _root_.SimpleGraph.sum_adj, false_or]
    exact ((_root_.SimpleGraph.edge_adj (Sum.inl (Sum.inl ())) (Sum.inr D₂.root)
      (glueCenter D₁ D₂) (glueRight D₁ D₂ D₂.root)).2
      ⟨Or.inl ⟨rfl, rfl⟩, by simp⟩)) .nil

/-- Glue two region decompositions across a vertex separation.  The new root
is the center bag `K`; each child root contains the part of `K` lying in that
child.  Besides constructing the decomposition, the conclusion records the
maximum of the center and child bag-cardinality bounds. -/
theorem glue {K : Finset V} (D₁ : RegionDecomposition G C₁)
    (D₂ : RegionDecomposition G C₂) (hsep : VertexSeparation G C C₁ C₂)
    (hoverlap : C₁ ∩ C₂ ⊆ K) (hK : K ⊆ C)
    (hroot₁ : K ∩ C₁ ⊆ D₁.bag D₁.root)
    (hroot₂ : K ∩ C₂ ⊆ D₂.bag D₂.root)
    {b₁ b₂ : ℕ} (hbound₁ : ∀ i, (D₁.bag i).card ≤ b₁)
    (hbound₂ : ∀ i, (D₂.bag i).card ≤ b₂) :
    ∃ D : RegionDecomposition G C,
      D.bag D.root = K ∧
        ∀ i, (D.bag i).card ≤ max K.card (max b₁ b₂) := by
  letI := D₁.nodeFintype
  letI := D₁.nodeDecidableEq
  letI := D₂.nodeFintype
  letI := D₂.nodeDecidableEq
  let center : ((Unit ⊕ D₁.Node) ⊕ D₂.Node) := glueCenter D₁ D₂
  let left : D₁.Node → ((Unit ⊕ D₁.Node) ⊕ D₂.Node) := glueLeft D₁ D₂
  let right : D₂.Node → ((Unit ⊕ D₁.Node) ⊕ D₂.Node) := glueRight D₁ D₂
  let bag : ((Unit ⊕ D₁.Node) ⊕ D₂.Node) → Finset V
    | Sum.inl (Sum.inl _) => K
    | Sum.inl (Sum.inr i) => D₁.bag i
    | Sum.inr j => D₂.bag j
  have hleft_map {v : V} {i j : D₁.Node} (hv : v ∈ C₁)
      (hi : v ∈ D₁.bag i) (hj : v ∈ D₁.bag j) :
      ∃ p : (attachTree D₁ D₂).Walk (left i) (left j),
        ∀ n ∈ p.support, v ∈ bag n := by
    rcases D₁.bag_walk hv hi hj with ⟨p, hp⟩
    let f := glueLeftHom D₁ D₂
    refine ⟨p.map f, ?_⟩
    intro n hn
    have hn' : n ∈ p.support.map f :=
      (congrArg (fun s => n ∈ s) (p.support_map f)).mp hn
    rcases List.mem_map.mp hn' with ⟨m, hm, rfl⟩
    exact hp m hm
  have hright_map {v : V} {i j : D₂.Node} (hv : v ∈ C₂)
      (hi : v ∈ D₂.bag i) (hj : v ∈ D₂.bag j) :
      ∃ p : (attachTree D₁ D₂).Walk (right i) (right j),
        ∀ n ∈ p.support, v ∈ bag n := by
    rcases D₂.bag_walk hv hi hj with ⟨p, hp⟩
    let f := glueRightHom D₁ D₂
    refine ⟨p.map f, ?_⟩
    intro n hn
    have hn' : n ∈ p.support.map f :=
      (congrArg (fun s => n ∈ s) (p.support_map f)).mp hn
    rcases List.mem_map.mp hn' with ⟨m, hm, rfl⟩
    exact hp m hm
  have hleft_connector {v : V} (hvK : v ∈ K)
      (hvr : v ∈ D₁.bag D₁.root) :
      ∀ n ∈ (glueLeftRootToCenter D₁ D₂).support, v ∈ bag n := by
    intro n hn
    simp only [glueLeftRootToCenter, _root_.SimpleGraph.Walk.support_cons,
      _root_.SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    rcases hn with rfl | rfl
    · simpa [bag, glueLeft] using hvr
    · simpa [bag, glueCenter] using hvK
  have hright_connector {v : V} (hvK : v ∈ K)
      (hvr : v ∈ D₂.bag D₂.root) :
      ∀ n ∈ (glueCenterToRightRoot D₁ D₂).support, v ∈ bag n := by
    intro n hn
    simp only [glueCenterToRightRoot, _root_.SimpleGraph.Walk.support_cons,
      _root_.SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    rcases hn with rfl | rfl
    · simpa [bag, glueCenter] using hvK
    · simpa [bag, glueRight] using hvr
  have hleft_connector_reverse {v : V} (hvK : v ∈ K)
      (hvr : v ∈ D₁.bag D₁.root) :
      ∀ n ∈ (glueLeftRootToCenter D₁ D₂).reverse.support, v ∈ bag n := by
    intro n hn
    rw [_root_.SimpleGraph.Walk.support_reverse] at hn
    exact hleft_connector hvK hvr n (by simpa using hn)
  have hright_connector_reverse {v : V} (hvK : v ∈ K)
      (hvr : v ∈ D₂.bag D₂.root) :
      ∀ n ∈ (glueCenterToRightRoot D₁ D₂).reverse.support, v ∈ bag n := by
    intro n hn
    rw [_root_.SimpleGraph.Walk.support_reverse] at hn
    exact hright_connector hvK hvr n (by simpa using hn)
  let D : RegionDecomposition G C :=
    { Node := ((Unit ⊕ D₁.Node) ⊕ D₂.Node)
      tree := attachTree D₁ D₂
      isTree := attachTree_isTree D₁ D₂
      root := center
      bag := bag
      bag_subset := by
        intro i
        rcases i with (⟨_ | i⟩ | j)
        · exact hK
        · exact D₁.bag_subset i |>.trans hsep.left_subset
        · exact D₂.bag_subset j |>.trans hsep.right_subset
      vertex_mem_bag := by
        intro v hv
        have hv' : v ∈ C₁ ∪ C₂ := hsep.cover.symm ▸ hv
        rcases mem_union.mp hv' with hv₁ | hv₂
        · rcases D₁.vertex_mem_bag hv₁ with ⟨i, hi⟩
          exact ⟨left i, hi⟩
        · rcases D₂.vertex_mem_bag hv₂ with ⟨j, hj⟩
          exact ⟨right j, hj⟩
      edge_mem_bag := by
        intro u v huv hu hv
        have hu' : u ∈ C₁ ∪ C₂ := hsep.cover.symm ▸ hu
        have hv' : v ∈ C₁ ∪ C₂ := hsep.cover.symm ▸ hv
        by_cases hu₁ : u ∈ C₁
        · by_cases hv₁ : v ∈ C₁
          · rcases D₁.edge_mem_bag huv hu₁ hv₁ with ⟨i, hiu, hiv⟩
            exact ⟨left i, hiu, hiv⟩
          · have hv₂ : v ∈ C₂ := (mem_union.mp hv').resolve_left hv₁
            by_cases hu₂ : u ∈ C₂
            · rcases D₂.edge_mem_bag huv hu₂ hv₂ with ⟨j, hju, hjv⟩
              exact ⟨right j, hju, hjv⟩
            · exact False.elim (hsep.no_cross hu₁ hu₂ hv₂ hv₁ huv)
        · have hu₂ : u ∈ C₂ := (mem_union.mp hu').resolve_left hu₁
          by_cases hv₂ : v ∈ C₂
          · rcases D₂.edge_mem_bag huv hu₂ hv₂ with ⟨j, hju, hjv⟩
            exact ⟨right j, hju, hjv⟩
          · have hv₁ : v ∈ C₁ := (mem_union.mp hv').resolve_right hv₂
            exact False.elim (hsep.no_cross hv₁ hv₂ hu₂ hu₁ (G.symm huv))
      bag_walk := by
        intro v hv i j hi hj
        rcases i with (⟨_ | i⟩ | i) <;> rcases j with (⟨_ | j⟩ | j)
        · exact ⟨.nil, by simpa [bag] using hi⟩
        · have hv₁ : v ∈ C₁ := D₁.bag_subset j hj
          have hvr : v ∈ D₁.bag D₁.root := hroot₁ (mem_inter.mpr ⟨hi, hv₁⟩)
          rcases hleft_map hv₁ hvr hj with ⟨p, hp⟩
          refine ⟨(glueLeftRootToCenter D₁ D₂).reverse.append p, ?_⟩
          intro n hn
          rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
          rcases hn with hn | hn
          · exact hleft_connector_reverse hi hvr n hn
          · exact hp n hn
        · have hv₂ : v ∈ C₂ := D₂.bag_subset j hj
          have hvr : v ∈ D₂.bag D₂.root := hroot₂ (mem_inter.mpr ⟨hi, hv₂⟩)
          rcases hright_map hv₂ hvr hj with ⟨p, hp⟩
          refine ⟨(glueCenterToRightRoot D₁ D₂).append p, ?_⟩
          intro n hn
          rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
          rcases hn with hn | hn
          · exact hright_connector hi hvr n hn
          · exact hp n hn
        · have hv₁ : v ∈ C₁ := D₁.bag_subset i hi
          have hvr : v ∈ D₁.bag D₁.root := hroot₁ (mem_inter.mpr ⟨hj, hv₁⟩)
          rcases hleft_map hv₁ hi hvr with ⟨p, hp⟩
          refine ⟨p.append (glueLeftRootToCenter D₁ D₂), ?_⟩
          intro n hn
          rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
          rcases hn with hn | hn
          · exact hp n hn
          · exact hleft_connector hj hvr n hn
        · exact hleft_map (D₁.bag_subset i hi) hi hj
        · have hv₁ : v ∈ C₁ := D₁.bag_subset i hi
          have hv₂ : v ∈ C₂ := D₂.bag_subset j hj
          have hvK : v ∈ K := hoverlap (mem_inter.mpr ⟨hv₁, hv₂⟩)
          have hvr₁ : v ∈ D₁.bag D₁.root :=
            hroot₁ (mem_inter.mpr ⟨hvK, hv₁⟩)
          have hvr₂ : v ∈ D₂.bag D₂.root :=
            hroot₂ (mem_inter.mpr ⟨hvK, hv₂⟩)
          rcases hleft_map hv₁ hi hvr₁ with ⟨p, hp⟩
          rcases hright_map hv₂ hvr₂ hj with ⟨q, hq⟩
          refine ⟨(p.append (glueLeftRootToCenter D₁ D₂)).append
            ((glueCenterToRightRoot D₁ D₂).append q), ?_⟩
          intro n hn
          rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
          rcases hn with hn | hn
          · rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
            exact hn.elim (hp n) (hleft_connector hvK hvr₁ n)
          · rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
            exact hn.elim (hright_connector hvK hvr₂ n) (hq n)
        · have hv₂ : v ∈ C₂ := D₂.bag_subset i hi
          have hvr : v ∈ D₂.bag D₂.root := hroot₂ (mem_inter.mpr ⟨hj, hv₂⟩)
          rcases hright_map hv₂ hi hvr with ⟨p, hp⟩
          refine ⟨p.append (glueCenterToRightRoot D₁ D₂).reverse, ?_⟩
          intro n hn
          rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
          rcases hn with hn | hn
          · exact hp n hn
          · exact hright_connector_reverse hj hvr n hn
        · have hv₂ : v ∈ C₂ := D₂.bag_subset i hi
          have hv₁ : v ∈ C₁ := D₁.bag_subset j hj
          have hvK : v ∈ K := hoverlap (mem_inter.mpr ⟨hv₁, hv₂⟩)
          have hvr₂ : v ∈ D₂.bag D₂.root :=
            hroot₂ (mem_inter.mpr ⟨hvK, hv₂⟩)
          have hvr₁ : v ∈ D₁.bag D₁.root :=
            hroot₁ (mem_inter.mpr ⟨hvK, hv₁⟩)
          rcases hright_map hv₂ hi hvr₂ with ⟨p, hp⟩
          rcases hleft_map hv₁ hvr₁ hj with ⟨q, hq⟩
          refine ⟨(p.append (glueCenterToRightRoot D₁ D₂).reverse).append
            ((glueLeftRootToCenter D₁ D₂).reverse.append q), ?_⟩
          intro n hn
          rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
          rcases hn with hn | hn
          · rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
            exact hn.elim (hp n)
              (hright_connector_reverse hvK hvr₂ n)
          · rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hn
            exact hn.elim (hleft_connector_reverse hvK hvr₁ n) (hq n)
        · exact hright_map (D₂.bag_subset i hi) hi hj }
  refine ⟨D, rfl, ?_⟩
  intro i
  rcases i with (⟨_ | i⟩ | j)
  · exact le_max_left _ _
  · exact (hbound₁ i).trans (le_max_of_le_right (le_max_left _ _))
  · exact (hbound₂ j).trans (le_max_of_le_right (le_max_right _ _))

end ReedTreeDecomposition.RegionDecomposition

end SimpleGraph

end Lax17Proofs
