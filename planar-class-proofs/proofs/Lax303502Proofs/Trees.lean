import Lax303502Proofs.LeafGeometry
import Lax68.TreeOuterplanar

set_option autoImplicit false

namespace Lax303502Proofs

universe u

/-- Proof-side circle-drawing data, keeping the real parameters available
when a leaf is inserted. -/
structure ParametricDrawing {V : Type u} (G : SimpleGraph V) where
  parameter : V → ℝ
  injective : Function.Injective parameter
  disjointEdges : ∀ {a b c d : V}, G.Adj a b → G.Adj c d →
    Disjoint ({a, b} : Set V) ({c, d} : Set V) →
    Disjoint (segment ℝ (circlePoint (parameter a)) (circlePoint (parameter b)))
      (segment ℝ (circlePoint (parameter c)) (circlePoint (parameter d)))

noncomputable def ParametricDrawing.toOuterplane {V : Type u} {G : SimpleGraph V}
    (D : ParametricDrawing G) : Lax68.Outerplanar.OuterplaneDrawing G where
  point v := circlePoint (D.parameter v)
  injective := circlePoint_injective.comp D.injective
  noVertexOnEdge := by
    intro a b c _ hca hcb
    exact circle_not_mem_segment (circlePoint_onCircle _) (circlePoint_onCircle _)
      (circlePoint_onCircle _) ((circlePoint_injective.comp D.injective).ne hca)
      ((circlePoint_injective.comp D.injective).ne hcb)
  disjointEdges := D.disjointEdges
  radius := 1
  radius_pos := by norm_num
  onBoundary v := by simpa using circlePoint_onCircle (D.parameter v)

theorem insert_leaf {V : Type u} [Fintype V] {G : SimpleGraph V} {v w : V}
    (hvw : G.Adj v w) (hleaf : ∀ z, G.Adj v z → z = w)
    (D : ParametricDrawing (G.induce {v}ᶜ)) : Nonempty (ParametricDrawing G) := by
  classical
  let W := {z : V // z ∈ ({v}ᶜ : Set V)}
  have hw : w ∈ ({v}ᶜ : Set V) := by simpa using hvw.ne.symm
  let w' : W := ⟨w, hw⟩
  let a := D.parameter w'
  obtain ⟨b, hab, hgap⟩ := finite_parameter_gap (Finset.univ.image D.parameter) a
  have hgap' (z : W) : D.parameter z ≤ a ∨ b < D.parameter z :=
    hgap _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)
  have hbne (z : W) : b ≠ D.parameter z := by
    rcases hgap' z with hz | hz <;> linarith
  let f : V → ℝ := fun z => if hz : z = v then b else D.parameter ⟨z, hz⟩
  have fv : f v = b := by simp [f]
  have fold (z : W) : f z.val = D.parameter z := by
    have hz : z.val ≠ v := z.property
    simp only [f, dif_neg hz]
    exact congrArg D.parameter (Subtype.ext rfl)
  have fw : f w = a := fold w'
  have fi : Function.Injective f := by
    intro x y h
    by_cases hx : x = v
    · subst x
      by_cases hy : y = v
      · exact hy.symm
      · have he : b = D.parameter ⟨y, hy⟩ := by simpa [f, hy] using h
        exact (hbne ⟨y, hy⟩ he).elim
    · by_cases hy : y = v
      · subst y
        have he : b = D.parameter ⟨x, hx⟩ := by simpa [f, hx] using h.symm
        exact (hbne ⟨x, hx⟩ he).elim
      · have he : D.parameter ⟨x, hx⟩ = D.parameter ⟨y, hy⟩ := by
          simpa [f, hx, hy] using h
        exact congrArg Subtype.val (D.injective he)
  have outside (z : V) (hzv : z ≠ v) (hzw : z ≠ w) : f z < a ∨ b < f z := by
    have hne : D.parameter ⟨z, hzv⟩ ≠ a := by
      intro h
      exact hzw (congrArg Subtype.val (D.injective h))
    rcases hgap' ⟨z, hzv⟩ with hz | hz
    · exact Or.inl (by rw [fold ⟨z, hzv⟩]; exact lt_of_le_of_ne hz hne)
    · exact Or.inr (by rw [fold ⟨z, hzv⟩]; exact hz)
  have leaf_edge (c d : V) (hcv : c ≠ v) (hcw : c ≠ w)
      (hdv : d ≠ v) (hdw : d ≠ w) :
      Disjoint (segment ℝ (circlePoint (f v)) (circlePoint (f w)))
        (segment ℝ (circlePoint (f c)) (circlePoint (f d))) := by
    rw [fv, fw, segment_symm ℝ (circlePoint b)]
    exact adjacent_chord_disjoint hab (outside c hcv hcw) (outside d hdv hdw)
  refine ⟨⟨f, fi, ?_⟩⟩
  intro x y z t hxy hzt hd
  have hne : x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t := by
    simpa [Set.disjoint_left, and_assoc] using hd
  by_cases hx : x = v
  · subst x
    have hy : y = w := hleaf y hxy
    subst y
    exact leaf_edge z t hne.1.symm hne.2.2.1.symm hne.2.1.symm hne.2.2.2.symm
  by_cases hy : y = v
  · subst y
    have hxw : x = w := hleaf x hxy.symm
    subst x
    rw [segment_symm ℝ (circlePoint (f w))]
    exact leaf_edge z t hne.2.2.1.symm hne.1.symm hne.2.2.2.symm hne.2.1.symm
  by_cases hz : z = v
  · subst z
    have htw : t = w := hleaf t hzt
    subst t
    exact (leaf_edge x y hne.1 hne.2.1 hne.2.2.1 hne.2.2.2).symm
  by_cases ht : t = v
  · subst t
    have hzw : z = w := hleaf z hzt.symm
    subst z
    rw [segment_symm ℝ (circlePoint (f w)) (circlePoint (f v))]
    exact (leaf_edge x y hne.2.1 hne.1 hne.2.2.2 hne.2.2.1).symm
  have hold := D.disjointEdges (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    (c := ⟨z, hz⟩) (d := ⟨t, ht⟩) hxy hzt (by
      rw [Set.disjoint_left]
      intro q hq hq'
      have hqv : q.val ∈ ({x, y} : Set V) := by
        rcases hq with hq | hq
        · left; exact congrArg Subtype.val hq
        · right; exact congrArg Subtype.val hq
      have hqv' : q.val ∈ ({z, t} : Set V) := by
        rcases hq' with hq | hq
        · left; exact congrArg Subtype.val hq
        · right; exact congrArg Subtype.val hq
      exact Set.disjoint_left.mp hd hqv hqv')
  simpa only [← fold] using hold

theorem tree_parametric {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) : Nonempty (ParametricDrawing G) := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hsub : Subsingleton V
    · let := hsub
      exact ⟨⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _,
        fun h _ _ => (h.ne (Subsingleton.elim _ _)).elim⟩⟩
    · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨w, hvw, hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      have htree : (G.induce {v}ᶜ).IsTree :=
        ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hv, hG.isAcyclic.induce _⟩
      have hcard : Fintype.card {z : V // z ∈ ({v}ᶜ : Set V)} < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := v) (by simp)
      obtain ⟨D⟩ := ih _ hcard (G.induce {v}ᶜ) htree rfl
      exact insert_leaf hvw hw D

/--
---
conclusion: Lax68.TreeOuterplanar.tree_outerplanar
---
Every finite tree admits a straight-line drawing with all vertices on the unit
circle, independently of the excluded-minor characterization.

# Proof strategy

Induct on the number of vertices. A nontrivial finite tree has a leaf, and
removing it leaves a tree. Keep the smaller tree's circle drawing and insert
the leaf immediately after its neighbour in the parameter order. Finiteness
provides a gap with no other vertex. The chord for the new edge strictly
separates all other old vertices from the empty circular cap, so it misses
every edge with disjoint endpoints. The same-circle tangent inequality rules
out vertices lying on edges. Single-vertex trees are handled directly.

# Attribution

Diestel, *Graph Theory*, sixth edition, Section 1.5, gives the leaf-removal
induction. Chapter 4, Exercise 23, states the outerplanarity characterization
but does not supply a direct drawing proof. As an additional source for the
geometric construction, Pach and Törőcsik, *Layout of rooted trees*,
CS-TR-369-92 (1992), page 2, Algorithm 1, recursively embed a tree into points
in convex position. Here the specialization to a circle is implemented by
leaf insertion and explicit rational coordinates; the separation algebra is
proved in this submission.
-/
theorem tree_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Trees.IsTree G → Lax68.Outerplanar.IsOuterplanar G := by
  intro hG
  let := Fintype.ofFinite V
  obtain ⟨D⟩ := tree_parametric G hG
  exact ⟨D.toOuterplane⟩

end Lax303502Proofs
