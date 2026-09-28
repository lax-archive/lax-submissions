import Lax303502Proofs.SmallPlanar
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FunProp

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.StraightLineDrawings Set Topology

/-- Edges and singleton vertices, including isolated vertices. -/
def DrawingCell {V : Type*} (G : SimpleGraph V) (a b : V) : Prop := a = b ∨ G.Adj a b

/-- All disjoint cells have disjoint geometric realizations. -/
def SeparatedPlacement {V : Type*} (G : SimpleGraph V) (p : V → Point) : Prop :=
  ∀ a b c d, DrawingCell G a b → DrawingCell G c d →
    Disjoint ({a,b} : Set V) ({c,d} : Set V) →
    Disjoint (segment ℝ (p a) (p b)) (segment ℝ (p c) (p d))

theorem drawing_separated {V : Type*} {G : SimpleGraph V} (D : StraightLineDrawing G) :
    SeparatedPlacement G D.point := by
  intro a b c d hab hcd hdis
  have hn : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
    simpa [Set.disjoint_left,and_assoc] using hdis
  rcases hab with rfl | hab <;> rcases hcd with rfl | hcd
  · simpa using D.injective.ne hn.1
  · simpa only [segment_same,Set.disjoint_singleton_left] using
      D.noVertexOnEdge hcd hn.1 hn.2.1
  · simpa only [segment_same,Set.disjoint_singleton_right] using
      D.noVertexOnEdge hab (Ne.symm hn.1) (Ne.symm hn.2.2.1)
  · exact D.disjointEdges hab hcd hdis

def separated_drawing {V : Type*} {G : SimpleGraph V} {p : V → Point}
    (h : SeparatedPlacement G p) : StraightLineDrawing G where
  point := p
  injective := by
    intro a b hab
    by_contra hn
    have hd := h a a b b (Or.inl rfl) (Or.inl rfl) (by simpa using hn)
    simp [hab] at hd
  noVertexOnEdge := by
    intro a b c hab hca hcb
    have hd := h c c a b (Or.inl rfl) (Or.inr hab) (by simp [hca,hcb])
    simpa only [segment_same,Set.disjoint_singleton_left] using hd
  disjointEdges hab hcd hdis := h _ _ _ _ (Or.inr hab) (Or.inr hcd) hdis

private theorem mem_segment_mix {p q z : Point} :
    z ∈ segment ℝ p q ↔ ∃ t : unitInterval, SP.mix t p q = z := by
  constructor
  · intro hz
    obtain ⟨t,ht,ht',he⟩ := SP.segment_mix hz
    exact ⟨⟨t,ht,ht'⟩,he⟩
  · rintro ⟨t,rfl⟩
    exact ⟨1-t,t,by have := t.property.2; linarith,t.property.1,by ring,rfl⟩

/-- Intersection of two closed segments is a closed condition on their four
endpoints. Compactness of the two interpolation parameters is essential. -/
theorem isClosed_segment_intersection {V : Type*} (a b c d : V) :
    IsClosed {p : V → Point | ¬Disjoint (segment ℝ (p a) (p b)) (segment ℝ (p c) (p d))} := by
  let Z : Set ((V → Point) × (unitInterval × unitInterval)) :=
    {z | SP.mix z.2.1 (z.1 a) (z.1 b) = SP.mix z.2.2 (z.1 c) (z.1 d)}
  have hZ : IsClosed Z := by
    apply isClosed_eq
    · dsimp [SP.mix]; fun_prop
    · dsimp [SP.mix]; fun_prop
  have hclosed := isClosedMap_fst_of_compactSpace Z hZ
  have heq : Prod.fst '' Z = {p : V → Point |
      ¬Disjoint (segment ℝ (p a) (p b)) (segment ℝ (p c) (p d))} := by
    ext p
    constructor
    · rintro ⟨⟨q,s,t⟩,h,rfl⟩ hd
      have hs : SP.mix s (q a) (q b) ∈ segment ℝ (q a) (q b) := mem_segment_mix.mpr ⟨s,rfl⟩
      have ht : SP.mix s (q a) (q b) ∈ segment ℝ (q c) (q d) := mem_segment_mix.mpr ⟨t,h.symm⟩
      exact Set.disjoint_left.mp hd hs ht
    · intro h
      obtain ⟨z,hz,hz'⟩ := Set.not_disjoint_iff.mp h
      obtain ⟨s,hs⟩ := mem_segment_mix.mp hz
      obtain ⟨t,ht⟩ := mem_segment_mix.mp hz'
      exact ⟨(p,s,t),hs.trans ht.symm,rfl⟩
  exact heq ▸ hclosed

/-- A finite straight-line drawing is stable under sufficiently small
perturbations of all its vertex coordinates. -/
theorem isOpen_separatedPlacement {V : Type*} [Finite V] (G : SimpleGraph V) :
    IsOpen {p : V → Point | SeparatedPlacement G p} := by
  unfold SeparatedPlacement
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro a
  apply isOpen_iInter_of_finite
  intro b
  apply isOpen_iInter_of_finite
  intro c
  apply isOpen_iInter_of_finite
  intro d
  apply isOpen_iInter_of_finite
  intro _
  apply isOpen_iInter_of_finite
  intro _
  apply isOpen_iInter_of_finite
  intro _
  have hc := isClosed_segment_intersection (V := V) a b c d
  have ho := hc.isOpen_compl
  convert ho using 1
  ext p
  simp

theorem drawing_eventually_separated {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : StraightLineDrawing G) : ∀ᶠ p in 𝓝 D.point, SeparatedPlacement G p :=
  (isOpen_separatedPlacement G).mem_nhds (drawing_separated D)

end Lax303502Proofs
