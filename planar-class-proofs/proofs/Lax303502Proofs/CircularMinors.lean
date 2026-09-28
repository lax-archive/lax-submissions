import Lax303502Proofs.CircleNormalization
import Lax303502Proofs.CircularOrder
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

namespace Lax303502Proofs

structure CircularDrawing {V : Type*} (G : SimpleGraph V) where
  parameter : V → ℝ
  injective : Function.Injective parameter
  noncrossing : ∀ {a b c d : V}, G.Adj a b → G.Adj c d →
    Disjoint ({a,b} : Set V) {c,d} →
    SameArc (parameter a) (parameter b) (parameter c) (parameter d)

def ParametricDrawing.toCircular {V : Type*} {G : SimpleGraph V}
    (D : ParametricDrawing G) : CircularDrawing G where
  parameter := D.parameter
  injective := D.injective
  noncrossing := by
    intro a b c d hab hcd hd
    have hn : a≠c ∧ a≠d ∧ b≠c ∧ b≠d := by
      simpa [Set.disjoint_left,and_assoc] using hd
    exact (disjoint_chords_iff_sameArc (D.injective.ne hab.ne) (D.injective.ne hcd.ne)
      (D.injective.ne hn.1) (D.injective.ne hn.2.1)
      (D.injective.ne hn.2.2.1) (D.injective.ne hn.2.2.2)).mp (D.disjointEdges hab hcd hd)

def CircularDrawing.toParametric {V : Type*} {G : SimpleGraph V}
    (D : CircularDrawing G) : ParametricDrawing G where
  parameter := D.parameter
  injective := D.injective
  disjointEdges := by
    intro a b c d hab hcd hd
    have hn : a≠c ∧ a≠d ∧ b≠c ∧ b≠d := by
      simpa [Set.disjoint_left,and_assoc] using hd
    exact (disjoint_chords_iff_sameArc (D.injective.ne hab.ne) (D.injective.ne hcd.ne)
      (D.injective.ne hn.1) (D.injective.ne hn.2.1)
      (D.injective.ne hn.2.2.1) (D.injective.ne hn.2.2.2)).mpr (D.noncrossing hab hcd hd)

theorem connected_constant {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hS : (G.induce S).Preconnected) (P : V → Prop)
    (hedge : ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → (P a ↔ P b))
    {a b : V} (ha : a∈S) (hb : b∈S) : P a ↔ P b := by
  obtain ⟨p⟩ := hS ⟨a,ha⟩ ⟨b,hb⟩
  have walk_constant {x y : S} (q : (G.induce S).Walk x y) : P x.val ↔ P y.val := by
    induction q with
    | nil => rfl
    | @cons x y z h q ih => exact (hedge x x.property y y.property h).trans ih
  exact walk_constant p

theorem CircularDrawing.connected_noncrossing {V : Type*} {G : SimpleGraph V}
    (D : CircularDrawing G) {S T : Set V}
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hST : Disjoint S T) {a b c d : V} (ha : a∈S) (hb : b∈S) (hc : c∈T) (hd : d∈T) :
    SameArc (D.parameter a) (D.parameter b) (D.parameter c) (D.parameter d) := by
  have ne {x y : V} (hx : x∈S) (hy : y∈T) : D.parameter x ≠ D.parameter y := by
    apply D.injective.ne
    intro he
    subst y
    exact Set.disjoint_left.mp hST hx hy
  have single {x y : V} (hx : x∈S) (hy : y∈S) (hxy : G.Adj x y) :
      SameArc (D.parameter x) (D.parameter y) (D.parameter c) (D.parameter d) := by
    apply connected_constant hT (fun z => (D.parameter x<D.parameter z ↔ D.parameter y<D.parameter z))
      (a:=c) (b:=d) ?_ hc hd
    intro z hz w hw hzw
    apply D.noncrossing hxy hzw
    rw [Set.disjoint_left]
    intro v hv hv'
    have hs : v∈S := by rcases hv with rfl | rfl; exact hx; exact hy
    have ht : v∈T := by rcases hv' with rfl | rfl; exact hz; exact hw
    exact Set.disjoint_left.mp hST hs ht
  apply (sameArc_symm (ne ha hc) (ne ha hd) (ne hb hc) (ne hb hd)).mpr
  apply connected_constant hS (fun z => (D.parameter c<D.parameter z ↔ D.parameter d<D.parameter z))
    (a:=a) (b:=b) ?_ ha hb
  intro x hx y hy hxy
  exact (sameArc_symm (ne hx hc) (ne hx hd) (ne hy hc) (ne hy hd)).mp (single hx hy hxy)

/-- Choose one vertex from each connected branch set. Its inherited circular
order is still noncrossing: each minor edge joins two connected branch sets. -/
noncomputable def CircularDrawing.minor {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (D : CircularDrawing G) (M : Lax68.GraphMinors.MinorModel H G) : CircularDrawing H := by
  classical
  let f : W → V := fun w => (Classical.choice (M.connected w).nonempty).val
  have hf (w : W) : f w ∈ M.branchSet w := (Classical.choice (M.connected w).nonempty).property
  have fi : Function.Injective f := by
    intro a b he
    by_contra hab
    exact Set.disjoint_left.mp (M.disjoint hab) (hf a) (he ▸ hf b)
  refine ⟨D.parameter ∘ f,D.injective.comp fi,?_⟩
  intro a b c d hab hcd hd
  have conn {x y : W} (hxy : H.Adj x y) :
      (G.induce (M.branchSet x ∪ M.branchSet y)).Connected := by
    obtain ⟨v,hv,w,hw,hvw⟩ := M.adjacent hxy
    exact SimpleGraph.connected_induce_union (M.connected x).preconnected
      (M.connected y).preconnected hv hw hvw
  have hn : a≠c ∧ a≠d ∧ b≠c ∧ b≠d := by
    simpa [Set.disjoint_left,and_assoc] using hd
  apply D.connected_noncrossing (conn hab).preconnected (conn hcd).preconnected
    (S:=M.branchSet a ∪ M.branchSet b) (T:=M.branchSet c ∪ M.branchSet d)
  · exact (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_right.mpr ⟨M.disjoint hn.1,M.disjoint hn.2.1⟩,
        Set.disjoint_union_right.mpr ⟨M.disjoint hn.2.2.1,M.disjoint hn.2.2.2⟩⟩)
  · exact Or.inl (hf a)
  · exact Or.inr (hf b)
  · exact Or.inl (hf c)
  · exact Or.inr (hf d)

theorem outerplanar_minor {V W : Type*} [Finite V] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : Lax68.Outerplanar.IsOuterplanar G) (hH : Lax68.GraphMinors.IsMinor H G) :
    Lax68.Outerplanar.IsOuterplanar H := by
  obtain ⟨D⟩ := hG
  obtain ⟨M⟩ := hH
  obtain ⟨P⟩ := outerplane_parametric D
  exact ⟨(P.toCircular.minor M).toParametric.toOuterplane⟩

theorem not_three_sameArc {a b c d : ℝ} (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    ¬(SameArc a b c d ∧ SameArc a c b d ∧ SameArc a d b c) := by
  have flip {x y : ℝ} (h : x≠y) : y<x ↔ ¬x<y := by
    constructor
    · intro h'; exact not_lt_of_ge h'.le
    · intro h'; exact lt_of_le_of_ne (le_of_not_gt h') (Ne.symm h)
  simp only [SameArc,flip hbc,flip hbd,flip hcd]
  tauto

theorem no_circular_K4 : ¬Nonempty (CircularDrawing Lax68.GraphMinors.K4) := by
  rintro ⟨D⟩
  have h₁ := D.noncrossing (a:=0) (b:=1) (c:=2) (d:=3) (by decide) (by decide) (by simp [Set.disjoint_left])
  have h₂ := D.noncrossing (a:=0) (b:=2) (c:=1) (d:=3) (by decide) (by decide) (by simp [Set.disjoint_left])
  have h₃ := D.noncrossing (a:=0) (b:=3) (c:=1) (d:=2) (by decide) (by decide) (by simp [Set.disjoint_left])
  exact not_three_sameArc (D.injective.ne (by decide : (1:Fin 4)≠2))
    (D.injective.ne (by decide : (1:Fin 4)≠3))
    (D.injective.ne (by decide : (2:Fin 4)≠3)) ⟨h₁,h₂,h₃⟩

theorem no_circular_K23 : ¬Nonempty (CircularDrawing Lax68.GraphMinors.K23) := by
  rintro ⟨D⟩
  let a : Fin 2 ⊕ Fin 3 := Sum.inl 0
  let b : Fin 2 ⊕ Fin 3 := Sum.inl 1
  have opposite (i j : Fin 3) (hij : i≠j) :
      ¬SameArc (D.parameter a) (D.parameter b) (D.parameter (.inr i)) (D.parameter (.inr j)) := by
    intro he
    have h₁ := D.noncrossing (a:=a) (b:=.inr i) (c:=b) (d:=.inr j)
      (by simp [a]) (by simp [b]) (by simp [a,b,Set.disjoint_left,hij])
    have h₂ := D.noncrossing (a:=a) (b:=.inr j) (c:=b) (d:=.inr i)
      (by simp [a]) (by simp [b]) (by simp [a,b,Set.disjoint_left,hij.symm])
    exact not_three_sameArc (D.injective.ne (by simp [b]))
      (D.injective.ne (by simp [b])) (D.injective.ne (by simpa using hij)) ⟨he,h₁,h₂⟩
  have h₁ := opposite 0 1 (by decide)
  have h₂ := opposite 0 2 (by decide)
  have h₃ := opposite 1 2 (by decide)
  unfold SameArc at h₁ h₂ h₃
  tauto

theorem outerplanar_excludes_minors {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : Lax68.Outerplanar.IsOuterplanar G) :
    Lax68.Outerplanar.IsOuterplanarByExcludedMinors G := by
  obtain ⟨D⟩ := hG
  obtain ⟨P⟩ := outerplane_parametric D
  constructor
  · rintro ⟨M⟩
    exact no_circular_K4 ⟨P.toCircular.minor M⟩
  · rintro ⟨M⟩
    exact no_circular_K23 ⟨P.toCircular.minor M⟩

end Lax303502Proofs
