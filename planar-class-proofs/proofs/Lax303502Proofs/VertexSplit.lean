import Lax303502Proofs.DrawingStability
import Lax303502Proofs.EdgeContraction

/-!
The local geometric step in Diestel's contraction proof (Chapter 4,
Lemma 4.4.3 and Exercise 19), isolated from the remaining face and cyclic-order
arguments. Kaiser's Lecture 3, page 4, describes placing the second vertex
close to the contracted vertex in the appropriate sector.

Here the sector is supplied by explicit linear inequalities, one separating
functional per disjoint pair of incident cells. The conclusion is the exact
Lax68 straight-line drawing certificate. This module does not yet derive
the inequalities from a facial order or assert preservation of convex faces.
-/

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.StraightLineDrawings Set Topology Filter

/-- A linear functional evaluated on a segment, relative to an origin. -/
private theorem linear_mix_sub (f : Point →ₗ[ℝ] ℝ) (o a b : Point) (s : ℝ) :
    f (SP.mix s a b - o) = (1-s) * f (a-o) + s * f (b-o) := by
  change f ((1-s) • a + s • b - o) = _
  simp only [map_sub, map_add, map_smul, smul_eq_mul]
  ring

/-- Moving the first endpoint strictly into a separating half-plane keeps
the new segment away from the old one. The second endpoint may lie on the
separating line, provided it is not on the old segment. -/
theorem disjoint_segment_shift {o a b w : Point} (f : Point →ₗ[ℝ] ℝ)
    (ha : f (a-o) ≤ 0) (hb : 0 ≤ f (b-o)) (hw : 0 < f w)
    (havoid : b ∉ segment ℝ o a) {t : ℝ} (ht : 0 < t) :
    Disjoint (segment ℝ o a) (segment ℝ (o + t • w) b) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨s,hs,hs',he⟩ := SP.segment_mix hz
  obtain ⟨r,hr,hr',he'⟩ := SP.segment_mix hz'
  have hleft : f (z-o) ≤ 0 := by
    rw [← he,linear_mix_sub]
    simpa using mul_nonpos_of_nonneg_of_nonpos hs ha
  have hright : f (z-o) = (1-r) * (t * f w) + r * f (b-o) := by
    rw [← he',linear_mix_sub]
    simp
  have hrb := mul_nonneg hr hb
  have hpos : 0 < t * f w := mul_pos ht hw
  have hr1 : r = 1 := by nlinarith
  rw [hr1,SP.mix_one] at he'
  exact havoid (he' ▸ hz)

/-- Move only the vertex `y`, by `t` times a chosen vector. -/
def splitPlacement {V : Type*} [DecidableEq V] (p : V → Point)
    (y : V) (w : Point) (t : ℝ) (v : V) : Point :=
  p v + if v = y then t • w else 0

@[simp] theorem splitPlacement_zero {V : Type*} [DecidableEq V]
    (p : V → Point) (y : V) (w : Point) : splitPlacement p y w 0 = p := by
  funext v
  simp [splitPlacement]

@[simp] theorem splitPlacement_self {V : Type*} [DecidableEq V]
    (p : V → Point) (y : V) (w : Point) (t : ℝ) :
    splitPlacement p y w t y = p y + t • w := by simp [splitPlacement]

theorem splitPlacement_of_ne {V : Type*} [DecidableEq V]
    (p : V → Point) (y : V) (w : Point) (t : ℝ) {v : V} (hv : v ≠ y) :
    splitPlacement p y w t v = p v := by simp [splitPlacement,hv]

theorem continuous_splitPlacement {V : Type*} [DecidableEq V]
    (p : V → Point) (y : V) (w : Point) : Continuous (splitPlacement p y w) := by
  apply continuous_pi
  intro v
  dsimp [splitPlacement]
  split_ifs <;> fun_prop

/-- A local half-plane certificate for splitting the coincident vertices
`x` and `y`. Each disjoint pair of incident cells may use its own separating
line; a single line separating all neighbours is not required. -/
def SplitDirection {V : Type*} (G : SimpleGraph V) (p : V → Point)
    (x y : V) (w : Point) : Prop :=
  ∀ a b, DrawingCell G x a → DrawingCell G y b → a ≠ y → b ≠ x → a ≠ b →
    ∃ f : Point →ₗ[ℝ] ℝ,
      f (p a-p x) ≤ 0 ∧ 0 ≤ f (p b-p x) ∧ 0 < f w

private theorem drawingCell_map {V W : Type*} {G : SimpleGraph V}
    (q : V → W) {a b : V} (h : DrawingCell G a b) :
    DrawingCell (G.map q) (q a) (q b) := by
  rcases h with rfl | hab
  · exact Or.inl rfl
  · by_cases he : q a = q b
    · exact Or.inl he
    · exact Or.inr (G.map_adj_apply' hab he)

private theorem contractMap_collision {V : Type*} [DecidableEq V]
    {x y a b : V} (hxy : x ≠ y) (hab : a ≠ b)
    (he : contractMap hxy a = contractMap hxy b) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  by_cases hay : a = y
  · subst a
    have hb := (contractMap_eq_iff hxy b ⟨x,hxy⟩).mp (by simpa using he.symm)
    rcases hb with hb | ⟨hb,_⟩
    · exact Or.inr ⟨rfl,hb⟩
    · exact (hab hb.symm).elim
  · by_cases hby : b = y
    · subst b
      have ha := (contractMap_eq_iff hxy a ⟨x,hxy⟩).mp (by simpa using he)
      rcases ha with ha | ⟨ha,_⟩
      · exact Or.inl ⟨ha,rfl⟩
      · exact (hay ha).elim
    · have he' : a = b := by simpa [contractMap,hay,hby,Subtype.ext_iff] using he
      exact (hab he').elim

/-- The two stars are separated for every positive displacement satisfying
the half-plane certificate. All other edge pairs are handled by stability. -/
theorem split_incident_cells {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : x ≠ y) (D : StraightLineDrawing (edgeContract G hxy))
    {w : Point} (hw : SplitDirection G (D.point ∘ contractMap hxy) x y w)
    {a b : V} (ha : DrawingCell G x a) (hb : DrawingCell G y b)
    (hd : Disjoint ({x,a} : Set V) ({y,b} : Set V)) {t : ℝ} (ht : 0 < t) :
    Disjoint
      (segment ℝ (splitPlacement (D.point ∘ contractMap hxy) y w t x)
        (splitPlacement (D.point ∘ contractMap hxy) y w t a))
      (segment ℝ (splitPlacement (D.point ∘ contractMap hxy) y w t y)
        (splitPlacement (D.point ∘ contractMap hxy) y w t b)) := by
  let p := D.point ∘ contractMap hxy
  have hn : x ≠ y ∧ x ≠ b ∧ a ≠ y ∧ a ≠ b := by
    simpa [Set.disjoint_left,and_assoc] using hd
  obtain ⟨f,hfa,hfb,hfw⟩ := hw a b ha hb hn.2.2.1 hn.2.1.symm hn.2.2.2
  change f (p a-p x) ≤ 0 at hfa
  change 0 ≤ f (p b-p x) at hfb
  have hpy : p y = p x := by simp [p,Function.comp_def,contractMap,hxy]
  change Disjoint (segment ℝ (splitPlacement p y w t x) (splitPlacement p y w t a))
    (segment ℝ (splitPlacement p y w t y) (splitPlacement p y w t b))
  rw [splitPlacement_of_ne p y w t hxy,
    splitPlacement_of_ne p y w t hn.2.2.1,splitPlacement_self,hpy]
  by_cases hby : b = y
  · subst b
    rw [splitPlacement_self,hpy,segment_same,Set.disjoint_singleton_right]
    intro hz
    obtain ⟨s,hs,_,he⟩ := SP.segment_mix hz
    have hh : f ((p x + t • w)-p x) ≤ 0 := by
      rw [← he,linear_mix_sub]
      simpa using mul_nonpos_of_nonneg_of_nonpos hs hfa
    have hp := mul_pos ht hfw
    simp only [add_sub_cancel_left,map_smul,smul_eq_mul] at hh
    linarith
  · rw [splitPlacement_of_ne p y w t hby]
    apply disjoint_segment_shift f hfa hfb hfw _ ht
    have hbx : contractMap hxy b ≠ contractMap hxy x := by
      intro he
      rcases contractMap_collision hxy hn.2.1.symm he with ⟨_,he⟩ | ⟨he,_⟩
      · exact hxy he
      · exact hby he
    have hba : contractMap hxy b ≠ contractMap hxy a := by
      intro he
      rcases contractMap_collision hxy hn.2.2.2.symm he with ⟨_,he⟩ | ⟨he,_⟩
      · exact hn.2.2.1 he
      · exact hby he
    have hh := drawing_separated D (contractMap hxy b) (contractMap hxy b)
      (contractMap hxy x) (contractMap hxy a) (Or.inl rfl)
      (drawingCell_map (contractMap hxy) ha) (by simp [hbx,hba])
    simpa only [segment_same,Set.disjoint_singleton_left,p,Function.comp_apply] using hh

/-- Segment pairs disjoint before a continuous perturbation stay disjoint
for all sufficiently small parameter values, uniformly over finitely many
vertex quadruples. -/
theorem eventually_separated_pairs {V : Type*} [Finite V] {p : ℝ → V → Point}
    (hp : Continuous p) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ a b c d,
      Disjoint (segment ℝ (p 0 a) (p 0 b)) (segment ℝ (p 0 c) (p 0 d)) →
      Disjoint (segment ℝ (p t a) (p t b)) (segment ℝ (p t c) (p t d)) := by
  simp only [Filter.eventually_all]
  intro a b c d hd
  have hc := isClosed_segment_intersection (V := V) a b c d
  have ho : IsOpen {q : V → Point |
      Disjoint (segment ℝ (q a) (q b)) (segment ℝ (q c) (q d))} := by
    convert hc.isOpen_compl using 1
    ext q
    simp
  exact hp.continuousAt.eventually (ho.mem_nhds hd)

private theorem contractMap_disjoint_or_split {V : Type*} [DecidableEq V]
    {x y a b c d : V} (hxy : x ≠ y)
    (hd : Disjoint ({a,b} : Set V) ({c,d} : Set V)) :
    Disjoint ({contractMap hxy a,contractMap hxy b} : Set _)
      {contractMap hxy c,contractMap hxy d} ∨
    (x ∈ ({a,b} : Set V) ∧ y ∈ ({c,d} : Set V)) ∨
    (y ∈ ({a,b} : Set V) ∧ x ∈ ({c,d} : Set V)) := by
  by_cases hh : Disjoint ({contractMap hxy a,contractMap hxy b} : Set _)
      {contractMap hxy c,contractMap hxy d}
  · exact Or.inl hh
  right
  have collision {u v : V} (hu : u ∈ ({a,b} : Set V)) (hv : v ∈ ({c,d} : Set V))
      (he : contractMap hxy u = contractMap hxy v) :
      (x ∈ ({a,b} : Set V) ∧ y ∈ ({c,d} : Set V)) ∨
      (y ∈ ({a,b} : Set V) ∧ x ∈ ({c,d} : Set V)) := by
    have huv : u ≠ v := fun h => Set.disjoint_left.mp hd (h ▸ hu) hv
    rcases contractMap_collision hxy huv he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨hu,hv⟩
    · exact Or.inr ⟨hu,hv⟩
  obtain ⟨z,hz,hz'⟩ := Set.not_disjoint_iff.mp hh
  rcases hz with rfl | rfl <;> rcases hz' with hz' | hz'
  all_goals exact collision (by simp) (by simp) hz'

private theorem drawingCell_symm {V : Type*} {G : SimpleGraph V} {a b : V}
    (h : DrawingCell G a b) : DrawingCell G b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- Split an edge contraction by moving just `y`. Explicit local half-plane
inequalities handle the incident cells; openness handles every other pair.
Every sufficiently small positive displacement is a valid drawing. -/
theorem vertex_split_small {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : x ≠ y) (D : StraightLineDrawing (edgeContract G hxy))
    {w : Point} (hw : SplitDirection G (D.point ∘ contractMap hxy) x y w) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      SeparatedPlacement G (splitPlacement (D.point ∘ contractMap hxy) y w t) := by
  let p := D.point ∘ contractMap hxy
  have hnear := eventually_separated_pairs (continuous_splitPlacement p y w)
  obtain ⟨ε,hε,hε'⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨ε,hε,?_⟩
  intro t ht htε
  have hfar := hε' (show dist t 0 < ε by simpa [Real.dist_eq,abs_of_pos ht] using htε)
  have hlocal {a b c d : V} (hab : DrawingCell G a b) (hcd : DrawingCell G c d)
      (hd : Disjoint ({a,b} : Set V) ({c,d} : Set V))
      (hx : x ∈ ({a,b} : Set V)) (hy : y ∈ ({c,d} : Set V)) :
      Disjoint (segment ℝ (splitPlacement p y w t a) (splitPlacement p y w t b))
        (segment ℝ (splitPlacement p y w t c) (splitPlacement p y w t d)) := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact split_incident_cells hxy D hw hab hcd hd ht
    · rw [segment_symm ℝ (splitPlacement p y w t c) (splitPlacement p y w t y)]
      apply split_incident_cells hxy D hw hab (drawingCell_symm hcd) _ ht
      simpa only [Set.pair_comm y c] using hd
    · rw [segment_symm ℝ (splitPlacement p y w t a) (splitPlacement p y w t x)]
      apply split_incident_cells hxy D hw (drawingCell_symm hab) hcd _ ht
      simpa only [Set.pair_comm x a] using hd
    · rw [segment_symm ℝ (splitPlacement p y w t a) (splitPlacement p y w t x),
        segment_symm ℝ (splitPlacement p y w t c) (splitPlacement p y w t y)]
      apply split_incident_cells hxy D hw (drawingCell_symm hab) (drawingCell_symm hcd) _ ht
      simpa only [Set.pair_comm x a,Set.pair_comm y c] using hd
  intro a b c d hab hcd hd
  rcases contractMap_disjoint_or_split hxy hd with hh | ⟨hx,hy⟩ | ⟨hy,hx⟩
  · apply hfar a b c d
    simpa only [splitPlacement_zero,p,Function.comp_apply] using
      drawing_separated D _ _ _ _ (drawingCell_map _ hab) (drawingCell_map _ hcd) hh
  · exact hlocal hab hcd hd hx hy
  · exact (hlocal hcd hab hd.symm hx hy).symm

/-- A certified splitting direction turns a drawing of the contraction into
a straight-line drawing of the original graph. -/
theorem planar_of_vertex_split {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : x ≠ y) (D : StraightLineDrawing (edgeContract G hxy))
    {w : Point} (hw : SplitDirection G (D.point ∘ contractMap hxy) x y w) :
    Lax68.Planar.IsPlanar G := by
  obtain ⟨ε,hε,hsplit⟩ := vertex_split_small hxy D hw
  exact ⟨separated_drawing (hsplit (ε/2) (by linarith) (by linarith))⟩

end Lax303502Proofs
