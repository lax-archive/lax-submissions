import Lax303502Proofs.SeriesParallelSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Lax303502Proofs
namespace SP

abbrev Point := ℝ × ℝ

def mix (u : ℝ) (p q : Point) : Point :=
  ((1-u)*p.1+u*q.1, (1-u)*p.2+u*q.2)

@[simp] theorem mix_zero (p q : Point) : mix 0 p q = p := by simp [mix]
@[simp] theorem mix_one (p q : Point) : mix 1 p q = q := by simp [mix]
@[simp] theorem mix_same (u : ℝ) (p : Point) : mix u p p = p := by
  ext <;> simp [mix] <;> ring

theorem segment_mix {p q z : Point} (h : z ∈ segment ℝ p q) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ mix u p q = z := by
  obtain ⟨a,b,ha,hb,hab,h⟩ := h
  refine ⟨b,hb,by linarith,?_⟩
  have he : a = 1-b := by linarith
  subst a
  exact h

/-- A cell is an edge or a supported singleton vertex. -/
def Cell {V : Type*} (G : SimpleGraph V) (a b : V) : Prop :=
  a ∈ G.support ∧ b ∈ G.support ∧ (a = b ∨ G.Adj a b)

theorem cell_edge {V : Type*} {G : SimpleGraph V} {a b : V}
    (h : G.Adj a b) : Cell G a b :=
  ⟨⟨b,h⟩,⟨a,h.symm⟩,Or.inr h⟩

theorem cell_vertex {V : Type*} {G : SimpleGraph V} {a : V}
    (h : a ∈ G.support) : Cell G a a := ⟨h,h,Or.inl rfl⟩

theorem cell_union {V : Type*} {G H : SimpleGraph V} {a b : V}
    (h : Cell (G ⊔ H) a b) : Cell G a b ∨ Cell H a b := by
  rcases h.2.2 with rfl | hab
  · rcases (show a ∈ G.support ∪ H.support from (support_union G H) ▸ h.1) with ha | ha
    · exact Or.inl (cell_vertex ha)
    · exact Or.inr (cell_vertex ha)
  · rcases hab with hab | hab
    · exact Or.inl (cell_edge hab)
    · exact Or.inr (cell_edge hab)

def Shared {V : Type*} (a b c d : V) : Prop := a=c ∨ a=d ∨ b=c ∨ b=d

theorem Shared.symm {V : Type*} {a b c d : V} (h : Shared a b c d) :
    Shared c d a b := by
  rcases h with h | h | h | h <;> simp_all [Shared]

/-- This single intersection condition also handles vertex injectivity and
vertices on edges by allowing singleton cells. -/
def Clean {V : Type*} (G : SimpleGraph V) (p : V → Point) : Prop :=
  ∀ {a b c d : V} {u v : ℝ}, Cell G a b → Cell G c d →
  0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
  mix u (p a) (p b) = mix v (p c) (p d) → Shared a b c d

def CrossClean {V : Type*} (G H : SimpleGraph V) (p q : V → Point) : Prop :=
  ∀ {a b c d : V} {u v : ℝ}, Cell G a b → Cell H c d →
  0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
  mix u (p a) (p b) = mix v (q c) (q d) → Shared a b c d

theorem clean_transform {V : Type*} {G : SimpleGraph V} {p : V → Point}
    (h : Clean G p) (f : Point → Point) (hi : Function.Injective f)
    (hm : ∀ u a b, mix u (f a) (f b) = f (mix u a b)) : Clean G (f ∘ p) := by
  intro a b c d u v hab hcd hu hu' hv hv' he
  exact h hab hcd hu hu' hv hv' (hi (by simpa only [Function.comp_apply, hm] using he))

noncomputable def merge {V : Type*} (G : SimpleGraph V) (p q : V → Point) : V → Point :=
  by classical exact fun v => if v ∈ G.support then p v else q v

theorem merge_left {V : Type*} {G : SimpleGraph V} {p q : V → Point} {v : V}
    (hv : v ∈ G.support) : merge G p q v = p v := by
  classical
  simp [merge,hv]

theorem merge_right {V : Type*} {G H : SimpleGraph V} {p q : V → Point}
    (agree : ∀ v, v ∈ G.support → v ∈ H.support → p v = q v) {v : V}
    (hv : v ∈ H.support) : merge G p q v = q v := by
  classical
  by_cases hg : v ∈ G.support
  · simpa [merge,hg] using agree v hg hv
  · simp [merge,hg]

theorem clean_merge {V : Type*} {G H : SimpleGraph V} {p q : V → Point}
    (hp : Clean G p) (hq : Clean H q)
    (agree : ∀ v, v ∈ G.support → v ∈ H.support → p v = q v)
    (cross : CrossClean G H p q) : Clean (G ⊔ H) (merge G p q) := by
  intro a b c d u v hab hcd hu hu' hv hv' he
  rcases cell_union hab with hab | hab <;> rcases cell_union hcd with hcd | hcd
  · rw [merge_left hab.1,merge_left hab.2.1,merge_left hcd.1,merge_left hcd.2.1] at he
    exact hp hab hcd hu hu' hv hv' he
  · rw [merge_left hab.1,merge_left hab.2.1,
      merge_right agree hcd.1,merge_right agree hcd.2.1] at he
    exact cross hab hcd hu hu' hv hv' he
  · rw [merge_right agree hab.1,merge_right agree hab.2.1,
      merge_left hcd.1,merge_left hcd.2.1] at he
    exact (cross hcd hab hv hv' hu hu' he.symm).symm
  · rw [merge_right agree hab.1,merge_right agree hab.2.1,
      merge_right agree hcd.1,merge_right agree hcd.2.1] at he
    exact hq hab hcd hu hu' hv hv' he

def clean_drawing {V : Type*} {G : SimpleGraph V} {p : V → Point}
    (h : Clean G p) (hs : G.support = Set.univ) :
    Lax68.StraightLineDrawings.StraightLineDrawing G where
  point := p
  injective := by
    intro a b he
    have ha : a ∈ G.support := hs ▸ Set.mem_univ a
    have hb : b ∈ G.support := hs ▸ Set.mem_univ b
    have hi := h (cell_vertex ha) (cell_vertex hb) (u:=0) (v:=0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using he)
    simpa [Shared] using hi
  noVertexOnEdge := by
    intro a b c hab hca hcb hc
    obtain ⟨u,hu,hu',he⟩ := segment_mix hc
    have hc' : c ∈ G.support := hs ▸ Set.mem_univ c
    have hi := h (cell_vertex hc') (cell_edge hab) (u:=0) (v:=u)
      (by norm_num) (by norm_num) hu hu' (by simpa using he.symm)
    simp [Shared,hca,hcb] at hi
  disjointEdges := by
    intro a b c d hab hcd hd
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨u,hu,hu',he⟩ := segment_mix hz
    obtain ⟨v,hv,hv',he'⟩ := segment_mix hz'
    have hi := h (cell_edge hab) (cell_edge hcd) hu hu' hv hv' (he.trans he'.symm)
    have hn : a≠c ∧ a≠d ∧ b≠c ∧ b≠d := by
      simpa [Set.disjoint_left,and_assoc] using hd
    rcases hi with hi | hi | hi | hi
    · exact hn.1 hi
    · exact hn.2.1 hi
    · exact hn.2.2.1 hi
    · exact hn.2.2.2 hi

end SP
end Lax303502Proofs
