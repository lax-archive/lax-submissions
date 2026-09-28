import Lax303502Proofs.CircularMinors

set_option autoImplicit false

namespace Lax303502Proofs

def CircularDrawing.reparam {V : Type*} {G : SimpleGraph V} (D : CircularDrawing G)
    (f : V → ℝ) (h : ∀ x y, f x < f y ↔ D.parameter x < D.parameter y) : CircularDrawing G where
  parameter := f
  injective := by
    intro x y he
    apply D.injective
    apply le_antisymm <;> apply le_of_not_gt <;> intro h'
    · have := (h y x).mpr h'; linarith
    · have := (h x y).mpr h'; linarith
  noncrossing := by
    intro a b c d hab hcd hd
    simpa only [SameArc, h] using D.noncrossing hab hcd hd

theorem CircularDrawing.bounded {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : CircularDrawing G) : ∃ E : CircularDrawing G, ∀ v, 0 < E.parameter v ∧ E.parameter v < 1 := by
  obtain ⟨r,hr⟩ := (Set.finite_range (fun v => |D.parameter v|)).bddAbove
  let B := max r 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hb v : |D.parameter v| < B := lt_of_le_of_lt (hr (Set.mem_range_self v)) (by dsimp [B]; linarith [le_max_left r 0])
  let f := fun v => (D.parameter v+B)/(2*B)
  have h x y : f x < f y ↔ D.parameter x < D.parameter y := by
    dsimp [f]
    rw [div_lt_div_iff_of_pos_right (by positivity : 0 < 2*B)]
    exact add_lt_add_iff_right B
  refine ⟨D.reparam f h, fun v => ?_⟩
  change 0 < f v ∧ f v < 1
  have hv := abs_lt.mp (hb v)
  dsimp [f]
  constructor
  · apply div_pos <;> linarith
  · apply (div_lt_one (by positivity : 0 < 2*B)).mpr; linarith

noncomputable def wrap (a x : ℝ) : ℝ := if x < a then x+1 else x

theorem wrap_lt {a x y : ℝ} (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) :
    wrap a x < wrap a y ↔ (x < y ↔ (x < a ↔ y < a)) := by
  by_cases hxa : x < a <;> by_cases hya : y < a
  · simp [wrap,hxa,hya]
  · have hxy : x < y := lt_of_lt_of_le hxa (le_of_not_gt hya)
    have hnot : ¬ x+1 < y := by linarith [hx.1,hy.2]
    simp [wrap,hxa,hya,hxy,hnot]
  · have hxy : ¬ x < y := by linarith
    have hlt : x < y+1 := by linarith [hx.2,hy.1]
    simp [wrap,hxa,hya,hxy,hlt]
  · simp [wrap,hxa,hya]

set_option maxHeartbeats 2000000 in
theorem wrap_sameArc {a b c d t : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hc : 0 < c ∧ c < 1) (hd : 0 < d ∧ d < 1) :
    SameArc (wrap t a) (wrap t b) (wrap t c) (wrap t d) ↔ SameArc a b c d := by
  simp only [SameArc,wrap_lt ha hc,wrap_lt hb hc,wrap_lt ha hd,wrap_lt hb hd]
  tauto

theorem CircularDrawing.rooted {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : CircularDrawing G) (v : V) : ∃ E : CircularDrawing G,
      E.parameter v = 0 ∧ ∀ x, 0 ≤ E.parameter x ∧ E.parameter x < 1 := by
  obtain ⟨D,hD⟩ := D.bounded
  let a := D.parameter v
  let f := fun x => wrap a (D.parameter x) - a
  have hf x : 0 ≤ f x ∧ f x < 1 := by
    dsimp [f,wrap,a]
    split_ifs with h <;> constructor <;> linarith [(hD x).1,(hD x).2,(hD v).1,(hD v).2]
  have hfi : Function.Injective f := by
    intro x y he
    apply D.injective
    dsimp [f,wrap] at he
    split_ifs at he <;> linarith [(hD x).1,(hD x).2,(hD y).1,(hD y).2]
  let E : CircularDrawing G := ⟨f,hfi,by
    intro b c d e hbc hde hd
    change SameArc (wrap a (D.parameter b) - a) (wrap a (D.parameter c) - a)
      (wrap a (D.parameter d) - a) (wrap a (D.parameter e) - a)
    simp only [SameArc,sub_lt_sub_iff_right]
    exact (wrap_sameArc (t:=a) (hD b) (hD c) (hD d) (hD e)).mpr (D.noncrossing hbc hde hd)⟩
  refine ⟨E,?_,hf⟩
  change wrap a a - a = 0
  simp [wrap]


def CircularDrawing.glue_data {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hcover : S ∪ T = Set.univ)
    (hedges : ∀ {a b}, G.Adj a b → (a ∈ S ∧ b ∈ S) ∨ (a ∈ T ∧ b ∈ T))
    (p : V → ℝ) (D : CircularDrawing (G.induce S)) (E : CircularDrawing (G.induce T))
    (hD : ∀ x : S, p x = D.parameter x) (hE : ∀ x : T, p x = E.parameter x)
    (hs : ∀ x ∈ S, 0 ≤ p x ∧ p x < 1)
    (ht : ∀ x ∈ T, p x = 0 ∨ 1 ≤ p x)
    (hz : ∀ x ∈ T, p x = 0 → x ∈ S) : CircularDrawing G := by
  have cover x : x ∈ S ∨ x ∈ T := by have := Set.mem_univ x; rwa [← hcover] at this
  have hip : Function.Injective p := by
    intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact congrArg Subtype.val (D.injective ((hD ⟨x,hx⟩).symm.trans (hxy.trans (hD ⟨y,hy⟩))))
      · have hyT := (cover y).resolve_left hy
        rcases ht y hyT with h | h
        · exact (hy (hz y hyT h)).elim
        · linarith [(hs x hx).2]
    · have hxT := (cover x).resolve_left hx
      by_cases hy : y ∈ S
      · rcases ht x hxT with h | h
        · exact (hx (hz x hxT h)).elim
        · linarith [(hs y hy).2]
      · have hyT := (cover y).resolve_left hy
        exact congrArg Subtype.val (E.injective ((hE ⟨x,hxT⟩).symm.trans (hxy.trans (hE ⟨y,hyT⟩))))
  have mixed {a b c d} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T) (hd : d ∈ T) :
      SameArc (p a) (p b) (p c) (p d) := by
    have h x (hx : x ∈ T) : p a < p x ↔ p b < p x := by
      rcases ht x hx with h | h
      · constructor <;> intro h' <;> linarith [(hs a ha).1,(hs b hb).1]
      · constructor <;> intro h' <;> linarith [(hs a ha).2,(hs b hb).2]
    exact iff_of_true (h c hc) (h d hd)
  have local_nc {U : Set V} (F : CircularDrawing (G.induce U))
      (hF : ∀ x : U, p x = F.parameter x) {a b c d}
      (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U)
      (hab : G.Adj a b) (hcd : G.Adj c d) (hdis : Disjoint ({a,b} : Set V) {c,d}) :
      SameArc (p a) (p b) (p c) (p d) := by
    have hn : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by simpa [Set.disjoint_left,and_assoc] using hdis
    have h := F.noncrossing (a:=⟨a,ha⟩) (b:=⟨b,hb⟩) (c:=⟨c,hc⟩) (d:=⟨d,hd⟩) hab hcd (by
      simp only [Set.disjoint_left,Set.mem_insert_iff,Set.mem_singleton_iff]
      rintro x (rfl | rfl) (he | he) <;>
        first | exact hn.1 (congrArg Subtype.val he) | exact hn.2.1 (congrArg Subtype.val he) |
          exact hn.2.2.1 (congrArg Subtype.val he) | exact hn.2.2.2 (congrArg Subtype.val he))
    simpa only [← hF] using h
  refine ⟨p,hip,?_⟩
  intro a b c d hab hcd hdis
  rcases hedges hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hedges hcd with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact local_nc D hD ha hb hc hd hab hcd hdis
  · exact mixed ha hb hc hd
  · have hn : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by simpa [Set.disjoint_left,and_assoc] using hdis
    exact (sameArc_symm (hip.ne hn.1) (hip.ne hn.2.1) (hip.ne hn.2.2.1) (hip.ne hn.2.2.2)).mpr
      (mixed hc hd ha hb)
  · exact local_nc E hE ha hb hc hd hab hcd hdis


theorem CircularDrawing.glue_disjoint {V : Type*} [Finite V] {G : SimpleGraph V} {S T : Set V}
    (hcover : S ∪ T = Set.univ) (hdis : Disjoint S T)
    (hedges : ∀ {a b}, G.Adj a b → (a ∈ S ∧ b ∈ S) ∨ (a ∈ T ∧ b ∈ T))
    (D : CircularDrawing (G.induce S)) (E : CircularDrawing (G.induce T)) :
    Nonempty (CircularDrawing G) := by
  classical
  obtain ⟨D,hD⟩ := D.bounded
  obtain ⟨E,hE⟩ := E.bounded
  have hc x (hx : x ∉ S) : x ∈ T := by
    have h : x ∈ S ∪ T := by rw [hcover]; trivial
    exact h.resolve_left hx
  let p : V → ℝ := fun x => if hx : x ∈ S then D.parameter ⟨x,hx⟩ else 1+E.parameter ⟨x,hc x hx⟩
  have hpS (x : S) : p x = D.parameter x := by simp [p,x.property]
  have hpT (x : T) : p x = 1+E.parameter x := by
    have hx : x.val ∉ S := fun h => Set.disjoint_left.mp hdis h x.property
    simp [p,hx]
  let F := E.reparam (fun x => 1+E.parameter x) (fun x y => by simp)
  refine ⟨CircularDrawing.glue_data hcover hedges p D F hpS hpT ?_ ?_ ?_⟩
  · intro x hx
    rw [hpS ⟨x,hx⟩]
    exact ⟨(hD ⟨x,hx⟩).1.le,(hD ⟨x,hx⟩).2⟩
  · intro x hx
    rw [hpT ⟨x,hx⟩]
    right; linarith [(hE ⟨x,hx⟩).1]
  · intro x hx hz
    rw [hpT ⟨x,hx⟩] at hz
    linarith [(hE ⟨x,hx⟩).1]

noncomputable def rightShift (x : ℝ) : ℝ := if x = 0 then 0 else 1+x

theorem rightShift_lt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    rightShift x < rightShift y ↔ x < y := by
  by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0
  · simp [rightShift,hx0,hy0]
  · have hpos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [rightShift,if_pos hx0,rightShift,if_neg hy0,hx0]
    constructor <;> intro h <;> linarith
  · have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [rightShift,if_neg hx0,rightShift,if_pos hy0,hy0]
    constructor <;> intro h <;> linarith
  · simp [rightShift,hx0,hy0]

theorem CircularDrawing.glue_vertex {V : Type*} [Finite V] {G : SimpleGraph V} {S T : Set V}
    (hcover : S ∪ T = Set.univ) {v : V} (hvS : v ∈ S) (hvT : v ∈ T)
    (hinter : ∀ x ∈ S, x ∈ T → x = v)
    (hedges : ∀ {a b}, G.Adj a b → (a ∈ S ∧ b ∈ S) ∨ (a ∈ T ∧ b ∈ T))
    (D : CircularDrawing (G.induce S)) (E : CircularDrawing (G.induce T)) :
    Nonempty (CircularDrawing G) := by
  classical
  obtain ⟨D,hDv,hD⟩ := D.rooted ⟨v,hvS⟩
  obtain ⟨E,hEv,hE⟩ := E.rooted ⟨v,hvT⟩
  have hc x (hx : x ∉ S) : x ∈ T := by
    have h : x ∈ S ∪ T := by rw [hcover]; trivial
    exact h.resolve_left hx
  let p : V → ℝ := fun x => if hx : x ∈ S then D.parameter ⟨x,hx⟩ else rightShift (E.parameter ⟨x,hc x hx⟩)
  have hpS (x : S) : p x = D.parameter x := by simp [p,x.property]
  have hpT (x : T) : p x = rightShift (E.parameter x) := by
    by_cases hx : x.val ∈ S
    · have he := hinter x hx x.property
      have hxv : x = ⟨v,hvT⟩ := Subtype.ext he
      subst x
      simp [p,hvS,hDv,hEv,rightShift]
    · simp [p,hx]
  let F := E.reparam (fun x => rightShift (E.parameter x))
    (fun x y => rightShift_lt (hE x).1 (hE y).1)
  refine ⟨CircularDrawing.glue_data hcover hedges p D F hpS hpT ?_ ?_ ?_⟩
  · intro x hx
    rw [hpS ⟨x,hx⟩]
    exact hD ⟨x,hx⟩
  · intro x hx
    rw [hpT ⟨x,hx⟩]
    by_cases he : E.parameter ⟨x,hx⟩ = 0
    · left; simp [rightShift,he]
    · right; simp only [rightShift,if_neg he]; linarith [(hE ⟨x,hx⟩).1]
  · intro x hx hz
    rw [hpT ⟨x,hx⟩] at hz
    have he : E.parameter ⟨x,hx⟩ = 0 := by
      by_contra he
      simp only [rightShift,if_neg he] at hz
      linarith [(hE ⟨x,hx⟩).1]
    have hxv : x = v := congrArg Subtype.val (E.injective (he.trans hEv.symm))
    exact hxv ▸ hvS

end Lax303502Proofs
