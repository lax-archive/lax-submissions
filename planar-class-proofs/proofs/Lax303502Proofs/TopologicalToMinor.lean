import Lax303502Proofs.FourFans

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.GraphMinors Lax68.GraphTopologicalMinors

/-- Contract each subdivision path towards its lesser endpoint. The final
edge of the path remains as the edge between its two branch sets. -/
noncomputable def topological_to_minor {V W : Type*} [LinearOrder W]
    {H : SimpleGraph W} {G : SimpleGraph V} (M : TopologicalMinorModel H G) : MinorModel H G := by
  classical
  let B (a : W) : Set V := {x | x = M.branch a ∨
    ∃ b, ∃ h : H.Adj a b, a < b ∧ x ∈ (M.route h).dropLast.support}
  have root a : M.branch a ∈ B a := Or.inl rfl
  have interior {a b} (h : H.Adj a b) {x}
      (hx : x ∈ (M.route h).dropLast.support) (hn : x ≠ M.branch a) : x ∈ walkInterior (M.route h) := by
    have hp := M.route_isPath h
    have hne := M.branch.injective.ne h.ne
    have hnil : ¬(M.route h).Nil := Walk.not_nil_of_ne hne
    refine ⟨?_,hn,?_⟩
    · apply List.mem_of_mem_dropLast
      simpa only [Walk.support_dropLast hnil] using hx
    · intro he
      exact path_end_not_dropLast hp hne (he ▸ hx)
  have classify {a x} (hx : x ∈ B a) : x = M.branch a ∨
      ∃ b, ∃ h : H.Adj a b, a < b ∧ x ∈ walkInterior (M.route h) := by
    rcases hx with hx | ⟨b,h,hab,hx⟩
    · exact Or.inl hx
    · by_cases he : x = M.branch a
      · exact Or.inl he
      · exact Or.inr ⟨b,h,hab,interior h hx he⟩
  refine ⟨B,?_,?_,?_⟩
  · intro a
    have : Nonempty (B a) := ⟨⟨M.branch a,root a⟩⟩
    have reach (x : B a) : (G.induce (B a)).Reachable ⟨M.branch a,root a⟩ x := by
      rcases x.property with he | ⟨b,h,hab,hx⟩
      · have he' : x = ⟨M.branch a,root a⟩ := Subtype.ext he
        subst x; exact .rfl
      · let q := (M.route h).dropLast.takeUntil x hx
        have hq : ∀ v ∈ q.support, v ∈ B a := by
          intro v hv
          exact Or.inr ⟨b,h,hab,(M.route h).dropLast.support_takeUntil_subset_support hx hv⟩
        exact ⟨q.induce (B a) hq⟩
    exact ⟨fun x y => (reach x).symm.trans (reach y)⟩
  · intro a c hac
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases classify hx with he | ⟨b,h,hab,hi⟩ <;> rcases classify hx' with he' | ⟨d,h',hcd,hi'⟩
    · exact hac (M.branch.injective (he.symm.trans he'))
    · exact M.branch_avoids_interiors h' a (he ▸ hi')
    · exact M.branch_avoids_interiors h c (he' ▸ hi)
    · apply Set.disjoint_left.mp (M.route_interiors_disjoint h h' ?_) hi hi'
      rintro (⟨he,_⟩ | ⟨rfl,rfl⟩)
      · exact hac he
      · exact (lt_asymm hab hcd)
  · intro a b h
    have forward {a b} (h : H.Adj a b) (hab : a < b) :
        ∃ x ∈ B a, ∃ y ∈ B b, G.Adj x y := by
      have hn : ¬(M.route h).Nil := Walk.not_nil_of_ne (M.branch.injective.ne h.ne)
      exact ⟨(M.route h).penultimate,Or.inr ⟨b,h,hab,(M.route h).dropLast.end_mem_support⟩,
        M.branch b,root b,(M.route h).adj_penultimate hn⟩
    rcases lt_or_gt_of_ne h.ne with hab | hab
    · exact forward h hab
    · obtain ⟨x,hx,y,hy,he⟩ := forward h.symm hab
      exact ⟨y,hy,x,hx,he.symm⟩

end Lax303502Proofs
