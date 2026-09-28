import Lax303502Proofs.PathFans

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.GraphMinors Lax68.GraphTopologicalMinors

/-- Choose the endpoints of one edge between each adjacent pair of branch sets,
consistently for the two orientations of that edge. -/
structure MinorPorts {V W : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    (M : MinorModel H G) where
  port : ∀ {a b}, H.Adj a b → V
  mem : ∀ {a b} (h : H.Adj a b), port h ∈ M.branchSet a
  adjacent : ∀ {a b} (h : H.Adj a b), G.Adj (port h) (port h.symm)

noncomputable def minorPorts {V W : Type*} [LinearOrder W]
    {H : SimpleGraph W} {G : SimpleGraph V} (M : MinorModel H G) : MinorPorts M := by
  classical
  let x {a b} (h : H.Adj a b) := (M.adjacent h).choose
  have hx {a b} (h : H.Adj a b) : x h ∈ M.branchSet a := (M.adjacent h).choose_spec.1
  let y {a b} (h : H.Adj a b) := (M.adjacent h).choose_spec.2.choose
  have hy {a b} (h : H.Adj a b) : y h ∈ M.branchSet b := (M.adjacent h).choose_spec.2.choose_spec.1
  have he {a b} (h : H.Adj a b) : G.Adj (x h) (y h) := (M.adjacent h).choose_spec.2.choose_spec.2
  let p {a b} (h : H.Adj a b) := if a < b then x h else y h.symm
  refine ⟨@p,?_,?_⟩
  · intro a b h
    dsimp only [p]
    split_ifs
    · exact hx h
    · exact hy h.symm
  · intro a b h
    rcases lt_or_gt_of_ne h.ne with hab | hab
    · simpa [p,hab,not_lt_of_ge hab.le] using he h
    · simpa [p,hab,not_lt_of_ge hab.le] using (he h.symm).symm

def MinorPorts.terminal {V W : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    {M : MinorModel H G} (P : MinorPorts M) (a : W) : H.neighborSet a → M.branchSet a :=
  fun b => ⟨P.port b.property,P.mem b.property⟩

/-- Disjoint local fans in minor branch sets glue to the paths of a
subdivision, using the chosen inter-branch edges. -/
noncomputable def minor_topological_of_fans {V W : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} (M : MinorModel H G) (P : MinorPorts M)
    (F : ∀ a, PathFan (G.induce (M.branchSet a)) (P.terminal a)) :
    TopologicalMinorModel H G := by
  classical
  let c : W → V := fun a => (F a).center.val
  have hc a : c a ∈ M.branchSet a := (F a).center.property
  have ci : Function.Injective c := by
    intro a b he
    by_contra hab
    exact Set.disjoint_left.mp (M.disjoint hab) (hc a) (he ▸ hc b)
  let valHom a : G.induce (M.branchSet a) →g G := ⟨Subtype.val,fun h => h⟩
  let leg {a b} (h : H.Adj a b) : G.Walk (c a) (P.port h) :=
    ((F a).arm ⟨b,h⟩).map (valHom a)
  have legPath {a b} (h : H.Adj a b) : (leg h).IsPath :=
    ((F a).isPath ⟨b,h⟩).map Subtype.val_injective
  have legMem {a b} (h : H.Adj a b) {x} (hx : x ∈ (leg h).support) : x ∈ M.branchSet a := by
    change x ∈ (((F a).arm ⟨b,h⟩).map (valHom a)).support at hx
    rw [Walk.support_map] at hx
    obtain ⟨z,_,he⟩ := List.mem_map.mp hx
    have he : z.val = x := he
    exact he ▸ z.property
  have legMeet {a b d e} (hab : H.Adj a b) (hde : H.Adj d e) {x}
      (hx : x ∈ (leg hab).support) (hx' : x ∈ (leg hde).support) (hn : x ≠ c a) : a = d ∧ b = e := by
    have had : a = d := by
      by_contra h
      exact Set.disjoint_left.mp (M.disjoint h) (legMem hab hx) (legMem hde hx')
    subst d
    refine ⟨rfl,?_⟩
    by_contra hbe
    change x ∈ (((F a).arm ⟨b,hab⟩).map (valHom a)).support at hx
    change x ∈ (((F a).arm ⟨e,hde⟩).map (valHom a)).support at hx'
    rw [Walk.support_map] at hx hx'
    obtain ⟨u,hu,heu⟩ := List.mem_map.mp hx
    obtain ⟨v,hv,hev⟩ := List.mem_map.mp hx'
    have huv : u = v := Subtype.ext (heu.trans hev.symm)
    subst v
    have he := (F a).meet (i:=⟨b,hab⟩) (j:=⟨e,hde⟩)
      (fun he => hbe (congrArg Subtype.val he)) u hu hv
    apply hn
    exact heu.symm.trans (congrArg Subtype.val he)
  let route {a b} (h : H.Adj a b) : G.Walk (c a) (c b) :=
    ((leg h).concat (P.adjacent h)).append (leg h.symm).reverse
  have routeMem {a b} (h : H.Adj a b) {x} (hx : x ∈ (route h).support) :
      x ∈ (leg h).support ∨ x ∈ (leg h.symm).support := by
    simp only [route,Walk.mem_support_append_iff,Walk.support_concat,List.mem_append,
      List.mem_singleton,Walk.support_reverse,List.mem_reverse] at hx
    rcases hx with (hx | rfl) | hx
    · exact Or.inl hx
    · exact Or.inr (leg h.symm).end_mem_support
    · exact Or.inr hx
  refine ⟨⟨c,ci⟩,@route,?_,?_,?_⟩
  · intro a b h
    apply path_append_of_meet
    · exact (legPath h).concat (fun hx => Set.disjoint_left.mp (M.disjoint h.ne)
        (legMem h hx) (P.mem h.symm)) (P.adjacent h)
    · exact (legPath h.symm).reverse
    · intro x hx hx'
      simp only [Walk.support_concat,List.mem_append,List.mem_singleton] at hx
      simp only [Walk.support_reverse,List.mem_reverse] at hx'
      rcases hx with hx | hx
      · exact (Set.disjoint_left.mp (M.disjoint h.ne) (legMem h hx) (legMem h.symm hx')).elim
      · exact hx
  · intro a b h w hx
    rcases routeMem h hx.1 with hs | hs
    · by_cases he : w = a
      · subst w; exact hx.2.1 rfl
      · exact Set.disjoint_left.mp (M.disjoint he) (hc w) (legMem h hs)
    · by_cases he : w = b
      · subst w; exact hx.2.2 rfl
      · exact Set.disjoint_left.mp (M.disjoint he) (hc w) (legMem h.symm hs)
  · intro a b d e hab hde hne
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases routeMem hab hx.1 with hs | hs <;> rcases routeMem hde hx'.1 with ht | ht
    · exact hne (Or.inl (legMeet hab hde hs ht hx.2.1))
    · exact hne (Or.inr (legMeet hab hde.symm hs ht hx.2.1))
    · have he := legMeet hab.symm hde hs ht hx.2.2
      exact hne (Or.inr ⟨he.2,he.1⟩)
    · have he := legMeet hab.symm hde.symm hs ht hx.2.2
      exact hne (Or.inl ⟨he.2,he.1⟩)

end Lax303502Proofs
