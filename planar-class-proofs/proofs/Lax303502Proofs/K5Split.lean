import Lax303502Proofs.KuratowskiMinorBridge

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.GraphMinors

def splitLabels (v : Fin 5) (f : Fin 4 → Fin 5) (k : Fin 3) : Fin 3 ⊕ Fin 3 → Fin 5 :=
  Sum.elim ![v,f k.castSucc,f 3]
    ![v,f (k.succAbove 0).castSucc,f (k.succAbove 1).castSucc]

theorem splitLabels_collision {v : Fin 5} {f : Fin 4 → Fin 5}
    (hf : Function.Injective f) (hne : ∀ i, v ≠ f i) (k : Fin 3)
    {a b : Fin 3 ⊕ Fin 3} (hab : a ≠ b) (he : splitLabels v f k a = splitLabels v f k b) :
    (a = Sum.inl 0 ∧ b = Sum.inr 0) ∨ (a = Sum.inr 0 ∧ b = Sum.inl 0) := by
  have hne' i : f i ≠ v := (hne i).symm
  rcases a with a | a <;> rcases b with b | b <;> fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp_all [splitLabels,hf.eq_iff]
  all_goals norm_num [Fin.succAbove,Fin.lt_def] at he
  all_goals have he' := congrArg Fin.val he; norm_num at he'

/-- Splitting one branch vertex of a `K₅` model into two adjacent connected
sets, each retaining two attachments, exposes a `K₃,₃` minor. -/
noncomputable def k5_split_minor {V : Type*} {G : SimpleGraph V}
    (M : MinorModel K5 G) (P : MinorPorts M) (v : Fin 5)
    (S : FourSplit (G.induce (M.branchSet v)) (P.terminal v ∘ k5NeighborEquiv v)) :
    MinorModel K33 G := by
  classical
  let e := k5NeighborEquiv v
  let f : Fin 4 → Fin 5 := fun i => (e i).val
  have hf : Function.Injective f := fun i j he => e.injective (Subtype.ext he)
  have hne i : v ≠ f i := (e i).property
  let k := S.index
  let L : Set V := Subtype.val '' S.left
  let R : Set V := Subtype.val '' S.right
  let valHom : G.induce (M.branchSet v) →g G := ⟨Subtype.val,fun h => h⟩
  have hLc : (G.induce L).Connected := connected_image valHom S.left_connected
  have hRc : (G.induce R).Connected := connected_image valHom S.right_connected
  have hL : L ⊆ M.branchSet v := by rintro x ⟨z,hz,rfl⟩; exact z.property
  have hR : R ⊆ M.branchSet v := by rintro x ⟨z,hz,rfl⟩; exact z.property
  have hLR : Disjoint L R := by
    rw [Set.disjoint_left]
    rintro x ⟨z,hz,rfl⟩ ⟨w,hw,he⟩
    have he : w = z := Subtype.ext he
    subst w
    exact Set.disjoint_left.mp S.disjoint hz hw
  have heLR : ∃ x ∈ L, ∃ y ∈ R, G.Adj x y := by
    obtain ⟨x,hx,y,hy,he⟩ := S.adjacent
    exact ⟨x,⟨x,hx,rfl⟩,y,⟨y,hy,rfl⟩,he⟩
  have heL (i : Fin 3) (hi : i ≠ k) :
      ∃ x ∈ L, ∃ y ∈ M.branchSet (f i.castSucc), G.Adj x y := by
    let h : K5.Adj v (f i.castSucc) := (e i.castSucc).property
    exact ⟨P.port h,⟨P.terminal v (e i.castSucc),S.left_terminal i hi,rfl⟩,
      P.port h.symm,P.mem h.symm,P.adjacent h⟩
  have heR : ∃ x ∈ R, ∃ y ∈ M.branchSet (f k.castSucc), G.Adj x y := by
    let h : K5.Adj v (f k.castSucc) := (e k.castSucc).property
    exact ⟨P.port h,⟨P.terminal v (e k.castSucc),S.right_terminal,rfl⟩,
      P.port h.symm,P.mem h.symm,P.adjacent h⟩
  have heLast : ∃ x ∈ R, ∃ y ∈ M.branchSet (f 3), G.Adj x y := by
    let h : K5.Adj v (f 3) := (e 3).property
    exact ⟨P.port h,⟨P.terminal v (e 3),S.last_terminal,rfl⟩,
      P.port h.symm,P.mem h.symm,P.adjacent h⟩
  let B : Fin 3 ⊕ Fin 3 → Set V := Sum.elim ![L,M.branchSet (f k.castSucc),M.branchSet (f 3)]
    ![R,M.branchSet (f (k.succAbove 0).castSucc),M.branchSet (f (k.succAbove 1).castSucc)]
  have hsub a : B a ⊆ M.branchSet (splitLabels v f k a) := by
    rcases a with a | a <;> fin_cases a <;> first | exact hL | exact hR | exact Set.Subset.rfl
  have hdis : ∀ {a b}, a ≠ b → Disjoint (B a) (B b) := by
    intro a b hab
    by_cases he : splitLabels v f k a = splitLabels v f k b
    · rcases splitLabels_collision hf hne k hab he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hLR
      · exact hLR.symm
    · exact (M.disjoint he).mono (hsub a) (hsub b)
  have hedge (i j : Fin 3) : ∃ x ∈ B (.inl i), ∃ y ∈ B (.inr j), G.Adj x y := by
    fin_cases i <;> fin_cases j
    · exact heLR
    · exact heL (k.succAbove 0) (k.succAbove_ne 0)
    · exact heL (k.succAbove 1) (k.succAbove_ne 1)
    · obtain ⟨x,hx,y,hy,he⟩ := heR
      exact ⟨y,hy,x,hx,he.symm⟩
    · apply M.adjacent
      apply hf.ne
      exact fun he => k.succAbove_ne 0 ((Fin.castSucc_injective _ he).symm)
    · apply M.adjacent
      apply hf.ne
      exact fun he => k.succAbove_ne 1 ((Fin.castSucc_injective _ he).symm)
    · obtain ⟨x,hx,y,hy,he⟩ := heLast
      exact ⟨y,hy,x,hx,he.symm⟩
    · apply M.adjacent
      apply hf.ne
      exact fun he => by have he' := congrArg Fin.val he; simp at he'; omega
    · apply M.adjacent
      apply hf.ne
      exact fun he => by have he' := congrArg Fin.val he; simp at he'; omega
  refine ⟨B,?_,hdis,?_⟩
  · intro a
    rcases a with a | a <;> fin_cases a <;>
      first | exact hLc | exact hRc | exact M.connected _
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · simp at hab
    · exact hedge a b
    · obtain ⟨x,hx,y,hy,he⟩ := hedge b a
      exact ⟨y,hy,x,hx,he.symm⟩
    · simp at hab

end Lax303502Proofs
