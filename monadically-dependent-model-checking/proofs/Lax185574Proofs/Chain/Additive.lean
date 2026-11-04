import Lax185574Proofs.Chain.Types

/-!
Additivity of atomic types (Lemma `lem:1-types-additive` of the companion
paper): if the atomic types of `G` grow at most linearly with ratio `γ`,
then the number of atomic types over `S₁ ∪ ⋯ ∪ S_t` met by a set `X` is
at most `γ` times the sum of the numbers of atomic types over the `Sᵢ`
met by `X`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A vertex `y ∈ S` that distinguishes two vertices of different atomic
types over `S` also distinguishes them over every `R ∋ y`. -/
theorem exists_distinguisher {S : Finset V} {x x' : V} (h : ¬ tpRel G S 0 x x') :
    ∃ y ∈ S, ∀ R : Finset V, y ∈ R → ¬ tpRel G R 0 x x' := by
  rw [tpRel_zero] at h
  push Not at h
  obtain ⟨hne, h⟩ := h
  by_cases hx : x ∈ S
  · exact ⟨x, hx, fun R hR h' => by
      rcases tpRel_zero.1 h' with h' | ⟨h', _, _⟩
      · exact hne h'
      · exact h' hR⟩
  by_cases hx' : x' ∈ S
  · exact ⟨x', hx', fun R hR h' => by
      rcases tpRel_zero.1 h' with h' | ⟨_, h', _⟩
      · exact hne h'
      · exact h' hR⟩
  obtain ⟨y, hy, hxy⟩ := h hx hx'
  exact ⟨y, hy, fun R hR h' => by
    rcases tpRel_zero.1 h' with h' | ⟨_, _, h'⟩
    · exact hne h'
    · exact (by tauto : ¬ (G.Adj x y ↔ G.Adj x' y)) (h' y hR)⟩

/-- For every set `X` there is `R ⊆ S` with fewer elements than the number
of atomic types over `S` met by `X`, such that vertices of `X` with the
same atomic type over `R` have the same atomic type over `S`. -/
theorem exists_small_separating (S X : Finset V) :
    ∃ R ⊆ S, R.card + 1 ≤ numCls (tpRel G S 0) X + (if X = ∅ then 1 else 0) ∧
      ∀ x ∈ X, ∀ x' ∈ X, tpRel G R 0 x x' → tpRel G S 0 x x' := by
  have hS := tpRel_isEquiv (G := G) S 0
  induction X using Finset.induction_on with
  | empty => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | @insert a X haX ih =>
    obtain ⟨R', hR'S, hcard, hsep⟩ := ih
    by_cases hold : ∃ x0 ∈ X, tpRel G S 0 a x0
    · obtain ⟨x0, hx0, hax0⟩ := hold
      have hXne : X ≠ ∅ := ne_empty_of_mem hx0
      refine ⟨R', hR'S, ?_, ?_⟩
      · rw [numCls_insert_of_rel hS hx0 hax0]; simp only [hXne, if_false] at hcard
        simp; omega
      · have key : ∀ x ∈ X, tpRel G R' 0 a x → tpRel G S 0 a x := by
          intro x hx hax
          have h1 : tpRel G R' 0 x0 a :=
            tpRel_anti hR'S 0 (hS.symm _ _ hax0)
          exact hS.trans _ _ _ hax0
            (hsep x0 hx0 x hx ((tpRel_isEquiv R' 0).trans _ _ _ h1 hax))
        intro x hx x' hx' hxx'
        rw [mem_insert] at hx hx'
        rcases hx with rfl | hx <;> rcases hx' with rfl | hx'
        · exact hS.refl _
        · exact key x' hx' hxx'
        · exact hS.symm _ _ (key x hx ((tpRel_isEquiv R' 0).symm _ _ hxx'))
        · exact hsep x hx x' hx' hxx'
    · push Not at hold
      rw [numCls_insert_of_not_rel hS hold]
      by_cases hcoll : ∃ x1 ∈ X, tpRel G R' 0 a x1
      · obtain ⟨x1, hx1, hax1⟩ := hcoll
        obtain ⟨y, hyS, hy⟩ := exists_distinguisher (hold x1 hx1)
        have hXne : X ≠ ∅ := ne_empty_of_mem hx1
        simp only [hXne, if_false] at hcard
        refine ⟨insert y R', insert_subset hyS hR'S, ?_, ?_⟩
        · simp only [insert_ne_empty, if_false]
          calc (insert y R').card + 1 ≤ R'.card + 1 + 1 := by
                have := card_insert_le y R'; omega
            _ ≤ _ := by omega
        · have key : ∀ x ∈ X, ¬ tpRel G (insert y R') 0 a x := by
            intro x hx hax
            have h1 : tpRel G R' 0 a x := tpRel_anti (subset_insert _ _) 0 hax
            have h2 : tpRel G S 0 x x1 := hsep x hx x1 hx1
              ((tpRel_isEquiv R' 0).trans _ _ _ ((tpRel_isEquiv R' 0).symm _ _ h1) hax1)
            have h3 : tpRel G (insert y R') 0 x x1 := tpRel_anti (insert_subset hyS hR'S) 0 h2
            exact hy _ (mem_insert_self _ _) ((tpRel_isEquiv _ 0).trans _ _ _ hax h3)
          intro x hx x' hx' hxx'
          rw [mem_insert] at hx hx'
          rcases hx with rfl | hx <;> rcases hx' with rfl | hx'
          · exact hS.refl _
          · exact absurd hxx' (key x' hx')
          · exact absurd ((tpRel_isEquiv _ 0).symm _ _ hxx') (key x hx)
          · exact hsep x hx x' hx' (tpRel_anti (subset_insert _ _) 0 hxx')
      · push Not at hcoll
        refine ⟨R', hR'S, ?_, ?_⟩
        · simp only [insert_ne_empty, if_false]
          split_ifs at hcard <;> omega
        · intro x hx x' hx' hxx'
          rw [mem_insert] at hx hx'
          rcases hx with rfl | hx <;> rcases hx' with rfl | hx'
          · exact hS.refl _
          · exact absurd hxx' (hcoll x' hx')
          · exact absurd ((tpRel_isEquiv _ 0).symm _ _ hxx') (hcoll x hx)
          · exact hsep x hx x' hx' hxx'

/-- Same atomic type over every `Sᵢ` gives the same atomic type over the
union. -/
theorem tpRel_biUnion {ι : Type*} {I : Finset ι} {S : ι → Finset V} {x y : V}
    (h : ∀ i ∈ I, tpRel G (S i) 0 x y) : tpRel G (I.biUnion S) 0 x y := by
  by_cases hxy : x = y
  · subst hxy; exact (tpRel_isEquiv _ 0).refl _
  rw [tpRel_zero]
  refine Or.inr ⟨fun hx => ?_, fun hy => ?_, fun z hz => ?_⟩
  · obtain ⟨i, hi, hx⟩ := mem_biUnion.1 hx
    rcases tpRel_zero.1 (h i hi) with h' | ⟨h', _, _⟩
    · exact hxy h'
    · exact h' hx
  · obtain ⟨i, hi, hy⟩ := mem_biUnion.1 hy
    rcases tpRel_zero.1 (h i hi) with h' | ⟨_, h', _⟩
    · exact hxy h'
    · exact h' hy
  · obtain ⟨i, hi, hz⟩ := mem_biUnion.1 hz
    rcases tpRel_zero.1 (h i hi) with h' | ⟨_, _, h'⟩
    · exact absurd h' hxy
    · exact h' z hz

/-- Over the empty set all vertices have the same atomic type. -/
theorem tpRel_empty (x y : V) : tpRel G ∅ 0 x y := by
  rw [tpRel_zero]; by_cases h : x = y
  · exact Or.inl h
  · exact Or.inr ⟨notMem_empty x, notMem_empty y, by simp⟩

theorem numCls_empty_le (X : Finset V) : numCls (tpRel G ∅ 0) X ≤ 1 := by
  unfold numCls
  refine card_le_one.2 fun a ha b hb => ?_
  obtain ⟨x, -, rfl⟩ := mem_image.1 ha
  obtain ⟨y, -, rfl⟩ := mem_image.1 hb
  exact (cls_eq_iff (tpRel_isEquiv _ 0)).2 (tpRel_empty x y)

/-- **Additivity of atomic types** (`lem:1-types-additive`). -/
theorem numCls_biUnion_le {γ : ℕ} (hγ : ∀ R : Finset V, R.Nonempty →
      numCls (tpRel G R 0) univ ≤ γ * R.card) (hγ1 : 1 ≤ γ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (hI : I.Nonempty) (S : ι → Finset V)
    (X : Finset V) :
    numCls (tpRel G (I.biUnion S) 0) X ≤ γ * ∑ i ∈ I, numCls (tpRel G (S i) 0) X := by
  by_cases hX : X = ∅
  · subst hX; simp [numCls]
  have hsep : ∀ i, ∃ R ⊆ S i, R.card ≤ numCls (tpRel G (S i) 0) X ∧
      ∀ x ∈ X, ∀ x' ∈ X, tpRel G R 0 x x' → tpRel G (S i) 0 x x' := by
    intro i
    obtain ⟨R, hR, hc, h⟩ := exists_small_separating (G := G) (S i) X
    simp only [hX, if_false] at hc
    exact ⟨R, hR, by omega, h⟩
  choose R hRS hRc hRsep using hsep
  let RR := I.biUnion R
  have hle : numCls (tpRel G (I.biUnion S) 0) X ≤ numCls (tpRel G RR 0) X := by
    refine numCls_le_of_le (tpRel_isEquiv _ 0) (tpRel_isEquiv _ 0) fun x hx y hy hxy => ?_
    exact tpRel_biUnion fun i hi =>
      hRsep i x hx y hy (tpRel_anti (subset_biUnion_of_mem R hi) 0 hxy)
  have hpos : 1 ≤ ∑ i ∈ I, numCls (tpRel G (S i) 0) X := by
    obtain ⟨i, hi⟩ := hI
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hX
    have : 1 ≤ numCls (tpRel G (S i) 0) X :=
      card_pos.2 ⟨_, mem_image_of_mem _ hx⟩
    exact this.trans (single_le_sum (f := fun i => numCls (tpRel G (S i) 0) X)
      (fun _ _ => Nat.zero_le _) hi)
  refine hle.trans ?_
  by_cases hRR : RR.Nonempty
  · calc numCls (tpRel G RR 0) X ≤ numCls (tpRel G RR 0) univ := numCls_mono _ (subset_univ _)
      _ ≤ γ * RR.card := hγ RR hRR
      _ ≤ γ * ∑ i ∈ I, (R i).card := Nat.mul_le_mul_left _ card_biUnion_le
      _ ≤ γ * ∑ i ∈ I, numCls (tpRel G (S i) 0) X :=
        Nat.mul_le_mul_left _ (sum_le_sum fun i _ => hRc i)
  · rw [not_nonempty_iff_eq_empty] at hRR
    rw [hRR]
    calc numCls (tpRel G ∅ 0) X ≤ 1 := numCls_empty_le X
      _ ≤ γ * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hpos

end Lax185574Proofs.Chain
