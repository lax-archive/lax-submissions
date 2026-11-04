import Lax185574Proofs.Chain.Ram.Refine
import Lax185574Proofs.Chain.Types
import Lax185574Proofs.Conversions.Ram.MergeSpec

/-!
The relations `tpRel G B k` on numbers, and the keys by which the
program refines them.

A labelling of the numbers below `n` by an equivalence relation `E`
maps `u` to the least `v` with `E v u` (`lbl`). Refining it by a key
`κ` gives the labelling of `E ∧ (κ v = κ u)` (`refine_lbl`). The
relation `tpRel G B 0` is the refinement of the trivial relation by the
membership in `B` (vertices of `B` are alone) and by the adjacency to
each vertex of `B` (`tpN_zero_iff`). The relation `tpRel G B (k+1)` is
the refinement of `tpRel G B k` by one key per vertex `y`, which records
whether `u` is complete or anticomplete to the class of `y` minus `u`,
computed from neighbor counts per class (`tpN_succ_iff`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

/-! ### Labellings -/

/-- An equivalence relation on the numbers below `n`. -/
structure IsEqv (n : ℕ) (E : ℕ → ℕ → Prop) : Prop where
  refl : ∀ u < n, E u u
  symm : ∀ u v, E u v → E v u
  trans : ∀ u v w, E u v → E v w → E u w

/-- The label of `u`: the least `v < n` with `E v u`. -/
noncomputable def lbl (n : ℕ) (E : ℕ → ℕ → Prop) (u : ℕ) : ℕ := leastBelow (fun v => E v u) n n

variable {n : ℕ} {E : ℕ → ℕ → Prop}

theorem lbl_spec (hE : IsEqv n E) {u : ℕ} (hu : u < n) :
    lbl n E u < n ∧ E (lbl n E u) u ∧ ∀ v < lbl n E u, ¬ E v u :=
  leastBelow_spec ⟨u, hu, hE.refl u hu⟩

theorem lbl_lt (hE : IsEqv n E) {u : ℕ} (hu : u < n) : lbl n E u < n := (lbl_spec hE hu).1

theorem lbl_le (hE : IsEqv n E) {u : ℕ} (hu : u < n) : lbl n E u ≤ u :=
  leastBelow_le_of hu (hE.refl u hu)

theorem lbl_eq_iff (hE : IsEqv n E) {u v : ℕ} (hu : u < n) (hv : v < n) :
    lbl n E u = lbl n E v ↔ E u v := by
  constructor
  · intro h
    have h1 := (lbl_spec hE hu).2.1
    have h2 := (lbl_spec hE hv).2.1
    rw [h] at h1
    exact hE.trans _ _ _ (hE.symm _ _ h1) h2
  · intro h
    unfold lbl
    exact leastBelow_congr fun w _ =>
      ⟨fun h' => hE.trans _ _ _ h' h, fun h' => hE.trans _ _ _ h' (hE.symm _ _ h)⟩

theorem IsEqv.conj (hE : IsEqv n E) (κ : ℕ → ℕ) :
    IsEqv n (fun v u => E v u ∧ κ v = κ u) :=
  ⟨fun u hu => ⟨hE.refl u hu, rfl⟩, fun u v h => ⟨hE.symm _ _ h.1, h.2.symm⟩,
    fun u v w h h' => ⟨hE.trans _ _ _ h.1 h'.1, h.2.trans h'.2⟩⟩

theorem IsEqv.of_iff {E' : ℕ → ℕ → Prop} (hE : IsEqv n E)
    (h : ∀ u < n, ∀ v < n, (E' u v ↔ E u v)) (hlt : ∀ u v, E' u v → u < n ∧ v < n) :
    IsEqv n E' :=
  ⟨fun u hu => (h u hu u hu).2 (hE.refl u hu),
    fun u v huv => by
      obtain ⟨hu, hv⟩ := hlt u v huv
      exact (h v hv u hu).2 (hE.symm _ _ ((h u hu v hv).1 huv)),
    fun u v w huv hvw => by
      obtain ⟨hu, hv⟩ := hlt u v huv
      obtain ⟨-, hw⟩ := hlt v w hvw
      exact (h u hu w hw).2 (hE.trans _ _ _ ((h u hu v hv).1 huv) ((h v hv w hw).1 hvw))⟩

/-- **The refinement of a labelling.** -/
theorem refine_lbl (hE : IsEqv n E) (κ : ℕ → ℕ) {u : ℕ} (hu : u < n) :
    leastBelow (fun v => lbl n E v = lbl n E u ∧ κ v = κ u) n n =
      lbl n (fun v u => E v u ∧ κ v = κ u) u :=
  leastBelow_congr fun v hv => by rw [lbl_eq_iff hE hv hu]

theorem lbl_congr {E' : ℕ → ℕ → Prop} (h : ∀ u < n, ∀ v < n, (E' v u ↔ E v u)) {u : ℕ}
    (hu : u < n) : lbl n E' u = lbl n E u :=
  leastBelow_congr fun v hv => h u hu v hv

/-! ### Types on numbers -/

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset (Fin n))

/-- Membership in `B`, on numbers. -/
def inBN (y : ℕ) : Prop := ∃ h : y < n, (⟨y, h⟩ : Fin n) ∈ B

/-- `tpRel G B k`, on numbers. -/
def tpN (k : ℕ) (u v : ℕ) : Prop := ∃ (hu : u < n) (hv : v < n), tpRel G B k ⟨u, hu⟩ ⟨v, hv⟩ = true

variable {G B}

theorem tpN_fin {k : ℕ} (u v : Fin n) : tpN G B k u v ↔ tpRel G B k u v = true :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨u.2, v.2, h⟩⟩

theorem tpN_isEqv (k : ℕ) : IsEqv n (tpN G B k) := by
  have h := tpRel_isEquiv (G := G) B k
  refine ⟨fun u hu => ⟨hu, hu, h.refl _⟩, fun u v ⟨hu, hv, huv⟩ => ⟨hv, hu, h.symm _ _ huv⟩,
    fun u v w ⟨hu, hv, huv⟩ ⟨_, hw, hvw⟩ => ⟨hu, hw, h.trans _ _ _ huv hvw⟩⟩

theorem gA_irrefl (u : ℕ) : ¬ gA G u u := fun ⟨_, _, h⟩ => G.irrefl h

theorem gA_iff {u v : ℕ} (hu : u < n) (hv : v < n) : gA G u v ↔ G.Adj ⟨u, hu⟩ ⟨v, hv⟩ :=
  gA_fin G ⟨u, hu⟩ ⟨v, hv⟩

theorem gA_lt {u v : ℕ} (h : gA G u v) : u < n ∧ v < n := ⟨h.1, h.2.1⟩

/-- The first key of the atomic types: vertices of `B` are alone. -/
noncomputable def key0 (B : Finset (Fin n)) (u : ℕ) : ℕ := ind (inBN B u) * (u + 1)

/-- The key of the atomic types for the vertex `y`: adjacency to `y` if
`y ∈ B`. -/
noncomputable def keyA (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) (y u : ℕ) : ℕ :=
  ind (inBN B y) * ind (gA G u y)

theorem key0_lt {u : ℕ} : key0 B u ≤ u + 1 := by
  unfold key0; have := ind_le_one (inBN B u); nlinarith

theorem keyA_le {y u : ℕ} : keyA G B y u ≤ 1 := by
  unfold keyA; have := ind_le_one (inBN B y); have := ind_le_one (gA G u y); nlinarith

theorem key0_eq_iff {u v : ℕ} : key0 B v = key0 B u ↔
    (v = u ∨ (¬ inBN B v ∧ ¬ inBN B u)) := by
  by_cases hvu : v = u
  · subst hvu; simp
  unfold key0 ind
  by_cases hv : inBN B v <;> by_cases hu : inBN B u <;> simp [hv, hu, hvu]

theorem keyA_eq_iff {y u v : ℕ} : keyA G B y v = keyA G B y u ↔
    (inBN B y → (gA G v y ↔ gA G u y)) := by
  unfold keyA ind
  by_cases hy : inBN B y <;> by_cases hv : gA G v y <;> by_cases hu : gA G u y <;> simp [hy, hv, hu]

/-- **The atomic types as a refinement.** -/
theorem tpN_zero_iff {u v : ℕ} (hu : u < n) (hv : v < n) :
    tpN G B 0 v u ↔ (True ∧ key0 B v = key0 B u) ∧ ∀ y < n, keyA G B y v = keyA G B y u := by
  rw [tpN_fin (k := 0) ⟨v, hv⟩ ⟨u, hu⟩, tpRel_zero (G := G), key0_eq_iff]
  simp only [keyA_eq_iff, true_and]
  have hB : ∀ x : ℕ, ∀ hx : x < n, inBN B x ↔ (⟨x, hx⟩ : Fin n) ∈ B :=
    fun x hx => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩
  constructor
  · rintro (h | ⟨h1, h2, h3⟩)
    · have : v = u := congrArg Fin.val h
      subst this; exact ⟨Or.inl rfl, fun _ _ _ => Iff.rfl⟩
    · refine ⟨Or.inr ⟨(hB v hv).not.2 h1, (hB u hu).not.2 h2⟩, fun y hy hyB => ?_⟩
      exact (gA_iff hv hy).trans ((h3 ⟨y, hy⟩ ((hB y hy).1 hyB)).trans (gA_iff hu hy).symm)
  · rintro ⟨h | ⟨h1, h2⟩, h3⟩
    · left; exact Fin.ext h
    · right
      refine ⟨fun h => h1 ⟨hv, h⟩, fun h => h2 ⟨hu, h⟩, fun y hy => ?_⟩
      exact (gA_iff hv y.2).symm.trans ((h3 y y.2 ⟨y.2, hy⟩).trans (gA_iff hu y.2))

/-! ### One more round -/

open Classical in
/-- The number of neighbors of `u` with label `c`. -/
noncomputable def cntN (G : SimpleGraph (Fin n)) (L : ℕ → ℕ) (u c : ℕ) : ℕ :=
  ((range n).filter fun z => gA G u z ∧ L z = c).card

open Classical in
/-- The number of vertices with label `c`. -/
noncomputable def szN (n : ℕ) (L : ℕ → ℕ) (c : ℕ) : ℕ := ((range n).filter fun z => L z = c).card

/-- The key of round `k + 1` for the vertex `y`: whether `u` is complete
and whether it is anticomplete to the class of `y` minus `u`. -/
noncomputable def keyS (G : SimpleGraph (Fin n)) (L : ℕ → ℕ) (y u : ℕ) : ℕ :=
  2 * ind (cntN G L u (L y) = szN n L (L y) - ind (L u = L y)) + ind (cntN G L u (L y) = 0)

theorem keyS_le {L : ℕ → ℕ} {y u : ℕ} : keyS G L y u ≤ 3 := by
  unfold keyS
  have := ind_le_one (cntN G L u (L y) = szN n L (L y) - ind (L u = L y))
  have := ind_le_one (cntN G L u (L y) = 0)
  omega

theorem two_ind_add_eq_iff {p q p' q' : Prop} :
    2 * ind p + ind q = 2 * ind p' + ind q' ↔ (p ↔ p') ∧ (q ↔ q') := by
  unfold ind
  by_cases hp : p <;> by_cases hq : q <;> by_cases hp' : p' <;> by_cases hq' : q' <;>
    simp [hp, hq, hp', hq']

section Round

variable {k : ℕ}

theorem lbl_tp_eq_iff {z y : ℕ} (hz : z < n) (hy : y < n) :
    lbl n (tpN G B k) z = lbl n (tpN G B k) y ↔ tpRel G B k ⟨y, hy⟩ ⟨z, hz⟩ = true := by
  rw [lbl_eq_iff (tpN_isEqv k) hz hy, tpN_fin (k := k) ⟨z, hz⟩ ⟨y, hy⟩]
  exact ⟨fun h => (tpRel_isEquiv (G := G) B k).symm _ _ h,
    fun h => (tpRel_isEquiv (G := G) B k).symm _ _ h⟩

theorem complete_iff {u y : ℕ} (hu : u < n) (hy : y < n) :
    IsComplete G ⟨u, hu⟩ (cls (tpRel G B k) ⟨y, hy⟩) ↔
      cntN G (lbl n (tpN G B k)) u (lbl n (tpN G B k) y) =
        szN n (lbl n (tpN G B k)) (lbl n (tpN G B k) y) -
          ind (lbl n (tpN G B k) u = lbl n (tpN G B k) y) := by
  classical
  set L := lbl n (tpN G B k)
  set S1 := (range n).filter fun z => gA G u z ∧ L z = L y
  set S2 := (range n).filter fun z => L z = L y ∧ z ≠ u
  have h12 : S1 ⊆ S2 := by
    intro z hz
    simp only [S1, S2, mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.2, fun h => gA_irrefl (G := G) u (h ▸ hz.2.1)⟩
  have hsz : szN n L (L y) - ind (L u = L y) = S2.card := by
    unfold szN
    have : (range n).filter (fun z => L z = L y) = if L u = L y then insert u S2 else S2 := by
      ext z
      simp only [S2, mem_filter, mem_range]
      split_ifs with h
      · simp only [mem_insert, mem_filter, mem_range]
        constructor
        · rintro ⟨hz, hzl⟩
          by_cases hzu : z = u
          · left; exact hzu
          · right; exact ⟨hz, hzl, hzu⟩
        · rintro (rfl | ⟨hz, hzl, -⟩)
          · exact ⟨hu, h⟩
          · exact ⟨hz, hzl⟩
      · simp only [S2, mem_filter, mem_range]
        constructor
        · rintro ⟨hz, hzl⟩; exact ⟨hz, hzl, fun hzu => h (hzu ▸ hzl)⟩
        · rintro ⟨hz, hzl, -⟩; exact ⟨hz, hzl⟩
    rw [this]
    unfold ind
    split_ifs with h
    · rw [card_insert_of_notMem (by simp [S2])]; omega
    · omega
  change _ ↔ S1.card = _
  rw [hsz]
  constructor
  · intro hc
    refine congrArg card (Subset.antisymm h12 fun z hz => ?_)
    simp only [S1, S2, mem_filter, mem_range] at hz ⊢
    refine ⟨hz.1, ?_, hz.2.1⟩
    have hzc : (⟨z, hz.1⟩ : Fin n) ∈ cls (tpRel G B k) ⟨y, hy⟩ :=
      mem_cls.2 ((lbl_tp_eq_iff hz.1 hy).1 hz.2.1)
    exact (gA_iff hu hz.1).2 (hc _ hzc fun h => hz.2.2 (congrArg Fin.val h))
  · intro hc z hz hzu
    have hzl : L z = L y := (lbl_tp_eq_iff z.2 hy).2 (mem_cls.1 hz)
    have hmem : (z : ℕ) ∈ S2 := by
      simp only [S2, mem_filter, mem_range]
      exact ⟨z.2, hzl, fun h => hzu (Fin.ext h)⟩
    have := (eq_of_subset_of_card_le h12 hc.ge) ▸ hmem
    simp only [S1, mem_filter] at this
    exact (gA_iff hu z.2).1 this.2.1

theorem anticomplete_iff {u y : ℕ} (hu : u < n) (hy : y < n) :
    IsAnticomplete G ⟨u, hu⟩ (cls (tpRel G B k) ⟨y, hy⟩) ↔
      cntN G (lbl n (tpN G B k)) u (lbl n (tpN G B k) y) = 0 := by
  classical
  unfold cntN
  rw [card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h z hz ⟨hzu, hzl⟩
    have hzn := mem_range.1 hz
    have hzc : (⟨z, hzn⟩ : Fin n) ∈ cls (tpRel G B k) ⟨y, hy⟩ :=
      mem_cls.2 ((lbl_tp_eq_iff hzn hy).1 hzl)
    exact h _ hzc (fun e => gA_irrefl (G := G) u (by
      have : z = u := congrArg Fin.val e
      exact this ▸ hzu)) ((gA_iff hu hzn).1 hzu)
  · intro h z hz _ hadj
    exact h (mem_range.2 z.2) ⟨(gA_iff hu z.2).2 hadj,
      (lbl_tp_eq_iff z.2 hy).2 (mem_cls.1 hz)⟩

/-- **One round of the types as a refinement.** -/
theorem tpN_succ_iff {u v : ℕ} (hu : u < n) (hv : v < n) :
    tpN G B (k + 1) v u ↔ tpN G B k v u ∧
      ∀ y < n, keyS G (lbl n (tpN G B k)) y v = keyS G (lbl n (tpN G B k)) y u := by
  rw [tpN_fin (k := k + 1) ⟨v, hv⟩ ⟨u, hu⟩, tpRel_succ (G := G), ← tpN_fin (k := k) ⟨v, hv⟩ ⟨u, hu⟩]
  refine and_congr_right fun _ => ?_
  unfold keyS
  constructor
  · intro h y hy
    obtain ⟨h1, h2⟩ := h ⟨y, hy⟩
    rw [two_ind_add_eq_iff, ← complete_iff hv hy, ← complete_iff hu hy, ← anticomplete_iff hv hy,
      ← anticomplete_iff hu hy]
    exact ⟨h1, h2⟩
  · intro h y
    have := h y y.2
    rw [two_ind_add_eq_iff, ← complete_iff hv y.2, ← complete_iff hu y.2, ← anticomplete_iff hv y.2,
      ← anticomplete_iff hu y.2] at this
    exact this

end Round

end Lax185574Proofs.Chain.Ram
