import Lax185574Proofs.Chain.Types

/-!
A weighted sampling lemma, which replaces Haussler's packing lemma in the
companion paper. If the atomic types of `G` grow at most linearly with
ratio `γ`, and the points of `X` are pairwise separated by weight at least
`δ` (measured on sets `D u v ⊆ Δ[u,v]`), then `|X| ≤ γ · k · L`, where
`k δ ≥ W` for the total weight `W` and `|X|² < 2^L`.

The proof averages over all sequences of `k L` vertices, weighted by the
product of their weights. A sequence avoids a fixed set of weight at least
`δ` with weight at most `(W − δ)^{kL} ≤ W^{kL} / 2^L`, so some sequence
meets every `D u v`. Its range `Y` separates the points of `X` into
different atomic types, and there are at most `γ |Y|` of those.

As a consequence the packing ratio of `G` is at most
`4γ(log₂ n + 1)`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If `0 ≤ a`, `a + δ ≤ W` and `W ≤ k δ` then `2 a^k ≤ W^k`. -/
theorem two_mul_pow_le {a W δ : ℝ} {k : ℕ} (ha : 0 ≤ a) (hδ : 0 < δ) (haW : a + δ ≤ W)
    (hk : W ≤ k * δ) : 2 * a ^ k ≤ W ^ k := by
  have hW : 0 < W := by linarith
  set x := (W - a) / W with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hW.le
  have hx1 : x ≤ 1 := (div_le_one hW).2 (by linarith)
  have ha' : a = W * (1 - x) := by rw [hx]; field_simp; ring
  have hkx : 1 ≤ k * x := by
    rw [hx, mul_div_assoc', le_div_iff₀ hW]
    nlinarith
  have h1 : (1 - x) ^ k * (1 + x) ^ k ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h2 : 2 ≤ (1 + x) ^ k := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ x by linarith) k
    linarith
  have h3 : 2 * (1 - x) ^ k ≤ 1 := by
    have hpos : 0 ≤ (1 - x) ^ k := pow_nonneg (by linarith) k
    nlinarith
  rw [ha', mul_pow]
  have hWk : 0 ≤ W ^ k := pow_nonneg hW.le k
  nlinarith

/-- The total weight of the sequences `f : Fin t → V` with all entries
in `D`, each weighted by the product of the weights of its entries. -/
theorem sum_prod_piFinset (w : V → ℕ) (D : Finset V) (t : ℕ) :
    (∑ f ∈ Fintype.piFinset (fun _ : Fin t => D), ∏ j, (w (f j) : ℝ)) =
      (∑ x ∈ D, (w x : ℝ)) ^ t := by
  rw [← Finset.prod_univ_sum (fun _ : Fin t => D) (fun _ x => (w x : ℝ))]
  simp

/-- **Weighted sampling lemma.** -/
theorem card_le_of_separated {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card)
    (w : V → ℕ) (X : Finset V) (D : V → V → Finset V)
    (hD : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → D u v ⊆ sdiff G u v)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → δ ≤ ∑ x ∈ D u v, (w x : ℝ))
    {k L : ℕ} (hk1 : 1 ≤ k) (hL1 : 1 ≤ L)
    (hk : (∑ x, (w x : ℝ)) ≤ k * δ) (hL : X.card * X.card < 2 ^ L) :
    X.card ≤ γ * (k * L) := by
  rcases Nat.lt_or_ge X.card 2 with hX2' | hX2'
  · by_cases hX0 : X.card = 0
    · rw [hX0]; exact Nat.zero_le _
    obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero hX0)
    have hγ1 : 1 ≤ γ := by
      have h := hγ {x} (singleton_nonempty x)
      have : 1 ≤ numCls (tpRel G {x} 0) univ := card_pos.2 ⟨_, mem_image_of_mem _ (mem_univ x)⟩
      simp at h; omega
    calc X.card ≤ 1 := by omega
      _ ≤ γ * (k * L) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega)
          (Nat.mul_ne_zero (by omega) (by omega)))
  set t := k * L with ht
  have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  set W : ℝ := ∑ x, (w x : ℝ) with hWdef
  -- Some sequence meets every `D u v`.
  have hex : ∃ f : Fin t → V, ∀ p ∈ X.offDiag, ∃ j, f j ∈ D p.1 p.2 := by
    by_contra hne
    push Not at hne
    have hX2 : X.offDiag ≠ ∅ := by
      obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.1 hX2'
      exact ne_empty_of_mem (a := (u, v)) (mem_offDiag.2 ⟨hu, hv, huv⟩)
    obtain ⟨p0, hp0⟩ := nonempty_iff_ne_empty.2 hX2
    have hp0' := mem_offDiag.1 hp0
    have hδW : δ ≤ W := (hsep _ hp0'.1 _ hp0'.2.1 hp0'.2.2).trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _)
    -- every sequence is bad for some pair
    have hbound : W ^ t ≤ ∑ p ∈ X.offDiag, (∑ x ∈ univ \ D p.1 p.2, (w x : ℝ)) ^ t := by
      rw [show W ^ t = ∑ f : Fin t → V, ∏ j, (w (f j) : ℝ) by
        rw [hWdef, ← sum_prod_piFinset w univ t]; simp]
      calc ∑ f : Fin t → V, ∏ j, (w (f j) : ℝ)
          ≤ ∑ f : Fin t → V, ∑ p ∈ X.offDiag,
              if ∀ j, f j ∉ D p.1 p.2 then ∏ j, (w (f j) : ℝ) else 0 := by
            refine sum_le_sum fun f _ => ?_
            obtain ⟨p, hp, hpf⟩ := hne f
            refine le_trans ?_ (single_le_sum (f := fun p => if ∀ j, f j ∉ D p.1 p.2
              then ∏ j, (w (f j) : ℝ) else 0) (fun _ _ => by
                split_ifs
                · exact prod_nonneg fun _ _ => Nat.cast_nonneg _
                · exact le_rfl) hp)
            rw [if_pos hpf]
        _ = ∑ p ∈ X.offDiag, ∑ f : Fin t → V,
              if ∀ j, f j ∉ D p.1 p.2 then ∏ j, (w (f j) : ℝ) else 0 := sum_comm
        _ = ∑ p ∈ X.offDiag, (∑ x ∈ univ \ D p.1 p.2, (w x : ℝ)) ^ t := by
            refine sum_congr rfl fun p _ => ?_
            rw [← sum_prod_piFinset, ← sum_filter]
            congr 1
            ext f; simp [Fintype.mem_piFinset]
    have hpair : ∀ p ∈ X.offDiag, (∑ x ∈ univ \ D p.1 p.2, (w x : ℝ)) ^ t * 2 ^ L ≤ W ^ t := by
      intro p hp
      have hp' := mem_offDiag.1 hp
      set a := ∑ x ∈ univ \ D p.1 p.2, (w x : ℝ)
      have ha0 : 0 ≤ a := sum_nonneg fun _ _ => Nat.cast_nonneg _
      have haW : a + δ ≤ W := by
        have := hsep _ hp'.1 _ hp'.2.1 hp'.2.2
        have hsplit : a + ∑ x ∈ D p.1 p.2, (w x : ℝ) = W := by
          rw [hWdef, ← sum_sdiff (subset_univ (D p.1 p.2))]
        linarith
      have h2 := two_mul_pow_le ha0 hδ haW hk
      rw [ht, pow_mul, pow_mul]
      have hak : 0 ≤ a ^ k := pow_nonneg ha0 k
      calc (a ^ k) ^ L * 2 ^ L = (2 * a ^ k) ^ L := by ring
        _ ≤ (W ^ k) ^ L := pow_le_pow_left₀ (by positivity) h2 L
    have hWt : 0 < W ^ t := pow_pos (lt_of_lt_of_le hδ hδW) t
    have hcard : (X.offDiag.card : ℝ) < 2 ^ L := by
      have : X.offDiag.card ≤ X.card * X.card := by
        rw [offDiag_card]; exact Nat.sub_le _ _
      exact_mod_cast lt_of_le_of_lt this hL
    have : W ^ t * 2 ^ L ≤ X.offDiag.card * W ^ t := by
      calc W ^ t * 2 ^ L ≤ (∑ p ∈ X.offDiag, (∑ x ∈ univ \ D p.1 p.2, (w x : ℝ)) ^ t) * 2 ^ L :=
            mul_le_mul_of_nonneg_right hbound (by positivity)
        _ = ∑ p ∈ X.offDiag, (∑ x ∈ univ \ D p.1 p.2, (w x : ℝ)) ^ t * 2 ^ L := sum_mul _ _ _
        _ ≤ ∑ p ∈ X.offDiag, W ^ t := sum_le_sum hpair
        _ = X.offDiag.card * W ^ t := by simp
    nlinarith
  obtain ⟨f, hf⟩ := hex
  set Y := univ.image f with hY
  have hYne : Y.Nonempty := ⟨f ⟨0, by omega⟩, mem_image_of_mem _ (mem_univ _)⟩
  have hYcard : Y.card ≤ t := card_image_le.trans (by simp)
  have hpw : ∀ x ∈ X, ∀ y ∈ X, tpRel G Y 0 x y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    obtain ⟨j, hj⟩ := hf (x, y) (mem_offDiag.2 ⟨hx, hy, hne⟩)
    have hj' := hD x hx y hy hne hj
    have hfY : f j ∈ Y := mem_image_of_mem _ (mem_univ _)
    rw [mem_sdiff] at hj'
    rcases hj'.2 with h | h | h
    · rw [h] at hfY; exact hne (eq_of_tpRel_of_mem hxy hfY)
    · rw [h] at hfY
      exact hne (eq_of_tpRel_of_mem ((tpRel_isEquiv Y 0).symm _ _ hxy) hfY).symm
    · exact h (adj_iff_of_tpRel hxy hfY)
  calc X.card ≤ numCls (tpRel G Y 0) univ :=
        card_le_numCls_of_pairwise (tpRel_isEquiv Y 0) (subset_univ _) hpw
    _ ≤ γ * Y.card := hγ Y hYne
    _ ≤ γ * t := Nat.mul_le_mul_left _ hYcard

/-- `n² < 4^{log₂ n + 1}`. -/
theorem sq_lt_two_pow (n : ℕ) : n * n < 2 ^ (2 * (Nat.log 2 n + 1)) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  rw [pow_mul', sq]
  exact Nat.mul_lt_mul'' h h

/-! ### Packing ratio -/

/-- `β` bounds the packing ratio of `G`: whenever the points of `X`
(at least two) pairwise have at least `k` vertices of `A` in their
closed symmetric difference, `|X| · k ≤ β · |A|`. -/
def IsPackingBound (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℕ) : Prop :=
  ∀ (A X : Finset V) (k : ℕ), 2 ≤ X.card →
    (∀ u ∈ X, ∀ v ∈ X, u ≠ v → k ≤ (sdiff G u v ∩ A).card) → X.card * k ≤ β * A.card

theorem IsPackingBound.mono {β β' : ℕ} (h : IsPackingBound G β) (hle : β ≤ β') :
    IsPackingBound G β' := fun A X k hX hk =>
  (h A X k hX hk).trans (Nat.mul_le_mul_right _ hle)

/-- The trivial packing bound `n`. -/
theorem isPackingBound_card : IsPackingBound G (Fintype.card V) := by
  intro A X k hX hk
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.1 hX
  have hkA : k ≤ A.card := (hk u hu v hv huv).trans (card_le_card inter_subset_right)
  exact Nat.mul_le_mul (card_le_univ X) hkA

/-- **Packing ratio from the growth of atomic types.** -/
theorem isPackingBound_of_growth {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card) :
    IsPackingBound G (4 * γ * (Nat.log 2 (Fintype.card V) + 1)) := by
  intro A X k hX hk
  obtain ⟨u0, hu0, v0, hv0, huv0⟩ := one_lt_card.1 hX
  by_cases hk0 : k = 0
  · simp [hk0]
  have hkA : k ≤ A.card := (hk u0 hu0 v0 hv0 huv0).trans (card_le_card inter_subset_right)
  set L := 2 * (Nat.log 2 (Fintype.card V) + 1)
  have h1 := Nat.div_add_mod (A.card + k - 1) k
  have h2 := Nat.mod_lt (A.card + k - 1) (show 0 < k by omega)
  generalize hcdef : (A.card + k - 1) / k = c at h1
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; simp at h1; omega
    · exact h
  have hck : A.card ≤ c * k := by rw [Nat.mul_comm]; omega
  have hck' : c * k ≤ 2 * A.card := by rw [Nat.mul_comm]; omega
  have hmain := card_le_of_separated (G := G) hγ (fun x => if x ∈ A then 1 else 0) X
    (fun u v => sdiff G u v ∩ A) (fun _ _ _ _ _ => inter_subset_left)
    (δ := k) (by exact_mod_cast Nat.pos_of_ne_zero hk0)
    (fun u hu v hv huv => by
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [← sum_filter]
      have : (sdiff G u v ∩ A).filter (· ∈ A) = sdiff G u v ∩ A :=
        filter_true_of_mem fun x hx => (mem_inter.1 hx).2
      rw [this]; simp only [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hk u hu v hv huv)
    (k := c) (L := L) hc1 (by omega)
    (by
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [← sum_filter, filter_mem_eq_inter, univ_inter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hck)
    ((Nat.mul_le_mul (card_le_univ X) (card_le_univ X)).trans_lt (sq_lt_two_pow _))
  calc X.card * k ≤ γ * (c * L) * k := Nat.mul_le_mul_right _ hmain
    _ = γ * L * (c * k) := by ring
    _ ≤ γ * L * (2 * A.card) := Nat.mul_le_mul_left _ hck'
    _ = 4 * γ * (Nat.log 2 (Fintype.card V) + 1) * A.card := by ring

end Lax185574Proofs.Chain
