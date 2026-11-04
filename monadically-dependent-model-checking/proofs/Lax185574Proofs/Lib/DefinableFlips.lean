import Lax185574Proofs.Lib.DefinableFlipsDefs
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Powerset

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.DefinableFlips

open Lax185574Proofs.Lib.DefinableFlips

universe u

theorem atomicProfile_eq_iff {V : Type u} (G : SimpleGraph V)
    (S : Finset V) (v w : V) :
    atomicProfile G S v = atomicProfile G S w ↔
      ∀ a ∈ S, (G.Adj v a ↔ G.Adj w a) ∧ (v = a ↔ w = a) := by
  classical
  constructor
  · intro h a ha
    have h₁ := congrArg (fun x : Finset V × Finset V => a ∈ x.1) h
    have h₂ := congrArg (fun x : Finset V × Finset V => a ∈ x.2) h
    simpa [atomicProfile, ha] using And.intro (Eq.to_iff h₁) (Eq.to_iff h₂)
  · intro h
    apply Prod.ext <;> apply Finset.ext <;> intro a <;>
      simp only [atomicProfile, Finset.mem_filter]
    · exact and_congr_right fun ha => (h a ha).1
    · exact and_congr_right fun ha => (h a ha).2

theorem atomicProfile_eq_of_subset {V : Type u} {G : SimpleGraph V}
    {S T : Finset V} (hST : S ⊆ T) {v w : V}
    (h : atomicProfile G T v = atomicProfile G T w) :
    atomicProfile G S v = atomicProfile G S w := by
  rw [atomicProfile_eq_iff] at h ⊢
  exact fun a ha => h a (hST ha)

theorem basedFlip_refl {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    IsBasedFlip G S G := by
  refine ⟨fun _ _ => False, fun _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl, ?_⟩
  intro u v
  simp only [Xor, not_false_eq_true, and_true, false_and, or_false]
  exact ⟨fun h => ⟨G.ne_of_adj h, h⟩, fun h => h.2⟩

theorem definableFlip_refl {V : Type u} (G : SimpleGraph V) :
    IsDefinableFlip G G 0 :=
  ⟨∅, by simp, basedFlip_refl G ∅⟩

theorem definableFlip_mono {V : Type u} {G H : SimpleGraph V}
    {s t : ℕ} (hst : s ≤ t) (h : IsDefinableFlip G H s) :
    IsDefinableFlip G H t := by
  obtain ⟨S, hS, hf⟩ := h
  exact ⟨S, hS.trans hst, hf⟩

theorem basedFlip_mono {V : Type u} {G H : SimpleGraph V}
    {S T : Finset V} (hST : S ⊆ T) (h : IsBasedFlip G S H) :
    IsBasedFlip G T H := by
  obtain ⟨toggle, hs, hc, he⟩ := h
  exact ⟨toggle, hs, fun u u' v v' hu hv =>
    hc u u' v v' (atomicProfile_eq_of_subset hST hu)
      (atomicProfile_eq_of_subset hST hv), he⟩

theorem atomicProfile_eq_after_flip {V : Type u} [DecidableEq V] {G H : SimpleGraph V}
    {S T : Finset V} (hflip : IsBasedFlip G S H) {v w : V}
    (h : atomicProfile G (S ∪ T) v = atomicProfile G (S ∪ T) w) :
    atomicProfile H T v = atomicProfile H T w := by
  classical
  obtain ⟨toggle, _hsymm, hconst, hadj⟩ := hflip
  have hS := atomicProfile_eq_of_subset Finset.subset_union_left h
  have hT := atomicProfile_eq_of_subset Finset.subset_union_right h
  rw [atomicProfile_eq_iff] at hT ⊢
  intro a ha
  refine ⟨?_, (hT a ha).2⟩
  rw [hadj, hadj]
  have ht := hconst v w a a hS rfl
  have he := (hT a ha).2
  have hg := (hT a ha).1
  simp only [Xor]
  tauto

theorem basedFlip_trans {V : Type u} [DecidableEq V] {G₀ G₁ G₂ : SimpleGraph V}
    {S₁ S₂ : Finset V} (h₁ : IsBasedFlip G₀ S₁ G₁)
    (h₂ : IsBasedFlip G₁ S₂ G₂) : IsBasedFlip G₀ (S₁ ∪ S₂) G₂ := by
  classical
  obtain ⟨t₁, hs₁, hc₁, he₁⟩ := h₁
  obtain ⟨t₂, hs₂, hc₂, he₂⟩ := h₂
  refine ⟨fun u v => Xor (t₁ u v) (t₂ u v), ?_, ?_, ?_⟩
  · intro u v
    simp only [Xor, hs₁ u v, hs₂ u v]
  · intro u u' v v' hu hv
    have ht₁ := hc₁ u u' v v'
      (atomicProfile_eq_of_subset Finset.subset_union_left hu)
      (atomicProfile_eq_of_subset Finset.subset_union_left hv)
    have hf₁ : IsBasedFlip G₀ S₁ G₁ := ⟨t₁, hs₁, hc₁, he₁⟩
    have ht₂ := hc₂ u u' v v'
      (atomicProfile_eq_after_flip hf₁ hu) (atomicProfile_eq_after_flip hf₁ hv)
    simp only [Xor, ht₁, ht₂]
  · intro u v
    rw [he₂, he₁]
    simp only [Xor]
    tauto

/--
Use the union of the two parameter sets and the exclusive-or of their
toggle relations. Atomic types over the union determine both steps.
-/
theorem definableFlip_trans {V : Type u} {G₀ G₁ G₂ : SimpleGraph V}
    {s₁ s₂ : ℕ} (h₁ : IsDefinableFlip G₀ G₁ s₁)
    (h₂ : IsDefinableFlip G₁ G₂ s₂) : IsDefinableFlip G₀ G₂ (s₁ + s₂) := by
  classical
  obtain ⟨S₁, hS₁, hf₁⟩ := h₁
  obtain ⟨S₂, hS₂, hf₂⟩ := h₂
  exact ⟨S₁ ∪ S₂, (Finset.card_union_le S₁ S₂).trans (Nat.add_le_add hS₁ hS₂),
    basedFlip_trans hf₁ hf₂⟩

/--
Use realized atomic profiles as labels. Each consists of two subsets
of the parameter set, so there are at most `4 ^ S.card` labels.
-/
theorem exists_bounded_partition {V : Type u} [Fintype V]
    (G H : SimpleGraph V) (S : Finset V) (h : IsBasedFlip G S H) :
    ∃ (p : ℕ) (part : V → Fin p) (toggle : Fin p → Fin p → Bool)
      (hsymm : ∀ i j, toggle i j = toggle j i),
      p ≤ 4 ^ S.card ∧ H =
        Lax185574Proofs.Lib.PartitionMetricConversion.flip G part toggle hsymm := by
  classical
  obtain ⟨t, hsymm, hconst, hadj⟩ := h
  let labels := Finset.univ.image (atomicProfile G S)
  let e := Fintype.equivFin labels
  let part : V → Fin (Fintype.card labels) :=
    fun v => e ⟨atomicProfile G S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩
  have hsurj : Function.Surjective part := by
    intro i
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 (e.symm i).property
    refine ⟨v, ?_⟩
    change e _ = i
    have hv' : (⟨atomicProfile G S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩ :
        labels) = e.symm i := Subtype.ext hv
    exact (congrArg e hv').trans (e.apply_symm_apply i)
  choose repr hrepr using hsurj
  have hprofile (v : V) : atomicProfile G S (repr (part v)) = atomicProfile G S v := by
    have hh := e.injective (hrepr (part v))
    exact congrArg Subtype.val hh
  let toggle : Fin (Fintype.card labels) → Fin (Fintype.card labels) → Bool :=
    fun i j => decide (t (repr i) (repr j))
  have htoggle : ∀ i j, toggle i j = toggle j i := by
    intro i j
    exact congrArg (fun p : Prop => decide p) (propext (hsymm _ _))
  refine ⟨Fintype.card labels, part, toggle, htoggle, ?_, ?_⟩
  · have hsub : labels ⊆ S.powerset ×ˢ S.powerset := by
      intro x hx
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hx
      simp only [Finset.mem_product, Finset.mem_powerset, atomicProfile]
      exact ⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩
    calc
      Fintype.card labels = labels.card := Fintype.card_coe _
      _ ≤ (S.powerset ×ˢ S.powerset).card := Finset.card_le_card hsub
      _ = 4 ^ S.card := by
        rw [Finset.card_product, Finset.card_powerset]
        rw [← mul_pow]
        rfl
  · apply SimpleGraph.ext
    funext v w
    apply propext
    change H.Adj v w ↔ v ≠ w ∧ Xor (G.Adj v w) (toggle (part v) (part w) = true)
    rw [hadj]
    have ht := hconst (repr (part v)) v (repr (part w)) w (hprofile v) (hprofile w)
    simp only [toggle, decide_eq_true_eq, ht]

end Lax185574Proofs.Lib.DefinableFlips
