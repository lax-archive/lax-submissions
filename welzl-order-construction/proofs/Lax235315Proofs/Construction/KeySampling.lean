import Lax235315Proofs.Construction.FiniteRandomKeys
import Lax235315Proofs.Construction.Sampling
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
Uniform sampling by collision-free random keys.
-/

namespace Lax235315Proofs.Construction.KeySampling

open Finset
open Lax235315Proofs.Construction.FiniteRandomKeys
open Lax235315Proofs.Construction.Sampling

/-- A random key assignment with no collisions. -/
abbrev KeyInjection (α : Type*) [Fintype α] (M : ℕ) :=
  {f : α → Fin M // Function.Injective f}

/-- Number of vertices whose key is strictly smaller than `x`'s key. -/
def keyRank {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (f : α → Fin M) (x : α) : ℕ :=
  (Finset.univ.filter fun y => f y < f x).card

lemma keyRank_lt {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (f : α → Fin M) (x : α) :
    keyRank f x < Fintype.card α := by
  unfold keyRank
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro h
  have hx := h (Finset.mem_univ x)
  simp at hx

def keyRankFin {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (f : α → Fin M) (x : α) : Fin (Fintype.card α) :=
  ⟨keyRank f x, keyRank_lt f x⟩

lemma keyRank_strictMono {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} {f : α → Fin M} {x y : α} (hxy : f x < f y) :
    keyRank f x < keyRank f y := by
  unfold keyRank
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz'.trans hxy⟩
  · intro hsub
    have hxmem : x ∈ Finset.univ.filter fun z => f z < f y :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    have := hsub hxmem
    simp at this

lemma keyRankFin_injective {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (f : KeyInjection α M) :
    Function.Injective (keyRankFin f.1) := by
  intro x y hrank
  apply f.2
  apply le_antisymm
  · apply le_of_not_gt
    intro hyx
    have := keyRank_strictMono hyx
    exact (Fin.ne_of_lt this) hrank.symm
  · apply le_of_not_gt
    intro hxy
    have := keyRank_strictMono hxy
    exact (Fin.ne_of_lt this) hrank

lemma keyRankFin_surjective {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (f : KeyInjection α M) :
    Function.Surjective (keyRankFin f.1) := by
  exact ((Fintype.bijective_iff_injective_and_card (keyRankFin f.1)).mpr
    ⟨keyRankFin_injective f, by simp⟩).2

/-- The vertices with the `s` smallest keys. -/
def keySample {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (f : KeyInjection α M) (s : ℕ) : Finset α :=
  Finset.univ.filter fun x => keyRank f.1 x < s

lemma card_keySample {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} (f : KeyInjection α M) (hs : s ≤ Fintype.card α) :
    (keySample f s).card = s := by
  classical
  let target : Finset (Fin (Fintype.card α)) :=
    Finset.univ.filter fun i => i.val < s
  have himage : (keySample f s).image (keyRankFin f.1) = target := by
    ext i
    constructor
    · rintro hi
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hx).2⟩
    · intro hi
      have his : i.val < s := (Finset.mem_filter.mp hi).2
      obtain ⟨x, hx⟩ := keyRankFin_surjective f i
      subst i
      exact Finset.mem_image.mpr ⟨x,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, his⟩, rfl⟩
  calc
    (keySample f s).card =
        ((keySample f s).image (keyRankFin f.1)).card :=
      (Finset.card_image_of_injective _ (keyRankFin_injective f)).symm
    _ = target.card := by rw [himage]
    _ = s := by
      rw [← Fintype.card_coe]
      simpa [target] using Fintype.card_fin_lt_of_le hs

lemma keySample_subset_univ {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} (f : KeyInjection α M) :
    keySample f s ⊆ Finset.univ := fun _ _ => Finset.mem_univ _

/-- Relabeling the domain of a collision-free key assignment. -/
def relabel {α : Type*} [Fintype α] {M : ℕ}
    (σ : Equiv.Perm α) (f : KeyInjection α M) : KeyInjection α M :=
  ⟨fun x => f.1 (σ.symm x), f.2.comp σ.symm.injective⟩

def relabelEquiv {α : Type*} [Fintype α] {M : ℕ}
    (σ : Equiv.Perm α) : KeyInjection α M ≃ KeyInjection α M where
  toFun := relabel σ
  invFun := relabel σ.symm
  left_inv := by
    intro f
    apply Subtype.ext
    funext x
    simp [relabel]
  right_inv := by
    intro f
    apply Subtype.ext
    funext x
    simp [relabel]

lemma keyRank_relabel {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (σ : Equiv.Perm α) (f : KeyInjection α M) (x : α) :
    keyRank (relabel σ f).1 (σ x) = keyRank f.1 x := by
  classical
  unfold keyRank
  let low := Finset.univ.filter fun y => f.1 y < f.1 x
  have heq : (Finset.univ.filter fun y => (relabel σ f).1 y <
      (relabel σ f).1 (σ x)) = low.map σ.toEmbedding := by
    ext y
    simp [low, relabel]
  rw [heq, Finset.card_map]

lemma keySample_relabel {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} (σ : Equiv.Perm α) (f : KeyInjection α M) :
    keySample (relabel σ f) s = (keySample f s).map σ.toEmbedding := by
  classical
  ext y
  constructor
  · intro hy
    let x := σ.symm y
    have hxrank : keyRank f.1 x < s := by
      rw [← keyRank_relabel σ f x]
      simpa [x] using (Finset.mem_filter.mp hy).2
    exact Finset.mem_map.mpr ⟨x,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxrank⟩, by simp [x]⟩
  · rintro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      change keyRank (relabel σ f).1 (σ x) < s
      rw [keyRank_relabel]
      exact (Finset.mem_filter.mp hx).2⟩

/-- Collision-free assignments selecting a prescribed sample. -/
def sampleFiber {α : Type*} [Fintype α] [DecidableEq α]
    (M s : ℕ) (W : Finset α) : Finset (KeyInjection α M) :=
  Finset.univ.filter fun f => keySample f s = W

lemma card_sampleFiber_eq_of_map {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} {W W' : Finset α} (σ : Equiv.Perm α)
    (hσ : W.map σ.toEmbedding = W') :
    (sampleFiber M s W).card = (sampleFiber M s W').card := by
  classical
  apply Finset.card_bijective (relabelEquiv σ)
  · exact (relabelEquiv σ).bijective
  · intro f
    simp only [sampleFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change keySample f s = W ↔ keySample (relabel σ f) s = W'
    rw [keySample_relabel]
    constructor
    · intro hf
      rw [hf, hσ]
    · intro hf
      exact Finset.map_injective σ.toEmbedding (hf.trans hσ.symm)

/-- All samples of the same size have equally many collision-free key
assignments. -/
lemma card_sampleFiber_eq_of_card {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} {W W' : Finset α} (hcard : W.card = W'.card) :
    (sampleFiber M s W).card = (sampleFiber M s W').card := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq W W' hcard
  exact card_sampleFiber_eq_of_map σ hσ

/-- The fibers of the collision-free key sampler are uniform on the
prescribed-size subsets. -/
lemma card_sampleFiber_eq {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} {W W' : Finset α}
    (hW : W ∈ samples (Finset.univ : Finset α) s)
    (hW' : W' ∈ samples (Finset.univ : Finset α) s) :
    (sampleFiber M s W).card = (sampleFiber M s W').card := by
  exact card_sampleFiber_eq_of_card
    ((Finset.mem_powersetCard.mp hW).2.trans
      (Finset.mem_powersetCard.mp hW').2.symm)

end Lax235315Proofs.Construction.KeySampling
