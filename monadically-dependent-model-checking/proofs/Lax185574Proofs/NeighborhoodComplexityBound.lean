import Lax185574.NeighborhoodComplexityBound
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Bounds

namespace Lax185574Proofs.NeighborhoodComplexityBound

open Lax185574.VCDimension Lax199508.NeighborhoodComplexity Finset

universe u

/-- A sum of binomial coefficients up to `e` is at most `(m + 1)^e`. -/
theorem sum_choose_le_pow (m e : ℕ) :
    ∑ i ∈ Iic e, m.choose i ≤ (m + 1) ^ e := by
  rw [add_pow, ← Nat.range_succ_eq_Iic]
  refine sum_le_sum fun i hi => ?_
  have hi : i ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [one_pow, mul_one]
  exact (Nat.choose_le_pow m i).trans
    (Nat.le_mul_of_pos_right _ (Nat.choose_pos hi))

/-- The traces of the neighborhoods of `G` on a finite set `S`, as a
family of finite subsets of `S`. -/
noncomputable def traceFamily {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset S) := by
  classical
  exact univ.filter fun T : Finset S =>
    ∃ v : V, ∀ s : S, s ∈ T ↔ G.Adj v s

theorem traceCount_eq_card {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    traceCount G (S : Set V) = (traceFamily G S).card := by
  classical
  let f : Finset S → Set V := fun T => Subtype.val '' (T : Set S)
  have hf : Function.Injective f := by
    intro T T' h
    ext s
    have := congrArg (fun X : Set V => (s : V) ∈ X) h
    simpa [f] using this
  have hset : {X : Set V | ∃ v : V, X = G.neighborSet v ∩ (S : Set V)} =
      f '' (traceFamily G S : Set (Finset S)) := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_image, coe_filter, traceFamily, mem_univ,
      true_and]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨univ.filter fun s : S => G.Adj v s, ⟨v, fun s => by simp⟩, ?_⟩
      ext x
      simp only [f, coe_filter, mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq,
        Set.mem_inter_iff, SimpleGraph.mem_neighborSet, mem_coe]
      constructor
      · rintro ⟨s, hs, rfl⟩; exact ⟨hs, s.2⟩
      · rintro ⟨hx, hS⟩; exact ⟨⟨x, hS⟩, hx, rfl⟩
    · rintro ⟨T, ⟨v, hv⟩, rfl⟩
      refine ⟨v, ?_⟩
      ext x
      simp only [f, Set.mem_image, mem_coe, Set.mem_inter_iff,
        SimpleGraph.mem_neighborSet]
      constructor
      · rintro ⟨s, hs, rfl⟩; exact ⟨(hv s).1 hs, s.2⟩
      · rintro ⟨hx, hS⟩; exact ⟨⟨x, hS⟩, (hv ⟨x, hS⟩).2 hx, rfl⟩
  unfold traceCount
  rw [hset, Set.ncard_image_of_injective _ hf, Set.ncard_coe_finset]

open Classical in
theorem vcDim_traceFamily_le {V : Type u} (G : SimpleGraph V) (S : Finset V) (d : ℕ)
    (hG : vcDim G ≤ d) : (traceFamily G S).vcDim ≤ d := by
  classical
  refine Finset.sup_le fun T hT => ?_
  have hsh : (traceFamily G S).Shatters T := mem_shatterer.mp hT
  have hGsh : Shatters G (T.map (Function.Embedding.subtype _)) := by
    intro B hB
    obtain ⟨U, hU, hTU⟩ := @hsh (T.filter fun s => (s : V) ∈ B) (filter_subset _ _)
    obtain ⟨v, hv⟩ := (mem_filter.mp hU).2
    refine ⟨v, fun a ha => ?_⟩
    obtain ⟨s, hs, rfl⟩ := mem_map.mp ha
    have := congrArg (fun X => s ∈ X) hTU
    simp only [mem_inter, mem_filter] at this
    simp only [Function.Embedding.subtype_apply]
    rw [← hv s]
    constructor
    · intro h; exact (this.mp ⟨hs, h⟩).2
    · intro h; exact (this.mpr ⟨hs, h⟩).2
  have h1 : ((T.map (Function.Embedding.subtype _)).card : ℕ∞) ≤ vcDim G :=
    le_iSup₂ (f := fun (A : Finset V) (_ : Shatters G A) => (A.card : ℕ∞)) _ hGsh
  rw [card_map] at h1
  exact_mod_cast h1.trans hG

/--
---
conclusion: Lax185574.NeighborhoodComplexityBound.neighborhoodComplexity_le
---
The Sauer–Shelah lemma. The traces on a set `S` of at most `k` vertices
form a family of subsets of `S` whose shattered sets are shattered by
the neighborhoods of `G`, so they have size at most `d`. By the
Sauer–Shelah lemma of mathlib (via Pajor's bound on the shatterer) the
family has at most `∑_{i ≤ d} C(|S|, i) ≤ (|S| + 1)^d ≤ (k + 1)^d`
members.
-/
theorem neighborhoodComplexity_le {V : Type u} (G : SimpleGraph V) (d : ℕ)
    (hG : vcDim G ≤ d) (k : ℕ) : neighborhoodComplexity G k ≤ (k + 1) ^ d := by
  classical
  refine csSup_le ⟨_, ∅, by simp, rfl⟩ ?_
  rintro _ ⟨S, hS, rfl⟩
  rw [traceCount_eq_card]
  calc (traceFamily G S).card ≤ (traceFamily G S).shatterer.card :=
        card_le_card_shatterer _
    _ ≤ ∑ i ∈ Iic (traceFamily G S).vcDim, (Fintype.card S).choose i :=
        card_shatterer_le_sum_vcDim
    _ ≤ (Fintype.card S + 1) ^ (traceFamily G S).vcDim := sum_choose_le_pow _ _
    _ ≤ (k + 1) ^ d := by
        rw [Fintype.card_coe]
        exact (Nat.pow_le_pow_left (by omega) _).trans
          (Nat.pow_le_pow_right (by omega) (vcDim_traceFamily_le G S d hG))

end Lax185574Proofs.NeighborhoodComplexityBound
