import Lax185574.GraphBalls
import Lax185574.VCDimension
import Lax185574Proofs.FlipBridge
import Lax185574Proofs.AtomicPartitionCount
import Lax185574Proofs.NeighborhoodComplexityBound

/-!
Auxiliary facts for the closure theorem: balls of radius 0, the flip
isolating a vertex, the number of atomic types over a set in terms of
the neighborhood complexity, and the number of flips for a partition.
-/

namespace Lax185574Proofs.ClosureHelpers

open Lax185574.Flips Lax185574.Partitions Lax185574.GraphBalls Lax185574.GaifmanGraph
open Lax185574.VCDimension Lax199508.NeighborhoodComplexity

universe u

variable {V : Type u}

theorem withinDist_zero {G : SimpleGraph V} {u v : V} : WithinDist G 0 u v ↔ u = v := by
  constructor
  · rintro ⟨w, hw⟩
    exact SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hw)
  · rintro rfl; exact ⟨.nil, le_rfl⟩

theorem graphBall_zero_singleton (G : SimpleGraph V) (v : V) : graphBall G 0 {v} = {v} := by
  ext u
  simp only [graphBall, Set.mem_singleton_iff, Set.mem_ofPred_eq, exists_eq_left,
    withinDist_zero]
  exact eq_comm

theorem graphBall_mono_center (G : SimpleGraph V) (r : ℕ) {C D : Set V} (h : C ⊆ D) :
    graphBall G r C ⊆ graphBall G r D :=
  fun _ ⟨c, hc, hw⟩ => ⟨c, h hc, hw⟩

/-- The graph `G` with all edges at `v` removed. -/
def isolate (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ v ∧ y ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

theorem isFlip_isolate (G : SimpleGraph V) (v : V) :
    IsFlip G (atomicTypes G ({v} : Set V)) (isolate G v) := by
  have hv : ∀ x, atomicTypes G ({v} : Set V) x v → x = v := by
    intro x h
    rcases (Lax185574Proofs.FlipBasics.atomicTypes_rel_iff' G _ x v).mp h with h | ⟨-, h, -⟩
    · exact h
    · exact absurd rfl h
  have hne : ∀ x a, a ≠ v → atomicTypes G ({v} : Set V) x a → x ≠ v := by
    rintro x a ha h rfl
    exact ha (hv a (Setoid.symm' _ h))
  have hadj : ∀ x a, a ≠ v → atomicTypes G ({v} : Set V) x a → (G.Adj x v ↔ G.Adj a v) := by
    intro x a ha h
    rcases (Lax185574Proofs.FlipBasics.atomicTypes_rel_iff' G _ x a).mp h with rfl | ⟨-, -, h⟩
    · rfl
    · exact h v rfl
  intro a b
  by_cases ha : a = v <;> by_cases hb : b = v
  · left; intro x y hx hy hxy
    rw [ha] at hx; rw [hb] at hy
    exact absurd ((hv x hx).trans (hv y hy).symm) hxy
  · rw [ha]
    by_cases hbv : G.Adj b v
    · right; intro x y hx hy hxy
      rw [hv x hx] at hxy ⊢
      have := (hadj y b hb hy).mpr hbv
      simp [isolate, G.adj_comm v y, this]
    · left; intro x y hx hy hxy
      rw [hv x hx] at hxy ⊢
      have := mt (hadj y b hb hy).mp hbv
      simp [isolate, G.adj_comm v y, this]
  · rw [hb]
    by_cases hav : G.Adj a v
    · right; intro x y hx hy hxy
      rw [hv y hy] at hxy ⊢
      have := (hadj x a ha hx).mpr hav
      simp [isolate, this]
    · left; intro x y hx hy hxy
      rw [hv y hy] at hxy ⊢
      have := mt (hadj x a ha hx).mp hav
      simp [isolate, this]
  · left; intro x y hx hy hxy
    simp [isolate, hne x a ha hx, hne y b hb hy]

theorem graphBall_isolate (G : SimpleGraph V) (v : V) (r : ℕ) :
    graphBall (isolate G v) r {v} ⊆ {v} := by
  rintro u ⟨c, hc, w, -⟩
  rw [Set.mem_singleton_iff] at hc ⊢
  subst hc
  cases w with
  | nil => rfl
  | cons h _ => exact absurd rfl h.2.1

/-- On a finite set `S`, the number of traces is at most `2^|S|`. -/
theorem traceCount_le (G : SimpleGraph V) (S : Finset V) :
    traceCount G (S : Set V) ≤ 2 ^ S.card := by
  rw [Lax185574Proofs.NeighborhoodComplexityBound.traceCount_eq_card]
  calc _ ≤ (Finset.univ : Finset (Finset S)).card := Finset.card_le_univ _
    _ = 2 ^ S.card := by simp

theorem traceCount_le_neighborhoodComplexity (G : SimpleGraph V) (S : Finset V) :
    traceCount G (S : Set V) ≤ neighborhoodComplexity G S.card := by
  refine le_csSup ⟨2 ^ S.card, ?_⟩ ⟨S, le_rfl, rfl⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (traceCount_le G T).trans (Nat.pow_le_pow_right (by omega) hT)

/-- The partition into atomic types over `A` has at most
`|A| + π_G(|A|)` parts. -/
theorem card_quotient_atomicTypes_le_nc [Finite V] (G : SimpleGraph V) (A : Finset V) :
    Nat.card (Quotient (atomicTypes G (A : Set V))) ≤
      A.card + neighborhoodComplexity G A.card := by
  classical
  let T := {X : Set V | ∃ v : V, X = G.neighborSet v ∩ (A : Set V)}
  let g : V → A ⊕ T := fun v =>
    if h : v ∈ A then .inl ⟨v, h⟩ else .inr ⟨G.neighborSet v ∩ (A : Set V), v, rfl⟩
  have hg : ∀ x y, atomicTypes G (A : Set V) x y ↔ g x = g y := by
    intro x y
    rw [Lax185574Proofs.FlipBasics.atomicTypes_rel_iff']
    constructor
    · rintro (rfl | ⟨hx, hy, h⟩)
      · rfl
      · have hx' : x ∉ A := hx
        have hy' : y ∉ A := hy
        simp only [g, hx', hy', dite_false, Sum.inr.injEq, Subtype.mk.injEq]
        ext s
        simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Finset.mem_coe]
        exact ⟨fun ⟨h1, h2⟩ => ⟨(h s h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h s h2).mpr h1, h2⟩⟩
    · intro h
      by_cases hx : x ∈ A
      · by_cases hy : y ∈ A
        · simp only [g, hx, hy, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at h
          exact Or.inl h
        · simp [g, hx, hy] at h
      · by_cases hy : y ∈ A
        · simp [g, hx, hy] at h
        · simp only [g, hx, hy, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at h
          refine Or.inr ⟨hx, hy, fun s hs => ?_⟩
          have := congrArg (fun X => s ∈ X) h
          simpa [hs, SimpleGraph.mem_neighborSet] using this
  have hT : T.Finite := Set.toFinite T
  have := hT.fintype
  refine (Lax185574Proofs.AtomicPartitionCount.card_quotient_le_of_iff _ g hg).trans ?_
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := A), Fintype.card_coe]
  refine Nat.add_le_add_left ?_ _
  have : Nat.card T = traceCount G (A : Set V) := by
    rw [traceCount, Nat.card_coe_set_eq]
  rw [this]
  exact traceCount_le_neighborhoodComplexity G A

/-- There are at most `2^(p²)` flips of `G` for a partition into `p`
parts. -/
theorem card_flips_le [Fintype V] (G : SimpleGraph V) (P : Setoid V)
    [Fintype (SimpleGraph V)] [DecidablePred (IsFlip G P)] :
    (Finset.univ.filter (IsFlip G P)).card ≤
      2 ^ (Nat.card (Quotient P) * Nat.card (Quotient P)) := by
  classical
  let part := Lax185574Proofs.FlipBridge.labeling P
  let p := Nat.card (Quotient P)
  let f : SimpleGraph V → Fin p → Fin p → Bool := fun H => Lax185574Proofs.FlipBridge.toggleOf G part H
  have hinj : Set.InjOn f (Finset.univ.filter (IsFlip G P) : Set (SimpleGraph V)) := by
    intro H hH H' hH' h
    have hH : IsFlip G (Setoid.ker part) H := by
      rw [Lax185574Proofs.FlipBridge.ker_labeling]; exact (Finset.mem_filter.mp hH).2
    have hH' : IsFlip G (Setoid.ker part) H' := by
      rw [Lax185574Proofs.FlipBridge.ker_labeling]; exact (Finset.mem_filter.mp hH').2
    rw [Lax185574Proofs.FlipBridge.eq_flip_toggleOf G part H hH,
      Lax185574Proofs.FlipBridge.eq_flip_toggleOf G part H' hH']
    have h' : Lax185574Proofs.FlipBridge.toggleOf G part H =
        Lax185574Proofs.FlipBridge.toggleOf G part H' := h
    simp only [h']
  calc _ = ((Finset.univ.filter (IsFlip G P)).image f).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin p → Fin p → Bool)).card := Finset.card_le_univ _
    _ = 2 ^ (p * p) := by simp [pow_mul]

/-- A set of `N` elements has at most `(N + 1)^m` subsets of size at
most `m`. -/
theorem card_small_subsets_le {α : Type*} [DecidableEq α] (X : Finset α) (m : ℕ) :
    (X.powerset.filter fun T => T.card ≤ m).card ≤ (X.card + 1) ^ m := by
  have hsub : (X.powerset.filter fun T => T.card ≤ m) ⊆
      (Finset.Iic m).biUnion fun i => X.powersetCard i := by
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    exact Finset.mem_biUnion.mpr ⟨T.card, Finset.mem_Iic.mpr hT.2,
      Finset.mem_powersetCard.mpr ⟨hT.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  simp only [Finset.card_powersetCard]
  exact Lax185574Proofs.NeighborhoodComplexityBound.sum_choose_le_pow _ _

end Lax185574Proofs.ClosureHelpers
