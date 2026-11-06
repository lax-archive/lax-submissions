import Lax185574.ClosureTheoremTuples
import Lax185574.ClosureTheorem
import Lax185574.FlipMetricMonotone
import Lax185574.PartitionMetricConversion
import Lax185574Proofs.AtomicPartitionCount
import Lax185574Proofs.ClosureHelpers
import Lax185574Proofs.Interface.Shim.ClosureTheorem

namespace Lax185574Proofs.ClosureTheoremTuples

open Lax199508.GraphClasses
open Lax185574.Flips Lax185574.GraphBalls Lax185574.Partitions Lax185574.GaifmanGraph

theorem mul_two_pow_mono {a b : ℕ} (h : a ≤ b) : a * 2 ^ a ≤ b * 2 ^ b :=
  Nat.mul_le_mul h (Nat.pow_le_pow_right (by omega) h)

/-- The closure theorem for tuples at radius `r` and tuple length `k`. -/
def ClosureTuplesAt (C : GraphClass) (r k : ℕ) : Prop :=
  ∃ c s a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ∀ A : Finset (Fin n), ∃ family : Finset (SimpleGraph (Fin n)),
      family.card ≤ a * (A.card + 1) ^ c ∧
      (∀ H ∈ family, ∃ P : Setoid (Fin n),
        Nat.card (Quotient P) ≤ s ∧ IsFlip G P H) ∧
      ∀ v : Fin k → Fin n, (∀ i, v i ∉ A) →
        ∃ H ∈ family, Disjoint (graphBall H r (Set.range v)) (A : Set (Fin n))

/-- The statement for the graph classes of the archive. -/
theorem closure_theorem_tuples_old (C : GraphClass)
    (hC : Lax185574.DpMinimality.DpMinimal (Lax185574Proofs.Interface.ofOld C)) (r k : ℕ) :
    ClosureTuplesAt C r k := by
  classical
  obtain ⟨c₀, s₀, a₀, hcl⟩ := Lax185574Proofs.Shim.ClosureTheorem.closure_theorem C hC (6 * r)
  let m := k * s₀
  let p := 3 ^ m
  refine ⟨c₀ * m, p * 2 ^ p, (a₀ + 1) ^ m, fun n G hG A => ?_⟩
  obtain ⟨Astar, hAcard, hsep⟩ := hcl n G hG A
  -- the flip attached to a set `T`
  have hconv := fun T : Finset (Fin n) =>
    Lax185574.PartitionMetricConversion.exists_refinement_flip G (atomicTypes G (T : Set (Fin n)))
  choose Q hQle hQcard H hHflip hHball using hconv
  let Ts := Astar.powerset.filter fun T => T.card ≤ m
  refine ⟨Ts.image H, ?_, ?_, ?_⟩
  · -- size of the family
    refine Finset.card_image_le.trans ((Lax185574Proofs.ClosureHelpers.card_small_subsets_le Astar m).trans ?_)
    calc (Astar.card + 1) ^ m ≤ ((a₀ + 1) * (A.card + 1) ^ c₀) ^ m := by
          refine Nat.pow_le_pow_left ?_ m
          have : 1 ≤ (A.card + 1) ^ c₀ := Nat.one_le_pow _ _ (by omega)
          nlinarith
      _ = (a₀ + 1) ^ m * (A.card + 1) ^ (c₀ * m) := by rw [mul_pow, ← pow_mul]
  · -- every member is a flip with few parts
    intro H' hH'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hH'
    have hTm : T.card ≤ m := (Finset.mem_filter.mp hT).2
    refine ⟨Q T, (hQcard T).trans ?_, hHflip T⟩
    have h3 : Nat.card (Quotient (atomicTypes G (T : Set (Fin n)))) ≤ p :=
      (Lax185574Proofs.AtomicPartitionCount.card_quotient_atomicTypes_le G T).trans
        (Nat.pow_le_pow_right (by omega) hTm)
    exact mul_two_pow_mono h3
  · -- separation of tuples
    intro v hv
    choose S hSA hScard F hFflip hFdisj using fun i => hsep (v i) (hv i)
    let T := Finset.univ.biUnion S
    have hTA : T ⊆ Astar := Finset.biUnion_subset.mpr fun i _ => hSA i
    have hTm : T.card ≤ m := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ i, (S i).card ≤ ∑ _i : Fin k, s₀ := Finset.sum_le_sum fun i _ => hScard i
        _ = m := by simp [m]
    refine ⟨H T, Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hTA, hTm⟩, rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro x ⟨_, ⟨i, rfl⟩, hx⟩ hxA
    have h1 : x ∈ flipBall G (atomicTypes G (T : Set (Fin n))) (6 * r) (v i) :=
      hHball T (v i) r ⟨v i, rfl, hx⟩
    have hle : atomicTypes G (T : Set (Fin n)) ≤ atomicTypes G (S i : Set (Fin n)) :=
      Lax185574Proofs.FlipBasics.atomicTypes_anti G
        (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)))
    have h2 := Lax185574.FlipMetricMonotone.flipBall_subset_of_le G hle (6 * r) (v i) h1
    exact Set.disjoint_left.mp (hFdisj i) ⟨v i, rfl, h2 (F i) (hFflip i)⟩ hxA

end Lax185574Proofs.ClosureTheoremTuples

namespace Lax185574Proofs.ClosureTheoremTuples

open Lax185574.Graphs Lax185574.DpMinimality
open Lax185574.Flips Lax185574.GraphBalls Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.ClosureTheoremTuples.closure_theorem_tuples
---
Apply the closure theorem at radius `6r` to obtain `A*` and the sets
`S(v)`. For every `T ⊆ A*` of size at most `k·s₀`, the partition-metric
conversion applied to `𝒫_T`, which has at most `3^{k s₀}` parts, gives one
flip `H_T` whose radius-`r` balls lie in the radius-`6r` balls of the
flip metric of `𝒫_T`. For a tuple `v̄` outside `A` take
`T = S(v₁) ∪ … ∪ S(v_k)`. As `𝒫_T` refines `𝒫_{S(vᵢ)}`, the flip metric
of `𝒫_T` dominates that of `𝒫_{S(vᵢ)}`, and the latter is at least the
distance in the `S(vᵢ)`-flip from the closure theorem, which exceeds `6r`.
So `H_T` separates `v̄` from `A` at distance more than `r`. There are at
most `(|A*| + 1)^{k s₀}` sets `T`.

The argument is carried out for the graph classes of the archive, and
transferred to the graph classes used here.
-/
theorem closure_theorem_tuples (C : GraphClass) (hC : DpMinimal C)
    (r k : ℕ) :
    ∃ c s a : ℕ, ∀ G ∈ C, ∀ A : Finset (Fin G.n),
      ∃ family : Finset (SimpleGraph (Fin G.n)),
        family.card ≤ a * (A.card + 1) ^ c ∧
        (∀ H ∈ family, ∃ P : Setoid (Fin G.n),
          Nat.card (Quotient P) ≤ s ∧ IsFlip G.toSimpleGraph P H) ∧
        ∀ v : Fin k → Fin G.n, (∀ i, v i ∉ A) →
          ∃ H ∈ family, Disjoint (graphBall H r (Set.range v)) (A : Set (Fin G.n)) := by
  obtain ⟨c, s, a, h⟩ := closure_theorem_tuples_old (toOld C) hC r k
  exact ⟨c, s, a, fun G hG => h G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.ClosureTheoremTuples
