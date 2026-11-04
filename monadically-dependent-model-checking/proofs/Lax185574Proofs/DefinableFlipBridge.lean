import Lax185574.DefinableFlips
import Lax185574.GraphBalls
import Lax185574Proofs.Lib.BallFlipMetric
import Lax185574Proofs.AtomicTypeBridge

/-!
Flips based on a parameter set with a toggle that is constant on
classes of atomic profiles are flips for the partition into atomic
types. Balls and neighborhood traces over finite sets agree with the
balls and atomic types used in the concepts.
-/

namespace Lax185574Proofs.DefinableFlipBridge

open Lax185574.Flips Lax185574.Partitions Lax185574.DefinableFlips Lax185574.GraphBalls
open Lax185574.GaifmanGraph Lax185574.AtomicTypes

universe u

variable {V : Type u}

theorem atomicProfile_eq_iff (G : SimpleGraph V) (S : Finset V) (x y : V) :
    Lax185574Proofs.Lib.DefinableFlips.atomicProfile G S x =
        Lax185574Proofs.Lib.DefinableFlips.atomicProfile G S y ↔
      atomicTypes G (S : Set V) x y := by
  classical
  rw [Lax185574Proofs.FlipBasics.atomicTypes_rel_iff]
  unfold Lax185574Proofs.Lib.DefinableFlips.atomicProfile
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · ext z
      have := congrArg (fun T => z ∈ T) h2
      simp only [Finset.mem_filter] at this
      simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz, rfl⟩; exact ⟨hz, ((this.mp ⟨hz, rfl⟩).2).symm⟩
      · rintro ⟨hz, rfl⟩; exact ⟨hz, ((this.mpr ⟨hz, rfl⟩).2).symm⟩
    · ext z
      have := congrArg (fun T => z ∈ T) h1
      simp only [Finset.mem_filter] at this
      simp only [Set.mem_inter_iff, Finset.mem_coe, SimpleGraph.mem_neighborSet]
      exact Iff.of_eq this
  · rintro ⟨h1, h2⟩
    constructor
    · ext z
      have := congrArg (fun T => z ∈ T) h2
      simp only [Set.mem_inter_iff, Finset.mem_coe, SimpleGraph.mem_neighborSet] at this
      simp only [Finset.mem_filter]
      exact Iff.of_eq this
    · ext z
      have := congrArg (fun T => z ∈ T) h1
      simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_singleton_iff] at this
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, rfl⟩; exact ⟨hz, ((this.mp ⟨hz, rfl⟩).2).symm⟩
      · rintro ⟨hz, rfl⟩; exact ⟨hz, ((this.mpr ⟨hz, rfl⟩).2).symm⟩

theorem isFlip_of_isBasedFlip {G H : SimpleGraph V} {S : Finset V}
    (h : Lax185574Proofs.Lib.DefinableFlips.IsBasedFlip G S H) :
    IsFlip G (atomicTypes G (S : Set V)) H := by
  obtain ⟨toggle, -, hinv, hH⟩ := h
  intro a b
  by_cases hab : toggle a b
  · right
    intro x y hx hy hxy
    have ht : toggle x y := (hinv x a y b ((atomicProfile_eq_iff G S x a).mpr hx)
      ((atomicProfile_eq_iff G S y b).mpr hy)).mpr hab
    rw [hH]
    simp only [Xor, ht]
    tauto
  · left
    intro x y hx hy hxy
    have ht : ¬ toggle x y := fun ht => hab ((hinv x a y b
      ((atomicProfile_eq_iff G S x a).mpr hx) ((atomicProfile_eq_iff G S y b).mpr hy)).mp ht)
    rw [hH]
    simp only [Xor, ht]
    tauto

theorem isDefinableFlip_of_lib {G H : SimpleGraph V} {s : ℕ}
    (h : Lax185574Proofs.Lib.DefinableFlips.IsDefinableFlip G H s) :
    IsDefinableFlip G s H := by
  obtain ⟨S, hS, hb⟩ := h
  exact ⟨S, hS, isFlip_of_isBasedFlip hb⟩

theorem coe_ball [Fintype V] (G : SimpleGraph V) (C : Finset V) (r : ℕ) :
    (Lax185574Proofs.Lib.BallFlips.ball G C r : Set V) = graphBall G r (C : Set V) := by
  ext v
  rw [Finset.mem_coe, Lax185574Proofs.Lib.BallFlipMetric.mem_ball]
  rfl

/-- Outside `A`, the number of distinct traces on `A` is the number of
atomic types over `A`. -/
theorem card_traces_eq (G : SimpleGraph V) (A B : Finset V) (hAB : Disjoint B A) :
    (Lax185574Proofs.Lib.BallFlips.traces G A B).card =
      atomicTypeCount G (B : Set V) (A : Set V) := by
  classical
  rw [Lax185574Proofs.AtomicTypeBridge.atomicTypeCount_eq_partCount, partCount,
    ← Set.ncard_coe_finset]
  unfold Lax185574Proofs.Lib.BallFlips.traces
  rw [Finset.coe_image]
  refine Lax185574Proofs.AtomicTypeBridge.ncard_image_congr _ _ fun x hx y hy => ?_
  rw [Quotient.eq, Lax185574Proofs.FlipBasics.atomicTypes_rel_iff']
  have hxA : x ∉ A := Finset.disjoint_left.mp hAB hx
  have hyA : y ∉ A := Finset.disjoint_left.mp hAB hy
  unfold Lax185574Proofs.Lib.BallFlips.trace
  constructor
  · intro h
    right
    refine ⟨hxA, hyA, fun s hs => ?_⟩
    have := congrArg (fun T => s ∈ T) h
    simpa [Finset.mem_coe.mp hs] using this
  · rintro (rfl | ⟨-, -, h⟩)
    · rfl
    · ext s
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨hs, h'⟩ => ⟨hs, (h s hs).mp h'⟩, fun ⟨hs, h'⟩ => ⟨hs, (h s hs).mpr h'⟩⟩

end Lax185574Proofs.DefinableFlipBridge
