import Lax185574.FlipsMonadicallyDependent
import Lax185574Proofs.Lib.BoundedFlipDependence
import Lax185574Proofs.FlipBridge
import Lax185574Proofs.AtomicPartitionCount
import Lax185574Proofs.Interface.DefinableFlipClass

namespace Lax185574Proofs.FlipsMonadicallyDependent

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax185574.DefinableFlips Lax185574Proofs.Interface.Old
open Lax185574Proofs.Lib.Internal.BoundedFlipDependence

/-- Every `s`-definable flip is a flip for a partition into at most
`3^s` parts, given by a labeling with a symmetric toggle. -/
theorem definableFlipClass_subset (C : GraphClass) (s n : ℕ) (H : SimpleGraph (Fin n))
    (hH : definableFlipClass C s n H) : BoundedFlipImage C (3 ^ s) n H := by
  obtain ⟨G, hG, S, hS, hflip⟩ := hH
  let P := Lax185574.Partitions.atomicTypes G (S : Set (Fin n))
  have hP : Nat.card (Quotient P) ≤ 3 ^ s :=
    (Lax185574Proofs.AtomicPartitionCount.card_quotient_atomicTypes_le G S).trans
      (Nat.pow_le_pow_right (by omega) hS)
  have hflip : Lax185574.Flips.IsFlip G (Setoid.ker (Lax185574Proofs.FlipBridge.labeling P)) H := by
    rw [Lax185574Proofs.FlipBridge.ker_labeling P]; exact hflip
  obtain ⟨toggle, hsymm, rfl⟩ :=
    Lax185574Proofs.FlipBridge.exists_eq_flip_of_isFlip G _ H hflip
  exact ⟨G, hG, _, hP, _, toggle, hsymm, rfl⟩

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem monadicallyDependent_definableFlipClass_old (C : GraphClass)
    (hC : MonadicallyDependent C) (s : ℕ) :
    MonadicallyDependent (definableFlipClass C s) := by
  intro hT
  apply Lax185574Proofs.Lib.BoundedFlipDependence.monadicallyDependent_boundedFlipImage C hC (3 ^ s)
  refine Lax185574Proofs.Lib.TransductionCalculus.Transduces.mono_source hT ?_
  rintro n M ⟨H, hH, rfl⟩
  exact ⟨H, definableFlipClass_subset C s n H hH, rfl⟩

end Lax185574Proofs.FlipsMonadicallyDependent

namespace Lax185574Proofs.FlipsMonadicallyDependent

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.FlipsMonadicallyDependent
open Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.FlipsMonadicallyDependent.monadicallyDependent_definableFlipClass
---
A flip for a partition into at most `p` parts is obtained from the
original graph by a fixed transduction: color the parts with `p` unary
predicates and flip the adjacency between the chosen pairs of colors.
This bounded-flip image of a class is transduced by it, and monadic
dependence is preserved under
transductions. Every `s`-definable flip is a flip for the partition into
atomic types over at most `s` vertices, which has at most `3^s` parts.

The argument is carried out for the graph classes of the archive and
their monadic dependence, and transferred to the graph classes used
here.
-/
theorem monadicallyDependent_definableFlipClass (C : GraphClass)
    (hC : MonadicallyDependent C) (s : ℕ) :
    MonadicallyDependent (definableFlipClass C s) :=
  monadicallyDependent_mono (definableFlipClass_subset_ofOld C s)
    ((monadicallyDependent_ofOld_iff _).mpr
      (monadicallyDependent_definableFlipClass_old (toOld C) (monadicallyDependent_toOld hC) s))

end Lax185574Proofs.FlipsMonadicallyDependent
