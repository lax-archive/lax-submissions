import Lax17Proofs.Source.Exponent7.RectangularTheorem415

namespace Lax17Proofs

/-!
# Rectangular Section 4.5 input and assembly

`Section45.Section45Input` uses one parameter `w` for the selected chain
length and connector width. The rectangular form makes these parameters
independent:

* `L` is the number of selected clusters;
* `W` is the consecutive-overlap threshold and the width of every nail and
  connector family.

The graph assembly remains `Section45.WeakPathOfSetsAssemblyData G L W`.
-/

namespace SimpleGraph
namespace Exponent7

universe u

open Finset

variable {V : Type u} [DecidableEq V]

/-- Input for rectangular Chuzhoy--Tan Section 4.5.

Unlike `Section45.Section45Input`, the selected length `L` and width `W` are
independent. The assembly field supplies the cluster, nail, connector,
disjointness, and weak-well-linkedness data. -/
structure RectangularSection45Input
    (G : _root_.SimpleGraph V) (N M D L W : ℕ) where
  sliceRows : Fin M → Finset (Fin N)
  length_pos : 0 < L
  width_pos : 0 < W
  N_large : 3 * W ≤ N
  D_square : 4 * N * W ≤ D ^ 2
  large : 2 * N * L ≤ D * M
  row_card : ∀ i : Fin M, D ≤ (sliceRows i).card
  assembly :
    ∀ (l : List (Fin M)) (hlen : l.length = L),
      l.IsChain (Section45.LargeOverlapRel sliceRows W) →
        Section45.WeakPathOfSetsAssemblyData G L W

/-- Rectangular Section 4.5 combines rectangular finite selection with the
graph assembly theorem. -/
theorem rectangular_section45_weak_pathOfSetsSystem
    {G : _root_.SimpleGraph V} {N M D L W : ℕ}
    (Input : RectangularSection45Input G N M D L W) :
    Nonempty (WeakPathOfSetsSystem G L W) := by
  rcases theorem415_rectangular Input.sliceRows Input.width_pos
      Input.N_large Input.D_square Input.large Input.row_card with
    ⟨l, hlen, hchain⟩
  exact Section45.weak_pathOfSetsSystem_of_section45_assembly
    (Input.assembly l hlen hchain)

/-- Rectangular Section 4.5 statement used by the exponent-seven construction. -/
def RectangularSection45Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {N M D L W : ℕ},
      RectangularSection45Input G N M D L W →
        Nonempty (WeakPathOfSetsSystem G L W)

theorem rectangularSection45Statement :
    RectangularSection45Statement.{u} := by
  intro V _ G N M D L W Input
  exact rectangular_section45_weak_pathOfSetsSystem Input

end Exponent7
end SimpleGraph

end Lax17Proofs
