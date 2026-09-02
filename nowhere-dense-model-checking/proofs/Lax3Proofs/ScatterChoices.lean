import Lax3.ScatterSentences
import Lax3Proofs.WalkDistance
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# The greedy scatter choice

`Lax3.ScatterSentences.ScatterChoice` is a parameter of the concept
surface: every statement about scatter sentences holds for every choice,
and the surface names none. The choices themselves are constructions, so
they live here. This file carries the source's greedy process in the
canonical order on `Fin n` — the one the algorithm's routines actually
compute — as `GreedyMem`, `greedySet` and `greedyChoice`; the
maximum-size choice is `Lax3Proofs.ScatterFml.maxChoice`, next to the
theory that uses it.

`greedyChoice` is the greedy process phrased as the recursion it is: a
vertex is selected exactly when it belongs to the set and no *earlier
selected* vertex is within distance `r` of it. Running the process along
a list and reading off its result gives the same set, one step of the
recursion at a time; the recursion is what the proofs use and what the
machine implements. It is `noncomputable` in the Lean sense because it
takes the cardinality of a set. "Computable" in the source's sense — and
the sense the algorithm needs — means computed by the RAM program of the
headline theorem, which runs exactly this `Fin`-order greedy over the
tabulated truth values of `β`; it has nothing to do with code extraction
from this definition.
-/

namespace Lax3Proofs.ScatterChoices

open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax12.UniformQuasiWideness

/-- The greedy process of the source, in the canonical order on
`Fin n`: the vertex `v` is selected exactly when it lies in `X` and no
earlier selected vertex is within distance `r` of it. -/
def GreedyMem {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) (v : Fin n) : Prop :=
  v ∈ X ∧ ∀ u : Fin n, u < v → GreedyMem G r X u → ¬ WithinDist G r u v
termination_by v.val

/-- The set the greedy process selects. -/
def greedySet {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) : Set (Fin n) :=
  {v | GreedyMem G r X v}

/-- The source's "greedy choice": the size of the set produced by the
greedy process on `X` in the canonical order on `Fin n`. That set is
scattered because a selected vertex is far from every earlier selected
one, and inclusion-wise maximal because a vertex of `X` it passed over
is within distance `r` of a selected one. -/
noncomputable def greedyChoice : ScatterChoice where
  size := fun {_n} G r X => (greedySet G r X).ncard
  spec := by
    intro n G r X
    have hmem : ∀ v : Fin n, v ∈ greedySet G r X ↔
        v ∈ X ∧ ∀ u : Fin n, u < v → u ∈ greedySet G r X → ¬ WithinDist G r u v := by
      intro v
      rw [greedySet, Set.mem_setOf_eq, GreedyMem]
      rfl
    have hsub : greedySet G r X ⊆ X := fun v hv => ((hmem v).1 hv).1
    have hind : DistIndependent G r (greedySet G r X) := by
      intro a ha b hb hab p
      rcases lt_or_gt_of_ne hab with h | h
      · by_contra hlen
        exact ((hmem b).1 hb).2 a h ha ⟨p, by omega⟩
      · by_contra hlen
        refine ((hmem a).1 ha).2 b h hb ⟨p.reverse, ?_⟩
        rw [SimpleGraph.Walk.length_reverse]
        omega
    refine ⟨greedySet G r X, hsub, ⟨⟨hsub, hind⟩, ?_⟩, rfl⟩
    rintro T ⟨hTX, hTind⟩ hST v hvT
    by_contra hvS
    rw [hmem] at hvS
    push Not at hvS
    obtain ⟨u, hlt, huS, w, hw⟩ := hvS (hTX hvT)
    exact absurd (hTind (hST huS) hvT (ne_of_lt hlt) w) (by omega)

end Lax3Proofs.ScatterChoices

namespace Lax3Proofs

/-! The three names are re-exported one level up, into `Lax3Proofs`
itself, so that every use site below reads as if they were declared
there — the twelve consumers all sit in a child namespace of
`Lax3Proofs` and reach them by parent-namespace resolution, exactly as
they reached the concept-side definitions through
`open Lax3.ScatterSentences`. -/

export ScatterChoices (GreedyMem greedySet greedyChoice)

end Lax3Proofs
