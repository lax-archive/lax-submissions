import Lax185574.Partitions

/-!
---
title: Splitting the parts of a partition by atomic types over a set
type: definition
---
Fix a graph G and a partition 𝒫 of V(G). For a set T ⊆ V(G), 𝒫 ∧ T is
the refinement of 𝒫 where each part P ∈ 𝒫 is split into atomic types
over T ∖ P, that is, into sets of the form P ∩ Q, where Q is the set of
all vertices of G with a given neighborhood in T ∖ P.

# Formalization notes

The partition 𝒫 ∧ T is the kernel of the map sending v to its part
𝒫(v) together with N(v) ∩ (T ∖ 𝒫(v)). Two vertices have the same image
exactly when they lie in the same part P and have the same neighborhood
in T ∖ P, which is the description of the paper. A vertex of P does not
lie in T ∖ P, so its atomic type over T ∖ P is given by this
neighborhood alone. If 𝒫 has a single part, then T ∖ P is empty and
𝒫 ∧ T = 𝒫.
-/

namespace Lax185574.TypeSplitting

universe z

variable {V : Type z}

/-- `𝒫 ∧ T`: each part `P` of `P` is split according to the
neighborhoods of its vertices in `T ∖ P`. -/
def split (G : SimpleGraph V) (P : Setoid V) (T : Set V) : Setoid V :=
  Setoid.ker fun v => (Quotient.mk P v, {t | t ∈ T ∧ ¬ P t v} ∩ G.neighborSet v)

end Lax185574.TypeSplitting
