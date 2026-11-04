import Lax185574.Algorithms
import Lax185574.ConstructionSequences
import Lax185574.Width

/-!
---
title: Model checking along a construction sequence
type: theorem
---
There is an algorithm which, given a sentence φ and an n-vertex graph G
together with a construction sequence of G of length λ, determines
whether G ⊨ φ in time

λ · n² · poly_φ(K),

where K is the radius-r depth-d width of the construction sequence, for
some r and d that depend only on φ.

# Formalization notes

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`,
one for all sentences. For each sentence there are the radius `r`, the
depth `d`, the degree `b` and the constant `c` of the time bound. The
input is the triple of G, a script of the construction sequence and φ,
with the encodings of `Lax185574.Encodings`. The construction sequence
is the run of the script, see `Lax185574.ConstructionSequences`, so λ is
the length of the run. K is the width of `Lax185574.Width`.

The time bound λ · n² · poly_φ(K) is spelled out as
`λ · (n+1)² · (K+1)^b`. The graph without vertices has construction
sequences of every length, and the factor (n+1)² keeps the bound large
enough to read them. The paper says that r and d are computable from
φ. Here they only exist. The algorithm is correct on every construction
sequence, whatever its width. So an algorithm that needs r and d can try
all pairs in parallel, and the right pair costs only a constant factor
that depends on φ.
-/

namespace Lax185574.ConstructionModelChecking

open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.Algorithms
open Lax185574.ConstructionSequences Lax185574.Width

/-- **Model checking along a construction sequence.** One algorithm
decides `G ⊨ φ`, given `G`, a construction sequence of `G` by its
script `σ`, and `φ`, in time `O(λ · (n+1)² · (K+1)^b)`, where `λ` is
the length of the sequence and `K` its radius-`r` depth-`d` width. The
numbers `r`, `d`, `b` and the constant `c` depend on `φ`. -/
axiom exists_program_modelChecking_sequence :
    ∃ A : Algorithm, ∀ φ : Sentence, ∃ r d c b : ℕ,
      ∀ (G : Graph) (σ : Script G.n), IsConstructionSequence G.toSimpleGraph σ.run →
        A.Decides c (G, σ, φ) (G ⊨ φ)
          (σ.run.length * (G.n + 1) ^ 2 * (width r d σ.run + 1) ^ b)

end Lax185574.ConstructionModelChecking
