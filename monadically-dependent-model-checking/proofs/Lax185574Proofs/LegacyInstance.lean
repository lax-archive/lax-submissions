import Lax185574Proofs.Legacy
import Lax185574.ConstructionModelChecking
import Lax185574Proofs.LegacyInputs

/-!
The input word of the model-checking program in its first form: a graph
in compressed sparse row form, followed by a sentence of
`Lax3.FirstOrder`.

`EncodesInstance` is available under its older name in
`Lax185574.InstanceEncoding`, together with the older encoding function
of first-order formulas.
-/

namespace Lax185574Proofs.Legacy

open Lax271696.GraphEncoding Lax185574.Encoding

/-- The word `x` encodes the graph `G` on `n` vertices together with the
sentence `φ`: it is the compressed sparse row encoding of `G`, followed
by the encoding of `φ`. The compressed sparse row form determines its own
length, through the vertex count and the edge count in front, so the
word splits uniquely into the two parts. -/
def EncodesInstance (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n))
    (φ : Lax3.FirstOrder.FO 0) : Prop :=
  ∃ g : List ℕ, EncodesGraph g n G ∧ x = g ++ encode φ

end Lax185574Proofs.Legacy

set_option linter.dupNamespace false
namespace Lax185574.InstanceEncoding
export Lax185574Proofs.Legacy (EncodesInstance)
end Lax185574.InstanceEncoding
