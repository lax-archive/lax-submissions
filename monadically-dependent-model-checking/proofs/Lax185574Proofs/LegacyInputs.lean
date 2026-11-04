import Lax185574Proofs.Legacy
import Lax185574.ConstructionSequences
import Lax271696.GraphEncoding
import Lax185574.Encodings

/-!
The input words of the programs of thm:skel-def-seq, thm:skel-few-types
and thm:mc in their first form, with the graph in compressed sparse row
form.

Each predicate is available under its older name, `EncodesInput` in
`Lax185574.DefinableSequences`, `Lax185574.FewTypes` and
`Lax185574.ConstructionModelChecking`.
-/

namespace Lax185574Proofs.Legacy

open Lax271696.GraphEncoding Lax185574.Encoding
open Lax185574.PartialGraphs Lax185574.ConstructionSequences

namespace DefSeq

/-- The word `x` encodes the radius `r`, the rational `ε` and the graph
`G` on `n` vertices: the word of the pair `(r, ε)`, and then the
compressed sparse row word of the graph. -/
def EncodesInput (x : List ℕ) (r : ℕ) (ε : ℚ) (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ g : List ℕ, EncodesGraph g n G ∧ x = encode (r, ε) ++ g

end DefSeq

namespace FewTypes

/-- The word `x` encodes `r`, `q`, the rational `ε` and the graph `G` on
`n` vertices: the word of the triple `(r, q, ε)`, and then the
compressed sparse row word of the graph. -/
def EncodesInput (x : List ℕ) (r q : ℕ) (ε : ℚ) (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ g : List ℕ, EncodesGraph g n G ∧ x = encode (r, q, ε) ++ g

end FewTypes

namespace CMC

/-- The word `x` encodes a graph `G` on `n` vertices in compressed
sparse row form, a sequence `s` of partial graphs on its vertices and a
sentence `φ`, in this order. -/
def EncodesInput (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n))
    (s : List (PartialGraph (Fin n))) (φ : Lax3.FirstOrder.FO 0) : Prop :=
  ∃ g y : List ℕ, EncodesGraph g n G ∧ EncodesSequence y s ∧ x = g ++ y ++ encode φ

end CMC

end Lax185574Proofs.Legacy

set_option linter.dupNamespace false
namespace Lax185574.DefinableSequences
export Lax185574Proofs.Legacy.DefSeq (EncodesInput)
end Lax185574.DefinableSequences

namespace Lax185574.FewTypes
export Lax185574Proofs.Legacy.FewTypes (EncodesInput)
end Lax185574.FewTypes

namespace Lax185574.ConstructionModelChecking
export Lax185574Proofs.Legacy.CMC (EncodesInput)
end Lax185574.ConstructionModelChecking
