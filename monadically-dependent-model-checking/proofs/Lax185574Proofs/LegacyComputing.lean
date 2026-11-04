import Lax185574.Encodings
import Lax808846.RamComputes

/-!
The older notion of computing an encoded output, in which the proofs of
the algorithmic statements were first written.

A word RAM program `p` computes the object `b` from the object `a` in
time `T`, for a word-length exponent `e` and a constant `c`, if the
following holds at every word length `w` at which the word `x` of `a`
is admissible, that is, `c · (|x| + v + 1)^e ≤ 2^w` for every entry
`v` of `x`.

1. Every halting run of `p` on `x` outputs the word of `b`.
2. If `T(|x|) ≤ 2^w`, then `p` halts on `x` within `T(|x|)` steps.

The notion of the statements is `Lax185574.Algorithms`. It differs in
the condition on the word length, which uses the sum of the entries,
and in the time bound, which is a real number with a constant factor
and an additive constant. `Lax185574Proofs.Interface.Computes` moves
between the two.

The definitions are available under their older names in
`Lax185574.Computing`.
-/

namespace Lax185574Proofs.Legacy.Computing

open Lax808846.Ram Lax808846.RamComputes Lax185574.Encoding

universe u v

/-- The word `x` is admissible at word length `w` for the exponent `e`
and the constant `c`: `c · (|x| + v + 1)^e ≤ 2^w` for each entry `v`
of `x`. -/
def WordAdmissible (e c w : ℕ) (x : List ℕ) : Prop :=
  ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w

/-- `Computes p e c a b T`: at every word length at which the word of
`a` is admissible, every halting run of `p` on the word of `a` outputs
the word of `b`, and if `T ‖a‖` fits into a word, then `p` halts within
`T ‖a‖` steps. -/
def Computes {α : Type u} {β : Type v} [Encode α] [Encode β]
    (p : Program) (e c : ℕ) (a : α) (b : β) (T : ℕ → ℕ) : Prop :=
  ∀ w : ℕ, WordAdmissible e c w (encode a) →
    (∀ (y : List ℕ) (t : ℕ), RunsTo w p (encode a) y t → y = encode b) ∧
    (T (wordLength a) ≤ 2 ^ w →
      ComputesInTime w p {encode a} (fun _ => encode b) (fun _ => T (wordLength a)))

end Lax185574Proofs.Legacy.Computing

set_option linter.dupNamespace false
namespace Lax185574.Computing
export Lax185574Proofs.Legacy.Computing (WordAdmissible Computes)
end Lax185574.Computing
