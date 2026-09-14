/-
The index form of the Post correspondence problem, as the book *Transducers* states it.

These are the first definitions of `RequestProject/PartB/PCPRed.lean` of the source
development, copied here on their own so that `Source/PCP/Index.lean` can be ported
verbatim: the rest of that file (the reduction to equivalence of rational relations)
belongs to Part B and is not part of this submission.
-/
import Mathlib

namespace Lax251941Proofs.Transducers.PCP

/-- An instance of the Post correspondence problem: a finite list of pairs of
strings over the alphabet `ℕ`. -/
abbrev Instance := List (List ℕ × List ℕ)

/-- The concatenation of the strings `ws` selected by a list of indices; this is
the homomorphic image of the index string. -/
def conc (ws : List (List ℕ)) (idx : List ℕ) : List ℕ :=
  (idx.map (fun i => ws.getD i [])).flatten

@[simp] lemma conc_nil (ws : List (List ℕ)) : conc ws [] = [] := rfl

@[simp] lemma conc_cons (ws : List (List ℕ)) (i : ℕ) (idx : List ℕ) :
    conc ws (i :: idx) = ws.getD i [] ++ conc ws idx := rfl

/-- **The Post correspondence problem.**  An instance is solvable if some
nonempty sequence of indices makes the two concatenations equal. -/
def Solvable (P : Instance) : Prop :=
  ∃ idx : List ℕ, idx ≠ [] ∧ (∀ i ∈ idx, i < P.length) ∧
    conc (P.map Prod.fst) idx = conc (P.map Prod.snd) idx

end Lax251941Proofs.Transducers.PCP
