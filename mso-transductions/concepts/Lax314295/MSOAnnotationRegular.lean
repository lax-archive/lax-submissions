import Lax314295.MSORelabellings

/-!
---
title: The correctly annotated strings of an MSO relabelling form a regular language
type: theorem
---
For an mso relabelling with formulas $\Phi$, the language over $A \times \Phi$
of the strings $(a_1, \varphi_1) \cdots (a_n, \varphi_n)$ such that for every
$i$ the formula $\varphi_i$ is true at position $i$ of $a_1 \cdots a_n$ is
regular (Claim C.4.6 of *Transducers*). For each formula, the strings with one
marked position at which the formula holds form a regular language by Lemma
C.4.2, and the claim's language is the intersection, over the formulas, of the
complements of the projections of the strings that violate it.

# Formalization notes

The input alphabet is assumed finite; the formulas are indexed by `R.Idx`.
-/

namespace Lax314295.MSOAnnotationRegular

open Lax314295.MSOLogic Lax314295.MSORelabellings

/-- The strings annotated at every position with a formula true there form a
regular language. -/
axiom isRegular_annotation {A B : Type} [Finite A] (R : MSORelabelling A B) :
    Language.IsRegular
      {u : List (A × R.Idx) | ∀ (p : ℕ) (hp : p < u.length),
        MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form (u.get ⟨p, hp⟩).2)}

end Lax314295.MSOAnnotationRegular
