import Lax314295.MSOLogic

/-!
---
title: Formulas with free variables define regular languages of annotated strings
type: theorem
---
Let $\varphi$ be an mso formula over $A$ whose free variables are among the
first-order variables $x_1, \ldots, x_k$ and the set variables
$X_1, \ldots, X_\ell$. Then the language over $A \times 2^{k+\ell}$ of the
annotated strings $w \otimes \{x_1\} \otimes \cdots \otimes \{x_k\} \otimes
X_1 \otimes \cdots \otimes X_\ell$ such that
$w \models \varphi(x_1, \ldots, x_k, X_1, \ldots, X_\ell)$ is regular
(Lemma C.4.2 of *Transducers*). The proof is an induction on the formula, with
a nondeterministic automaton guessing the value of a quantified variable.

# Formalization notes

The free variables are among `0, …, k-1` and `0, …, l-1`; the language is that
of the annotations `annotate k l w fo so` of valuations by positions and sets
of positions of `w` under which `w` satisfies `φ`. The alphabet is assumed
finite.
-/

namespace Lax314295.MSOFreeVariables

open Lax314295.MSOLogic

/-- The annotated strings satisfying a formula form a regular language. -/
axiom isRegular_annotated {A : Type} [Finite A] (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ}

end Lax314295.MSOFreeVariables
