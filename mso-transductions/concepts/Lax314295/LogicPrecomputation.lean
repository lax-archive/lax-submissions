import Lax765601.ElementaryProperties
import Lax132576.RationalFunctions
import Lax314295.MSOLogic

/-!
---
title: Precomputing the answers of MSO formulas by a rational function
type: theorem
---
For a finite set of mso formulas with one or two free first-order variables
there is a letter-to-letter rational function $f : A^* \to C^*$ such that each
formula $\varphi(x)$ with one free variable corresponds to a set of letters
$F \subseteq C$ — $w \models \varphi(x)$ exactly when the letter of $f(w)$ at
position $x$ is in $F$ — and each formula $\varphi(x, y)$ with two free
variables corresponds to a regular language $L \subseteq C^*$ — for
$x \le y$, $w \models \varphi(x, y)$ exactly when the infix of $f(w)$ from
$x$ to $y$ belongs to $L$ (Lemma C.4.10 of *Transducers*). The function
decorates every position with the states, on the prefix and on the suffix, of
the automata of Lemma C.4.2 for the formulas.

# Formalization notes

The formulas with one free variable use the variable `0`; those with two use
`0` and `1`, evaluated at `x ≤ y`. The infix from `x` to `y` is
`((f w).drop x).take (y - x + 1)`. The alphabet is assumed finite.
-/

namespace Lax314295.LogicPrecomputation

open Lax765601.ElementaryProperties Lax132576.RationalFunctions Lax314295.MSOLogic

/-- The answers of finitely many mso formulas with one or two free variables are
read off a letter-to-letter rational function: as letters, respectively as regular
languages of infixes. -/
axiom exists_rational_precomputation {A : Type} [Finite A]
    (Φ₁ Φ₂ : Set (MSO A)) (hΦ₁ : Φ₁.Finite) (hΦ₂ : Φ₂.Finite) :
    ∃ (C : Type) (_ : Finite C) (f : List A → List C),
      IsRationalFun f ∧ LengthPreserving f ∧
      (∀ φ ∈ Φ₁, ∃ F : Set C, ∀ (w : List A) (x : ℕ), x < w.length →
        (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ ∃ c ∈ F, (f w)[x]? = some c)) ∧
      (∀ φ ∈ Φ₂, ∃ L : Language C, L.IsRegular ∧ ∀ (w : List A) (x y : ℕ),
        x ≤ y → y < w.length →
        (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) φ ↔
          ((f w).drop x).take (y - x + 1) ∈ L))

end Lax314295.LogicPrecomputation
