import Lax185574.MonadicDependence

/-!
---
title: Monadic dependence through the independence property
type: theorem
---
A formula φ(x, y) in the signature of colored graphs has the
*independence property* on a graph class 𝒞 if for every n there are a
coloring G⁺ of a graph G ∈ 𝒞, vertices a₁, …, aₙ, and vertices b_J for
J ⊆ [n] such that G⁺ ⊨ φ(aᵢ, b_J) holds exactly when i ∈ J. A class is
monadically dependent if and only if no formula has the independence
property on it.

By a result of Baldwin and Shelah, one may equivalently allow formulas
φ(x̄, ȳ) with tuples of variables, and tuples āᵢ and b̄_J. On a
monadically dependent class, no such formula has the independence
property either.

# Formalization notes

The paper defines monadic dependence by transductions, like
`Lax185574.MonadicDependence`, and states the characterization by the
independence property as a theorem of Baldwin and Shelah, in its
appendix on forbidden patterns. The first statement of this concept is
this characterization for formulas in two single variables. The second
is the tuple form, in the direction the paper uses.

Formulas and colorings are those of `Lax185574.FirstOrderLogic`. A
formula φ(x̄, ȳ) has the free variables x₀, …, x_{p+p'−1}. The first p
of them form the tuple x̄ and the last p' form ȳ. The assignment
`Fin.append ā b̄` gives x̄ the values ā and ȳ the values b̄, which is the
paper's φ(ā, b̄). A formula φ(x, y) in two single variables is the case
p = p' = 1, written `1 + 1`.
-/

namespace Lax185574.IndependenceProperty

open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.MonadicDependence

/-- The formula `φ(x̄, ȳ)` with `k` colors, whose free variables are a
tuple `x̄` of `p` variables followed by a tuple `ȳ` of `p'` variables,
has the *independence property* on `C`: for every `m` there are a graph
`G ∈ C`, a coloring of `G`, tuples `a i` for `i < m` and tuples `b J`
for `J ⊆ {0, …, m - 1}` such that `φ(a i, b J)` holds exactly when
`i ∈ J`. -/
def HasIP (C : GraphClass) {k p p' : ℕ} (φ : Formula (Fin k) (p + p')) : Prop :=
  ∀ m : ℕ, ∃ G ∈ C, ∃ (col : Fin k → Set (Fin G.n)) (a : Fin m → Fin p → Fin G.n)
    (b : Finset (Fin m) → Fin p' → Fin G.n),
    ∀ (i : Fin m) (J : Finset (Fin m)), φ.Holds G col (Fin.append (a i) (b J)) ↔ i ∈ J

/-- A graph class is monadically dependent if and only if no formula
`φ(x, y)` of colored graphs, in two single variables, has the
independence property on it. -/
axiom monadicallyDependent_iff_forall_not_hasIP (C : GraphClass) :
    MonadicallyDependent C ↔ ∀ (k : ℕ) (φ : Formula (Fin k) (1 + 1)), ¬ HasIP C φ

/-- On a monadically dependent class, no formula `φ(x̄, ȳ)` of colored
graphs, in tuples of variables, has the independence property
(Baldwin–Shelah). -/
axiom not_hasIP_of_monadicallyDependent (C : GraphClass) (hC : MonadicallyDependent C)
    {k p p' : ℕ} (φ : Formula (Fin k) (p + p')) : ¬ HasIP C φ

end Lax185574.IndependenceProperty
