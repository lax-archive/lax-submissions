import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Left distance and bounded variation
type: definition
---
The *left distance* $\|w_1, w_2\|$ of two strings (Definition B.4.7 of
*Transducers*) is the smallest $k$ such that the strings decompose as
$$w_1 = v\,v_1, \qquad w_2 = v\,v_2 \qquad \text{with } |v_1|, |v_2| \le k,$$
i.e. the larger of the two lengths that remain after the longest common prefix
has been removed. It measures how far apart two outputs of a transducer can be
allowed to be after reading the same input. A partial function $f$ has
*bounded variation* if for all $w_1, w_2$ the left distances
$\|f(w w_1), f(w w_2)\|$ are bounded, $w$ ranging over the strings for which
both values are defined (Theorem B.4.8); for a total function, the relation
$$w_1 \sim w_2 \quad\Longleftrightarrow\quad \sup_w \|f(w w_1), f(w w_2)\| < \infty$$
is an equivalence relation on input strings, and its index is what
characterises the rational functions (Theorem B.4.13).

# Formalization notes

`leftDist` is the infimum of the set of admissible `k`, which is nonempty
(`max |w₁| |w₂|` always works), so the infimum is attained and the convention
`sInf ∅ = 0` is never exercised. `BoundedVarRel f` is the relation `∼`, and
`BoundedVariation` the property of a partial function.
-/

namespace Lax132576.LeftDistance

/-- The left distance `‖w₁, w₂‖`: the least `k` such that `w₁ = v v₁` and
`w₂ = v v₂` with `|v₁|, |v₂| ≤ k`. -/
noncomputable def leftDist {B : Type} (w₁ w₂ : List B) : ℕ :=
  sInf {k : ℕ | ∃ v v₁ v₂ : List B,
    w₁ = v ++ v₁ ∧ w₂ = v ++ v₂ ∧ v₁.length ≤ k ∧ v₂.length ≤ k}

/-- The relation `w₁ ∼ w₂` of Theorem B.4.13: the left distances
`‖f (w w₁), f (w w₂)‖` are bounded uniformly in `w`. -/
def BoundedVarRel {A B : Type} (f : List A → List B) (w₁ w₂ : List A) : Prop :=
  ∃ K : ℕ, ∀ w : List A, leftDist (f (w ++ w₁)) (f (w ++ w₂)) ≤ K

/-- A partial function has bounded variation if for all `w₁, w₂` the left distances
`‖f (w w₁), f (w w₂)‖` are bounded, over the `w` for which both are defined. -/
def BoundedVariation {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
    f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K

end Lax132576.LeftDistance
