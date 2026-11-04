import Lax185574.PartialGraphs
import Lax185574.Encodings
import Lax3.DistFO

/-!
---
title: Distance logic over partial graphs and distance rank
type: definition
---
The logic distFO extends first-order logic over partial graphs by
*distance atoms*. Its atoms are

- the first-order atoms x = y, E(x, y), N(x, y) and Y(x), for colors Y;
- for each radius r ∈ ℕ, the *binary distance atom* dist(x, y) ≤ r;
- for each radius r ∈ ℕ and color Y, the *unary distance atom*
  dist(x, Y) < r, equivalent to ∃y (Y(y) ∧ dist(x, y) < r).

Distances are measured in the Gaifman graph of the partial graph, that
is, along resolved pairs. A formula is built from atoms by negation,
conjunction and the *local quantifier* ∃y (dist(xᵢ, y) ≤ s ∧ φ(x̄ y)).

The horizon functions are ρ⁻(k, q) = 9^((k+q+1)q) and
ρ⁺(k, q) = 9^((k+q)(q+1)). A formula has *distance rank (k, q)* if it is
a Boolean combination of

- first-order atoms,
- binary distance atoms of radius at most ρ⁻(k, q),
- unary distance atoms of radius at most ρ⁺(k, q), and
- formulas ∃y (dist(xᵢ, y) ≤ ρ⁺(k+1, q−1) ∧ φ(x̄ y)), where q ≥ 1, xᵢ is a
  free variable and φ has distance rank (k+1, q−1).

# Formalization notes

As in `Lax3.FirstOrder`, free variables are counted: `DistFO ℓ` has ℓ
free variables `Fin ℓ`, and the local quantifier binds the new last
variable. The radius of a local quantifier is part of the syntax, and
the distance rank requires it to be exactly ρ⁺(k+1, q−1), as in the
paper. The horizon functions are those of `Lax3.DistFO`, which are the
functions of the paper.

"dist(x, y) ≤ r" holds if a walk of length at most r joins the two
vertices along resolved pairs. "dist(x, Y) < r" holds if some vertex of
color Y is joined to x by a walk of length less than r. In particular
it is false for r = 0.

The works that the paper cites for this logic also allow the
unrestricted quantifier ∃y φ(x̄ y), and call the formulas of distance
rank (k, q) *local*. The paper considers only these formulas, and omits
the adjective. So the syntax here has the local quantifier only, and the
formulas of distance rank (k, q) are the same as in the paper.

Formulas are handed to algorithms in the derived encoding of
`Lax185574.Encoding`, a prefix code: the number of the constructor,
from 0 for `eq` to 8 for `exLocal`, followed by the arguments in order.
-/

namespace Lax185574.DistanceLogic

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.Encoding
open Lax3.DistFO (rhoMinus rhoPlus)

/-- Formulas of distance logic over partial graphs with `ℓ` free
variables. -/
inductive DistFO : ℕ → Type
  /-- `xᵢ = xⱼ`. -/
  | eq {ℓ : ℕ} (i j : Fin ℓ) : DistFO ℓ
  /-- `E(xᵢ, xⱼ)`. -/
  | edge {ℓ : ℕ} (i j : Fin ℓ) : DistFO ℓ
  /-- `N(xᵢ, xⱼ)`. -/
  | nonEdge {ℓ : ℕ} (i j : Fin ℓ) : DistFO ℓ
  /-- `Y(xᵢ)`. -/
  | color {ℓ : ℕ} (Y : ℕ) (i : Fin ℓ) : DistFO ℓ
  /-- `dist(xᵢ, xⱼ) ≤ r`. -/
  | distLe {ℓ : ℕ} (r : ℕ) (i j : Fin ℓ) : DistFO ℓ
  /-- `dist(xᵢ, Y) < r`. -/
  | distColorLt {ℓ : ℕ} (r Y : ℕ) (i : Fin ℓ) : DistFO ℓ
  /-- Negation. -/
  | not {ℓ : ℕ} (φ : DistFO ℓ) : DistFO ℓ
  /-- Conjunction. -/
  | and {ℓ : ℕ} (φ ψ : DistFO ℓ) : DistFO ℓ
  /-- `∃y (dist(xᵢ, y) ≤ s ∧ φ(x̄ y))`, binding the new last variable. -/
  | exLocal {ℓ : ℕ} (i : Fin ℓ) (s : ℕ) (φ : DistFO (ℓ + 1)) : DistFO ℓ
  deriving Encode

namespace DistFO

/-- The formula is an atom. -/
def IsAtom {ℓ : ℕ} : DistFO ℓ → Prop
  | .not _ | .and _ _ | .exLocal _ _ _ => False
  | _ => True

/-- Some walk of length less than `r` joins `u` and `v`. -/
def WithinDistLt {W : Type*} (G : SimpleGraph W) (r : ℕ) (u v : W) : Prop :=
  ∃ p : G.Walk u v, p.length < r

variable {V : Type*}

/-- Satisfaction in the partial graph `G` under the assignment `m` of
vertices to the free variables. -/
def Sat (G : PartialGraph V) : {ℓ : ℕ} → (Fin ℓ → V) → DistFO ℓ → Prop
  | _, m, .eq i j => m i = m j
  | _, m, .edge i j => G.edge.Adj (m i) (m j)
  | _, m, .nonEdge i j => G.nonEdge.Adj (m i) (m j)
  | _, m, .color Y i => G.color (m i) = Y
  | _, m, .distLe r i j => WithinDist G.resolved r (m i) (m j)
  | _, m, .distColorLt r Y i => ∃ v, G.color v = Y ∧ WithinDistLt G.resolved r (m i) v
  | _, m, .not φ => ¬ Sat G m φ
  | _, m, .and φ ψ => Sat G m φ ∧ Sat G m ψ
  | _, m, .exLocal i s φ =>
      ∃ v, WithinDist G.resolved s (m i) v ∧ Sat G (Fin.snoc m v) φ

/-- `DRank k q φ`: the formula `φ` has distance rank `(k, q)`. -/
inductive DRank : ℕ → ℕ → {ℓ : ℕ} → DistFO ℓ → Prop
  | eq {k q ℓ : ℕ} (i j : Fin ℓ) : DRank k q (.eq i j)
  | edge {k q ℓ : ℕ} (i j : Fin ℓ) : DRank k q (.edge i j)
  | nonEdge {k q ℓ : ℕ} (i j : Fin ℓ) : DRank k q (.nonEdge i j)
  | color {k q ℓ : ℕ} (Y : ℕ) (i : Fin ℓ) : DRank k q (.color Y i)
  | distLe {k q ℓ : ℕ} (r : ℕ) (i j : Fin ℓ) :
      r ≤ rhoMinus k q → DRank k q (.distLe r i j)
  | distColorLt {k q ℓ : ℕ} (r Y : ℕ) (i : Fin ℓ) :
      r ≤ rhoPlus k q → DRank k q (.distColorLt r Y i)
  | not {k q ℓ : ℕ} {φ : DistFO ℓ} : DRank k q φ → DRank k q (.not φ)
  | and {k q ℓ : ℕ} {φ ψ : DistFO ℓ} :
      DRank k q φ → DRank k q ψ → DRank k q (.and φ ψ)
  | exLocal {k q ℓ : ℕ} (i : Fin ℓ) {φ : DistFO (ℓ + 1)} :
      DRank (k + 1) q φ → DRank k (q + 1) (.exLocal i (rhoPlus (k + 1) q) φ)

end DistFO

end Lax185574.DistanceLogic
