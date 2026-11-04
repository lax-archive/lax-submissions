import Lax185574.TypeTrees

/-!
---
title: Locality of type trees
type: lemma
---
Every node at depth j of tree_{k,q}(a) is tree_{k+j,q−j}(v̄) for some
tuple v̄ from Ball_{ρ⁺(k,q)}(a), and every color mentioned in the root
label of that node intersects this ball.

# Formalization notes

By the definition of extensions, the nodes at depth j of tree_{k,q}(a)
are the trees tree_{k+j,q−j}(v̄) of the tuples v̄ = (v₀, …, v_j) with
v₀ = a in which every vᵢ with i ≥ 1 is within distance ρ⁺(k+i, q−i) of
an earlier entry. The statement is made for these tuples. The root label
of the node is atp_{k+j,q−j}(v̄), which consists of the atoms that hold.
An atom mentions the color Y if it is Y(xᵢ) or dist(xᵢ, Y) < r.

The paper assumes k ≥ 1, so that the single vertex a has a tree of
rank (k, q). The statement about guarded tuples does not need this
hypothesis, and it holds for all k.
-/

namespace Lax185574.TreeLocality

open Lax185574.PartialGraphs Lax185574.GaifmanGraph
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The atom mentions the color `Y`. -/
def MentionsColor (Y : ℕ) {ℓ : ℕ} : DistFO ℓ → Prop
  | .color Y' _ => Y' = Y
  | .distColorLt _ Y' _ => Y' = Y
  | _ => False

/-- **Locality of type trees.** A tuple reached from `v 0` by guarded
extensions lies in the ball of radius `ρ⁺(k, q)` around `v 0`, and so
does a vertex of every color mentioned in its atomic type. -/
axiom ball_of_guarded {V : Type*} (G : PartialGraph V) (k q j : ℕ) (hj : j ≤ q)
    (v : Fin (j + 1) → V)
    (hv : ∀ i : Fin (j + 1), 0 < i.val → ∃ i' : Fin (j + 1), i'.val < i.val ∧
      WithinDist G.resolved (rhoPlus (k + i.val) (q - i.val)) (v i') (v i)) :
    (∀ i, v i ∈ G.ball (rhoPlus k q) (v 0)) ∧
    ∀ φ ∈ atp G (k + j) (q - j) v, ∀ Y : ℕ, MentionsColor Y φ →
      ∃ u ∈ G.ball (rhoPlus k q) (v 0), G.color u = Y

end Lax185574.TreeLocality
