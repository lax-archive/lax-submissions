import Lax17Proofs.Source.ChekuriChuzhoyTheorem221
import Lax17Proofs.Source.ReedNodeWellLinkedOracle

namespace Lax17Proofs

universe u v w

/-!
# Routable sets from a node-well-linked producer

This module isolates the axiom-free reduction from a quantitative producer of
node-well-linked terminals to the routable-set input used in the proof of
Chekuri--Chuzhoy Theorem 2.21.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical

/-- A positive-factor producer of node-well-linked terminals gives the
routable-set theorem with constants `(c, 1, 1, 1)`. -/
theorem routableSetFromTreewidth_of_large_nodeWellLinked
    (c : ℕ) (hc : 0 < c)
    (hproducer :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V),
          ∃ T : Finset V,
            NodeWellLinkedIn G Finset.univ T ∧
              treewidth G ≤ c * T.card) :
    RoutableSetFromTreewidth.{u} c 1 1 1 := by
  refine ⟨hc, by decide, by decide, by decide, ?_⟩
  intro V _ _ G k κ hk _hκ htw hlarge
  let L := Nat.log 2 k
  have hLpos : 0 < L := by
    simpa [L] using
      Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
  rcases hproducer G with ⟨T, hTnode, htwT⟩
  have hcκL_lt : c * κ * L < c * T.card := by
    calc
      c * κ * L < k := by simpa [L] using hlarge
      _ ≤ treewidth G := htw
      _ ≤ c * T.card := htwT
  have hcκ_le : c * κ ≤ c * κ * L := by
    calc
      c * κ = (c * κ) * 1 := by simp
      _ ≤ (c * κ) * L := Nat.mul_le_mul_left (c * κ) hLone
      _ = c * κ * L := rfl
  have hκT : κ ≤ T.card := by
    have hcκ_lt : c * κ < c * T.card := hcκ_le.trans_lt hcκL_lt
    exact Nat.le_of_lt ((Nat.mul_lt_mul_left hc).mp hcκ_lt)
  rcases Finset.exists_subset_card_eq hκT with ⟨X, hXT, hXcard⟩
  refine ⟨X, hXcard, ?_⟩
  have hXnode : NodeWellLinkedIn G Finset.univ X :=
    NodeWellLinkedIn.mono_terminals hTnode hXT
  simpa [L] using NodeWellLinkedIn.toRoutableSetIn hXnode hLpos

/-- Existential-constant form of
`routableSetFromTreewidth_of_large_nodeWellLinked`, witnessing exactly
`(c, 1, 1, 1)`. -/
theorem exists_routableSetFromTreewidth_of_large_nodeWellLinked
    (c : ℕ) (hc : 0 < c)
    (hproducer :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V),
          ∃ T : Finset V,
            NodeWellLinkedIn G Finset.univ T ∧
              treewidth G ≤ c * T.card) :
    ∃ cSet cSetLog cRoute cRouteLog : ℕ,
      RoutableSetFromTreewidth.{u} cSet cSetLog cRoute cRouteLog := by
  exact ⟨c, 1, 1, 1,
    routableSetFromTreewidth_of_large_nodeWellLinked c hc hproducer⟩

/-- The completed WP1A endpoint.  Reed's recursive balanced-separator
decomposition supplies the factor-nine node-well-linked set, and the routing
reduction contributes one logarithmic factor of congestion. -/
theorem routableSetFromTreewidth_proved :
    RoutableSetFromTreewidth.{u} 9 1 1 1 := by
  exact routableSetFromTreewidth_of_large_nodeWellLinked 9 (by decide)
    (fun G => exists_nodeWellLinked_treewidth_le_nine_mul_card G)

/-- Existential-constant form used by the A.2 source-input composition. -/
theorem exists_routableSetFromTreewidth_proved :
    ∃ cSet cSetLog cRoute cRouteLog : ℕ,
      RoutableSetFromTreewidth.{u} cSet cSetLog cRoute cRouteLog :=
  ⟨9, 1, 1, 1, routableSetFromTreewidth_proved⟩

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
