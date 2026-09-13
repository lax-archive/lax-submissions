import Lax17Proofs.Source.Theorem214Nonconstructive

namespace Lax17Proofs

universe u v w

/-!
# Contract for Chekuri--Chuzhoy Theorem 2.14

This file states the boosting theorem used by Chuzhoy--Tan Section 4.6 as
Theorem 4.20.  The source is Chekuri--Chuzhoy, Theorem 2.14 in
`chekuri-chuzhoy-2.pdf`.

The nonconstructive graph-theoretic proof is in
`«statements-and-proofs».Theorem214Nonconstructive`.  Its sharp constant uses the
self-contained auxiliary max-flow/min-cut routing theorem in
`«statements-and-proofs».FlowWellLinked`, followed by the minimum balanced-separation
argument from Chekuri--Chuzhoy Appendix A.1.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


/-- Chekuri--Chuzhoy Theorem 2.14, in the scaled natural-number form needed by
Chuzhoy--Tan Theorem 4.20.

If `T` has `κ` terminals, is `alphaNum / alphaDen` cut-well-linked in the
connected cluster `C`, and the ambient graph has maximum degree at most
`Δ ≥ 3`, then `T` contains a node-well-linked subset of size at least
`⌊(3 * alphaNum * κ) / (10 * Δ * alphaDen)⌋`.

The paper suppresses this integer rounding in the displayed expression
`3ακ/(10Δ)`. -/
theorem theorem214_nodeWellLinkedSubset_contract
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {C T : Finset V} {alphaNum alphaDen Δ κ : ℕ}
    (hcluster : IsCluster G C)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hcard : T.card = κ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen) :
    ∃ T' : Finset V,
      T' ⊆ T ∧
        (3 * alphaNum * κ) / (10 * Δ * alphaDen) ≤ T'.card ∧
          NodeWellLinkedIn G C T'
    :=
  theorem214_nodeWellLinkedSubset_floor
    (G := G) (C := C) (T := T) (alphaNum := alphaNum)
    (alphaDen := alphaDen) (Δ := Δ) (κ := κ)
    hcluster hdegree hDelta halpha_pos halpha_le hcard hwell

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
