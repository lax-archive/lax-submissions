import Lax10Proofs.Consequences
import Lax10.Theorem2
import Lax10.FragileFourColorable

namespace Lax10Proofs.Main

universe u

private theorem source_threeConnected_iff_concept {V : Type u} [Finite V]
    (G : SimpleGraph V) :
    Lax10Proofs.ThreeConnected G ↔
      Lax10.ThreeConnectedAndColorable.ThreeConnected G := by
  rfl

private theorem concept_no_three_connected_to_source {V : Type u} [Finite V]
    {G : SimpleGraph V}
    (hfragile : Lax10.Fragile.HasNoThreeConnectedSubgraph G) :
    Lax10Proofs.HasNoThreeConnectedSubgraph G := by
  intro H hH
  exact hfragile H ((source_threeConnected_iff_concept H.coe).mp hH)

/--
---
conclusion: Lax10.Theorem2.theorem2
---
The chromatic-number form of Theorem 2.
-/
theorem theorem2 {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hchi : ((m + 1 : Nat) : ℕ∞) ≤ G.chromaticNumber) :
    ∃ H : G.Subgraph,
      Lax10.ThreeConnectedAndColorable.ThreeConnected H.coe ∧
        (m : ℕ∞) ≤ H.coe.chromaticNumber := by
  obtain ⟨H, hHconn, hHchi⟩ := Lax10Proofs.theorem2 m G hm hchi
  exact ⟨H, (source_threeConnected_iff_concept H.coe).mp hHconn, hHchi⟩

/--
---
conclusion: Lax10.FragileFourColorable.fragile_four_colorable
---
The main 4-colorability corollary.
-/
theorem fragile_four_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hfragile : Lax10.Fragile.HasNoThreeConnectedSubgraph G) :
    Lax10.ThreeConnectedAndColorable.KColorable 4 G :=
  Lax10Proofs.kColorable_iff_mathlib_colorable.mp
    (Lax10Proofs.fragile_four_colorable G
      (concept_no_three_connected_to_source hfragile))

end Lax10Proofs.Main
