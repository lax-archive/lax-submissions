import Lax185574.LocalDefinability
import Lax185574.Chains
import Lax185574Proofs.LocalToGlobal
import Lax185574Proofs.WithinDistBasics

/-!
Monotonicity facts used by the skeleton compositions: the width of a
chain grows with the radius, and radius-`r` definability survives more
predicates and more parameters.
-/

namespace Lax185574Proofs.Compose

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Partitions Lax185574.Flips Lax185574.Chains Lax185574.LocalDefinability
open Lax185574.Colorings Lax185574.GaifmanGraph

universe z

variable {V : Type z}

theorem partCount_mono (P : Setoid V) {X Y : Set V} (hXY : X ⊆ Y) (hY : Y.Finite) :
    partCount P X ≤ partCount P Y :=
  Set.ncard_le_ncard (Set.image_mono hXY) (hY.image _)

theorem flipBall_mono (G : SimpleGraph V) (P : Setoid V) {r r' : ℕ} (h : r ≤ r') (v : V) :
    flipBall G P r v ⊆ flipBall G P r' v := fun _ hu H hH =>
  Lax185574Proofs.WithinDistBasics.withinDist_mono h (hu H hH)

/-- The width of a chain grows with the radius. -/
theorem chainWidth_mono [Finite V] (G : SimpleGraph V) (S : List (Finset V)) {r r' : ℕ}
    (h : r ≤ r') : chainWidth G r S ≤ chainWidth G r' S := by
  have hbdd : BddAbove {K | ∃ (t : ℕ) (ht : t + 1 < S.length) (v : V),
      K = partCount (atomicTypes G (S[t + 1] : Set V))
        (flipBall G (atomicTypes G (S[t] : Set V)) r' v)} := by
    refine ⟨Nat.card V, ?_⟩
    rintro K ⟨t, ht, v, rfl⟩
    unfold partCount
    exact (Set.ncard_image_le (Set.toFinite _)).trans (Set.ncard_le_card _)
  unfold chainWidth
  apply csSup_le'
  rintro K ⟨t, ht, v, rfl⟩
  exact le_trans (partCount_mono _ (flipBall_mono G _ h v) (Set.toFinite _))
    (le_csSup hbdd ⟨t, ht, v, rfl⟩)

/-- The map of color languages that renames color `i` to color `i` of a
larger palette. -/
def colorLift {c c' : ℕ} (hc : c ≤ c') : colorLanguage c →ᴸ colorLanguage c' where
  onFunction := fun _ f => Empty.elim f
  onRelation := fun {_} R => match R with
    | .color i => .color (Fin.castLE hc i)

/-- The colors padded by empty sets. -/
def padColors {c c' : ℕ} (colors : Fin c → Set V) : Fin c' → Set V :=
  fun i => if h : (i : ℕ) < c then colors ⟨i, h⟩ else ∅

theorem colorLift_isExpansionOn {c c' : ℕ} (hc : c ≤ c') (colors : Fin c → Set V) :
    @LHom.IsExpansionOn _ _ (colorLift hc) V (colorStructure colors)
      (colorStructure (padColors (c' := c') colors)) := by
  letI := colorStructure colors
  letI := colorStructure (padColors (c' := c') colors)
  refine ⟨fun f _ => Empty.elim f, ?_⟩
  intro n R x
  cases R with
  | color i =>
      show (x 0 ∈ padColors colors (Fin.castLE hc i)) = (x 0 ∈ colors i)
      simp [padColors, i.isLt]

/-- **More predicates and parameters.** Radius-`r` definability with
`c` predicates and `s` parameters gives it with `c' ≥ c` predicates and
`s' ≥ s` parameters. -/
theorem isRadiusDefinable_mono {G : SimpleGraph V} {s : List (Lax185574.PartialGraphs.PartialGraph V)}
    {r c c' s₁ s₂ q₀ : ℕ} (hc : c ≤ c') (hs : s₁ ≤ s₂) (h : IsRadiusDefinable G s r c s₁ q₀) :
    IsRadiusDefinable G s r c' s₂ q₀ := by
  intro t ht v
  obtain ⟨colors, S, hS, hD⟩ := h t ht v
  refine ⟨padColors colors, S, hS.trans hs, ?_⟩
  letI : (withColors Language.graph c).Structure V := expansion G colors
  letI : (withColors Language.graph c').Structure V := expansion G (padColors colors)
  letI := colorStructure colors
  letI := colorStructure (padColors (c' := c') colors)
  letI : Language.graph.Structure V := G.structure
  haveI := colorLift_isExpansionOn hc colors
  let Φ : withColors Language.graph c →ᴸ withColors Language.graph c' :=
    (LHom.id Language.graph).sumMap (colorLift hc)
  haveI : Φ.IsExpansionOn V := LHom.sumMap_isExpansionOn _ _ V
  intro k R
  obtain ⟨φ, hq, hφ⟩ := hD R
  refine ⟨Φ.onFormula φ, ?_, fun x => ?_⟩
  · rw [← Lax185574Proofs.LocalToGlobal.quantifierRank_onBoundedFormula Φ φ] at hq
    exact hq
  · rw [LHom.realize_onFormula]
    exact hφ x

end Lax185574Proofs.Compose
