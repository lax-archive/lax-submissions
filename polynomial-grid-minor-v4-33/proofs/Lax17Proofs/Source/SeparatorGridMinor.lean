import Lax17Proofs.Source.Degree
import Lax17Proofs.Source.GridMinor
import Lax17Proofs.Source.Separator

namespace Lax17Proofs

universe u v w

/-!
# Separator-to-grid-minor theorem interface

This file packages the finite separator theorem used after the auxiliary
cut-matching graph has been proved to have bounded degree and no small
balanced separator.  The theorem itself is supplied by the relevant proof or
contract module; this file only gives the proof-facing proposition and small
transport lemmas around its numerical parameters.
-/

namespace SimpleGraph

/-- Fixed-parameter form of the separator theorem needed by the crossbar-grid
assembly.

At degree scale `d` and target grid order `g`, the statement says that every
finite graph with maximum degree at most `d` and no balanced separator smaller
than `|V| / (24d)` contains a `g x g` grid minor.  This is deliberately a
proposition, not an axiom: concrete proof modules or contract files can provide
terms of this type at the scales they establish. -/
def SeparatorGridMinorTheoremAt (d g : ℕ) : Prop :=
  ∀ {X : Type} [Fintype X] [DecidableEq X] (H : _root_.SimpleGraph X),
    MaxDegreeAtMost H d →
      NoSmallBalancedSeparator H (24 * d) →
        ContainsGridMinor H g

namespace SeparatorGridMinorTheoremAt

/-- If the separator-to-grid theorem is available at a larger degree scale, it
can be used at any smaller degree scale. -/
theorem mono_degree {d e g : ℕ}
    (h : SeparatorGridMinorTheoremAt e g) (hde : d ≤ e) :
    SeparatorGridMinorTheoremAt d g := by
  intro X _ _ H hdeg hnosep
  exact h H (maxDegreeAtMost_mono hdeg hde)
    (NoSmallBalancedSeparator.mono hnosep (Nat.mul_le_mul_left 24 hde))

/-- If the separator theorem gives a larger grid minor, it also gives every
smaller requested grid order. -/
theorem mono_order {d g h : ℕ}
    (hsep : SeparatorGridMinorTheoremAt d h) (hgh : g ≤ h) :
    SeparatorGridMinorTheoremAt d g := by
  intro X _ _ H hdeg hnosep
  exact (hsep H hdeg hnosep).of_order_le hgh

/-- Simultaneous monotonicity in the degree scale and requested grid order. -/
theorem mono {d e g h : ℕ}
    (hsep : SeparatorGridMinorTheoremAt e h) (hde : d ≤ e) (hgh : g ≤ h) :
    SeparatorGridMinorTheoremAt d g :=
  mono_order (mono_degree hsep hde) hgh

end SeparatorGridMinorTheoremAt

end SimpleGraph

end Lax17Proofs
