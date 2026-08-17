import Lax3Proofs.Refine.ArenaWidth
import Lax3Proofs.Refine.OrderActiveBudget

/-!
# The active root's word-width gate

The active order and cover have removed carrier-wide *time* charges, but
their current public root contract still exposes two resident-space bounds:

* `WordBoundK B n D ...` addresses an active-cover prefix of size `n * D`;
* `activeOrderWidth d D₁ R ...` addresses the compact augmentation
  workspace.

The word-RAM headline fixes its domain constant before the input and admits
the smallest word length with `2^w` only a constant factor above the input
length.  Consequently an input-dependent coefficient cannot be hidden in
that constant.  The two theorems below compile this exact seam at the
headline's empty-graph words.  They do **not** say that the logical arrays'
declared lengths must be below `B`: the IMP+ simulation deliberately does
not require that.  They say that an index the executed program actually
forms must be below `B`, which is the load-bearing distinction.
-/

namespace Lax3Proofs.Refine.ActiveBridgeWidth

open Lax11.GraphEncoding
open Lax13Proofs.Compile (Layout)
open Lax3Proofs.RamDriver (WordBoundK)
open Lax3Proofs.Refine.BridgeSeamProbe (emptyWord)
open Lax3Proofs.Refine.OrderActiveBudget (activeOrderWidth)

/-! ## The cover-pointer coefficient -/

/-- At a tight word admitted by the headline domain, no value bound can
simultaneously fit the layout and the current active-cover arena clause once
`n * D + n` already exceeds the domain's linear address ceiling.

This is deliberately pointwise in `n` and `D`.  A final parameter theorem
may use it with any proposed instance-dependent degree profile, without
committing this file to a particular real-exponent rounding convention. -/
theorem no_wordBoundK_at_tight_word (L : Layout) {c n D : ℕ}
    (hc : 0 < c) (hcross : 4 * c * (n + 2) ≤ n * D + n) :
    ∃ w : ℕ,
      (∀ v ∈ emptyWord n,
        c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (B ns cap mb : ℕ), L.FitsWords B w →
        ¬ WordBoundK B n D ns cap mb := by
  obtain ⟨w, hdom, hw⟩ :=
    Lax3Proofs.Refine.ArenaWidth.exists_w_tight c n hc
  refine ⟨w, hdom, ?_⟩
  intro B ns cap mb hfit hB
  have hbound := hfit.bound
  have harena := hB.1
  omega

/-- Therefore no constant chosen before the input can discharge the current
cover-pointer contract for an unbounded degree profile.  `D` is intentionally
only assumed unbounded on carriers of size at least two; no monotonicity or
particular rate is needed. -/
theorem no_wordConst_for_unbounded_degree (L : Layout) (D : ℕ → ℕ)
    (hunbounded : ∀ k, ∃ n, 2 ≤ n ∧ k ≤ D n) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n w : ℕ),
      (∀ v ∈ emptyWord n,
        c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) →
      ∃ B : ℕ, L.FitsWords B w ∧ WordBoundK B n (D n) 0 0 0 := by
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn, hD⟩ := hunbounded (8 * c)
  have hcross : 4 * c * (n + 2) ≤ n * D n + n := by
    calc
      4 * c * (n + 2) ≤ 4 * c * (2 * n) :=
        Nat.mul_le_mul_left (4 * c) (by omega)
      _ = n * (8 * c) := by ring
      _ ≤ n * D n := Nat.mul_le_mul_left n hD
      _ ≤ n * D n + n := Nat.le_add_right _ _
  obtain ⟨w, hdom, hno⟩ :=
    no_wordBoundK_at_tight_word L hc hcross
  obtain ⟨B, hfit, hB⟩ := h n w hdom
  exact hno B 0 0 0 hfit hB

/-! ## The compact-order resident width -/

/-- The same tight-word obstruction for the second resident-space premise
of `ActiveRoot.driverRootActive_decides_sentence`.  If the concrete active
ordering width at the root already exceeds the domain's linear address
ceiling, no `B` satisfying `Layout.FitsWords` can discharge `hwidthB`.

Unlike the cover theorem, this statement mentions the exact executable
width function.  It therefore catches dependence hidden in the coefficient
`activeOrderWidthCoeff d D₁ R`, not merely a carrier-sized loop. -/
theorem no_activeOrderWidth_at_tight_word (L : Layout) {c n d D₁ R : ℕ}
    (hc : 0 < c)
    (hcross : 4 * c * (n + 2) ≤ n + activeOrderWidth d D₁ R n + 1) :
    ∃ w : ℕ,
      (∀ v ∈ emptyWord n,
        c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ B : ℕ, L.FitsWords B w →
        ¬ (n + activeOrderWidth d D₁ R n + 1 < B) := by
  obtain ⟨w, hdom, hw⟩ :=
    Lax3Proofs.Refine.ArenaWidth.exists_w_tight c n hc
  refine ⟨w, hdom, ?_⟩
  intro B hfit hwidth
  have hbound := hfit.bound
  omega

/-- More generally, no fixed domain constant pays a resident-width profile
that is superlinear in the carrier.  This is the form needed to audit a
proposed instantiation whose `d` or `D₁` depends on the input: instantiate
`width n` with the resulting `activeOrderWidth ... n`, then prove (or fail to
prove) the displayed growth premise. -/
theorem no_wordConst_for_superlinear_width (L : Layout) (width : ℕ → ℕ)
    (hwide : ∀ k, ∃ n, 2 ≤ n ∧ k * n ≤ width n) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n w : ℕ),
      (∀ v ∈ emptyWord n,
        c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) →
      ∃ B : ℕ, L.FitsWords B w ∧ n + width n + 1 < B := by
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn, hwidth⟩ := hwide (8 * c)
  have hcross : 4 * c * (n + 2) ≤ n + width n + 1 := by
    calc
      4 * c * (n + 2) ≤ 4 * c * (2 * n) :=
        Nat.mul_le_mul_left (4 * c) (by omega)
      _ = (8 * c) * n := by ring
      _ ≤ width n := hwidth
      _ ≤ n + width n + 1 := by omega
  obtain ⟨w, hdom, hw⟩ :=
    Lax3Proofs.Refine.ArenaWidth.exists_w_tight c n hc
  obtain ⟨B, hfit, hB⟩ := h n w hdom
  have hbound := hfit.bound
  omega

/-! ## Controls -/

-- The cover obstruction is not an empty statement: a square degree profile
-- crosses a generous fixed domain constant at an explicit input size.
#guard 4 * (10 ^ 6) * (10 ^ 8 + 2) ≤ (10 ^ 8) * (10 ^ 8) + 10 ^ 8

-- Conversely a fixed degree coefficient does not cross that ceiling at the
-- same point.  The distinction is dependence on the instance, not merely a
-- large numeral chosen before it.
#guard ¬ (4 * (10 ^ 6) * (10 ^ 8 + 2) ≤ (10 ^ 8) * 8 + 10 ^ 8)

/-! ## Axiom audit -/

#print axioms no_wordBoundK_at_tight_word
#print axioms no_wordConst_for_unbounded_degree
#print axioms no_activeOrderWidth_at_tight_word
#print axioms no_wordConst_for_superlinear_width

end Lax3Proofs.Refine.ActiveBridgeWidth
