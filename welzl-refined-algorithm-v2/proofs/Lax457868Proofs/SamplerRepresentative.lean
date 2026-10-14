import Mathlib.Tactic
import Lax457868Proofs.SamplerCharging

/-!
Exact finite-uniform representative disagreement inside one binary fiber.
The identities are counting statements; no probabilistic coupling is assumed.
-/

namespace Lax457868Proofs.SamplerRepresentative

/-- Number of members of `C` whose binary label differs from representative `r`.
-/
def disagreementToRepresentative {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) (r : β) : ℕ :=
  (C.filter fun v => P v != P r).card

/-- Number of false-labeled members in a finite class. -/
def falseLabelCount {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) : ℕ :=
  (C.filter fun v => P v = false).card

/-- Number of true-labeled members in a finite class. -/
def trueLabelCount {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) : ℕ :=
  (C.filter fun v => P v = true).card

/-- The two label fibers partition the class. -/
lemma card_eq_false_add_true {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) :
    C.card = falseLabelCount C P + trueLabelCount C P := by
  classical
  unfold falseLabelCount trueLabelCount
  have h := Finset.card_filter_add_card_filter_not
    (s := C) (fun v => P v = false)
  have heq : C.filter (fun v => ¬ P v = false) =
      C.filter (fun v => P v = true) := by
    ext v
    simp
  rw [heq] at h
  omega

/-- Relative to a fixed representative label, exactly the opposite label fiber
disagrees with that representative. -/
lemma disagreementToRepresentative_eq {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) (r : β) :
    disagreementToRepresentative C P r =
      if P r then falseLabelCount C P else trueLabelCount C P := by
  classical
  by_cases hr : P r = true
  · have hfilter : C.filter (fun v => P v != P r) =
        C.filter (fun v => P v = false) := by
      ext v
      simp [hr]
    simp [disagreementToRepresentative, falseLabelCount, hr]
  · have hrfalse : P r = false := by cases h : P r <;> simp_all
    have hfilter : C.filter (fun v => P v != P r) =
        C.filter (fun v => P v = true) := by
      ext v
      simp [hrfalse]
    simp [disagreementToRepresentative, trueLabelCount, hrfalse]

/-- Summing over every possible representative counts each cross-label
ordered pair exactly once: the total is `2 * falseCount * trueCount`. -/
lemma sum_disagreementToRepresentative {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) :
    (∑ r ∈ C, disagreementToRepresentative C P r) =
      2 * falseLabelCount C P * trueLabelCount C P := by
  classical
  let x := falseLabelCount C P
  let y := trueLabelCount C P
  have hpoint (r : β) (hr : r ∈ C) :
      disagreementToRepresentative C P r = if P r then x else y := by
    rw [disagreementToRepresentative_eq]
  calc
    (∑ r ∈ C, disagreementToRepresentative C P r) =
        ∑ r ∈ C, if P r then x else y := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hpoint r hr
    _ = (trueLabelCount C P) * x + (falseLabelCount C P) * y := by
          simp [Finset.sum_ite, x, y, trueLabelCount, falseLabelCount,
            Nat.mul_comm]
    _ = 2 * falseLabelCount C P * trueLabelCount C P := by
          dsimp [x, y]
          ring

/-- The arithmetic mean disagreement for a uniformly chosen representative
from a nonempty finite class, expressed as a rational number. -/
def uniformRepresentativeMean {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) : ℚ :=
  (∑ r ∈ C, disagreementToRepresentative C P r : ℚ) / C.card

/-- The exact finite-uniform mean is `2*x*y/(x+y)`. -/
lemma uniformRepresentativeMean_eq {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) :
    uniformRepresentativeMean C P =
      (2 * (falseLabelCount C P : ℚ) * trueLabelCount C P) / C.card := by
  unfold uniformRepresentativeMean
  have hsumQ : (∑ r ∈ C, (disagreementToRepresentative C P r : ℚ)) =
      2 * (falseLabelCount C P : ℚ) * trueLabelCount C P := by
    exact_mod_cast sum_disagreementToRepresentative C P
  rw [hsumQ]

/-- A nonempty finite binary class has mean disagreement at most twice the
smaller label fiber, by the denominator-cleared arithmetic lemma. -/
lemma uniformRepresentativeMean_le_two_min {β : Type*} [DecidableEq β]
    (C : Finset β) (P : β → Bool) (hne : C.Nonempty) :
    uniformRepresentativeMean C P ≤
      2 * min (falseLabelCount C P) (trueLabelCount C P) := by
  classical
  let x := falseLabelCount C P
  let y := trueLabelCount C P
  have hcard : C.card = x + y := by
    simpa [x, y] using card_eq_false_add_true C P
  have hcardQ : (C.card : ℚ) = (x : ℚ) + y := by
    exact_mod_cast hcard
  have hposNat : 0 < x + y := by
    rw [← hcard]
    exact hne.card_pos
  have hposQ : (0 : ℚ) < (x : ℚ) + y := by exact_mod_cast hposNat
  have hnumQ : 2 * (x : ℚ) * y ≤
      2 * (min x y : ℚ) * ((x : ℚ) + y) := by
    exact_mod_cast
      Lax457868Proofs.SamplerCharging.twice_mul_le_twice_min_mul_add x y
  rw [uniformRepresentativeMean_eq, hcardQ, div_le_iff₀ hposQ]
  simpa [x, y] using hnumQ

/-- The binary label induced by membership of a fixed coordinate in a
neighborhood/set-valued observation. -/
noncomputable def coordinateLabel {α β : Type*} (N : β → Finset α) (a : α) : β → Bool :=
  by
    classical
    exact fun b => decide (a ∈ N b)

/-- For one coordinate, the total representative disagreement is twice the
product of the sizes of its two fibers. -/
lemma sum_coordinateDisagreement {α β : Type*} [DecidableEq β]
    (C : Finset β) (N : β → Finset α) (a : α) :
    (∑ r ∈ C, disagreementToRepresentative C (coordinateLabel N a) r) =
      2 * falseLabelCount C (coordinateLabel N a) *
        trueLabelCount C (coordinateLabel N a) := by
  exact sum_disagreementToRepresentative C (coordinateLabel N a)

/-- The finite-uniform representative mean for a single coordinate is bounded
by twice the smaller coordinate fiber. This is the coordinatewise form used
for adjacency or membership observations. -/
lemma uniform_coordinateDisagreement_le_two_min {α β : Type*} [DecidableEq β]
    (C : Finset β) (N : β → Finset α) (a : α) (hne : C.Nonempty) :
    uniformRepresentativeMean C (coordinateLabel N a) ≤
      2 * min (falseLabelCount C (coordinateLabel N a))
        (trueLabelCount C (coordinateLabel N a)) := by
  exact uniformRepresentativeMean_le_two_min C (coordinateLabel N a) hne

end Lax457868Proofs.SamplerRepresentative
