import Lax3Proofs.DriverSchedule
import Lax3Proofs.DriverArena
import Lax3Proofs.DriverCorrect
import Lax3Proofs.DriverCost

/-!
# E9 — the abstract algorithm (§8 step 4): the file family's head

§5's pseudocode over §4's interface, abstractly — `SimpleGraph`, `Set`
and functions instead of CSR arrays, each routine consumed through its
landed spec, the two input-dependent routines as parameters. The family:

* `DriverSchedule` — the compile-time data (§5 line 0): the palette
  tower, the fixed per-level rewrite `stepFml = iso ∘ rel`, the
  schedule `ℱ_j` (`F`), the decompositions `dec`, `top`, the rank
  invariant (L0) and L1 (`localConst`). All proved.
* `DriverArena` — the abstract `Arena`, the per-node constructions
  (cluster/centre/compaction/batch/child), the driver `tables` and `MC`
  as Lean recursions on structural fuel, functions of the cover routine
  (`CoverSpec.OrderingRoutine`) and the scatter choice.
* `DriverCorrect` — §5's chain composed per node (`sat_child_iff`),
  **unconditional** table and root correctness (`tables_correct`,
  `mc_correct`), and the `ReachedS` invariant (`Inv`, `inv_root`,
  `inv_child`, `eq_bot_of_inv_depth`): line 10's leaf test is
  exhaustive within the UQW round budget.
* `DriverCost` — §7's accounting (`dcost`), the node inequality with
  (★) discharged (`dcost_node_le`), and the named remainder
  (`CostMajorant`) with the headline it yields.

This file adds the campaign's entry point: `mkSetup` builds the `Setup`
from `(C, hC, φ, hφ, choice)` by `Classical.choose` on
`UqwInstantiation.exists_roundBudget` — §3's `ℓ = N(2s+2)` at game
radius `2R` — and `m = ℓ·(2R+1)`, and the theorems below hand every
invariant consumer its hypotheses: the margin for every member of `C`
(`mkSetup_margin`), the budget identity (`mkSetup_depth`), and the width
bound at every depth below `ℓ` (`mkSetup_width_le`), so that
`eq_bot_of_inv_depth` and `inv_child` apply along any run on a member.
`mkSetup_mc_correct` restates the root correctness at this setup — it
holds for **every** ordering routine and every scatter choice; the
algorithm's canonical instantiation is `choice := greedyChoice`.
-/

namespace Lax3Proofs.Driver

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3Proofs.UqwInstantiation

variable {L : ℕ}

/-! ### The budget, chosen once from the class -/

/-- The UQW threshold function of the class at cap `cap`, chosen once
(`exists_roundBudget`). -/
noncomputable def budgetN (C : GraphClass) (hC : NowhereDense C) (cap : ℕ) : ℕ → ℕ :=
  (exists_roundBudget C hC cap).choose

/-- The UQW separator bound of the class at cap `cap`, chosen once. -/
noncomputable def budgetS (C : GraphClass) (hC : NowhereDense C) (cap : ℕ) : ℕ :=
  (exists_roundBudget C hC cap).choose_spec.choose

/-- §3's round budget `ℓ = N(2s+2)`. -/
noncomputable def budgetDepth (C : GraphClass) (hC : NowhereDense C) (cap : ℕ) : ℕ :=
  budgetN C hC cap (2 * budgetS C hC cap + 2)

/-- The chosen budget's specification: every member of the class has the
splitter margin at the chosen `N`, `s`. -/
theorem budget_margin (C : GraphClass) (hC : NowhereDense C) (cap : ℕ) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      SplitterMargin G (budgetN C hC cap) (budgetS C hC cap) cap := by
  have h := (exists_roundBudget C hC cap).choose_spec.choose_spec
  obtain ⟨ℓ, -, hmargin⟩ := h
  exact hmargin

/-! ### The setup from the campaign's data -/

/-- **The setup of the algorithm, from `(C, φ, choice)`** — §3's
constants: `R = ρ⁻(0, q)` (via `Setup.R`), `ℓ = N(2s+2)` at cap `R`,
`m = ℓ·(2R+1)`. Everything downstream — schedule, driver, invariants,
accounting — is a function of this record (D5); `ε` enters only the cost
layer, through `δ = ε/(ℓ+2)` in `CostMajorant`. -/
noncomputable def mkSetup (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice) : Setup L where
  q := q
  φ := φ
  hφ := hφ
  choice := choice
  depth := budgetDepth C hC (rhoMinus 0 q)
  width := budgetDepth C hC (rhoMinus 0 q) * (2 * rhoMinus 0 q + 1)

@[simp] theorem mkSetup_R (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice) :
    (mkSetup C hC φ hφ choice).R = rhoMinus 0 q := rfl

/-- The budget identity `ℓ = N(2s+2)`, at the setup's own cap. -/
theorem mkSetup_depth (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice) :
    (mkSetup C hC φ hφ choice).depth =
      budgetN C hC ((mkSetup C hC φ hφ choice).R)
        (2 * budgetS C hC ((mkSetup C hC φ hφ choice).R) + 2) := rfl

/-- The margin, at the setup's own cap, for every member of the class —
the hypothesis `eq_bot_of_inv_depth` consumes. -/
theorem mkSetup_margin (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    {n : ℕ} {G : SimpleGraph (Fin n)} (hG : C n G) :
    SplitterMargin G (budgetN C hC ((mkSetup C hC φ hφ choice).R))
      (budgetS C hC ((mkSetup C hC φ hφ choice).R))
      ((mkSetup C hC φ hφ choice).R) :=
  budget_margin C hC _ n G hG

/-- §3's `m = ℓ·(2R+1)` covers every batch below the leaf level — the
width hypothesis `inv_child` consumes, at every depth `j < ℓ`. -/
theorem mkSetup_width_le (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    {j : ℕ} (hj : j < (mkSetup C hC φ hφ choice).depth) :
    1 + j * (2 * (mkSetup C hC φ hφ choice).R + 1) ≤
      (mkSetup C hC φ hφ choice).width := by
  show 1 + j * (2 * rhoMinus 0 q + 1) ≤
    budgetDepth C hC (rhoMinus 0 q) * (2 * rhoMinus 0 q + 1)
  have hj' : j + 1 ≤ budgetDepth C hC (rhoMinus 0 q) := hj
  calc 1 + j * (2 * rhoMinus 0 q + 1)
      ≤ (j + 1) * (2 * rhoMinus 0 q + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
    _ ≤ budgetDepth C hC (rhoMinus 0 q) * (2 * rhoMinus 0 q + 1) :=
        Nat.mul_le_mul_right _ hj'

/-! ### The headline, at the setup -/

/-- **The abstract algorithm decides `φ`** — at the campaign's setup,
for every ordering routine (the correctness of the driver does not
depend on the routine's quality; only the cost does) and every scatter
choice, on every input. The canonical instantiation is
`choice := greedyChoice`. -/
theorem mkSetup_mc_correct (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    MC (mkSetup C hC φ hφ choice) ord G col ↔ Sat G col Fin.elim0 φ :=
  mc_correct (mkSetup C hC φ hφ choice) ord G col

/-- **Line 10's leaf test is exhaustive on the class** — the invariant's
payoff at the campaign setup: on a member of `C`, an arena at depth `ℓ`
satisfying the run invariant is edgeless, so the structural fuel of
`tables` never truncates a node with edges. -/
theorem mkSetup_eq_bot_of_inv_depth (C : GraphClass) (hC : NowhereDense C)
    {q : ℕ} (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    {n₀ Λ : ℕ} {G₀ : SimpleGraph (Fin n₀)} (hG₀ : C n₀ G₀) {A : Arena Λ n₀}
    (h : Inv (mkSetup C hC φ hφ choice) G₀ (mkSetup C hC φ hφ choice).depth A) :
    A.G = ⊥ :=
  eq_bot_of_inv_depth (mkSetup C hC φ hφ choice)
    (mkSetup_margin C hC φ hφ choice hG₀)
    (mkSetup_depth C hC φ hφ choice) h

/-- One descent on a member of the class, hypothesis-free: below the
leaf level the invariant carries to every child. -/
theorem mkSetup_inv_child (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    {n₀ Λ : ℕ} {G₀ : SimpleGraph (Fin n₀)} {j : ℕ} {A : Arena Λ n₀}
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (hInv : Inv (mkSetup C hC φ hφ choice) G₀ j A) (hbot : A.G ≠ ⊥)
    (hj : j < (mkSetup C hC φ hφ choice).depth) :
    Inv (mkSetup C hC φ hφ choice) G₀ (j + 1)
      (childArena (mkSetup C hC φ hφ choice) A π u) :=
  inv_child (mkSetup C hC φ hφ choice) π u hInv hbot
    (mkSetup_width_le C hC φ hφ choice hj)

/-! ### The cost, wired to the campaign's one assumption -/

/-- `2n ≤ 2^n` from `n ≥ 1` — the side condition of the augmentation
chain depth `t := R`. -/
theorem two_mul_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have h2 : 2 ≤ 2 ^ k :=
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      calc 2 * (k + 1) = 2 * k + 2 := by ring
        _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add (ih hk) h2
        _ = 2 ^ (k + 1) := by ring

/-- **E9's cost side, wired to the design's one unproved import**
(`CoverSpec.CoverOrderingTime`): on a nowhere dense class satisfying the
cover-ordering time assumption, there are an ordering routine and
constants `c_D, f ≥ 0` — all fixed before any input is read — such that
on **every member** of the class, for every per-child constant
`c ≥ c_D`, the driver's cost at the root obeys §7's headline
`K^(ℓ+1) · ‖A₀‖^(1+ε)` with the chosen `K = KD`. The degree constant
comes from `wreach_degree_of_isCoverOrdering` (the landed half of the
cover spec) at chain depth `t := R`, rounds `3R`; the time constant is
the assumption itself. -/
theorem mkSetup_dcost_root_le (C : GraphClass) (hC : NowhereDense C)
    (hT : CoverSpec.CoverOrderingTime C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ord : CoverSpec.OrderingRoutine) (cD f : ℝ), 0 ≤ cD ∧ 0 ≤ f ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L) (c : ℝ), cD ≤ c →
        1 ≤ weight (rootArena (L := L) G col) →
        dcost (mkSetup C hC φ hφ choice) ord c 0 (rootArena G col) ≤
          KD (mkSetup C hC φ hφ choice) c cD f ^
              ((mkSetup C hC φ hφ choice).depth + 1) *
            (weight (rootArena (L := L) G col) : ℝ) ^ (1 + ε) := by
  have hδ : 0 < ε / (((mkSetup C hC φ hφ choice).depth : ℝ) + 2) := by positivity
  obtain ⟨f₀, ord, hA⟩ := hT (3 * (mkSetup C hC φ hφ choice).R)
    (ε / (((mkSetup C hC φ hφ choice).depth : ℝ) + 2)) hδ
  obtain ⟨cdeg, hdeg⟩ := CoverSpec.wreach_degree_of_isCoverOrdering C hC
    ((mkSetup C hC φ hφ choice).R) (3 * (mkSetup C hC φ hφ choice).R)
    ((mkSetup C hC φ hφ choice).R) le_rfl
    (two_mul_le_two_pow (mkSetup C hC φ hφ choice).one_le_R) _ f₀ hδ hA
  refine ⟨ord, max cdeg 0, max f₀ 0, le_max_right _ _, le_max_right _ _, ?_⟩
  intro n G hG col c hc hW
  refine dcost_root_le (mkSetup C hC φ hφ choice) ord (le_max_right _ _) hc
    (le_max_right _ _) hε.le ?_ ?_ col hW
  · intro m H hH
    refine (hA.time n G hG m H hH).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro m H hH v
    refine (hdeg n G hG m H hH v).trans (Nat.ceil_le_ceil ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Lax3Proofs.Driver
