import Lax3Proofs.ProgFrame
import Lax3Proofs.Headline

/-!
# F4 — the driver as one program: `ℓ+1` levels

F3 (`ProgFrame`) delivered one frame of the unrolled driver as a
cost-carrying NREST program, its two call sites abstracted into slots:
the cover pass (`coverProg`, hypothesis `hcover`) and the recursion
into the level below (`nxProg`, hypothesis `hnx`). This file closes the
**recursion slot** by recursion on the level index, mirroring
`Unroll.unrollAux` (`Unroll.lean`): level `k+1` is `frameProg` wired to
level `k` one depth down, level `0` is the bottom frame. The cover slot
stays parametric — a family with one quantified spec-and-charge
obligation (`CoverSlotSpec`), which F5 discharges with the GKS sweep.

## The program

`driverProg S ℓp htabF coverProg k j A` — the recursion is on the
**level index `k` only**, never on the program's own value at the same
level (E10's point, inherited: a machine realizes the driver as `k+1`
static code blocks, block `j` jumping only into block `j+1`, which is
F6's layout). Per node the program instantiates `frameProg`'s two
per-arena inputs canonically:

* the leaf rows `colBof A` — the boolean color rows agreeing with the
  arena's coloring by construction (`colBof_spec`); the machine's
  actual rows are `recordProfiles`' output, a seam F6 crosses, and
  every bottom-level lemma here is stated for an arbitrary `colB` with
  the row hypothesis, so nothing is lost;
* the history table `htabF j A` at `ℓp j` rounds — free parameters
  exactly as F3's `htab` is free (the refinement constrains neither;
  they enter only the charge).

**The bottom frame** (`botProg`). `Unroll.unrollAux`'s fuel-`0` value
is `botFrame S j A` — satisfaction at the node's own arena, for *every*
arena. The machine's row evaluator `Impl.botEval` computes it exactly
at edgeless arenas (`botEval_eq_sat`), and the run invariant proves the
fuel-`0`-with-edges case is **dead on the class**
(`Unroll.memLeaf_eq_bot` / `mkSetup_memLeaf_eq_bot`: within the UQW
budget every arena a run bottoms out at is edgeless). The level
induction nevertheless needs the bottom program's refinement
**unconditionally in the arena** — F3's recursion-slot obligation
quantifies over every child arena, dead or not. So `botProg` branches:
on an edgeless arena it is the machine route (`botEval` over the rows,
exactly `frameProg`'s own leaf branch); on an arena with edges it
returns the abstract value `Unroll.botFrame S j A` outright, at the
same leaf charge — dead code priced like the abstract layer prices it
(`unrollCostAux`'s fuel-`0` clause charges the leaf regardless), with
the deadness theorem, not this file, carrying the machine claim.

## The refinement theorem

`driverProg_le_spec`, by induction on `k`, consuming
`frameProg_le_spec` at every level: given `S.choice = greedyChoice`
(threaded, per F3) and the cover slot's quantified obligation, the
driver program at level `k` refines *"the returned table is
`Unroll.unrollAux S ord k j A`, for budget `driverCharge`"*.
`driverProg_le_spec_tables` instantiates `k := S.depth - j`: the table
is `Unroll.unrolledTables = Driver.tables` (the landed equality).
`driverProg_le_spec_root` is its root form: the returned table is
`tables S ord 0 (rootArena G col)` — the whole driver, one program.

## `MC` at the root

`mcProg` composes the final evaluation: run the root driver, pay the
guarded `Impl.greedyScatter` counts over the returned table — one call
per scatter atom of `top`'s decomposition, at marking parameter
`W := ‖rootArena‖`, the §6.5 instantiation, priced by
`topScatterCost` — and return `top`'s boolean combination with its
local sentence atoms as compile-time constants (L1, `localConst`).
`mcProg_le_spec`: the returned proposition **is**
`Unroll.unrolledMC S ord G col`, for budget `mcCharge` (the guarded
count decides each scatter atom exactly, `le_greedyScatter_iff`).
`mcProg_correct` and `mcProg_headline` are the Headline chain on top:
the value is `Sat G col Fin.elim0 S.φ` on every graph, and at the
campaign setup `headlineSetup C hC φ` it is
`Lax3.FirstOrder.Sat G Fin.elim0 φ` — the axiom's semantic object.

## The charge

`driverCharge` is **structurally the level recursion of
`frameCharge`**: level `k+1` is `frameCharge` at the level's own
parameters — the cover slot's `covC j A`, the oracle table
`Unroll.unrollAux S ord k (j+1)` (the dependence `frameCharge` has on
its `nx`) — wired to level `k`'s charge as the recursion slot's
vector, exactly as `Unroll.unrollCostAux` is `frameCost` wired to
itself one level down; the bottom is F3's leaf charge `botC`. No
comparison against `Unroll.frameCost`/`unrollCostAux` is attempted
here (F3c owns the frame-level comparison, and `ProgFrame`'s module
docstring records the two shape obstructions); because the charge is
the same level-sum, F3c's per-frame result lifts to `driverCharge` by
the same induction on `k` that proves `driverProg_le_spec`. `mcCharge`
adds the root evaluation's one scatter column (`"top.scatter"`) on
top of the root `driverCharge`.
-/

namespace Lax3Proofs.Prog

open Lax62Proofs.Refine
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun

variable {L n₀ : ℕ}

/-! ## The per-node leaf rows

`frameProg` consumes boolean color rows `colB` (its leaf branch's §6.4
evaluator reads them) under the row hypothesis `hcol`. The driver
instantiates them canonically per node: the rows that agree with the
arena's coloring by construction. The machine's actual rows are
`recordProfiles`' output — the seam F6 crosses; every refinement below
that touches rows is proved for an arbitrary `colB` with `hcol`. -/

open Classical in
/-- The canonical color rows of an arena: `true` exactly on the
coloring's members. -/
noncomputable def colBof {Λ : ℕ} (A : Arena Λ n₀) : Fin A.N → Fin Λ → Bool :=
  fun v c => decide (v ∈ A.col c)

/-- `colBof` satisfies the row hypothesis definitionally. -/
theorem colBof_spec {Λ : ℕ} (A : Arena Λ n₀) :
    ∀ (v : Fin A.N) (c : Fin Λ), colBof A v c = true ↔ v ∈ A.col c := by
  intro v c
  simp [colBof]

/-! ## The bottom frame -/

/-- The row evaluator computes `Unroll.botFrame` at an edgeless arena —
`botTable_eq_frameEval`'s content at the fuel-`0` frame
(`botEval_eq_sat`, then the edgeless rewrite). -/
theorem botTable_eq_botFrame (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {colB : Fin A.N → Fin (S.pal j) → Bool}
    (hcol : ∀ v c, colB v c = true ↔ v ∈ A.col c) (hbot : A.G = ⊥) :
    (fun (v : Fin A.N) (β : DistFO (S.pal j) 1) =>
        Impl.botEval colB (fun _ => v) β = true)
      = Unroll.botFrame S j A := by
  funext v β
  show (Impl.botEval colB (fun _ => v) β = true) = Sat A.G A.col (fun _ => v) β
  refine propext ((Impl.botEval_eq_sat colB A.col hcol β (fun _ => v)).trans ?_)
  rw [hbot]

open Classical in
/-- **The bottom program** (fuel exhausted): on an edgeless arena, the
§6.4 row evaluator over the machine's color rows — `frameProg`'s own
leaf route, at the leaf charge `botC`. On an arena with edges — the
branch `Unroll.memLeaf_eq_bot` proves is **never executed** in a run
on the class — the abstract value `Unroll.botFrame S j A`, at the same
leaf charge (`unrollCostAux`'s fuel-`0` clause prices the leaf
regardless of the branch). The dead branch is what keeps the
refinement unconditional in the arena, which the level induction
requires: F3's recursion-slot obligation quantifies over *every* child
arena. -/
noncomputable def botProg (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (colB : Fin A.N → Fin (S.pal j) → Bool) :
    NRest (Fin A.N → DistFO (S.pal j) 1 → Prop) ECost :=
  if A.G = ⊥ then
    NRest.consume
      (NRest.returnT fun (v : Fin A.N) (β : DistFO (S.pal j) 1) =>
        Impl.botEval colB (fun _ => v) β = true)
      (liftACost (botC S j A))
  else
    NRest.consume (NRest.returnT (Unroll.botFrame S j A)) (liftACost (botC S j A))

/-- The bottom program refines `Unroll.botFrame`, for the leaf charge —
unconditionally in the arena (module docstring: the edged branch is
dead on the class, and holds the abstract value). -/
theorem botProg_le_spec (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {colB : Fin A.N → Fin (S.pal j) → Bool}
    (hcol : ∀ v c, colB v c = true ↔ v ∈ A.col c) :
    botProg S j A colB ≤
      NRest.spec (fun T => T = Unroll.botFrame S j A)
        (fun _ => liftACost (botC S j A)) := by
  rw [botProg]
  by_cases hbot : A.G = ⊥
  · rw [if_pos hbot]
    exact consume_returnT_le_spec (P := fun T => T = Unroll.botFrame S j A)
      (botTable_eq_botFrame S j A hcol hbot) _
  · rw [if_neg hbot]
    exact consume_returnT_le_spec (P := fun T => T = Unroll.botFrame S j A) rfl _

/-! ## The cover slot's obligation — F5's contract, stated once -/

/-- **The cover slot's obligation, quantified once over every node**:
at each level `j` and arena `A`, the slot's program returns exactly the
routine's ordering `(ord A.N A.G).order`, for the slot's own budget
`covC j A`. The budget is a function of the node, so a per-node
`sweepCharge`-shaped bound slots in unchanged; F5 fills the slot by
exhibiting `(coverProg, covC)` with this property. -/
def CoverSlotSpec (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost)
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ) : Prop :=
  ∀ (j : ℕ) (A : Arena (S.pal j) n₀),
    coverProg j A ≤
      NRest.spec (fun π => π = (ord A.N A.G).order)
        (fun _ => liftACost (covC j A))

/-! ## The driver -/

/-- **The driver, as one program** — `Unroll.unrollAux`'s mirror in the
refinement tower's monad: level `k+1` is `frameProg` at the node's
canonical rows and history table, its cover slot the parametric family
`coverProg j A`, its recursion slot the level-`k` driver one depth
down; level `0` is the bottom program. The recursion is on the **level
index only** — no level refers to itself, so F6 can lay the levels out
as `k+1` static code blocks, block `j` jumping only into block
`j+1`. -/
noncomputable def driverProg (S : Setup L) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost) :
    (k : ℕ) → (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Fin A.N → DistFO (S.pal j) 1 → Prop) ECost
  | 0, j, A => botProg S j A (colBof A)
  | k + 1, j, A =>
    frameProg S j A (htabF j A) (colBof A) (coverProg j A)
      (fun B => driverProg S ℓp htabF coverProg k (j + 1) B)

/-- **The driver's advertised budget**: structurally the level
recursion of `frameCharge` — level `k+1` is `frameCharge` at the
level's own parameters (the cover slot's `covC j A`, the oracle table
`Unroll.unrollAux S ord k (j+1)`), wired to level `k`'s charge as the
recursion slot's vector, exactly as `Unroll.unrollCostAux` is
`frameCost` wired to itself one level down; the bottom is the leaf
charge `botC`. Because the shape is the same level-sum, F3c's
frame-level comparison lifts to this charge by the same induction on
`k` that proves `driverProg_le_spec` — no comparison is stated here
(F3c owns it; `ProgFrame`'s module docstring records the two shape
obstructions the comparison must resolve). -/
noncomputable def driverCharge (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ) :
    (k : ℕ) → (j : ℕ) → (A : Arena (S.pal j) n₀) → ACost String ℕ
  | 0, j, A => botC S j A
  | k + 1, j, A =>
    frameCharge S ord j A (ℓp j) (htabF j A)
      (fun B => Unroll.unrollAux S ord k (j + 1) B)
      (covC j A)
      (fun B => driverCharge S ord ℓp htabF covC k (j + 1) B)

/-- **F4's refinement theorem.** Given the canonical scatter choice
(`S.choice = greedyChoice`, threaded to every frame) and the cover
slot's quantified obligation, the driver program at level `k` refines
the specification *"the returned table is `Unroll.unrollAux S ord k j
A`, for budget `driverCharge`"* — by induction on the level index,
consuming `frameProg_le_spec` at every level and `botProg_le_spec` at
the bottom. -/
theorem driverProg_le_spec (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    {coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost}
    {covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ}
    (hchoice : S.choice = greedyChoice)
    (hcover : CoverSlotSpec S ord coverProg covC) :
    ∀ (k j : ℕ) (A : Arena (S.pal j) n₀),
      driverProg S ℓp htabF coverProg k j A ≤
        NRest.spec (fun T => T = Unroll.unrollAux S ord k j A)
          (fun _ => liftACost (driverCharge S ord ℓp htabF covC k j A)) := by
  intro k
  induction k with
  | zero =>
    intro j A
    rw [driverProg, driverCharge, Unroll.unrollAux]
    exact botProg_le_spec S j A (colBof_spec A)
  | succ k ih =>
    intro j A
    rw [driverProg, driverCharge, Unroll.unrollAux]
    exact frameProg_le_spec S ord j A (htabF j A) (colBof_spec A) hchoice
      (hcover j A) (fun B => ih (j + 1) B)

/-- The driver at fuel `ℓ − j` computes **`Driver.tables`** — the
corollary at the campaign fuel, through the landed equality
`unrolledTables_eq_tables`. -/
theorem driverProg_le_spec_tables (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    {coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost}
    {covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ}
    (hchoice : S.choice = greedyChoice)
    (hcover : CoverSlotSpec S ord coverProg covC)
    (j : ℕ) (A : Arena (S.pal j) n₀) :
    driverProg S ℓp htabF coverProg (S.depth - j) j A ≤
      NRest.spec (fun T => T = tables S ord j A)
        (fun _ => liftACost
          (driverCharge S ord ℓp htabF covC (S.depth - j) j A)) :=
  le_spec_weaken
    (driverProg_le_spec S ord ℓp htabF hchoice hcover (S.depth - j) j A)
    (fun _ hT => hT.trans (Unroll.unrolledTables_eq_tables S ord j A)) le_rfl

/-- **The root driver computes the root table**: at fuel `ℓ` from the
root arena, the returned table is `tables S ord 0 (rootArena G col)` —
the whole driver of §5, one program. -/
theorem driverProg_le_spec_root (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    {coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost}
    {covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ}
    (hchoice : S.choice = greedyChoice)
    (hcover : CoverSlotSpec S ord coverProg covC)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L) :
    driverProg S ℓp htabF coverProg S.depth 0 (rootArena G col) ≤
      NRest.spec (fun T => T = tables S ord 0 (rootArena G col))
        (fun _ => liftACost
          (driverCharge S ord ℓp htabF covC S.depth 0 (rootArena G col))) :=
  le_spec_weaken
    (driverProg_le_spec S ord ℓp htabF hchoice hcover S.depth 0 (rootArena G col))
    (fun _ hT => hT.trans (Unroll.unrolledTables_eq_tables S ord 0 (rootArena G col)))
    le_rfl

/-! ## `MC` at the root -/

/-- The root evaluation's scatter account: one guarded `greedyScatter`
call per scatter atom of `top`'s decomposition, each at the routine's
own cost with marking parameter `W := ‖rootArena‖` (§6.5's `W := ‖A‖`
instantiation at the root), at table `T`. Zero outright at `σ.t = 0` —
the guard is a cost statement (`greedyScatterCost_zero`). -/
noncomputable def topScatterCost (S : Setup L) (G : SimpleGraph (Fin n₀))
    (col : Coloring n₀ L) (T : Fin n₀ → DistFO L 1 → Prop) : ℕ :=
  ((scatterAtoms S.choice S.φ S.hφ).map fun σ =>
    Impl.greedyScatterCost G σ.r {v | T v σ.β}
      (weight (rootArena G col)) σ.t).sum

/-- **§5 lines 1–6, as one program**: run the root driver, pay the
guarded scatter counts over the returned table — one `greedyScatter`
call per scatter atom of `top` — and return `top`'s boolean
combination, its local sentence atoms as compile-time constants (L1,
`localConst`), its scatter atoms decided by the guarded counts. -/
noncomputable def mcProg (S : Setup L) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L) : NRest Prop ECost :=
  NRest.bindT (driverProg S ℓp htabF coverProg S.depth 0 (rootArena G col)) fun T =>
    NRest.consume
      (NRest.returnT ((top S).eval (Sum.elim (fun ψ => localConst ψ)
        (fun σ => σ.t ≤ Impl.greedyScatter G σ.r {v | T v σ.β} σ.t))))
      (liftACost (ACost.cost "top.scatter" (topScatterCost S G col T)))

/-- `mcProg`'s advertised budget: the root driver's charge plus the
root evaluation's one scatter column, in its own currency
`"top.scatter"`, priced at the delivered table (`Driver.tables` at the
root — the same dependence `centreCharge` has on its slot's delivered
table). -/
noncomputable def mcCharge (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L) : ACost String ℕ :=
  driverCharge S ord ℓp htabF covC S.depth 0 (rootArena G col)
    + ACost.cost "top.scatter"
        (topScatterCost S G col (tables S ord 0 (rootArena G col)))

/-- **The program decides `MC`, in its unrolled form**: `mcProg`'s
returned proposition is `Unroll.unrolledMC S ord G col`, for budget
`mcCharge` — the root driver's postcondition pins the table, and the
guarded count decides each scatter atom of `top` exactly
(`le_greedyScatter_iff` at the canonical choice). -/
theorem mcProg_le_spec (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    {coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost}
    {covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ}
    (hchoice : S.choice = greedyChoice)
    (hcover : CoverSlotSpec S ord coverProg covC)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L) :
    mcProg S ℓp htabF coverProg G col ≤
      NRest.spec (fun b : Prop => b = Unroll.unrolledMC S ord G col)
        (fun _ => liftACost (mcCharge S ord ℓp htabF covC G col)) := by
  rw [mcProg, mcCharge]
  simp only [liftACost_add]
  refine bindT_le_spec
    (driverProg_le_spec S ord ℓp htabF hchoice hcover S.depth 0 (rootArena G col))
    fun T hT => ?_
  subst hT
  have heq : Unroll.unrollAux S ord S.depth 0 (rootArena G col)
      = tables S ord 0 (rootArena G col) :=
    Unroll.unrolledTables_eq_tables S ord 0 (rootArena G col)
  rw [heq]
  refine consume_returnT_le_spec
    (P := fun b : Prop => b = Unroll.unrolledMC S ord G col) ?_ _
  -- the value: the guarded counts decide the scatter atoms exactly
  rw [Unroll.unrolledMC_eq_MC, MC]
  refine congrArg (fun f => (top S).eval f) (funext fun x => ?_)
  cases x with
  | inl ψ => rfl
  | inr σ =>
    simp only [Sum.elim_inr, hchoice]
    exact propext (Impl.le_greedyScatter_iff _ _ _ _)

/-- **The program is correct** — the Headline chain's first step, on
every graph and coloring: `mcProg`'s returned proposition is
satisfaction of `S.φ` itself (`unrolledMC_correct`, E9's correctness
inherited verbatim by the unrolled form). -/
theorem mcProg_correct (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    {coverProg : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost}
    {covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ}
    (hchoice : S.choice = greedyChoice)
    (hcover : CoverSlotSpec S ord coverProg covC)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L) :
    mcProg S ℓp htabF coverProg G col ≤
      NRest.spec (fun b : Prop => b ↔ Sat G col Fin.elim0 S.φ)
        (fun _ => liftACost (mcCharge S ord ℓp htabF covC G col)) :=
  le_spec_weaken (mcProg_le_spec S ord ℓp htabF hchoice hcover G col)
    (fun b hb => by rw [hb]; exact Unroll.unrolledMC_correct S ord G col)
    le_rfl

/-- **The program decides the axiom's semantic object** — the Headline
chain, composed: at the campaign setup of a plain first-order sentence
(`headlineSetup`, whose scatter choice is `greedyChoice`
definitionally), `mcProg`'s returned proposition is
`Lax3.FirstOrder.Sat G Fin.elim0 φ`, on every graph and for every
coloring of the empty palette. -/
theorem mcProg_headline (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    {coverProg : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n₀) →
      NRest (Equiv.Perm (Fin A.N)) ECost}
    {covC : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n₀ →
      ACost String ℕ}
    (hcover : CoverSlotSpec (Headline.headlineSetup C hC φ) ord coverProg covC)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ 0) :
    mcProg (Headline.headlineSetup C hC φ) ℓp htabF coverProg G col ≤
      NRest.spec (fun b : Prop => b ↔ Lax3.FirstOrder.Sat G Fin.elim0 φ)
        (fun _ => liftACost
          (mcCharge (Headline.headlineSetup C hC φ) ord ℓp htabF covC G col)) :=
  le_spec_weaken
    (mcProg_le_spec (Headline.headlineSetup C hC φ) ord ℓp htabF rfl hcover G col)
    (fun b hb => by
      rw [hb, Unroll.unrolledMC_eq_MC]
      exact Headline.headlineSetup_mc_correct C hC φ ord G col)
    le_rfl

end Lax3Proofs.Prog
