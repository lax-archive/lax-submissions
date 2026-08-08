import Lax3Proofs.Refine.KillListPass
import Lax3Proofs.Refine.CoverBlock
import Lax3Proofs.Refine.BlockLeaves
import Lax3Proofs.Refine.ScatterDeadTurn
import Lax3Proofs.Refine.DeadSweep

/-!
# The C0 close, run at the constants the package has actually measured

`Refine/G2ExistsRevalidation.lean` §3 compiled the M-class close at
**borrowed** constants: `g2M 68 12 68 12 68 12 0 200 (10^4) 8` plugs the
order phase's measured `68`/`12` into the cover and dead slots as well,
and reads the turn at the pre-R1.8 `200`. This file re-runs the same
landed chain at each phase's own measured number, and back-solves the
coefficient ceiling every remaining engine wave has to hit.

Nothing landed is edited, restated or attributed. `phaseM`, `phaseMR`,
`phaseBudgetM`, `g2M`, `g2m_exists`, `rootBudgetM`, `rootBudgetM_closes`
and `mclass_c0_shape` are **consumed**.

## The headline

**The close does not hold at the landed constants, and the single
reason is the scatter leaf.** Every other phase clears its ceiling by
four to thirteen orders of magnitude. `ksc` — the per-atom scatter
charge that rides the turn's size slot — is instantiated at the landed
`Refine.ScatterDeadPass.ballBudget_carrier`, which supplies the whole
carrier as the ball budget (`bw := ns`, `nb := n`); §4 compiles that it
is then bounded below by `131·n`, so **no constant `ksc` exists**, and
the ε = 1/2 and ε = 1/4 gates of §2 fail at it while they pass at a
constant. §2's close is therefore stated with the constant-`ksc`
hypothesis `hKsc` **named**. The ε = 1 gate passes even at the
carrier-charged reading — a quadratic cost is inside an `n^2` budget —
which is why the landed guards, all at ε = 1, could not see this.

**Wave E4c-a corrected the attribution of that hypothesis.** `hKsc` is
*not* E4c's deliverable. Control 1b splits the `131·n` into the part an
accounting wave can re-charge (`108·n + 18`) and the part that is
program text (`23·n + 12`, the two calling-convention copies), and
`narrow_leaf_refutes_constant_ksc` compiles that no narrowing of the
probe bound, the member counts or the ball budget produces a constant
`ksc` while those copies stand. Beyond them the honest reading is the
turn's **cluster**, not a constant, so the close needs the turn's size
slot read as well — `turnCostSize` discards it today.

## The four sections

* **§1** the measured constant table: each `(a, b)` pair tied to the
  landed measured cost function it comes from, or declared opaque with
  the reason. Two hazards are resolved here and one is refuted:
  `bexpPass`'s `30·d` is paid by the turn slot's WEIGHT reading and the
  Σ mass side condition, not by any member-linear phase form
  (`bexpK_not_memberForm`, `descendLeaves_sum_le_mass`); and the cover
  phase does **not** fit the M-class slot at the natural `(a, b)` split
  (`cover_measured_pair_insufficient`), so its slot pair is the budget
  pair `(kcov, kcov)`.
* **§2** the assembled close: `g2m_exists` at the measured constants,
  `rootBudgetM_closes`, and `mclass_c0_shape` — the latter at exponent
  `ℓ + 1`, because `rootBudgetM`'s own constant is **not** `D`-free
  (`rootBudgetM_le_cstar`). `#guard`s at ε = 1, 1/2, 1/4.
* **§3** the ceiling per phase, each pinned in both directions (the
  ceiling clears, the ceiling plus one does not), next to the phase's
  measured value.
* **§4** the honesty controls: the carrier-charged scatter leaf, a
  carrier-bearing phase form, the un-narrowed `hKd` slot and the landed
  base — four compiled refutations, in `Refine.CostShapeProbe` style.

## What this file does NOT claim

That any landed *walk* meets these slots. The gap ledger is
`G2CostProbe` §7 and is unchanged. This file's question is the
arithmetic one: given the measured leaf costs, what does the Σ
interface close to, and what does each unfinished wave have to deliver.
-/

namespace Lax3Proofs.Refine.C0CloseProbe

open Finset
open Lax3Proofs.Refine.G2ExistsRevalidation
  (phaseM phaseMR phaseBudgetM phaseMR_le_budget phaseBudgetM_eq g2M g2m_exists rootBudgetM
   rootBudgetM_closes mclass_c0_shape)
open Lax3Proofs.Refine.G2CostProbe (turnCostSizeA)

/-! ### §1 The measured constant table

| phase | constant | value | source |
|---|---|---|---|
| order | `aOrd`, `bOrd` | `68`, `12` | `OrderSigProbeM.phaseClockK`, synthesized whole-phase |
| order rounds | `R` | **opaque** | the augment/relink round count; E-order owns it |
| cover | `kcCov` | `150` | `CoverBlock.centreK_root_admissible` |
| cover | `ka` | **opaque** | the arena-driven residue; E3b owns it |
| cover slot | `aCovSlot`, `bCovSlot` | `kcov 150 ka D` twice | forced, see `cover_measured_pair_insufficient` |
| descend | — | `200` at the block WEIGHT | `G2CostProbe.blockLeaves_le_weight` |
| turn | `ctTurn` | `KillListPass.ctKL` = `443` | `200 + 84 + klc`, R1.8 |
| dead | `aDead`, `bd` | `0`, **opaque** | R1.8 took the sweep out; landed reading `12` |
| scatter | `ksc` | **opaque, and refuted at the landed reading AND at every narrowing of it** | §4, control 1/1b |
| base | `Cb` | **opaque — T4b unstarted, and refuted at the landed reading** | §4 |
| root decode | `kdecRoot` | `87` | `G2ExistsRevalidation.decodeDLCost_le_weight` |
-/

/-- **Order, member coefficient — MEASURED.** `Refine.OrderSigProbeM`
synthesized the member-driven order phase whole and ran its clock on the
tower's executable semantics at two carrier widths: `68·m + 12`, with
the carrier absent. -/
def aOrd : ℕ := 68

/-- **Order, empty-arena charge — MEASURED**, the same run. -/
def bOrd : ℕ := 12

/-- The tie: the measured law *is* `phaseM aOrd bOrd`. Consumed from
`G2ExistsRevalidation.phaseClockK_eq_phaseM`; not re-derived. -/
theorem ord_pair_measured (m : ℕ) :
    Lax3Proofs.Refine.OrderSigProbeM.phaseClockK m = phaseM aOrd bOrd m :=
  Lax3Proofs.Refine.G2ExistsRevalidation.phaseClockK_eq_phaseM m

/-- **Cover, the per-centre engine coefficient — MEASURED.**
`CoverBlock.centreK_root_admissible` reads `150` off the landed engine
(`RamCover.centreCost n ns ≤ 150·(n + ns + 1)`); it is not chosen. -/
def kcCov : ℕ := 150

theorem kcCov_measured (n ns : ℕ) :
    Lax3Proofs.RamCover.centreCost n ns ≤ kcCov * (n + ns + 1) :=
  Lax3Proofs.Refine.G2CostProbe.centreCost_le_weight n ns

/-- **Cover, the arena-driven residue — OPAQUE, no measurement.** `ka`
pays `CoverBlock.coverPhaseCostB`'s third summand: the block-offset
copy, the assignment copy and the compaction scan, which are
member-driven only after E2 (`CoverBlock` design §3c). E3b owns it.
Every theorem below carries `ka` as a parameter; this numeral is the
landed demo's reading (`CoverBlock.coverPhaseCostB_demo`) and appears
only inside `#guard`s, so that §3's ceilings are concrete. -/
def kaProbe : ℕ := 20

/-- The cover phase's **measured** member coefficient at cover degree
`D`: `(kc + 4) + 162·D − ka`'s aggregate, i.e. what `kcov` charges per
member once the constant is split off. -/
def aCovMeas (D : ℕ) : ℕ := 162 * D + 154

/-- The cover phase's **measured** empty-arena charge: at zero members
and zero emitted members the phase costs the two loop epilogues and the
arena residue, `ka + 12`. Compiled below, not chosen. -/
def bCovMeas (ka : ℕ) : ℕ := ka + 12

/-- **The empty-arena charge is computed, not guessed.** -/
theorem bCovMeas_eq_empty (ka : ℕ) (bw : ℕ → ℕ) :
    Lax3Proofs.Refine.CoverBlock.coverPhaseCostB kcCov ka 0 bw 0 = bCovMeas ka := by
  simp [Lax3Proofs.Refine.CoverBlock.coverPhaseCostB,
    Lax3Proofs.Refine.CoverBlock.coverLoopK, Lax3Proofs.Refine.CoverBlock.memCopyK, bCovMeas]
  omega

/-- **The measured pair sums to the landed weight coefficient.** -/
theorem cov_pair_sum (ka D : ℕ) :
    aCovMeas D + bCovMeas ka = Lax3Proofs.Refine.CoverBlock.kcov kcCov ka D := by
  simp only [aCovMeas, bCovMeas, kcCov, Lax3Proofs.Refine.CoverBlock.kcov]
  omega

/-- **HAZARD, compiled: the measured cover pair does not pay the cover
phase through the M-class slot.**

The M-class phase slot is `∀ m ≤ w, phaseM ac bc m ≤ Kc j w`, i.e. a
demand on `Kc` at the member count. `coverPhaseCostB` is not a function
of the member count: it reads the Σ of the centres' ball weights and the
emitted member count, both of which the mass condition bounds by
`D·(w+1)` and neither of which `mlen` bounds. At `ka = 0`, `D = 1`,
`w = mlen = 1`, one centre of ball weight `2` and `mm = 2` — all three
mass hypotheses of `coverPhaseCostB_le_weight` satisfied — the phase
costs `490` and the slot demands only `328`.

So the `(a, b)` split whose *sum* is `kcov` is a **budget** split, not a
slot; the slot pair has to be `(kcov, kcov)` (below), which is what makes
the demand at `m = w` reach `kcov·(w+1)`. This is the cover twin of the
`30·d` hazard: a phase that reads weights cannot be charged at members. -/
theorem cover_measured_pair_insufficient :
    ¬ (Lax3Proofs.Refine.CoverBlock.coverPhaseCostB kcCov 0 1 (fun _ => 2) 2
        ≤ phaseM (aCovMeas 1) (bCovMeas 0) 1) := by
  decide

-- the two sides of that refutation, cell by cell, and the mass
-- hypotheses it satisfies (`mlen ≤ w`, `Σ bw ≤ D·(w+1)`, `mm ≤ D·(w+1)`)
#guard Lax3Proofs.Refine.CoverBlock.coverPhaseCostB kcCov 0 1 (fun _ => 2) 2 = 490
#guard phaseM (aCovMeas 1) (bCovMeas 0) 1 = 328
#guard (∑ k ∈ range 1, (fun _ => 2) k) ≤ 1 * (1 + 1)
#guard (2 : ℕ) ≤ 1 * (1 + 1)

/-- **The cover slot pair**: the landed weight coefficient in *both*
components, so that the slot's demand at `m = w` is `kcov·(w + 1)` —
exactly the bound `coverPhaseCostB_le_weight` supplies. -/
def aCovSlot (ka D : ℕ) : ℕ := Lax3Proofs.Refine.CoverBlock.kcov kcCov ka D

/-- …and the same in the constant component. -/
def bCovSlot (ka D : ℕ) : ℕ := Lax3Proofs.Refine.CoverBlock.kcov kcCov ka D

/-- **The cover phase is paid by the slot.** Any `Kc` meeting the
M-class cover slot at the slot pair covers the landed measured cover
phase cost, under the three mass hypotheses of
`CoverBlock.coverPhaseCostB_le_weight` (the first two are
`MassWeight.mass_of_alive_compaction_weight`'s conjuncts; the third is
F-2's named open producer). -/
theorem coverPhase_paid_by_slot {ka mlen mm D w Kc : ℕ} {bw : ℕ → ℕ}
    (hslot : ∀ m, m ≤ w → phaseMR (aCovSlot ka D) (bCovSlot ka D) 0 m ≤ Kc)
    (hmlen : mlen ≤ w) (hball : (∑ k ∈ range mlen, bw k) ≤ D * (w + 1))
    (hmm : mm ≤ D * (w + 1)) :
    Lax3Proofs.Refine.CoverBlock.coverPhaseCostB kcCov ka mlen bw mm ≤ Kc := by
  have h := Lax3Proofs.Refine.CoverBlock.coverPhaseCostB_le_weight
    (kc := kcCov) (ka := ka) hmlen hball hmm
  have hw := hslot w le_rfl
  simp only [phaseMR, phaseM, aCovSlot, bCovSlot] at hw
  have hrw : Lax3Proofs.Refine.CoverBlock.kcov kcCov ka D * (w + 1)
      = (1 + 0) * (Lax3Proofs.Refine.CoverBlock.kcov kcCov ka D * w +
          Lax3Proofs.Refine.CoverBlock.kcov kcCov ka D) := by ring
  omega

/-- **Descend / turn — MEASURED at the block WEIGHT.** The four
block-driven leaves of a turn (`BlockLeaves` §3–§5) fit `200·(s + ds + 1)`
at block size `s` and degree sum `ds`; that is
`G2CostProbe.blockLeaves_le_weight`, consumed. -/
def ctBlockLeaves : ℕ := 200

/-- **The turn coefficient — MEASURED, and it is `ctKL`, not `200`.**
R1.8 absorbed the kill-time write and then the kill *list* into the
turn's own size slot; `Refine.KillListPass.ctKL = 284 + klc` is the live
constant and the fits at the empty block are exact in both directions
there. This definition IS the landed constant — no numeral is
transcribed. -/
def ctTurn : ℕ := Lax3Proofs.Refine.KillListPass.ctKL

-- the measured instance, and the two superseded readings it is not
#guard Lax3Proofs.Refine.KillListPass.klc = 159
#guard ctTurn = 443
#guard ¬ (ctTurn = 200)
#guard ¬ (ctTurn = 284)
#guard ctBlockLeaves + 84 + Lax3Proofs.Refine.KillListPass.klc = ctTurn

/-- **HAZARD, compiled: `bexpPass`'s `30·d` does not fit a member-linear
phase form.** `d = degSum` counts the arena slots the block's members
own — edges, not members — so at a fixed member count it is unbounded.
No `(a, b)` absorbs it into `a·m + b`. -/
theorem bexpK_not_memberForm (a b : ℕ) :
    ¬ (∀ m d : ℕ, Lax3Proofs.Refine.BlockLeaves.bexpK m d ≤ phaseM a b m) := by
  intro h
  have h0 := h 0 (b + 1)
  simp only [Lax3Proofs.Refine.BlockLeaves.bexpK, phaseM] at h0
  omega

/-- **…and the turn slot's weight reading is what pays it.**
`turnCostSizeA` is read at `s := blockWeight`, and `blockWeight` is
`blockSize + blockDegSum` exactly
(`MassWeight.blockWeight_eq_add_degSum`), so `s + ds` is the slot's own
argument. `RamDriverRoot.clusterStepAt` already reads the slot there. -/
theorem descendLeaves_le_turnSlot {ct ksc s ds Kin : ℕ} (hct : ctBlockLeaves ≤ ct) :
    Lax3Proofs.Refine.BlockLeaves.blockLoadK s s + Lax3Proofs.Refine.BlockLeaves.bandK s +
        Lax3Proofs.Refine.BlockLeaves.bsubK s + Lax3Proofs.Refine.BlockLeaves.bexpK s ds
      ≤ turnCostSizeA ct ksc (s + ds) Kin := by
  have h := Lax3Proofs.Refine.G2CostProbe.blockLeaves_le_weight s ds
  have hmul : 200 * (s + ds + 1) ≤ (ct + ksc) * (s + ds + 1) :=
    Nat.mul_le_mul_right _ (by simp only [ctBlockLeaves] at hct; omega)
  simp only [turnCostSizeA]
  omega

/-- **The block-weight decomposition, cited.** `MassWeight`'s equality,
in the `≤` direction the Σ bound consumes. -/
theorem block_split_le_weight {n : ℕ} {H : SimpleGraph (Fin n)} {Xoff Xmem : ℕ → ℕ} {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    Lax3Proofs.Refine.MassMath.blockSize Xoff c +
        Lax3Proofs.Refine.MassWeight.blockDegSum n H Xoff Xmem c
      ≤ Lax3Proofs.Refine.MassWeight.blockWeight n H Xoff Xmem c :=
  le_of_eq (Lax3Proofs.Refine.MassWeight.blockWeight_eq_add_degSum H Xoff Xmem hmem).symm

/-- **HAZARD 1, resolved in the affirmative: summed over a level's turns,
the `30·d` terms are inside the Σ interface's mass side condition.**

`g2m_exists`'s level clause quantifies over every `bs` with
`∑_{c<t} bs c ≤ D·(w+1)`, and at the real blocks `bs c` is the block
weight, which is size plus degree sum (`block_split_le_weight`). So the
degree half is charged by the same side condition that charges the size
half, and the four descend leaves summed over the turns cost
`200·(D·(w+1) + t)` — no `n`, and no separate degree budget. -/
theorem descendLeaves_sum_le_mass {t D w : ℕ} {sz dg bs : ℕ → ℕ}
    (hb : ∀ k, sz k + dg k ≤ bs k)
    (hsum : (∑ k ∈ range t, bs k) ≤ D * (w + 1)) :
    (∑ k ∈ range t, (Lax3Proofs.Refine.BlockLeaves.blockLoadK (sz k) (sz k) +
        Lax3Proofs.Refine.BlockLeaves.bandK (sz k) + Lax3Proofs.Refine.BlockLeaves.bsubK (sz k) +
        Lax3Proofs.Refine.BlockLeaves.bexpK (sz k) (dg k)))
      ≤ 200 * (D * (w + 1) + t) := by
  calc (∑ k ∈ range t, (Lax3Proofs.Refine.BlockLeaves.blockLoadK (sz k) (sz k) +
          Lax3Proofs.Refine.BlockLeaves.bandK (sz k) +
          Lax3Proofs.Refine.BlockLeaves.bsubK (sz k) +
          Lax3Proofs.Refine.BlockLeaves.bexpK (sz k) (dg k)))
      ≤ ∑ k ∈ range t, 200 * (bs k + 1) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine le_trans (Lax3Proofs.Refine.G2CostProbe.blockLeaves_le_weight (sz k) (dg k)) ?_
        exact Nat.mul_le_mul_left _ (by have := hb k; omega)
    _ = 200 * (∑ k ∈ range t, (bs k + 1)) := (Finset.mul_sum _ _ _).symm
    _ = 200 * ((∑ k ∈ range t, bs k) + t) := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ 200 * (D * (w + 1) + t) := Nat.mul_le_mul_left _ (by omega)

/-- **Dead, member coefficient — ZERO.** Wave R1.8-T3-flip took
`RamDriver.sweepCom` out of the driver's program: the level's
postcondition is `TableInvOn` at `alive ∪ D` and the kills are written
at kill time, inside the turn. There is no per-level dead pass left to
charge at the member count. -/
def aDead : ℕ := 0

/-- **Dead, per-level residue — OPAQUE.** What remains per level is
`O(1)` bookkeeping (the outside count and the default bit ride the
turn). The landed closures `DeadRowProbe.deadRow_interface_closes` and
`KillListPass.killList_interface_closes` read it at `12`; that number is
a chosen residue with no measured leaf under it, so every theorem below
carries it as a parameter and this numeral appears only in `#guard`s. -/
def bDeadProbe : ℕ := 12

/-- **Scatter leaf — OPAQUE, and E4c's deliverable.** `ksc` bounds the
per-level scatter charge `Ksc j` that rides `turnCostSizeA`'s size slot.
At the landed instantiation it is not a constant at all — §4's
`landed_scatter_leaf_unbounded`. This numeral is the landed probe's
placeholder, used only to make §2's and §3's numerics concrete. -/
def kscProbe : ℕ := 10 ^ 4

/-- **Base coefficient — OPAQUE. This is the known hole (T4b).** No wave
has measured the base level. Worse than unmeasured: §4's
`landed_base_needs_carrier_Cb` shows the landed `hKbase` slot admits no
constant at all. -/
def CbProbe : ℕ := 10 ^ 4

/-- **Root sentence charge — OPAQUE.** The root's `hKsent` slot bounds a
finite list of atom charges plus the sentence expression's size; both
are determined by `φ` before `n`, but no wave has measured the
coefficient. -/
def ksentProbe : ℕ := 10 ^ 4

/-- **Root decode charge — MEASURED at `87`**
(`G2ExistsRevalidation.decodeDLCost_le_weight`, rebase E-mem). -/
def kdecRoot : ℕ := 87

theorem kdecRoot_measured (n ns : ℕ) :
    Lax3Proofs.Refine.DriverRootD.decodeDLCost n ns ≤ kdecRoot * (n + ns + 1) :=
  Lax3Proofs.Refine.G2ExistsRevalidation.decodeDLCost_le_weight n ns

/-! ### §2 The assembled close

`g2m_exists` at the measured constants, `rootBudgetM_closes` on top of
it, and `mclass_c0_shape` to carry the root budget into `n^{1+ε}`.

**One correction to the landed §3's arithmetic is forced here.**
`mclass_c0_shape` takes the root's coefficient `C` as a constant and the
cover degree as `D = ⌈c·w^{ε/ℓ}⌉₊`, which GROWS with `w`. But
`rootBudgetM`'s own `C = ℓ·g2M + Cb` is not `D`-free: `g2M` contains
`(ct + ksc + 3)·(D + 1)`, and the cover slot pair contains `162·D`. So
the landed §3 gates, which fix `D = 8`, cannot be read as instances of
the shape theorem at a growing `D`. `rootBudgetM_le_cstar` repairs it by
absorbing the one extra `(D + 1)`: the honest exponent budget is
`ℓ + 1`, i.e. the cover degree must be read at `⌈c·w^{ε/(ℓ+1)}⌉₊`. -/

/-- The `D`-free part of the per-level constant. -/
def g2Const (ao bo kcC ad bd R ct ksc : ℕ) : ℕ :=
  (1 + R) * (ao + bo) + (kcC + (ad + bd)) + (ct + ksc + 3) + 14

/-- **The `D`-free root constant.** `cstarM` is what `mclass_c0_shape`
may legitimately be applied at, once the extra `(D + 1)` is absorbed. -/
def cstarM (ℓ Cb ao bo kcC ad bd R ct ksc kdec ksent : ℕ) : ℕ :=
  kdec + ksent + Cb + ℓ * g2Const ao bo kcC ad bd R ct ksc

/-- **The cover slot pair is `(D + 1)`-linear at a `D`-free
coefficient** — which is what lets the root constant be `D`-free at
exponent `ℓ + 1`. -/
def kcovC (ka : ℕ) : ℕ := 2 * (kcCov + ka + 28)

theorem cov_slot_le_kcovC (ka D : ℕ) : aCovSlot ka D + bCovSlot ka D ≤ kcovC ka * (D + 1) := by
  simp only [aCovSlot, bCovSlot, kcovC, kcCov, Lax3Proofs.Refine.CoverBlock.kcov]
  nlinarith [Nat.zero_le (ka * D), Nat.zero_le D, Nat.zero_le ka]

/-- **The root budget is `D`-free at exponent `ℓ + 1`.** Every summand
of `g2M` is either already `(D + 1)`-linear or bounded by its own
coefficient times `(D + 1)`, so one extra factor absorbs the whole
`D`-dependence and `cstarM` is a constant of the parameters alone. -/
theorem rootBudgetM_le_cstar {ℓ Cb ao bo ac bc kcC ad bd R ct ksc D kdec ksent : ℕ}
    (hcov : ac + bc ≤ kcC * (D + 1)) :
    rootBudgetM ℓ Cb ao bo ac bc ad bd R ct ksc D kdec ksent
      ≤ cstarM ℓ Cb ao bo kcC ad bd R ct ksc kdec ksent * (D + 1) ^ (ℓ + 1) := by
  have hD : 0 < D + 1 := Nat.succ_pos _
  have hg : g2M ao bo ac bc ad bd R ct ksc D ≤ g2Const ao bo kcC ad bd R ct ksc * (D + 1) := by
    have h1 : (1 + R) * (ao + bo) ≤ (1 + R) * (ao + bo) * (D + 1) :=
      Nat.le_mul_of_pos_right _ hD
    have h3 : ad + bd ≤ (ad + bd) * (D + 1) := Nat.le_mul_of_pos_right _ hD
    have h4 : (14 : ℕ) ≤ 14 * (D + 1) := Nat.le_mul_of_pos_right _ hD
    have hexp : g2Const ao bo kcC ad bd R ct ksc * (D + 1)
        = (1 + R) * (ao + bo) * (D + 1) + kcC * (D + 1) + (ad + bd) * (D + 1) +
            (ct + ksc + 3) * (D + 1) + 14 * (D + 1) := by
      simp only [g2Const]; ring
    simp only [g2M]
    omega
  have hmain : kdec + ksent + (ℓ * g2M ao bo ac bc ad bd R ct ksc D + Cb)
      ≤ cstarM ℓ Cb ao bo kcC ad bd R ct ksc kdec ksent * (D + 1) := by
    have hg' : ℓ * g2M ao bo ac bc ad bd R ct ksc D
        ≤ ℓ * (g2Const ao bo kcC ad bd R ct ksc * (D + 1)) := Nat.mul_le_mul_left _ hg
    have hb : kdec + ksent + Cb ≤ (kdec + ksent + Cb) * (D + 1) :=
      Nat.le_mul_of_pos_right _ hD
    have hrhs : cstarM ℓ Cb ao bo kcC ad bd R ct ksc kdec ksent * (D + 1)
        = (kdec + ksent + Cb) * (D + 1) +
            ℓ * (g2Const ao bo kcC ad bd R ct ksc * (D + 1)) := by
      simp only [cstarM]; ring
    omega
  calc rootBudgetM ℓ Cb ao bo ac bc ad bd R ct ksc D kdec ksent
      = (kdec + ksent + (ℓ * g2M ao bo ac bc ad bd R ct ksc D + Cb)) * (D + 1) ^ ℓ := rfl
    _ ≤ (cstarM ℓ Cb ao bo kcC ad bd R ct ksc kdec ksent * (D + 1)) * (D + 1) ^ ℓ :=
        Nat.mul_le_mul_right _ hmain
    _ = cstarM ℓ Cb ao bo kcC ad bd R ct ksc kdec ksent * (D + 1) ^ (ℓ + 1) := by ring

/-- The C0 cover degree, at the honest exponent budget `ℓ + 1`. -/
noncomputable def coverDeg (c ε : ℝ) (ℓ w : ℕ) : ℕ := ⌈c * (w : ℝ) ^ (ε / ((ℓ + 1 : ℕ) : ℝ))⌉₊

/-- **The real-exponent close.** The root budget, read at the cover
degree `⌈c·w^{ε/(ℓ+1)}⌉₊`, is inside `n^{1+ε}` at a constant
`cstarM·(c+2)^{ℓ+1}`. `mclass_c0_shape` is consumed at `ℓ + 1`; nothing
is re-derived. -/
theorem c0_shape_real {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    {ℓ Cb ao bo ac bc kcC ad bd R ct ksc kdec ksent w K : ℕ} (hw : 1 ≤ w)
    (hcov : ac + bc ≤ kcC * (coverDeg c ε ℓ w + 1))
    (hK : K ≤ rootBudgetM ℓ Cb ao bo ac bc ad bd R ct ksc (coverDeg c ε ℓ w) kdec ksent * (w + 1)) :
    (K : ℝ) ≤ ((cstarM ℓ Cb ao bo kcC ad bd R ct ksc kdec ksent : ℝ) * (c + 2) ^ (ℓ + 1))
      * ((w : ℝ) + 1) ^ (1 + ε) := by
  refine mclass_c0_shape (ℓ := ℓ + 1) hc hε (by omega) hw ?_
  refine le_trans hK ?_
  exact Nat.mul_le_mul_right _ (rootBudgetM_le_cstar hcov)

/-- **The assembled close, at the measured constants.**

The M-class phase slots at the order phase's measured `68`/`12`, the
cover phase's measured `kcov 150 ka D` slot pair, the dead phase's
post-R1.8 `(0, bd)` and the turn at the measured `ctTurn = ctKL`; the
landed Σ-interface shapes of `RamDriverRoot.driverRoot_decides_sentence`
verbatim; the cover phase's own measured cost paid; and the restated
root's cost text inside `cstarM · (D+1)^{ℓ+1} · (|x|+1)`.

**The named condition `hKsc` is E4c's deliverable and nothing else.**
It asks for a per-level scatter charge bounded by a constant chosen
before `n`. §4 compiles that the LANDED instantiation — the whole
carrier as the ball budget, `Refine.ScatterDeadPass.ballBudget_carrier` —
does not supply one. Everything else in this theorem is measured. -/
theorem c0_close_at_measured {ka bd Cb ksent kscN R ℓ D : ℕ} (Ksc : ℕ → ℕ)
    (hKsc : ∀ j < ℓ, Ksc j ≤ kscN) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      -- the M-class phase slots, at each phase's own measured constants
      (∀ j w m, m ≤ w → phaseMR aOrd bOrd R m ≤ Ko j w) ∧
      (∀ j w m, m ≤ w → phaseMR (aCovSlot ka D) (bCovSlot ka D) 0 m ≤ Kc j w) ∧
      (∀ j w m, m ≤ w → phaseMR aDead bd 0 m ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl ℓ w) ∧
      -- the landed Σ-interface shapes, verbatim
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < ℓ, ∀ s : ℕ, turnCostSizeA ctTurn (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
      (∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ range t, bs c) ≤ D * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      -- the cover phase's measured cost is actually paid
      (∀ j w mlen mm : ℕ, ∀ bw : ℕ → ℕ, mlen ≤ w →
        (∑ k ∈ range mlen, bw k) ≤ D * (w + 1) → mm ≤ D * (w + 1) →
        Lax3Proofs.Refine.CoverBlock.coverPhaseCostB kcCov ka mlen bw mm ≤ Kc j w) ∧
      -- the restated root's cost text, inside the D-free closed form
      (∀ Kdec Ksent : ℕ → ℕ → ℕ, ∀ n ns nsd : ℕ, nsd ≤ ns →
        Kdec n ns ≤ kdecRoot * (n + ns + 1) → Ksent n ns ≤ ksent * (n + ns + 1) →
        Kdec n ns + (Kl 0 (n + nsd) + Ksent n ns)
          ≤ cstarM ℓ Cb aOrd bOrd (kcovC ka) aDead bd R ctTurn kscN kdecRoot ksent
              * (D + 1) ^ (ℓ + 1) * (n + ns + 1)) := by
  obtain ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKc, hKd, hbase, hmono, hKs, hKlS, hcl⟩ :=
    g2m_exists ℓ D Cb R aOrd bOrd (aCovSlot ka D) (bCovSlot ka D) aDead bd ctTurn kscN Ksc hKsc
  refine ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKc, hKd, hbase, hmono, hKs, hKlS, ?_, ?_⟩
  · exact fun j w mlen mm bw h1 h2 h3 =>
      coverPhase_paid_by_slot (fun m hm => hKc j w m hm) h1 h2 h3
  · intro Kdec Ksent n ns nsd hns hdec hsent
    refine le_trans (rootBudgetM_closes (ksent := ksent) hns (hmono 0) hdec hsent hcl) ?_
    exact Nat.mul_le_mul_right _ (rootBudgetM_le_cstar (cov_slot_le_kcovC ka D))

/-! #### The gates at the measured constants

The instance family is `C0Probe`'s own: sparse members, `|x| = 3·n + 3`,
the star carrier `ns = 2·(n − 1)`, `R = 0`, `D = 8`, `ℓ = 3`, all
constants chosen before `n`. What changed against
`G2ExistsRevalidation` §3 is the *constants*: the cover slot at
`kcov 150 20 8 = 1482` twice instead of a borrowed `68`/`12`, the dead
slot at `(0, 12)` instead of a borrowed `68`/`12`, and the turn at the
measured `443` instead of the pre-R1.8 `200`. -/

-- the per-level constant at the measured family, cell by cell
#guard g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead bDeadProbe 0
    ctTurn kscProbe 8
  = (1 + 0) * (68 + 12) + (((1482 + 1482) + (0 + 12)) + ((443 + 10 ^ 4 + 3) * 9 + 14))
#guard g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead bDeadProbe 0
    ctTurn kscProbe 8 = 97084

-- …and the root budget it induces. The borrowed-constant reading is
-- BELOW it: the landed §3 gate was optimistic by the cover and turn
-- deltas together.
#guard rootBudgetM 3 CbProbe aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
    bDeadProbe 0 ctTurn kscProbe 8 kdecRoot ksentProbe = 226966131
#guard rootBudgetM 3 (10 ^ 4) 68 12 68 12 68 12 0 200 (10 ^ 4) 8 87 (10 ^ 4)
  < rootBudgetM 3 CbProbe aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
      bDeadProbe 0 ctTurn kscProbe 8 kdecRoot ksentProbe

/-- The star instance's arena weight at carrier `n`: `n + 2·(n − 1)`. -/
def starW (n : ℕ) : ℕ := n + 2 * (n - 1)

/-- The measured family's root budget at level count `ℓ`, cover degree
`D` and scatter coefficient `ksc`. -/
def budgetAt (ℓ D ksc : ℕ) : ℕ :=
  rootBudgetM ℓ CbProbe aOrd bOrd (aCovSlot kaProbe D) (bCovSlot kaProbe D) aDead
    bDeadProbe 0 ctTurn ksc D kdecRoot ksentProbe

-- **ε = 1** at `c = 10⁹`, `n = 10⁹` (`C0Probe`'s first guard, the one
-- the landed root's cubic floor lost)
#guard budgetAt 3 8 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2

-- **ε = 1/2** at `c = 10⁷`, `n = 10⁸`, in `C0Probe`'s squared form
#guard (budgetAt 3 8 kscProbe * (starW (10 ^ 8) + 1)) ^ 2
  ≤ (10 ^ 7) ^ 2 * (3 * 10 ^ 8 + 4) ^ 3

-- **ε = 1/4** at `c = 10¹⁰`, `n = 10⁸`, in the fourth-power form
#guard (budgetAt 3 8 kscProbe * (starW (10 ^ 8) + 1)) ^ 4
  ≤ (10 ^ 10) ^ 4 * (3 * 10 ^ 8 + 4) ^ 5

-- **the rounds are affordable**: `R = 4` augment/relink rounds move the
-- order phase by a factor on a constant, not on the carrier
#guard rootBudgetM 3 CbProbe aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
    bDeadProbe 4 ctTurn kscProbe 8 kdecRoot ksentProbe * (starW (10 ^ 9) + 1)
  ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2

/-! #### Sensitivity in `ℓ` and `D` (hazard 5)

`ℓ` is the splitter round count `N (2s + 2)` and `D` is the cover degree
`Kmass = ⌈c·n^δ⌉` — neither is `3` or `8` in any instance the theorem is
about. The two must move TOGETHER: C0 fixes `δ = ε/(ℓ+1)`, so a larger
`ℓ` is a smaller `D`. Held apart, the gate collapses; held at the C0
pairing, it does not. -/

-- at a FIXED `D = 8` the ε = 1 gate dies between `ℓ = 12` and `ℓ = 15` —
-- so the landed `(ℓ, D) = (3, 8)` pairing is not evidence at realistic `ℓ`
#guard budgetAt 12 8 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2
#guard ¬ (budgetAt 15 8 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2)

-- …and at the C0 pairing `D ≈ ⌈w^{1/(ℓ+1)}⌉` it survives at every round
-- count checked, because the round count buys the degree back
#guard budgetAt 3 1443 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2
#guard budgetAt 5 79 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2
#guard budgetAt 10 9 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2
#guard budgetAt 20 3 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2

-- the `D`-only sensitivity at `ℓ = 3`: the geometric factor buys three
-- more orders of cover degree and then stops
#guard budgetAt 3 1024 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2
#guard ¬ (budgetAt 3 4096 kscProbe * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2)

/-! ### §3 The ceiling — a number for each remaining wave

Each ceiling is the largest value of ONE constant that still clears the
gate with every other constant at its measured value, pinned in both
directions: the ceiling clears, the ceiling plus one does not. The
binding gate is ε = 1/2 (`c = 10⁷`, `n = 10⁸`); ε = 1 and ε = 1/4 are
recorded for the shape of the dependence.

| constant | wave | measured / landed | ceiling at ε = 1/2 | margin |
|---|---|---|---|---|
| `aOrd` | E-order | `68` | `79 093 857` | ×10⁶ |
| `ka` | E3b | unmeasured | `39 546 914` | — |
| `bd` | `hKd` deletion | `12` (chosen) | `79 093 801` | ×10⁶ |
| `ctTurn` | E4c descend | `443` | `8 788 641` | ×10⁴ |
| `ksc` | **E4c scatter** | `131·n + …` | `8 798 198` | **DEFICIT ×1489 at `n = 10⁸`, and growing** |
| `Cb` | T4b | none | `237 291 369` | — |
| `ksentProbe` | — | none | `237 291 369` | — |
| `R` | E-order | unmeasured | `988 672` | — |

`ksc` is the only entry whose measured value is above its ceiling, and
it is the only one whose measured value is not a constant. -/

/-- The ε = 1/2 gate, as a predicate on a root budget. -/
def gateHalf (b : ℕ) : Prop := (b * (starW (10 ^ 8) + 1)) ^ 2 ≤ (10 ^ 7) ^ 2 * (3 * 10 ^ 8 + 4) ^ 3

instance : DecidablePred gateHalf := fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- The measured family at ε = 1/2, with one constant free. -/
def famHalf (ao ka bd ct ksc Cb ksent R : ℕ) : ℕ :=
  rootBudgetM 3 Cb ao bOrd (aCovSlot ka 8) (bCovSlot ka 8) aDead bd R ct ksc 8 kdecRoot ksent

/-- The measured reading of every constant at once. -/
def famHalfMeasured : ℕ := famHalf aOrd kaProbe bDeadProbe ctTurn kscProbe CbProbe ksentProbe 0

#guard famHalfMeasured = 226966131
#guard gateHalf famHalfMeasured

-- **`aOrd` — E-order.** Measured `68`; ceiling `79 093 857`.
#guard gateHalf (famHalf 79093857 kaProbe bDeadProbe ctTurn kscProbe CbProbe ksentProbe 0)
#guard ¬ gateHalf (famHalf 79093858 kaProbe bDeadProbe ctTurn kscProbe CbProbe ksentProbe 0)
#guard aOrd < 79093857

-- **`ka` — E3b's cover residue.** Unmeasured; ceiling `39 546 914`.
#guard gateHalf (famHalf aOrd 39546914 bDeadProbe ctTurn kscProbe CbProbe ksentProbe 0)
#guard ¬ gateHalf (famHalf aOrd 39546915 bDeadProbe ctTurn kscProbe CbProbe ksentProbe 0)

-- **`bd` — the dead residue / `hKd` slot.** Landed reading `12`;
-- ceiling `79 093 801`.
#guard gateHalf (famHalf aOrd kaProbe 79093801 ctTurn kscProbe CbProbe ksentProbe 0)
#guard ¬ gateHalf (famHalf aOrd kaProbe 79093802 ctTurn kscProbe CbProbe ksentProbe 0)

-- **`ct` — E4c's descend leaves plus R1.8's kill writes.** Measured
-- `443`; ceiling `8 788 641`.
#guard gateHalf (famHalf aOrd kaProbe bDeadProbe 8788641 kscProbe CbProbe ksentProbe 0)
#guard ¬ gateHalf (famHalf aOrd kaProbe bDeadProbe 8788642 kscProbe CbProbe ksentProbe 0)
#guard ctTurn < 8788641

-- **`ksc` — E4c's scatter leaf. The one deficit.** Ceiling `8 798 198`;
-- the landed reading at `n = 10⁸` is at least `131·10⁸ + 96`, which is
-- a factor `1488` over it. §4 compiles the lower bound.
#guard gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn 8798198 CbProbe ksentProbe 0)
#guard ¬ gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn 8798199 CbProbe ksentProbe 0)
#guard ¬ gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn (131 * 10 ^ 8 + 96) CbProbe
  ksentProbe 0)
#guard 1488 * 8798198 ≤ 131 * 10 ^ 8 + 96

-- **`Cb` — T4b's base.** No measurement; ceiling `237 291 369`.
#guard gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn kscProbe 237291369 ksentProbe 0)
#guard ¬ gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn kscProbe 237291370 ksentProbe 0)

-- **`ksent` — the root's sentence charge.** No measurement; same
-- ceiling as `Cb`, since both are additive at the root.
#guard gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn kscProbe CbProbe 237291369 0)
#guard ¬ gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn kscProbe CbProbe 237291370 0)

-- **`R` — E-order's augment/relink rounds.** Ceiling `988 672`.
#guard gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn kscProbe CbProbe ksentProbe 988672)
#guard ¬ gateHalf (famHalf aOrd kaProbe bDeadProbe ctTurn kscProbe CbProbe ksentProbe 988673)

/-- The ε = 1 gate, for the record: at a quadratic budget every ceiling
is seven orders looser, which is why the landed §3 guards — all at
ε = 1 — could not see the scatter deficit. -/
def gateOne (b : ℕ) : Prop := b * (starW (10 ^ 9) + 1) ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2

instance : DecidablePred gateOne := fun _ => inferInstanceAs (Decidable (_ ≤ _))

def famOne (ksc : ℕ) : ℕ :=
  rootBudgetM 3 CbProbe aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
    bDeadProbe 0 ctTurn ksc 8 kdecRoot ksentProbe

-- the ε = 1 ceiling on `ksc`, and the fact the landed carrier-charged
-- reading at `n = 10⁹` clears it — the gate is blind here
#guard gateOne (famOne 152415790731588)
#guard ¬ gateOne (famOne 152415790731589)
#guard gateOne (famOne (131 * 10 ^ 9 + 96))

-- the ε = 1/4 ceilings, for the two constants that bind
#guard ((famHalf aOrd kaProbe bDeadProbe 66852400 kscProbe CbProbe ksentProbe 0 *
    (starW (10 ^ 8) + 1)) ^ 4 ≤ (10 ^ 10) ^ 4 * (3 * 10 ^ 8 + 4) ^ 5)
#guard ¬ ((famHalf aOrd kaProbe bDeadProbe 66852401 kscProbe CbProbe ksentProbe 0 *
    (starW (10 ^ 8) + 1)) ^ 4 ≤ (10 ^ 10) ^ 4 * (3 * 10 ^ 8 + 4) ^ 5)
#guard ((famHalf aOrd kaProbe bDeadProbe ctTurn 66861957 CbProbe ksentProbe 0 *
    (starW (10 ^ 8) + 1)) ^ 4 ≤ (10 ^ 10) ^ 4 * (3 * 10 ^ 8 + 4) ^ 5)
#guard ¬ ((famHalf aOrd kaProbe bDeadProbe ctTurn 66861958 CbProbe ksentProbe 0 *
    (starW (10 ^ 8) + 1)) ^ 4 ≤ (10 ^ 10) ^ 4 * (3 * 10 ^ 8 + 4) ^ 5)

/-! ### §4 The honesty controls

Four compiled refutations, each naming a wave that is load-bearing
rather than decorative. The pattern is `Refine.CostShapeProbe`'s: state
what the landed object costs, and show no constant of the interface
covers it. -/

/-- **The empty-arena floor, once for all four phase slots.** Any phase
slot bounded below by a quantity `F` that the arena does not read forces
`t·F` at the root over the root level's `t` turns — the mechanism of
`C0Probe.level_interface_floor`, re-read through the M-class Σ shape.
`F` is a parameter, so each control below supplies it from its own
slot. -/
theorem nested_slot_floor {F n ns ℓ D ct : ℕ} {Ksc : ℕ → ℕ}
    {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hℓ : 2 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ s : ℕ, turnCostSizeA ct (Ksc j) s (Kl (j + 1) s) ≤ Ks j s)
    (hF : F ≤ Ko 1 0 + (Kc 1 0 + Kd 1 0))
    (hKl : ∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
      (∑ c ∈ range t, bs c) ≤ D * (w + 1) →
      Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j w) :
    n * F ≤ Kl 0 (n + ns) := by
  have h10 : F ≤ Kl 1 0 := by
    have h := hKl 1 (by omega) 0 0 le_rfl (fun _ => 0) (by simp)
    simp only [Finset.range_zero, Finset.sum_empty] at h
    omega
  have hks : Kl 1 0 ≤ Ks 0 0 := by
    have h := hKs 0 (by omega) 0
    simp only [Nat.zero_add, turnCostSizeA] at h
    omega
  have h0 := hKl 0 (by omega) (n + ns) n (by omega) (fun _ => 0) (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h0
  calc n * F ≤ n * (Ks 0 0 + 11) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ Kl 0 (n + ns) := by omega

/-! #### Control 1 — the scatter leaf is carrier-charged (E4c)

`RamDriverRoot.clusterStepAt` instantiates the atom's ball budget with
`Refine.ScatterDeadPass.ballBudget_carrier`, which supplies the WHOLE
carrier: `bw := ns`, `nb := n`, and `mm1 = mm = n`. Five summands of
`ScatterDeadPass.scatDeadK` are then carrier-width — the outside probe,
the atom's member filter, the two calling-convention copies and the
engine's own member scan — for `131·n` before any pick is charged. -/

/-- **The landed per-atom charge is at least `131·n`.** -/
theorem scatDeadK_carrier_floor {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (n mb ns t : ℕ) :
    131 * n ≤ Lax3Proofs.Refine.ScatterDeadPass.scatDeadK β n n mb n ns n t := by
  simp only [Lax3Proofs.Refine.ScatterDeadPass.scatDeadK,
    Lax3Proofs.Refine.ScatterDeadPass.outProbeCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomMemCost,
    Lax3Proofs.Refine.ScatterDeadPass.outCntCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomFlagCost,
    Lax3Proofs.Refine.ScatterDeadPass.killSumCost,
    Lax3Proofs.Refine.ScatterBlock.scatBlockK_eq]
  omega

/-- …and so is the atom the driver actually charges. -/
theorem deadAtomK_carrier_floor {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (n mb ns t : ℕ) :
    131 * n ≤ Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n n mb n ns n t := by
  have h := scatDeadK_carrier_floor β n mb ns t
  simp only [Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK]
  omega

/-- **THE HEADLINE REFUTATION: no constant `ksc` exists at the landed
ball budget.** `hbnd` forces `Kb` above the per-atom charge, `hcostI`
forces `Ki ≥ Kb·(#atoms) + 1` and `hKsc` forces `Ksc j ≥ Ki·(#tables) + 1`;
with either list nonempty the chain gives `Ksc j ≥ deadAtomK`, which is
`Ω(n)`. So `c0_close_at_measured`'s `hKsc` — a bound by a constant
chosen before `n` — is unsatisfiable at what is landed.

**Wave E4c-a: the residual did not move, and that is the result.** The
statement below is at the landed reading `n n mb n ns n` and stays at
`131·n`, because none of the three narrowings E4c-a was asked for can be
*expressed* at this instantiation: `hbnd` fixes `Kb` before the turn's
cluster exists, so a cluster-scale charge has nowhere to be written.
Control 1b is the compiled ceiling and `narrow_leaf_refutes_constant_ksc`
the refutation that survives every narrowing. -/
theorem landed_scatter_leaf_unbounded {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (ksc mb ns t : ℕ) :
    ∃ n : ℕ, ¬ (Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n n mb n ns n t ≤ ksc) := by
  refine ⟨ksc + 1, fun h => ?_⟩
  have := deadAtomK_carrier_floor β (ksc + 1) mb ns t
  omega

/-- **The chain from the atom charge to `Ksc`.** The two list lengths
are `(bcAtomsOf …).2.length` and `(tablesAt …).length`; the hypothesis
is that neither is empty, which is exactly the case where the level runs
an atom at all. -/
theorem ksc_ge_atom {Kb Ki Ksc la lt : ℕ} (hla : 1 ≤ la) (hlt : 1 ≤ lt)
    (hcostI : Kb * la + 1 ≤ Ki) (hKsc : Ki * lt + 1 ≤ Ksc) : Kb ≤ Ksc := by
  have h1 : Kb ≤ Kb * la := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : Ki ≤ Ki * lt := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-! #### Control 1b — the accounting ceiling, and what is left under it (E4c-a)

Wave E4c-a asked how much of the `131·n` above comes off **without
touching program text**. The answer is read off the closed form below.
`deadAtomK`'s five carrier summands split into two classes:

| summand | coefficient | class |
|---|---|---|
| `outProbeCost n` — the outside probe's scan | `20` | accounting: the scan stops at the first out-of-cluster vertex, and `Refine.ScatterDeadPass.outProbeCom_specB` charges the same program text at `min (xb + 1) n` |
| `atomMemCost n` — the atom's member filter | `23` | accounting: the walk is over the child's member list, whose length is the *cluster's*, not the carrier's |
| `scatBlockK`'s `65·mm` — the engine's two member walks | `65` | accounting: `mm` is the filtered list's length |
| `12·n + 6` — the mask copy | `12` | **program text** |
| `11·n + 6` — the distance fill | `11` | **program text** |

So the accounting ceiling is `108·n + 18`, and the residual any
accounting wave leaves behind is `23·n + 12` — the two
calling-convention copies, which are `RamDriver.scatDeadCom`'s own text
and cannot be re-charged, only rewritten over the member list.

`narrow_leaf_refutes_constant_ksc` compiles the consequence: **even a
perfect accounting wave does not produce §2's constant `ksc`.** And the
narrowing that the accounting ceiling *does* reach is the cluster's
size, not a constant — the reading `RamDriverRoot.clusterStepAt` grants
is uniform in the turn's cluster (`hbnd` fixes `Kb` before `X` exists),
so a cluster-scale charge cannot be stated there at all. Cashing it
needs the turn's **size slot** — `RamDriverRoot.turnCostSize` discards
its size argument today (`turnCostSize_size_blind`, `SlotSweep` control
4) while `G2CostProbe.turnCostSizeA` reads it — which is B4's, not
E4c's. -/

/-- **The landed per-atom charge in closed form**, at the root's own
instantiation. Two of its terms are opaque and neither reads the
carrier: `killSumCost mb` is the batch width, a formula constant, and
`atomBitCost β` is the generated evaluator's fragment. -/
theorem deadAtomK_root_eq {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (n mb ns t : ℕ) :
    Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n n mb n ns n t
      = (44 * ns + 110 * n + 140) * t + 131 * n + 14 * mb +
        Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 90 := by
  simp only [Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK,
    Lax3Proofs.Refine.ScatterDeadPass.scatDeadK,
    Lax3Proofs.Refine.ScatterDeadPass.outProbeCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomMemCost,
    Lax3Proofs.Refine.ScatterDeadPass.outCntCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomFlagCost,
    Lax3Proofs.Refine.ScatterDeadPass.killSumCost,
    Lax3Proofs.Refine.ScatterBlock.scatBlockK_eq]
  ring

/-- **The accounting ceiling**: the three in-scope summands are exactly
`108·n + 18` of the `131·n` floor. -/
theorem scatter_leaf_accounting_ceiling (n : ℕ) :
    Lax3Proofs.Refine.ScatterDeadPass.outProbeCost n +
        Lax3Proofs.Refine.ScatterDeadPass.atomMemCost n + 65 * n = 108 * n + 18 := by
  simp only [Lax3Proofs.Refine.ScatterDeadPass.outProbeCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomMemCost]
  omega

/-- **The residual, at any narrowing whatsoever.** The mask copy and the
distance fill are carrier walks in `RamDriver.scatDeadCom`'s text, so
`23·n + 12` survives every choice of the probe bound, the two member
counts and the ball budget. This is the compiled statement of which
`n`-terms remain when E4c is done. -/
theorem scatDeadK_narrow_floor {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (n mm1 kq mm bw nb t : ℕ) :
    23 * n + 12 ≤ Lax3Proofs.Refine.ScatterDeadPass.scatDeadK β n mm1 kq mm bw nb t := by
  simp only [Lax3Proofs.Refine.ScatterDeadPass.scatDeadK]
  omega

theorem deadAtomK_narrow_floor {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (n mm1 kq mm bw nb t : ℕ) :
    23 * n + 12 ≤ Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n mm1 kq mm bw nb t := by
  have h := scatDeadK_narrow_floor β n mm1 kq mm bw nb t
  simp only [Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK]
  omega

/-! #### Control 1c — E4c-b: what the copies cost at the member list, and
why they are still in the program

Wave E4c-b built the two touched-only replacements
(`Refine.ScatterDeadPass` §5f: `memCopyAt` at `15·mm1 + 6`, `memFillAt`
at `14·mm1 + 6`, clocked carrier-blind on the executable semantics
against the landed passes as the growing control) and **could not wire
either into the atom**. The residual below therefore does not move, and
the two reasons are compiled next door:

* the mask copy needs `"alv"` zero off the child's alive set, and `"alv"`
  is a `RamDriverFrames.scratchArrs` entry — `RamDriver.LevelMem` gives
  its *length* only, the turn's descent, the level's cover phase and the
  nested driver all scribble on it, and
  `ScatterDeadPass.alv_touched_only_needs_clean_scratch` runs the pass
  from the state that actually arrives and exhibits a dead vertex left
  alive — and `ScatterDeadPass.mask_junk_flips_the_engine` compiles that
  the leftover is *semantic*: the engine's own flag moves from `1` to
  `0` when only the off-support mask cells change. Supplying that
  invariant is the driver-wide clean-scratch discipline, R1.6, and
  `per_turn_copy_escapes_size_slot` below is why moving the pass to the
  turn is not a way around it;
* the distance fill cannot produce `Refine.ScatterBlock.ArenaA`'s
  seventh clause at all, at any caller discipline: the clause is the
  *whole* array at the atom's own radius, consecutive atoms of a turn
  carry different radii, and
  `ScatterDeadPass.dist_touched_only_refuted` is that gap on data. The
  clause would have to narrow to the mask's support first, which is the
  engine's contract (`Refine.BfsBlock.unwind_run` restores the array as
  a literal list over every `i < n`).

What the wave does deliver to B4 execution is the **arithmetic of the
post-wiring charge**, modelled below with no landed definition touched:
`23·n + 12` would become `43·mm1 + 18`, the surviving carrier term would
be exactly the outside probe's `20·n + 10` — whose narrowing is
accounting, `ScatterDeadPass.outProbeCostB` — and the cluster reading
would fit the same `atomCoeff` shape, with `131` moving to `151` and the
constant to `96`, both still inside `221`. -/

/-- **The per-atom charge with the two copies at the member list.** The
model of E4c-b's success: `ScatterDeadPass.scatDeadK`'s nine summands
with the mask copy, its restore and the distance fill replaced by
`ScatterDeadPass.entryMemCost`, plus the fold's flag assignment. Nothing
landed is edited — this is `Refine.B4Design`'s house style, one file
down. -/
noncomputable def deadAtomKB {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (n mm1 kq mm bw nb t : ℕ) : ℕ :=
  Lax3Proofs.Refine.ScatterDeadPass.killSumCost kq +
      Lax3Proofs.Refine.ScatterDeadPass.outProbeCost n +
      Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β +
      Lax3Proofs.Refine.ScatterDeadPass.outCntCost +
      Lax3Proofs.Refine.ScatterDeadPass.atomMemCost mm1 +
      Lax3Proofs.Refine.ScatterDeadPass.entryMemCost mm1 +
      Lax3Proofs.Refine.ScatterBlock.scatBlockK mm bw nb t +
      Lax3Proofs.Refine.ScatterDeadPass.atomFlagCost + 2

/-- **The model in closed form.** Against `deadAtomK_root_eq`'s landed
`43·n + 23·mm1 + … + 90`: the carrier coefficient falls to the probe's
`20`, the child's member count carries `66`, and the constant is `96` —
six more, the extra pass's own head. -/
theorem deadAtomKB_closed {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (n mm1 kq mm bw nb t : ℕ) :
    deadAtomKB β n mm1 kq mm bw nb t
      = (44 * bw + 110 * nb + 140) * t + 20 * n + 66 * mm1 + 65 * mm + 14 * kq +
        Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 96 := by
  simp only [deadAtomKB, Lax3Proofs.Refine.ScatterDeadPass.outProbeCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomMemCost,
    Lax3Proofs.Refine.ScatterDeadPass.outCntCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomFlagCost,
    Lax3Proofs.Refine.ScatterDeadPass.killSumCost,
    Lax3Proofs.Refine.ScatterDeadPass.entryMemCost,
    Lax3Proofs.Refine.ScatterDeadPass.memCopyAtCost,
    Lax3Proofs.Refine.ScatterDeadPass.memFillAtCost,
    Lax3Proofs.Refine.ScatterBlock.scatBlockK_eq]
  ring

/-- **The trade, exactly.** The landed charge plus the replacement's
member walks is the modelled charge plus the two copies' carrier walks:
`23·n + 12` out, `43·mm1 + 18` in, and every other summand identical. -/
theorem deadAtomKB_trade {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (n mm1 kq mm bw nb t : ℕ) :
    Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n mm1 kq mm bw nb t + (43 * mm1 + 18)
      = deadAtomKB β n mm1 kq mm bw nb t + (23 * n + 12) := by
  rw [deadAtomKB_closed, Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK,
    Lax3Proofs.Refine.ScatterDeadPass.scatDeadK]
  simp only [Lax3Proofs.Refine.ScatterDeadPass.outProbeCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomMemCost,
    Lax3Proofs.Refine.ScatterDeadPass.outCntCost,
    Lax3Proofs.Refine.ScatterDeadPass.atomFlagCost,
    Lax3Proofs.Refine.ScatterDeadPass.killSumCost,
    Lax3Proofs.Refine.ScatterBlock.scatBlockK_eq]
  ring

/-- **The surviving carrier term is the probe's, and nothing else.** At
fixed member data and ball budget the modelled charge still grows in the
carrier — this is the refutation E4c-b keeps alive rather than deleting
— but the coefficient is `20`, the outside probe's, and its narrowing is
`ScatterDeadPass.outProbeCostB`: accounting, not program text. -/
theorem deadAtomKB_probe_floor {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (n mm1 kq mm bw nb t : ℕ) : 20 * n + 10 ≤ deadAtomKB β n mm1 kq mm bw nb t := by
  rw [deadAtomKB_closed]; omega

theorem deadAtomKB_unbounded {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (ksc mm1 kq mm bw nb t : ℕ) :
    ∃ n : ℕ, ¬ (deadAtomKB β n mm1 kq mm bw nb t ≤ ksc) := by
  refine ⟨ksc + 1, fun h => ?_⟩
  have := deadAtomKB_probe_floor β (ksc + 1) mm1 kq mm bw nb t
  omega

/-- **And hoisting the copies out of the atom does not help.** The
obvious repair — run the mask copy once per turn instead of once per
atom, since the atoms of a turn share the child's mask — escapes the
size-read turn slot just as the per-atom reading escapes the
coefficient: at a block of weight zero the slot grants `ct + ksc` and
the copy alone costs `12·n + 6`. The scratch discipline is not
avoidable by moving the pass; it has to be *established*. -/
theorem per_turn_copy_escapes_size_slot (ct ksc Kin : ℕ) :
    ∃ n : ℕ, ¬ (12 * n + 6 + Kin ≤ turnCostSizeA ct ksc 0 Kin) := by
  refine ⟨ct + ksc + 1, fun h => ?_⟩
  simp only [Lax3Proofs.Refine.G2CostProbe.turnCostSizeA] at h
  omega

/-- The per-atom coefficient `Refine.B4Design.atomCoeff` reads, restated
here — that file is downstream, and this statement must not wait on
which name survives execution. -/
def atomCoeffB4 (kq abit t : ℕ) : ℕ := 294 * t + 14 * kq + abit + 221

/-- **The modelled charge still fits the B4 coefficient.** At the
cluster reading in all four in-scope arguments and a block-scale ball
budget, `deadAtomKB` is inside `atomCoeff·(s + 1)` — the slope rises
from `154·t + 131` to `154·t + 151` and the constant from `90` to `96`,
and both stay under the `221` the coefficient already grants. So E4c-b's
replacement, once its two blockers move, does not cost B4 a larger
coefficient. -/
theorem deadAtomKB_le_atomCoeff {L : ℕ} (β : Lax3.DistFO.DistFO L 1) {m bw nb s kq t : ℕ}
    (hm : m ≤ s) (hbw : bw ≤ s) (hnb : nb ≤ s) :
    deadAtomKB β m m kq m bw nb t
      ≤ atomCoeffB4 kq (Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β) t * (s + 1) := by
  rw [deadAtomKB_closed]
  have hball : (44 * bw + 110 * nb + 140) * t ≤ (154 * s + 140) * t :=
    Nat.mul_le_mul_right _ (by omega)
  have hslope : (154 * s + 140) * t = 154 * t * s + 140 * t := by ring
  have hm' : 151 * m ≤ 151 * s := Nat.mul_le_mul_left _ hm
  have hj : 154 * t * s + 151 * s
      ≤ (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) * s := by
    have h1 : (154 * t + 151) * s
        ≤ (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) * s :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (154 * t + 151) * s = 154 * t * s + 151 * s := by ring
    omega
  have hexp : atomCoeffB4 kq (Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β) t * (s + 1)
      = (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) * s
        + (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) := by
    simp only [atomCoeffB4]; ring
  omega

/-- **The narrowed leaf is still unbounded.** At *fixed* member data,
ball budget and probe bound — the state E4c is trying to reach — the
per-atom charge still grows without bound in the carrier, because the
two copies do. -/
theorem narrow_scatter_leaf_unbounded {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (ksc mm1 kq mm bw nb t : ℕ) :
    ∃ n : ℕ, ¬ (Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n mm1 kq mm bw nb t ≤ ksc) := by
  refine ⟨ksc + 1, fun h => ?_⟩
  have := deadAtomK_narrow_floor β (ksc + 1) mm1 kq mm bw nb t
  omega

/-- **THE E4c-a FINDING, compiled: accounting alone cannot produce §2's
`hKsc`.** Take the `hbnd`/`hcostI`/`hKsc` chain at *any* narrowing of the
four in-scope arguments — the probe bound, the two member counts and the
ball budget, all chosen before the carrier — and there is still a
carrier at which no constant `ksc` bounds the scatter phase. So E4c's
deliverable is **not** reachable by re-charging the landed walks: the
mask copy and the distance fill have to be rewritten over the member
list (program text, the next wave), and the reading that remains after
that is the *cluster's*, which only the turn's size slot can cash. -/
theorem narrow_leaf_refutes_constant_ksc {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (ksc mm1 kq mm bw nb t : ℕ) :
    ∃ n : ℕ, ∀ Kb Ki Ksc la lt : ℕ, 1 ≤ la → 1 ≤ lt →
      Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n mm1 kq mm bw nb t ≤ Kb →
      Kb * la + 1 ≤ Ki → Ki * lt + 1 ≤ Ksc → ¬ (Ksc ≤ ksc) := by
  refine ⟨ksc + 1, fun Kb Ki Ksc la lt hla hlt hKb hcostI hKsc hle => ?_⟩
  have hfloor := deadAtomK_narrow_floor β (ksc + 1) mm1 kq mm bw nb t
  have hchain := ksc_ge_atom (Kb := Kb) (Ki := Ki) (Ksc := Ksc) hla hlt hcostI hKsc
  omega

/-! #### Control 2 — a carrier-bearing phase form breaks the close -/

/-- A phase cost of the carrier-bearing shape `a·m + c·n`: linear in the
members AND in the carrier. This is the shape every landed size-blind
phase has, and the shape the M-class re-derivation exists to remove. -/
def phaseCarrier (a cc m n : ℕ) : ℕ := a * m + cc * n

/-- **The carrier term is load-bearing, at the measured constants.** No
cost family satisfies the M-class turn and level shapes with ONE phase
slot at a carrier-bearing form and stays inside the measured family's
closed form: the carrier term survives on the empty arena, the root
runs `n` turns of it, and `cc·n²` is outside a budget linear in the
weight. `cc = 1` suffices — the control is not an artefact of a large
coefficient. -/
theorem carrier_phase_load_bearing (cc : ℕ) (hcc : 1 ≤ cc) (Ksc : ℕ → ℕ) :
    ¬ ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
        (∀ j w m, m ≤ w → phaseCarrier aOrd cc m (10 ^ 10) ≤ Ko j w) ∧
        (∀ j < 3, ∀ s : ℕ, turnCostSizeA ctTurn (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
        (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
          (∑ c ∈ range t, bs c) ≤ 8 * (w + 1) →
          Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
            ≤ Kl j w) ∧
        (∀ w, Kl 0 w ≤ (3 * g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
          bDeadProbe 0 ctTurn kscProbe 8 + CbProbe) * (8 + 1) ^ 3 * (w + 1)) := by
  rintro ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKs, hKl, hcl⟩
  have hF : cc * 10 ^ 10 ≤ Ko 1 0 + (Kc 1 0 + Kd 1 0) := by
    have h := hKo 1 0 0 le_rfl
    simp only [phaseCarrier, Nat.mul_zero, Nat.zero_add] at h
    omega
  have hfloor := nested_slot_floor (n := 10 ^ 10) (ns := 2 * (10 ^ 10 - 1))
    (ℓ := 3) (D := 8) (ct := ctTurn) (Ksc := Ksc) (by omega) hKs hF hKl
  have hup := hcl (10 ^ 10 + 2 * (10 ^ 10 - 1))
  have hlow : 10 ^ 10 * 10 ^ 10 ≤ 10 ^ 10 * (cc * 10 ^ 10) := by
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have hbad : 10 ^ 10 * 10 ^ 10 ≤
      (3 * g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead bDeadProbe 0
        ctTurn kscProbe 8 + CbProbe) * (8 + 1) ^ 3 * (10 ^ 10 + 2 * (10 ^ 10 - 1) + 1) :=
    le_trans hlow (le_trans hfloor hup)
  exact absurd hbad (by decide +kernel)

/-! #### Control 3 — the root's `hKd` slot has NOT been narrowed

R1.8 removed `RamDriver.sweepCom` from the driver's program, but
`RamDriverRoot.levelAt`'s `hKd` still reserves
`Refine.DeadSweep.sweepCost q_top cap mb j n φ` — a CARRIER walk — and
`hKl` still sums `Kd j w`. The M-class dead slot `(0, bd)` reads the
post-R1.8 program; the root slot reads the pre-R1.8 one. The delta is
real and has not been cashed. -/

/-- The retired sweep costs at least `4·n + 6`. -/
theorem sweepCost_floor (q_top cap mb jd n : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    4 * n + 6 ≤ Lax3Proofs.Refine.DeadSweep.sweepCost q_top cap mb jd n φ := by
  simp only [Lax3Proofs.Refine.DeadSweep.sweepCost]
  have : 4 * n ≤ (Lax3Proofs.RamDriverBot.turnCost q_top cap mb jd φ + 4) * n :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The un-narrowed `hKd` slot forces `Ω(n²)`.** Any cost family
meeting the root's own dead slot pays the retired carrier sweep on the
EMPTY arena of a nested level, and the root level runs `n` turns of it.
This is a delta to be cashed by deleting the slot, not one already
cashed. -/
theorem landed_hKd_slot_floor {n ns ℓ D ct q_top cap mb : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hℓ : 2 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ s : ℕ, turnCostSizeA ct (Ksc j) s (Kl (j + 1) s) ≤ Ks j s)
    (hKd : ∀ j w, Lax3Proofs.Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j w)
    (hKl : ∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
      (∑ c ∈ range t, bs c) ≤ D * (w + 1) →
      Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j w) :
    n * (4 * n + 6) ≤ Kl 0 (n + ns) := by
  have hF : 4 * n + 6 ≤ Ko 1 0 + (Kc 1 0 + Kd 1 0) := by
    have h1 := sweepCost_floor q_top cap mb 1 n φ
    have h2 := hKd 1 0
    omega
  exact nested_slot_floor hℓ hKs hF hKl

/-- **…and it is outside the measured family's closed form.** At
`n = 10¹⁰` on the star carrier the floor is `4·10²⁰`; the closed form
grants under `7·10¹⁸`. So the M-class close and the landed `hKd` slot
are not simultaneously satisfiable: the slot must go. -/
theorem landed_hKd_load_bearing {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (Ksc : ℕ → ℕ) :
    ¬ ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
        (∀ j w, Lax3Proofs.Refine.DeadSweep.sweepCost q_top cap mb j (10 ^ 10) φ ≤ Kd j w) ∧
        (∀ j < 3, ∀ s : ℕ, turnCostSizeA ctTurn (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
        (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
          (∑ c ∈ range t, bs c) ≤ 8 * (w + 1) →
          Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
            ≤ Kl j w) ∧
        (∀ w, Kl 0 w ≤ (3 * g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
          bDeadProbe 0 ctTurn kscProbe 8 + CbProbe) * (8 + 1) ^ 3 * (w + 1)) := by
  rintro ⟨Ko, Kc, Kd, Ks, Kl, hKd, hKs, hKl, hcl⟩
  have hfloor := landed_hKd_slot_floor (n := 10 ^ 10) (ns := 2 * (10 ^ 10 - 1))
    (ℓ := 3) (D := 8) (ct := ctTurn) (Ksc := Ksc) (by omega) hKs hKd hKl
  have hup := hcl (10 ^ 10 + 2 * (10 ^ 10 - 1))
  have hbad : 10 ^ 10 * (4 * 10 ^ 10 + 6) ≤
      (3 * g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead bDeadProbe 0
        ctTurn kscProbe 8 + CbProbe) * (8 + 1) ^ 3 * (10 ^ 10 + 2 * (10 ^ 10 - 1) + 1) :=
    le_trans hfloor hup
  exact absurd hbad (by decide +kernel)

/-! #### Control 4 — the base is a hole AND a refutation (T4b) -/

/-- **No constant `Cb` meets the landed base slot.** `hKbase` reads the
CARRIER (`RamDriverBot.baseCost = sweepCost` since R1.8-T4a) and is
quantified over every arena weight, including `0`. So a base budget
`Cb·(w+1)` — which is `Cb` at the empty arena — has to exceed `4·n + 6`.
T4b is therefore not merely unstarted: the slot it has to replace is
refutable as it stands. -/
theorem landed_base_needs_carrier_Cb {q_top cap mb ℓ n Cb : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {Kl : ℕ → ℕ → ℕ}
    (hKbase : ∀ m, Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hle : Kl ℓ 0 ≤ Cb) : 4 * n + 6 ≤ Cb := by
  have h1 := sweepCost_floor q_top cap mb ℓ n φ
  have h2 : Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ n φ
      = Lax3Proofs.Refine.DeadSweep.sweepCost q_top cap mb ℓ n φ :=
    Lax3Proofs.Refine.DeadSweep.baseCost_eq q_top cap mb ℓ n φ
  have h3 := hKbase 0
  omega

/-- …and no constant survives that, since `n` is chosen after it. -/
theorem no_constant_Cb (Cb : ℕ) : ¬ (4 * (Cb + 1) + 6 ≤ Cb) := by omega

/-! #### Control 5 — the ceilings themselves

Each ceiling of §3 is pinned in both directions there. The two lines
below are the aggregate: the measured family clears the gate and a
family with every constant one step over its ceiling does not. -/

#guard gateHalf famHalfMeasured
#guard ¬ gateHalf (famHalf 79093858 39546915 79093802 8788642 8798199 237291370 237291370 988673)

/-! ### §5 Axioms -/

#print axioms coverPhase_paid_by_slot
#print axioms descendLeaves_le_turnSlot
#print axioms descendLeaves_sum_le_mass
#print axioms block_split_le_weight
#print axioms cover_measured_pair_insufficient
#print axioms bexpK_not_memberForm
#print axioms rootBudgetM_le_cstar
#print axioms c0_shape_real
#print axioms c0_close_at_measured
#print axioms nested_slot_floor
#print axioms scatDeadK_carrier_floor
#print axioms deadAtomK_carrier_floor
#print axioms landed_scatter_leaf_unbounded
#print axioms deadAtomK_root_eq
#print axioms scatDeadK_narrow_floor
#print axioms narrow_scatter_leaf_unbounded
#print axioms narrow_leaf_refutes_constant_ksc
#print axioms carrier_phase_load_bearing
#print axioms landed_hKd_slot_floor
#print axioms landed_hKd_load_bearing
#print axioms landed_base_needs_carrier_Cb

-- wave E4c-b: the modelled post-wiring charge (control 1c)
#print axioms deadAtomKB_closed
#print axioms deadAtomKB_trade
#print axioms per_turn_copy_escapes_size_slot
#print axioms deadAtomKB_probe_floor
#print axioms deadAtomKB_unbounded
#print axioms deadAtomKB_le_atomCoeff

end Lax3Proofs.Refine.C0CloseProbe
