import Lax3Proofs.Refine.C0CloseProbe
import Lax3Proofs.Refine.MassWeight

/-!
# B4-design: does the turn's size-read cost slot close?

`Refine/C0CloseProbe.lean` proved the C0 close at every phase's measured
constant except the scatter leaf, and wave E4c-a corrected the
attribution: the leaf cannot be made a **constant** at all. It splits
into `108·n + 18` an accounting wave can re-charge and `23·n + 12` that
is program text (the mask copy and the distance fill, E4c-b's job), and
`C0CloseProbe.narrow_leaf_refutes_constant_ksc` compiles that no
narrowing of the probe bound, the member counts or the ball budget
yields a constant while those copies stand. Beyond them the honest
reading is the turn's **cluster**, not a constant.

Which lands on a slot that already exists and is deliberately empty:
`RamDriverRoot.turnCostSize` takes a size argument `_s` and **discards
it** (`turnCostSize_eq` is `rfl`), with its own docstring saying the
slot is free until B4 fills it, while the proposed
`G2CostProbe.turnCostSizeA ct ksc s Kin = (ct + ksc)·(s + 1) + Kin`
reads it and `G2ExistsRevalidation.g2m_exists` already closes at it.

This file is the design gate for filling that slot, in the house style
of `Refine/G2CostProbe.lean`: **nothing landed is edited**. Every
landed object below is consumed — `CostRecurrence` through `g2m_exists`,
`rootBudgetM_closes`, `mclass_c0_shape`, `C0CloseProbe`'s measured
constants and its refutations, `MassWeight`'s weight algebra,
`ScatterDeadTurn.deadAtomK`, `ScatterBlock.BallBudget`,
`RamDriverCluster.spec_conj`. The proposed forms move to the real
declarations only in B4 execution.

## Coefficient versus total — the standing distinction of this file

`turnCostSizeA`'s third argument is multiplied by `(s + 1)`. So the
number the interface calls `ksc` is a **coefficient**, and
`C0CloseProbe`'s ceiling `ksc ≤ 8 798 198` is a ceiling on that
coefficient. The number the LANDED walk supplies through
`clusterStepAt`'s `hbnd`/`hcostI`/`hKsc` chain is a **total**: at least
the per-atom charge, times the atom list, times the table list. Every
statement below says which of the two it is; §4 is where the two are
reconciled, and hazard 1 of the brief is that conflating them makes a
refutation read as good news.

## The five quantities, kept apart

`ScatterDeadTurn.deadAtomK β n mm1 kq mm bw nb t` reads five different
sizes, and `deadAtomK_closed` (§1) exhibits each with its own
coefficient so that no two can be silently merged:

| argument | what it counts | coefficient |
|---|---|---|
| `n` | the carrier — the outside probe's scan and the two copies | `43` |
| `mm1` | the **child's member list**, the atom's filter walk | `23` |
| `mm` | the **engine's member count**, its two block walks | `65` |
| `bw` | the ball's **slot weight** (`BallBudget`'s first number) | `44·t` |
| `nb` | the ball's **cardinality** (`BallBudget`'s second number) | `110·t` |

`mm1` and `mm` are distinct arguments and are conflated in prose
elsewhere; block **size** and block **weight** are two further
quantities, and §3 is exactly the question of which of those two the
slot's `s` must be.

**A sixth name, and a collision to watch.** `deadAtomK`'s last argument
`t` is the atom's **pick count** — a field of the `ScatterSentence`, so
a quantity of the formula, fixed before the arena. The landed Σ-shaped
`hKl` also writes `t`, and there it is the level's **turn count**. This
file keeps the landed argument names in both places rather than
inventing new ones; every statement below that mentions both spells out
which is which, and `blind_slot_floor` is stated at `turns` so that no
binder shadows the other.

## The six sections

* **§1** floor-death, extended past the copies. The post-E4c-b charge
  is modelled by reading `deadAtomK` at the cluster in all four in-scope
  arguments at once; it is still `131·(cluster)`, and the LANDED
  size-blind `turnCostSize` pays `Ksc` in full at every `s`, so a level
  running `t` turns pays `t · Ksc` and the close dies quadratically.
  **The death is the slot's shape, not the copies.**
* **§2** the proposed B4 slot, existence: the size-read form stated
  locally, the `CostRecurrence` witness satisfying it and the landed
  Σ-shaped `hKl` verbatim, plus the new per-turn payment clause, closing
  to the same `(D + 1)^ℓ` shape and the same root text.
* **§3** what `s` must be. **Weight, not size** — and the side
  condition does not have to change, because
  `MassWeight.mass_of_alive_compaction_weight` already delivers the
  weight version. The ball term fits `ksc·(s + 1)` **only** under a
  block-scale ball budget; the sum over a level's turns is checked, not
  just the pointwise fit.
* **§4** the coefficient ceiling at the new shape, back-solved and
  `#guard`ed both directions at ε = 1, 1/2, 1/4, and the reconciliation
  with `8 798 198`.
* **§5** the `hbud` wall: the close does not need the frames
  decoupling; the walk does. The narrowed hypothesis is stated and
  compiled to be **weaker** than the landed one.
* **§6** the honesty controls.

## The verdict, in one line

The size-read interface **closes, conditionally** — on E4c-b removing
the two copies, on `s` being the block **weight**, and on a block-scale
ball budget, which the landed `hbud` (quantified over all masks) cannot
supply. §5 names the declarations that would have to move.
-/

namespace Lax3Proofs.Refine.B4Design

open Finset
open Lax3Proofs.Refine.G2ExistsRevalidation
  (phaseM phaseMR phaseBudgetM g2M g2m_exists rootBudgetM rootBudgetM_closes mclass_c0_shape)
open Lax3Proofs.Refine.G2CostProbe (turnCostSizeA)
open Lax13Proofs.Imp (Env Com)
open Lax13Proofs.Reasoning (Spec)
open Lax13Proofs.Reasoning.Lib (Csr)
open Lax3Proofs.Refine.C0CloseProbe
  (aOrd bOrd aCovSlot bCovSlot aDead ctTurn ctBlockLeaves kaProbe bDeadProbe CbProbe
   ksentProbe kdecRoot kscProbe starW gateHalf gateOne famHalf cstarM kcovC
   cov_slot_le_kcovC rootBudgetM_le_cstar c0_shape_real coverDeg ksc_ge_atom)

/-! ### §1 Floor-death, extended past the copies

E4c-b's deliverable is program text: rewrite `RamDriver.scatDeadCom`'s
mask copy and distance fill over the member list instead of the
carrier. This section grants that wave everything it could possibly
deliver — the probe stopped at the pigeonhole bound, both member counts
at the cluster, the two copies at the cluster — and compiles that the
LANDED slot still cannot pay.
-/

/-- **The per-atom charge in closed form, at fully general arguments.**
Every one of the five sizes carries its own coefficient; this is the
statement that keeps hazard 4 honest. `C0CloseProbe.deadAtomK_root_eq`
is the same identity specialised to the root's carrier instantiation
`n n mb n ns n`, where `43 + 23 + 65` collapses to the `131·n` of that
file's headline. -/
theorem deadAtomK_closed {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (n mm1 kq mm bw nb t : ℕ) :
    Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n mm1 kq mm bw nb t
      = (44 * bw + 110 * nb + 140) * t + 43 * n + 23 * mm1 + 65 * mm + 14 * kq +
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

/-- **The post-E4c-b charge, modelled.** E4c-b's success is exactly the
statement that the first argument — the carrier, which the probe scan
and the two copies read — becomes the turn's cluster; and the two member
counts and the ball are the narrowings E4c-a was asked for. Reading
`deadAtomK` at the cluster count `m` in all four in-scope positions at
once models every one of them simultaneously, with no new definition
and nothing transcribed. -/
theorem deadAtomK_cluster {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (m kq bw nb t : ℕ) :
    Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β m m kq m bw nb t
      = (44 * bw + 110 * nb + 140) * t + 131 * m + 14 * kq +
        Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 90 := by
  rw [deadAtomK_closed]; ring

/-- **…and it is still cluster-linear.** The `131` did not move: E4c-b
buys the *argument* the coefficient is read at, not the coefficient.
This is the compiled sense in which "beyond the copies the honest
reading is the turn's cluster". -/
theorem deadAtomK_cluster_floor {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (m kq bw nb t : ℕ) :
    131 * m ≤ Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β m m kq m bw nb t := by
  rw [deadAtomK_cluster]; omega

/-- **No constant survives E4c-b either.** At any fixed kill count, ball
budget and pick count — all chosen before the arena — there is a cluster
at which the post-E4c-b per-atom charge exceeds any constant. This is
`C0CloseProbe.narrow_scatter_leaf_unbounded` moved from the carrier to
the cluster: the same conclusion at the *narrowed* reading. -/
theorem post_copies_atom_unbounded {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (ksc kq bw nb t : ℕ) :
    ∃ m : ℕ, ¬ (Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β m m kq m bw nb t ≤ ksc) := by
  refine ⟨ksc + 1, fun h => ?_⟩
  have := deadAtomK_cluster_floor β (ksc + 1) kq bw nb t
  omega

/-- **The landed slot is blind, in both directions.** `turnCostSize`
takes the size argument and does not read it, so the same turn cost is
charged at every block. -/
theorem landed_turnCostSize_blind (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc s s' Kin : ℕ) :
    Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc s Kin
      = Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc s' Kin := rfl

/-- **…and it pays `Ksc` in full, whatever `s` is.** The scatter charge
enters `RamDriverRoot.turnCost` additively (it is the sixth summand),
and `turnCostSize` is that function with the size argument dropped. So
the turn slot is bounded below by the level's whole scatter charge at
*every* block, including the empty one. -/
theorem landed_turnCostSize_ge_Ksc (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc s Kin : ℕ) :
    Ksc + Kin ≤ Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc s Kin := by
  simp only [Lax3Proofs.RamDriverRoot.turnCostSize, Lax3Proofs.RamDriverRoot.turnCost]
  omega

/-- **The blind-slot floor.** A level running `t` turns pays its whole
scatter charge `t` times, because the size slot cannot tell the turns
apart. The Σ-shaped `hKl` is the landed one verbatim and is instantiated
at the *empty* blocks (`bs = 0`), so the mass side condition is
satisfied with room to spare — the floor is not an artefact of a large
block. This is `C0CloseProbe.nested_slot_floor`'s mechanism moved from a
phase slot to the turn's own `Ksc`. -/
theorem blind_slot_floor {n ns cap mb q_top ℓ D turns : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hℓ : 0 < ℓ) (ht : turns ≤ n + ns)
    (hKs : ∀ j < ℓ, ∀ s : ℕ,
      Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) s (Kl (j + 1) s)
        ≤ Ks j s)
    (hKl : ∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
      (∑ c ∈ range t, bs c) ≤ D * (w + 1) →
      Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j w) :
    turns * Ksc 0 ≤ Kl 0 (n + ns) := by
  have hks : Ksc 0 ≤ Ks 0 0 := by
    have h := hKs 0 hℓ 0
    have h2 := landed_turnCostSize_ge_Ksc n ns cap mb q_top 0 φ (Ksc 0) 0 (Kl (0 + 1) 0)
    omega
  have h0 := hKl 0 hℓ (n + ns) turns ht (fun _ => 0) (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h0
  calc turns * Ksc 0 ≤ turns * (Ks 0 0 + 11) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ Kl 0 (n + ns) := by omega

/-- **THE §1 REFUTATION: the landed size-blind slot cannot pay a
cluster-scale charge, even after E4c-b.**

The hypothesis is the *best case E4c-b can produce*: the level's scatter
charge pays one atom, read at the cluster in all four narrowed
positions, with the ball at whatever budget the wave arranges. The
level then runs `10¹⁰` turns of it — a turn count the mass side
condition permits at every block empty — and the root level's bill is
`131·10²⁰`, against a closed form granting under `7·10¹⁸`.

So the deficit is **not** the two copies and **not** the coefficient:
it is that `Ksc` enters the landed slot additively and uniformly. No
accounting wave, and no re-measurement of the leaf, closes this while
`turnCostSize` discards its size argument. -/
theorem post_copies_blind_slot_refuted {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (kq bw nb t cap mb q_top : ℕ) (φ : Lax3.FirstOrder.FO 0) (Ksc : ℕ → ℕ) :
    ¬ ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
        -- the level's scatter charge pays one post-E4c-b atom at its largest cluster
        Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β (10 ^ 10) (10 ^ 10) kq (10 ^ 10)
            bw nb t ≤ Ksc 0 ∧
        -- the LANDED turn slot and the landed Σ-shaped level condition, verbatim
        (∀ j < 3, ∀ s : ℕ,
          Lax3Proofs.RamDriverRoot.turnCostSize (10 ^ 10) (2 * (10 ^ 10 - 1)) cap mb q_top j φ
            (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
        (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
          (∑ c ∈ range t, bs c) ≤ 8 * (w + 1) →
          Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
            ≤ Kl j w) ∧
        -- and the measured family's closed form
        (∀ w, Kl 0 w ≤ (3 * g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
          bDeadProbe 0 ctTurn kscProbe 8 + CbProbe) * (8 + 1) ^ 3 * (w + 1)) := by
  rintro ⟨Ko, Kc, Kd, Ks, Kl, hatom, hKs, hKl, hcl⟩
  have hfloor := blind_slot_floor (n := 10 ^ 10) (ns := 2 * (10 ^ 10 - 1))
    (ℓ := 3) (D := 8) (turns := 10 ^ 10) (cap := cap) (mb := mb) (q_top := q_top) (φ := φ)
    (Ksc := Ksc) (by omega) (by omega) hKs hKl
  have hlow : 10 ^ 10 * (131 * 10 ^ 10) ≤ 10 ^ 10 * Ksc 0 := by
    refine Nat.mul_le_mul_left _ ?_
    have := deadAtomK_cluster_floor β (10 ^ 10) kq bw nb t
    omega
  have hup := hcl (10 ^ 10 + 2 * (10 ^ 10 - 1))
  have hbad : 10 ^ 10 * (131 * 10 ^ 10) ≤
      (3 * g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead bDeadProbe 0
        ctTurn kscProbe 8 + CbProbe) * (8 + 1) ^ 3 * (10 ^ 10 + 2 * (10 ^ 10 - 1) + 1) :=
    le_trans hlow (le_trans hfloor hup)
  exact absurd hbad (by decide +kernel)

/-! ### §2 The proposed B4 slot, and its existence witness

The repair is the one the landed docstring already names: read the
size. The form is `G2CostProbe.turnCostSizeA` — restated here as a
local `def` so that this file's statements do not depend on which name
survives execution — with `s` the turn's block weight (§3) and `ksc` a
**coefficient**.
-/

/-- **PROPOSED** replacement for `RamDriverRoot.turnCostSize`: one turn
on a block of weight `s` pays its block-driven leaves and its scatter
chain at `s`, plus the nested driver once. Definitionally
`G2CostProbe.turnCostSizeA`, which `g2m_exists` already closes at. -/
def turnCostSizeB4 (ct ksc s Kin : ℕ) : ℕ := (ct + ksc) * (s + 1) + Kin

theorem turnCostSizeB4_eq_probe (ct ksc s Kin : ℕ) :
    turnCostSizeB4 ct ksc s Kin = turnCostSizeA ct ksc s Kin := rfl

/-- **The proposed slot reads the size** — the property the landed one
lacks (`landed_turnCostSize_blind`). -/
theorem turnCostSizeB4_reads_size : turnCostSizeB4 0 1 0 0 ≠ turnCostSizeB4 0 1 1 0 := by
  decide

/-- **One turn's own bill fits the proposed slot.** The four
block-driven descend leaves are `G2CostProbe.blockLeaves_le_weight` at
the block's members and slots, and the turn's scatter charge is whatever
the walk supplies at the turn's own block; if that charge is inside the
coefficient's grant then the two together are inside the slot, with the
nested driver's budget passed through untouched.

`ct` and `ksc` are the two coefficients, and they are added — this is
the compiled statement that the turn slot has room for both. -/
theorem turn_leaves_and_scatter_paid {ct ksc sz ds Kin Kscat : ℕ}
    (hct : ctBlockLeaves ≤ ct) (hsc : Kscat ≤ ksc * (sz + ds + 1)) :
    (Lax3Proofs.Refine.BlockLeaves.blockLoadK sz sz + Lax3Proofs.Refine.BlockLeaves.bandK sz +
        Lax3Proofs.Refine.BlockLeaves.bsubK sz + Lax3Proofs.Refine.BlockLeaves.bexpK sz ds)
      + Kscat + Kin
      ≤ turnCostSizeB4 ct ksc (sz + ds) Kin := by
  have h := Lax3Proofs.Refine.G2CostProbe.blockLeaves_le_weight sz ds
  have hct' : 200 ≤ ct := by
    simpa only [Lax3Proofs.Refine.C0CloseProbe.ctBlockLeaves] using hct
  have hmul : 200 * (sz + ds + 1) ≤ ct * (sz + ds + 1) := Nat.mul_le_mul_right _ hct'
  have hexp : turnCostSizeB4 ct ksc (sz + ds) Kin
      = ct * (sz + ds + 1) + ksc * (sz + ds + 1) + Kin := by
    simp only [turnCostSizeB4]; ring
  omega

/-- **THE §2 EXISTENCE PROBE: the size-read slot is satisfiable, and it
closes to the same shape.**

For every level count, cover degree, base and round budget, and every
per-level scatter **coefficient** family bounded by a constant, there
are cost functions satisfying:

* the three M-class phase slots at `C0CloseProbe`'s measured constants;
* the **size-read** turn slot `turnCostSizeB4` at the measured `ctTurn`;
* the landed Σ-shaped `hKl` of `RamDriverRoot.driverRoot_decides_sentence`
  **verbatim**, and `hKmono`, and the base clause;
* the new per-turn payment clause: at every block, the turn's four
  descend leaves and any scatter charge inside the coefficient's grant
  are both paid by the slot;
* the closed form `(ℓ·g2M + Cb)·(D + 1)^ℓ·(w + 1)`, and the restated
  root's cost text inside the `D`-free `cstarM·(D + 1)^{ℓ+1}`.

Nothing here is re-derived: the witness is `CostRecurrence`'s canonical
solution through `g2m_exists`, the root text is `rootBudgetM_closes`,
and the `D`-free absorption is `rootBudgetM_le_cstar`.

**`hKscCoeff` is a bound on a COEFFICIENT.** It is *not*
`C0CloseProbe.c0_close_at_measured`'s `hKsc` read again: there the same
inequality bounded the number the landed walk supplies, which is a
total. §3 and §5 are what it takes to make a coefficient the thing the
walk supplies. -/
theorem b4_size_slot_exists {ka bd Cb ksent kscN R ℓ D : ℕ} (Ksc : ℕ → ℕ)
    (hKscCoeff : ∀ j < ℓ, Ksc j ≤ kscN) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      -- the M-class phase slots, at each phase's own measured constants
      (∀ j w m, m ≤ w → phaseMR aOrd bOrd R m ≤ Ko j w) ∧
      (∀ j w m, m ≤ w → phaseMR (aCovSlot ka D) (bCovSlot ka D) 0 m ≤ Kc j w) ∧
      (∀ j w m, m ≤ w → phaseMR aDead bd 0 m ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl ℓ w) ∧
      (∀ j, Monotone (Kl j)) ∧
      -- **the size-read turn slot**
      (∀ j < ℓ, ∀ s : ℕ, turnCostSizeB4 ctTurn (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
      -- the landed Σ-shaped level condition, verbatim
      (∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ range t, bs c) ≤ D * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      -- **new**: the turn's leaves and its scatter charge, at the turn's own block
      (∀ j < ℓ, ∀ sz ds Kscat : ℕ, Kscat ≤ Ksc j * (sz + ds + 1) →
        (Lax3Proofs.Refine.BlockLeaves.blockLoadK sz sz +
            Lax3Proofs.Refine.BlockLeaves.bandK sz + Lax3Proofs.Refine.BlockLeaves.bsubK sz +
            Lax3Proofs.Refine.BlockLeaves.bexpK sz ds)
          + Kscat + Kl (j + 1) (sz + ds) ≤ Ks j (sz + ds)) ∧
      -- the closed form
      (∀ w, Kl 0 w ≤ (ℓ * g2M aOrd bOrd (aCovSlot ka D) (bCovSlot ka D) aDead bd R ctTurn
        kscN D + Cb) * (D + 1) ^ ℓ * (w + 1)) ∧
      -- and the restated root's cost text inside the D-free closed form
      (∀ Kdec Ksent : ℕ → ℕ → ℕ, ∀ n ns nsd : ℕ, nsd ≤ ns →
        Kdec n ns ≤ kdecRoot * (n + ns + 1) → Ksent n ns ≤ ksent * (n + ns + 1) →
        Kdec n ns + (Kl 0 (n + nsd) + Ksent n ns)
          ≤ cstarM ℓ Cb aOrd bOrd (kcovC ka) aDead bd R ctTurn kscN kdecRoot ksent
              * (D + 1) ^ (ℓ + 1) * (n + ns + 1)) := by
  obtain ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKc, hKd, hbase, hmono, hKs, hKlS, hcl⟩ :=
    g2m_exists ℓ D Cb R aOrd bOrd (aCovSlot ka D) (bCovSlot ka D) aDead bd ctTurn kscN Ksc
      hKscCoeff
  refine ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKc, hKd, hbase, hmono, hKs, hKlS, ?_, hcl, ?_⟩
  · intro j hj sz ds Kscat hKscat
    exact le_trans (turn_leaves_and_scatter_paid (ct := ctTurn) (by decide) hKscat)
      (hKs j hj (sz + ds))
  · intro Kdec Ksent n ns nsd hns hdec hsent
    refine le_trans (rootBudgetM_closes (ksent := ksent) hns (hmono 0) hdec hsent hcl) ?_
    exact Nat.mul_le_mul_right _ (rootBudgetM_le_cstar (cov_slot_le_kcovC ka D))

/-- **…and it reaches `n^{1+ε}`.** `C0CloseProbe.c0_shape_real` is
consumed at the cover degree `⌈c·w^{ε/(ℓ+1)}⌉₊`; nothing is
re-derived. -/
theorem b4_c0_close_real {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    {ℓ Cb ka bd R kscN kdec ksent w K : ℕ} (hw : 1 ≤ w)
    (hK : K ≤ rootBudgetM ℓ Cb aOrd bOrd (aCovSlot ka (coverDeg c ε ℓ w))
      (bCovSlot ka (coverDeg c ε ℓ w)) aDead bd R ctTurn kscN (coverDeg c ε ℓ w) kdec ksent
      * (w + 1)) :
    (K : ℝ) ≤ ((cstarM ℓ Cb aOrd bOrd (kcovC ka) aDead bd R ctTurn kscN kdec ksent : ℝ)
      * (c + 2) ^ (ℓ + 1)) * ((w : ℝ) + 1) ^ (1 + ε) :=
  c0_shape_real hc hε hw (cov_slot_le_kcovC ka (coverDeg c ε ℓ w)) hK

/-! ### §3 What `s` must be — the load-bearing question

Block **size** or block **weight**? The answer is **weight**, the side
condition does **not** have to change, and the ball term fits only under
a block-scale ball budget.
-/

/-- **The block's weight is its two currencies added** —
`MassWeight.blockWeight_eq_add_degSum`, cited. The turn slot's `s` is
this number, and `G2CostProbe.blockLeaves_le_weight`'s `s + ds` is
exactly its two summands. -/
theorem s_is_block_weight {n : ℕ} {G : SimpleGraph (Fin n)} (Xoff Xmem : ℕ → ℕ) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    Lax3Proofs.Refine.MassWeight.blockWeight n G Xoff Xmem c
      = Lax3Proofs.Refine.MassMath.blockSize Xoff c +
        Lax3Proofs.Refine.MassWeight.blockDegSum n G Xoff Xmem c :=
  Lax3Proofs.Refine.MassWeight.blockWeight_eq_add_degSum G Xoff Xmem hmem

/-- **The machine's degree reading of a block is the mathematical one**,
on a simple CSR — the same `rowLen_eq_vdeg` chain
`MassWeight.blockDegSum_le_ns` uses, run as an equality. -/
theorem blockRowSum_eq_blockDegSum {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T Xoff Xmem : ℕ → ℕ}
    (hcsrS : Lax3Proofs.RamElim.CsrSimple G ns O T) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    Lax3Proofs.Refine.MassWeight.blockRowSum O Xoff Xmem c
      = Lax3Proofs.Refine.MassWeight.blockDegSum n G Xoff Xmem c := by
  simp only [Lax3Proofs.Refine.MassWeight.blockRowSum,
    Lax3Proofs.Refine.MassWeight.blockDegSum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_Ico] at hp
  rw [Lax3Proofs.Refine.MassWeight.natW_val _ (hmem p hp.1 hp.2),
    Lax3Proofs.Refine.MassWeight.rowLen_eq_vdeg hcsrS (hmem p hp.1 hp.2)]

/-- **THE TIE: the ball budget's two numbers ARE the block weight's two
currencies.**

`ScatterBlock.BallBudget n r G M O bw nb` bounds a ball by its slot
weight `bw` (`∑ rowLen O`) and its cardinality `nb`. On a mask supported
inside the turn's cluster, the natural witness is the block's own member
set: its cardinality is `blockSize` and its slot weight is
`blockRowSum`, and the two add to exactly the block's weight. So the
`s` that pays the ball term is the same `s` that pays the descend
leaves, with no second currency anywhere. -/
theorem ball_budget_numbers_are_block_weight {n ns : ℕ} {G : SimpleGraph (Fin n)}
    {O T Xoff Xmem : ℕ → ℕ} (hcsrS : Lax3Proofs.RamElim.CsrSimple G ns O T) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    Lax3Proofs.Refine.MassMath.blockSize Xoff c +
        Lax3Proofs.Refine.MassWeight.blockRowSum O Xoff Xmem c
      = Lax3Proofs.Refine.MassWeight.blockWeight n G Xoff Xmem c := by
  rw [blockRowSum_eq_blockDegSum hcsrS hmem, s_is_block_weight Xoff Xmem hmem]

/-- **`s := block SIZE` is REFUTED.** A block's member count says
nothing about the arena slots its members own, and `BallBudget`'s first
number is a slot weight. For every coefficient there is a one-member
block whose ball term escapes `ksc·(size + 1)` — the block below has
`blockSize = 1` and `blockRowSum = 2·ksc + 1`, and the pick's ball term
alone is `44·(2·ksc + 1) + 140`, against a grant of `2·ksc`.

This is the scatter twin of `MassWeight`'s `turn_size_refuted`: the
degree half of the weight is load-bearing in the scatter leaf for the
same reason it is in `bexpK`. -/
theorem size_reading_refuted (ksc : ℕ) :
    ∃ O Xoff Xmem : ℕ → ℕ,
      Lax3Proofs.Refine.MassMath.blockSize Xoff 0 = 1 ∧
      Lax3Proofs.Refine.MassWeight.blockRowSum O Xoff Xmem 0 = 2 * ksc + 1 ∧
      ¬ ((44 * Lax3Proofs.Refine.MassWeight.blockRowSum O Xoff Xmem 0 + 140) * 1
          ≤ ksc * (Lax3Proofs.Refine.MassMath.blockSize Xoff 0 + 1)) := by
  have hsz : Lax3Proofs.Refine.MassMath.blockSize (fun c => c) 0 = 1 := by
    simp [Lax3Proofs.Refine.MassMath.blockSize]
  have hrs : Lax3Proofs.Refine.MassWeight.blockRowSum (fun v => (2 * ksc + 1) * v)
      (fun c => c) (fun p => p) 0 = 2 * ksc + 1 := by
    simp [Lax3Proofs.Refine.MassWeight.blockRowSum, Csr.rowLen]
  exact ⟨_, _, _, hsz, hrs, by rw [hsz, hrs]; omega⟩

/-- **…and `s := block WEIGHT` works.** At a block-scale ball budget —
both of `BallBudget`'s numbers under the block's weight, which
`ball_budget_numbers_are_block_weight` says is the natural witness — the
whole post-E4c-b per-atom charge is inside `atomCoeff·(s + 1)` for a
coefficient built only from the pick count, the kill count and the
generated evaluator's own fragment. Every one of those three is fixed by
the formula before the arena exists. -/
def atomCoeff (kq abit t : ℕ) : ℕ := 294 * t + 14 * kq + abit + 221

theorem atomK_le_atomCoeff {L : ℕ} (β : Lax3.DistFO.DistFO L 1) {m bw nb s kq t : ℕ}
    (hm : m ≤ s) (hbw : bw ≤ s) (hnb : nb ≤ s) :
    Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β m m kq m bw nb t
      ≤ atomCoeff kq (Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β) t * (s + 1) := by
  rw [deadAtomK_cluster]
  have hball : (44 * bw + 110 * nb + 140) * t ≤ (154 * s + 140) * t :=
    Nat.mul_le_mul_right _ (by omega)
  have hslope : (154 * s + 140) * t = 154 * t * s + 140 * t := by ring
  have hm' : 131 * m ≤ 131 * s := Nat.mul_le_mul_left _ hm
  have hj : 154 * t * s + 131 * s
      ≤ (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) * s := by
    have h1 : (154 * t + 131) * s
        ≤ (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) * s :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (154 * t + 131) * s = 154 * t * s + 131 * s := by ring
    omega
  have hexp : atomCoeff kq (Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β) t * (s + 1)
      = (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) * s
        + (294 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 221) := by
    simp only [atomCoeff]; ring
  omega

/-- **HAZARD 2, discharged: the SUM over a level's turns, not just the
pointwise fit.** `Ks j (bs c)` is applied at each turn's own block and
the side condition bounds `∑ bs c`; a per-turn charge inside
`ksc·(bs c + 1)` therefore sums to `ksc·(D + 1)·(w + 1)` — linear in the
arena weight, with the turn count `t ≤ w` paying the `+1`s. This is
where a charge that fits pointwise but escapes in the sum would be
caught, and it does not escape. -/
theorem size_slot_sum_le_mass {t D w ksc : ℕ} {bs : ℕ → ℕ} (ht : t ≤ w)
    (hsum : (∑ c ∈ range t, bs c) ≤ D * (w + 1)) :
    (∑ c ∈ range t, ksc * (bs c + 1)) ≤ ksc * (D + 1) * (w + 1) := by
  calc (∑ c ∈ range t, ksc * (bs c + 1)) = ksc * (∑ c ∈ range t, (bs c + 1)) :=
        (Finset.mul_sum _ _ _).symm
    _ = ksc * ((∑ c ∈ range t, bs c) + t) := by rw [Finset.sum_add_distrib]; simp
    _ ≤ ksc * (D * (w + 1) + (w + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = ksc * (D + 1) * (w + 1) := by ring

/-- **The side condition does NOT have to change.**
`MassWeight.mass_of_alive_compaction_weight` — E6, landed — already
delivers `hKl`'s side condition at the **weight** reading: the turn
count is under the arena weight and the turns' block weights sum to
`d·(w + 1)`. So moving `s` from size to weight costs the interface
nothing: the same landed producer supplies the same landed shape. -/
theorem mass_side_condition_at_weight {n : ℕ} {G H : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg cps : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {cnum d r m : ℕ}
    (hord : Lax3Proofs.RamCover.OrdersBy n π ord)
    (h : Lax3Proofs.RamCover.CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : Lax3Proofs.Refine.MassMath.BlockInj n Xoff Xmem)
    (hk : ∀ v : Fin n,
      (Lax12.ColoringNumbers.wreach (Lax3Proofs.RamBfs.masked G A₀) π (2 * r) v).ncard ≤ d)
    (hcomp : Lax3Proofs.RamDriver.Compacted n cnum m A₀ ord Xoff cps) :
    cnum ≤ Lax3Proofs.Refine.MassWeight.arenaWeight n H A₀ ∧
      (∑ k ∈ range cnum, Lax3Proofs.Refine.MassWeight.blockWeight n H Xoff Xmem (cps k))
        ≤ d * (Lax3Proofs.Refine.MassWeight.arenaWeight n H A₀ + 1) :=
  Lax3Proofs.Refine.MassWeight.mass_of_alive_compaction_weight H hord h hinj hk hcomp

/-! ### §4 The coefficient ceiling at the new shape

The arithmetic family of §2's close is `C0CloseProbe`'s own: `g2M` is
unchanged, because `g2m_exists` was already stated at the size-reading
`turnCostSizeA`. So **`8 798 198` survives, unmoved**, and it is a
ceiling on the **coefficient**.

`C0CloseProbe` §3's `DEFICIT ×1489` line is not thereby wrong, and this
is worth stating precisely. That line compares the ceiling against
`131·n + 96`, a **total** — and the comparison is exactly right *for
the landed walk*, because the landed `hbnd`/`hcostI`/`hKsc` chain feeds
a total into the coefficient slot. What B4 changes is not the ceiling
but what the walk supplies: once the chain is restated size-relatively
the number entering the slot is a coefficient, and the same ceiling
becomes reachable. The deficit was never a claim that the coefficient is
too small; it was a claim about which quantity the walk delivers.

What B4 adds is a ceiling one level down: the coefficient is now
*built* out of the walk's chain, so the ceiling back-solves into a
budget on the **formula**, which is what the remaining waves can
actually check.
-/

/-- The measured family with the scatter **coefficient** free — literally
`C0CloseProbe.famHalf` at every other constant measured. -/
def b4Fam (ksc : ℕ) : ℕ := famHalf aOrd kaProbe bDeadProbe ctTurn ksc CbProbe ksentProbe 0

/-- **The B4 shape's arithmetic family IS the measured family.** `g2M`
never mentioned the landed size-blind turn cost, so filling the size
slot moves no number in the close. -/
theorem b4Fam_eq_measured (ksc : ℕ) :
    b4Fam ksc = famHalf aOrd kaProbe bDeadProbe ctTurn ksc CbProbe ksentProbe 0 := rfl

/-- The ε = 1/4 gate, at `C0Probe`'s own instance family. -/
def gateQuarter (b : ℕ) : Prop :=
  (b * (starW (10 ^ 8) + 1)) ^ 4 ≤ (10 ^ 10) ^ 4 * (3 * 10 ^ 8 + 4) ^ 5

instance : DecidablePred gateQuarter := fun _ => inferInstanceAs (Decidable (_ ≤ _))

-- **the reconciliation.** `8 798 198` survives, unmoved, in both
-- directions — and it is a ceiling on the COEFFICIENT.
#guard gateHalf (b4Fam 8798198)
#guard ¬ gateHalf (b4Fam 8798199)
#guard gateOne (b4Fam 152415790731588)
#guard ¬ gateOne (b4Fam 152415790731589)
#guard gateQuarter (b4Fam 66861957)
#guard ¬ gateQuarter (b4Fam 66861958)

/-- **The level's scatter coefficient, off the walk's own chain.**
`clusterStepAt` composes three factors: one atom (`hbnd`), the atom list
of a table (`hcostI`), and the depth's table list (`hKsc`). Read
size-relatively — each `≤ ·(s + 1)` instead of `≤ ·` — the chain
multiplies the same way, so the level's coefficient is the per-atom
coefficient times the two list lengths. `C0CloseProbe.ksc_ge_atom` is the
compiled form of the chain's lower half; this is its upper half. -/
def kscChain (cA na nt : ℕ) : ℕ := (cA * na + 1) * nt + 1

theorem kscChain_ge_atom {cA na nt : ℕ} (hna : 1 ≤ na) (hnt : 1 ≤ nt) :
    cA ≤ kscChain cA na nt :=
  ksc_ge_atom hna hnt (le_refl (cA * na + 1)) (le_refl ((cA * na + 1) * nt + 1))

/-- A concrete per-atom coefficient, for the back-solve: two picks, a
kill batch of `24`, an evaluator fragment of `40`. Every one of the
three is a formula quantity; the numerals are the probe's, and appear
only inside `#guard`s. -/
def cAProbe : ℕ := atomCoeff 24 40 2

#guard cAProbe = 1185

/-! #### The formula budget the ceiling grants, `#guard`ed both directions

At `cAProbe`, with one table (`nt = 1`), the ceiling on the coefficient
back-solves into a ceiling on the **atom count** of the scatter step;
and with the two list lengths held equal it back-solves into a ceiling
on each. The binding gate is ε = 1/2 — ε = 1/4 is looser only because
`C0Probe`'s instance carries `c = 10¹⁰` there against `c = 10⁷` at
ε = 1/2.

| gate | atoms at one table | balanced `#atoms = #tables` |
|---|---|---|
| ε = 1 | `128 620 920 448` | `358 637` |
| ε = 1/2 | `7 424` | `86` |
| ε = 1/4 | `56 423` | `237` |

**These are diagnostics of how the constant scales, NOT a bound on the
formula, and no successor wave should read them as one.** C0
(`Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`)
quantifies `∃ p c T` **after** `∀ φ ε`, so the constant may depend on
both: a formula with more atoms is paid for by a larger `c`, not by a
failure to close. Each row above holds `c` fixed at the instance
family's own value — which is also the whole of why ε = 1/4 looks looser
than ε = 1/2 — and reads off how much formula that particular `c` buys.
The closing theorem `b4_c0_close_real` carries `c` universally and
absorbs `kscN` into `cstarM`, which is where the dependence actually
lives. What these numbers are good for is comparing *currencies*: the
last two `#guard`s put the chain's coefficient at the probe's formula
inside the ceiling and the landed carrier-charged total outside it, on
one screen. -/

-- **ε = 1**
#guard gateOne (b4Fam (kscChain cAProbe 128620920448 1))
#guard ¬ gateOne (b4Fam (kscChain cAProbe 128620920449 1))
#guard gateOne (b4Fam (kscChain cAProbe 358637 358637))
#guard ¬ gateOne (b4Fam (kscChain cAProbe 358638 358638))

-- **ε = 1/2**, the binding gate
#guard gateHalf (b4Fam (kscChain cAProbe 7424 1))
#guard ¬ gateHalf (b4Fam (kscChain cAProbe 7425 1))
#guard gateHalf (b4Fam (kscChain cAProbe 86 86))
#guard ¬ gateHalf (b4Fam (kscChain cAProbe 87 87))

-- **ε = 1/4**
#guard gateQuarter (b4Fam (kscChain cAProbe 56423 1))
#guard ¬ gateQuarter (b4Fam (kscChain cAProbe 56424 1))
#guard gateQuarter (b4Fam (kscChain cAProbe 237 237))
#guard ¬ gateQuarter (b4Fam (kscChain cAProbe 238 238))

-- the chain's coefficient is inside the ceiling at the probe's formula,
-- and the landed carrier-charged TOTAL is not — the two currencies, on
-- one screen
#guard kscChain cAProbe 86 86 ≤ 8798198
#guard ¬ (131 * 10 ^ 8 + 96 ≤ 8798198)

/-! ### §5 The `hbud` wall — does the CLOSE need it, or only the walk?

E4c-a found that `RamDriverCluster.clusterStepImplements` takes
`hbud : ∀ (M' : ℕ → ℕ) (r : ℕ), BallBudget n r G M' O bw nb` — quantified
over **all** masks, because the descent's `Alv'` is existential inside
the proof — and that the same hypothesis character-for-character is
`RamDriverFrames.clusterFrames`. This section separates the two
questions the wall raises.
-/

/-- **The close does not mention the ball budget.** §2's existence probe
is an arithmetic statement about `Ko…Kl`; `hbud` does not occur in it,
in its hypotheses, or in anything it consumes. What the close needs is
`hKscCoeff`, a bound on a coefficient — and *that* is the obligation the
ball budget feeds. So the wall is a **supply** problem, not a shape
problem. The two theorems below are its two halves. -/
theorem close_is_bud_free {ka bd Cb ksent kscN R ℓ D : ℕ} (Ksc : ℕ → ℕ)
    (hKscCoeff : ∀ j < ℓ, Ksc j ≤ kscN) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      (∀ j < ℓ, ∀ s : ℕ, turnCostSizeB4 ctTurn (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
      (∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ range t, bs c) ≤ D * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      (∀ w, Kl 0 w ≤ (ℓ * g2M aOrd bOrd (aCovSlot ka D) (bCovSlot ka D) aDead bd R ctTurn
        kscN D + Cb) * (D + 1) ^ ℓ * (w + 1)) := by
  obtain ⟨Ko, Kc, Kd, Ks, Kl, -, -, -, -, -, hKs, hKlS, -, hcl, -⟩ :=
    b4_size_slot_exists (ka := ka) (bd := bd) (Cb := Cb) (ksent := ksent) (kscN := kscN)
      (R := R) (ℓ := ℓ) (D := D) Ksc hKscCoeff
  exact ⟨Ko, Kc, Kd, Ks, Kl, hKs, hKlS, hcl⟩

/-- **…but the coefficient obligation DOES need the narrowing.** At the
landed ball budget — `ScatterDeadPass.ballBudget_carrier`, which supplies
`bw := ns`, `nb := n` — the ball term alone is `110·n·t`, which no
coefficient chosen before the carrier bounds at a fixed block. So
`hKscCoeff` at the landed `hbud` is exactly as unsatisfiable as
`C0CloseProbe`'s `hKsc` was: the size slot buys nothing until the ball
is read at the block.

This is the compiled answer to "does the close need `hbud` narrowed":
not in its shape, but in its hypothesis — and the hypothesis is the
whole content. -/
theorem carrier_bud_refutes_size_coefficient {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (ksc kq s t : ℕ) (ht : 1 ≤ t) :
    ∃ n ns : ℕ, ¬ (Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β s s kq s ns n t
      ≤ ksc * (s + 1)) := by
  refine ⟨ksc * (s + 1) + 1, 0, fun h => ?_⟩
  rw [deadAtomK_cluster] at h
  have hb : 110 * (ksc * (s + 1) + 1) * 1 ≤ (44 * 0 + 110 * (ksc * (s + 1) + 1) + 140) * t := by
    have := Nat.mul_le_mul_left (44 * 0 + 110 * (ksc * (s + 1) + 1) + 140) ht
    omega
  omega

/-- **The narrowed hypothesis a size-read scatter step needs.** The
descent's mask is supported inside the turn's cluster — that fact is
already inside `clusterStepImplements` (it is the `hsub₁` the descend
clause produces, and what `hwAB` consumes) — so the budget only has to
hold of masks with that support. `bw`/`nb` are then block-scale and
`atomK_le_atomCoeff` applies. -/
def ClusterBallBudget {n : ℕ} (G : SimpleGraph (Fin n)) (M ord O : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (cap k bw nb : ℕ) : Prop :=
  ∀ M' : ℕ → ℕ,
    (∀ v : Fin n, M' (v : ℕ) ≠ 0 →
      v ∈ Lax3Proofs.Refine.MassMath.clusterAt G M π ord cap k) →
    ∀ r : ℕ, Lax3Proofs.Refine.ScatterBlock.BallBudget n r G M' O bw nb

/-- **The narrowing is a WEAKENING.** The landed all-masks hypothesis
implies the cluster-supported one, so replacing `hbud` by
`ClusterBallBudget` breaks no existing consumer — in particular
`ScatterDeadPass.ballBudget_carrier` still discharges it, at the carrier
numbers, for any caller that does not want the narrow reading. The edit
is therefore additive: `clusterStepImplements` may take the weaker
hypothesis and every current call site keeps compiling. -/
theorem clusterBallBudget_of_landed {n : ℕ} {G : SimpleGraph (Fin n)} {M ord O : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {cap k bw nb : ℕ}
    (h : ∀ (M' : ℕ → ℕ) (r : ℕ), Lax3Proofs.Refine.ScatterBlock.BallBudget n r G M' O bw nb) :
    ClusterBallBudget G M ord O π cap k bw nb :=
  fun M' _ r => h M' r

/-- **The lever, compiled: `spec_conj` discards the second cost.** Two
specifications of one command are one specification, **at the first
one's budget** — the second's `K'` does not occur in the conclusion.
So `levelImplements`'s `hframe`, which is merged into `hstep` by exactly
this lemma, is charged a budget that is never read: its cost argument is
dead weight and can be decoupled from `hstep`'s.

The instance below makes it undeniable: the frame may be granted a
budget larger by any margin whatsoever and the merged specification is
still at the step's own budget. -/
theorem frames_cost_is_dead_weight {B : ℕ} {P : Env → Prop} {c : Com}
    {Q Q' : Env → Env → Prop} {K : ℕ} (margin : ℕ)
    (h : Spec B P c Q K) (h' : Spec B P c Q' (K + margin)) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Q' σ σ') K :=
  Lax3Proofs.RamDriverCluster.spec_conj h h'

/-! #### What a decoupling would own

The close needs none of this; the **walk** does. Precisely three
declarations carry the coupled reading, and a decoupling wave owns
exactly them:

1. `RamDriverCluster.clusterStepImplements` — its `hbud` becomes
   `ClusterBallBudget` (a weakening, `clusterBallBudget_of_landed`), so
   the step may run `bw`/`nb` at block scale.
2. `RamDriverFrames.clusterFrames` — its `hbud` is character-for-character
   the same hypothesis, but the frames path needs no narrow reading at
   all; it keeps `ballBudget_carrier` at `bw := ns`, `nb := n`.
3. `RamDriverCluster.levelImplements` — its `hframe` clause, today stated
   at `Ks j (wB Xoff Xmem k)`, takes its own cost function instead. This
   is the only clause where the two paths are welded together, and
   `frames_cost_is_dead_weight` is why the weld is unnecessary:
   `spec_conj` at line 1849 already throws the frames' budget away.

The two root-side instantiations then split: `RamDriverRoot.clusterStepAt`
passes the **narrowed** budget (its `hbnd` moves from the carrier
instantiation `deadAtomK σs.β n n mb n ns n σs.t` to the block reading,
which is expressible there because `blockWeight n G Xoff Xmem k` is
already one of its arguments), while `RamDriverRoot.clusterFramesAt`
keeps `ScatterDeadPass.ballBudget_carrier` unchanged.
`RamDriverRoot.levelAt`'s `hbnd`/`hcostI`/`hKsc` chain is where the
coefficient reading replaces the total (§4's `kscChain`), and it is the
last declaration to move. Note that `Ksc` there is per-LEVEL
(`Ksc : ℕ → ℕ`, indexed by `j` alone): under the size-read slot that is
sound precisely because the number becomes a coefficient — `Ksc j` is
multiplied by `(s + 1)` at each turn's own block — and unsound as long
as it stays a total.
-/

/-! ### §6 Honesty controls

`Refine.CostShapeProbe` style: every positive statement above has a
compiled negative twin. A section proving only the good case is not a
design gate.
-/

/-- **Control 1 — undersized coefficients fail.** A coefficient below
the charge's slope in the block weight loses at large blocks, whatever
the constant term. `154·t + 131` is that slope: `44 + 110` per pick from
the ball, and `131` from the probe, the two member walks and the two
copies at the cluster. -/
theorem undersized_coeff_fails {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (kq t ksc : ℕ)
    (h : ksc < 154 * t + 131) :
    ∃ s : ℕ, ¬ (Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β s s kq s s s t
      ≤ ksc * (s + 1)) := by
  refine ⟨ksc + 1, fun hle => ?_⟩
  rw [deadAtomK_cluster] at hle
  have hd : (44 * (ksc + 1) + 110 * (ksc + 1) + 140) * t
      = 154 * t * (ksc + 1) + 140 * t := by ring
  have hlow : (ksc + 1) * (ksc + 1) ≤ 154 * t * (ksc + 1) + 131 * (ksc + 1) := by
    have h1 : (ksc + 1) * (ksc + 1) ≤ (154 * t + 131) * (ksc + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (154 * t + 131) * (ksc + 1) = 154 * t * (ksc + 1) + 131 * (ksc + 1) := by ring
    omega
  have hhigh : ksc * (ksc + 1 + 1) + 1 = (ksc + 1) * (ksc + 1) := by ring
  omega

/-- **Control 2 — the empty block forces the constant term.** A
coefficient that pays the charge at the empty block must already cover
the pick count, the kill batch and the evaluator's fragment, so no
coefficient is free of the formula. -/
theorem empty_block_forces_constant {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (kq t ksc : ℕ)
    (h : Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β 0 0 kq 0 0 0 t ≤ ksc * (0 + 1)) :
    140 * t + 14 * kq + Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 90 ≤ ksc := by
  rw [deadAtomK_cluster] at h
  omega

/-- **Control 3 — a size-blind charge breaks the close.** This is §1's
`post_copies_blind_slot_refuted`, restated as the control it is: the
close of §2 and the LANDED turn slot are not simultaneously satisfiable,
at any scatter charge that pays one post-E4c-b atom. Filling the size
slot is therefore load-bearing, not cosmetic. -/
theorem size_blind_slot_breaks_close {L : ℕ} (β : Lax3.DistFO.DistFO L 1)
    (kq bw nb t cap mb q_top : ℕ) (φ : Lax3.FirstOrder.FO 0) (Ksc : ℕ → ℕ) :
    ¬ ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
        Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β (10 ^ 10) (10 ^ 10) kq (10 ^ 10)
            bw nb t ≤ Ksc 0 ∧
        (∀ j < 3, ∀ s : ℕ,
          Lax3Proofs.RamDriverRoot.turnCostSize (10 ^ 10) (2 * (10 ^ 10 - 1)) cap mb q_top j φ
            (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
        (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
          (∑ c ∈ range t, bs c) ≤ 8 * (w + 1) →
          Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)))
            ≤ Kl j w) ∧
        (∀ w, Kl 0 w ≤ (3 * g2M aOrd bOrd (aCovSlot kaProbe 8) (bCovSlot kaProbe 8) aDead
          bDeadProbe 0 ctTurn kscProbe 8 + CbProbe) * (8 + 1) ^ 3 * (w + 1)) :=
  post_copies_blind_slot_refuted β kq bw nb t cap mb q_top φ Ksc

/-- **Control 4 — the TOTAL reading is still refuted, at the size slot.**
`C0CloseProbe.narrow_leaf_refutes_constant_ksc` is consumed at the
post-E4c-b arguments: if the walk keeps supplying `Ksc` as a total
through `hbnd`/`hcostI`/`hKsc`, then no constant bounds it however the
four in-scope arguments are narrowed — the size slot does not repair
that by itself. The repair is that the chain must be *restated*
size-relatively (§4's `kscChain`); this control is what says the
restatement is mandatory. -/
theorem total_reading_still_refuted {L : ℕ} (β : Lax3.DistFO.DistFO L 1) (ksc kq m t : ℕ) :
    ∃ n : ℕ, ∀ Kb Ki Ksc' la lt : ℕ, 1 ≤ la → 1 ≤ lt →
      Lax3Proofs.Refine.ScatterDeadTurn.deadAtomK β n m kq m m m t ≤ Kb →
      Kb * la + 1 ≤ Ki → Ki * lt + 1 ≤ Ksc' → ¬ (Ksc' ≤ ksc) :=
  Lax3Proofs.Refine.C0CloseProbe.narrow_leaf_refutes_constant_ksc β ksc m kq m m m t

-- **Control 5 — the ceilings themselves.** The chain's coefficient at
-- the probe's formula clears the binding gate; one atom more at the
-- balanced reading does not.
#guard gateHalf (b4Fam (kscChain cAProbe 86 86))
#guard ¬ gateHalf (b4Fam (kscChain cAProbe 87 87))

-- **Control 6 — the size reading is refuted on data.** A one-member
-- block owning `2·ksc + 1` arena slots: the grant is `2·ksc`, the ball
-- term alone is `44·(2·ksc + 1) + 140`.
#guard ¬ ((44 * (2 * 1000 + 1) + 140) * 1 ≤ 1000 * (1 + 1))
#guard (44 * (2 * 1000 + 1) + 140) * 1 ≤ 1000 * ((1 + (2 * 1000 + 1)) + 1)

/-! ### §7 Axioms -/

#print axioms deadAtomK_closed
#print axioms deadAtomK_cluster
#print axioms deadAtomK_cluster_floor
#print axioms post_copies_atom_unbounded
#print axioms landed_turnCostSize_blind
#print axioms landed_turnCostSize_ge_Ksc
#print axioms blind_slot_floor
#print axioms post_copies_blind_slot_refuted
#print axioms turnCostSizeB4_eq_probe
#print axioms turnCostSizeB4_reads_size
#print axioms turn_leaves_and_scatter_paid
#print axioms b4_size_slot_exists
#print axioms b4_c0_close_real
#print axioms s_is_block_weight
#print axioms blockRowSum_eq_blockDegSum
#print axioms ball_budget_numbers_are_block_weight
#print axioms size_reading_refuted
#print axioms atomK_le_atomCoeff
#print axioms size_slot_sum_le_mass
#print axioms mass_side_condition_at_weight
#print axioms kscChain_ge_atom
#print axioms b4Fam_eq_measured
#print axioms close_is_bud_free
#print axioms carrier_bud_refutes_size_coefficient
#print axioms clusterBallBudget_of_landed
#print axioms frames_cost_is_dead_weight
#print axioms undersized_coeff_fails
#print axioms empty_block_forces_constant
#print axioms size_blind_slot_breaks_close
#print axioms total_reading_still_refuted

end Lax3Proofs.Refine.B4Design
