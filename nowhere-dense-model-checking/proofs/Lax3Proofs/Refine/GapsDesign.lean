import Lax3Proofs.Refine.C0CloseProbe
import Lax3Proofs.Refine.G2ExistsRevalidation
import Lax3Proofs.Refine.BaseShed
import Lax3Proofs.Refine.DeadRowDomain
import Lax3Proofs.Refine.MemThreadGate
import Lax3Proofs.Refine.CompactPreps
import Lax3Proofs.Refine.OrderSigProbeM

/-!
# Gaps-design: the three non-scatter slots of the `hK` ledger, priced up front

`Refine/G2CostProbe.lean` §7 carries a five-entry gap ledger. The
scatter row (`hKs`/`hbnd`) is E4's road and `Refine/B4Design.lean` is
its design gate. This file is the design gate for the other three
— `hKbase`, `hKc`, `hKo` — and it exists because the scatter leaf took
four execution waves, each blocker discovered only when the previous one
cleared. The four questions of that road are asked here **once, for all
three slots, before any of the three execution waves opens**:

1. what the landed walk charges, as a closed form with every size
   carrying its own coefficient;
2. what the target shape is, and whether it fits the M-class slot the
   close already grants (`G2ExistsRevalidation.phaseM`/`phaseBudgetM`,
   `g2m_exists`);
3. what blocks it, and whether the blocker is **accounting**, **program
   text**, or **semantic** — compiled, not asserted;
4. what the closing wave must own, including whether the import order
   forces a driver-file edit.

House style is `Refine/G2CostProbe.lean` and `Refine/B4Design.lean`:
**nothing landed is edited**. Every landed object below is consumed;
every proposed form is a local `def` of this namespace; every claim has
a compiled counterpart or is marked **not compiled**; every proposed
shape carries a negative control.

## The verdicts, in one table

| slot | landed closed form | target fits? | blocker | class | driver-file edit? |
|---|---|---|---|---|---|
| `hKbase` | `(blockCost + 10)·n + 6`, one size (`n`) | **YES**, §1.4/§1.6 | member walk owes only `alive ∪ D`; `levelImplements`' `hbase` is typed at `LevelImplementsFull` | program text **+** semantic (one hypothesis) | **yes** — a new body for `RamDriver.baseCom` (§1.8), `RamDriverCluster.levelImplements` |
| `hKc` | `112·n² + 50·n·ns + 281·n + 156` | **YES** as `kcov·(w+1)`, §2.3 — but its third hypothesis is unproducible, §2.4 | copy at the runtime pointer is still `≥ 12·n + 6`; `coverCost`'s `100·n²`; the carrier-wide `asg` | accounting **then** program text ×2 **then** semantic | **yes** — `RamCover.coverCom`, `RamDriver.coverSave`, `RamDriverCompose.coverImplements` |
| `hKo` | `1600·n + 1350·ns + 60·W + 650` | **YES**, measured `68·m + 12` (`rfl`) | the E2 engines kill the §1 floor and eleven couplings; **one** survives: `OrdersBy`'s carrier-wide contract | semantic, and it is `hKc`'s | **yes** — `RamDriver.orderCom`, `RamCover.OrdersBy`'s consumers |

## Cheapest and riskiest, in one line

**Cheapest: `hKbase`.** Its target fit is compiled end to end
(`base_fits_the_close`), its semantic move is one hypothesis and is a
*weakening* (`baseImplementsD_of_baseImplements`,
`levelImplementsD_bot_of_landed` — so the two halves land in separate
waves with the package green in between), its program delta is one loop
header on one `Com`, and the only missing mathematics was the
member→weight bridge, which is §1.1 and is now landed.

**Riskiest: `hKc`.** Not because its arithmetic is worse — `hKo`'s is —
but because it is the slot that *carries* the shared contract. Its three
blockers must be cleared in a forced order (accounting, then two program
deltas, then the contract), the third is `hKo`'s too (§4), and clearing
it means reopening `RamDriverCluster.levelImplements`' partition step,
whose argument lives inside an induction and is stated nowhere separately
(§5, `MemberOrderContract`). `hKo` is *second* riskiest and it is
strictly downstream: everything of `hKo` except the contract is already
landed capital.

## The finding this wave exists to produce

**`hKo`'s blocker is no longer the twelve interior couplings, and it is
not `hKo`'s own.** `Refine/OrderEngineProbe.lean` refuted twelve member
shapes against the landed engines and named a floor that "survives even
a FREE interior" — the first `elimCom`'s share of the phase clock,
`159·n + 276`. Wave E2 has since landed compacted-arena engines for all
three families, and their charges are carrier-free
(`elimCompactCost mm w = 900·mm + 900·w + 400`,
`symCompactCost mm cs = 300·mm + 200·cs + 400`,
`augCompactCost mm kd W = 8000·W + 9100·mm + 100·kd + 9200`). §3.3
compiles that the floor dies against the E2 form at
`OrderEngineProbe`'s own instance. Of the seven coupling rows, six are
**removed rather than repaired** by compaction (§3.4 records which, and
which of the removals is itself still unstated) — and the seventh,
`OrderEngineProbe` §5's contract-seam, is not removed at all. §4
compiles that this seventh blocker is *the same statement* that blocks
`hKc`: `RamCover.OrdersBy` pins the order array at every carrier
position and `RamCover.CoverOut.asg_lt` pins the assignment array at
every carrier vertex, and a single junk-off-the-members condition
refutes both. So `hKo` and `hKc` are **one semantic obligation with two
cost slots**, not two independent leaves, and no wave can sequence them
apart.

Correspondingly the route this file recommends for `hKbase` differs from
the route the brief for T4b would have taken. `Refine/DeadSweep.lean`
§4b refuted the naive member-list header for the *retired sweep* on the
grounds that `BaseImplements` owes the **whole carrier** — and it does.
But the flip R1.8-T3-flip (c2b) already built the weaker contract
(`RamDriver.LevelImplementsD`, `LevelPostD`, `TableInvOn` at
`alive ∪ D`), and `RamDriverCluster.levelImplements`' bottom case
already holds the incoming `TableInvOn … D` in its own precondition and
already discards it (`hσ.2.2.2.2` is unused; the base's carrier-wide
post is read down by `LevelPost.onD`). §1.5 compiles that the retyped
`hbase` — `LevelImplementsD` in place of `LevelImplementsFull` — is
**sufficient**: the bottom case closes with `Spec.pre` and nothing else.
So the semantic half of `hKbase` is *one hypothesis and one deleted
`.onD`*, which is the cheapest contract move on this road.

## The sections

* **§0** the three landed closed forms, and that all three read the
  carrier at the light arena.
* **§1** `hKbase`: the member→weight bridge (which does not exist and is
  built here), the M-class fit through `g2m_exists`, the contract move
  compiled, the two negative controls.
* **§2** `hKc`: the closed form, the `kcov` slot as an M-class budget,
  and the three blockers each compiled and classified.
* **§3** `hKo`: the measured target, the E2 engine floor discharged, the
  surviving coupling isolated, and the augmentation's `W` residue.
* **§4** the shared semantic seam, compiled once, and its cross-slot
  consequence.
* **§5** the opaque parameters this wave could not close, the
  differential control, and the axiom prints.
-/

namespace Lax3Proofs.Refine.GapsDesign

open Finset
open Lax3Proofs.FormulaTables
open Lax13Proofs.Imp (Env Com)
open Lax13Proofs.Reasoning (Spec)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.Refine.G2ExistsRevalidation
  (phaseM phaseMR phaseBudgetM phaseMR_le_budget phaseMR_empty g2M g2m_exists)

/-! ### §0 The three landed charges, in closed form

Each of the three is restated with every size variable carrying a
distinct coefficient, so that the collapsed carrier reading is visible
as a *special case* and not as the statement. This is
`C0CloseProbe.deadAtomK_root_eq` / `B4Design.deadAtomK_closed`'s
discipline applied to the phase costs. -/

/-- **The landed base charge, closed.** ONE size occurs — the carrier
`n` — at a coefficient determined by the formula alone
(`RamDriverBot.blockCost` of the depth's table list, a quantity of `φ`
fixed before `n`). There is no member count, no slot count and no
width: nothing else to re-attribute, which is why no accounting wave
can move this slot. -/
theorem baseCost_closed (q_top cap mb ℓ n : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ n φ
      = (Lax3Proofs.RamDriverBot.blockCost (tablesAt q_top cap mb φ ℓ) + 10) * n + 6 := by
  simp only [Lax3Proofs.RamDriverBot.baseCost, Lax3Proofs.RamDriverBot.turnCost]

/-- **The landed cover charge, closed.** Four sizes with four distinct
coefficients: the carrier squared, the carrier against the slot count,
the carrier, and the constant. `ns` never occurs alone — every slot term
is multiplied by a carrier term, which is the precise sense in which the
cover phase has no arena-sized reading at all. -/
theorem coverPhaseCost_closed (n ns : ℕ) :
    Lax3Proofs.RamDriverCompose.coverPhaseCost n ns
      = 112 * (n * n) + 50 * (n * ns) + 281 * n + 156 := by
  simp only [Lax3Proofs.RamDriverCompose.coverPhaseCost, Lax3Proofs.RamCover.coverCost]
  ring

/-- …and the cover charge at zero slots is still carrier-quadratic. -/
theorem coverPhaseCost_slotless (n : ℕ) :
    Lax3Proofs.RamDriverCompose.coverPhaseCost n 0 = 112 * (n * n) + 281 * n + 156 := by
  rw [coverPhaseCost_closed]; ring

/-- **The landed order charge, closed.** Three sizes with three distinct
coefficients — carrier, slot count, allocation width — and, unlike the
cover, each appears *alone*. That is why the order slot's repair is a
re-derivation of the interior and not a re-attribution: the carrier term
is a term of its own and there is nothing to hide it in. -/
theorem orderPhaseCost_closed (n ns W : ℕ) :
    Lax3Proofs.RamDriverCompose.orderPhaseCost n ns W
      = 1600 * n + 1350 * ns + 60 * W + 650 := rfl

/-- …and at the light arena it is still `1600·n + 650`. -/
theorem orderPhaseCost_light_arena (n : ℕ) :
    Lax3Proofs.RamDriverCompose.orderPhaseCost n 0 0 = 1600 * n + 650 := by
  simp only [Lax3Proofs.RamDriverCompose.orderPhaseCost]

/-- **All three read the carrier, at the light arena, at once.** The
single statement the three slots have in common, and the reason all
three sit in the ledger: at `ns = W = 0` — an arena of weight `O(1)`
inside a carrier of `n` — each of the three charges is `Ω(n)`. Every
`k·(w + 1)` budget is `k` there. -/
theorem all_three_read_the_carrier (q_top cap mb ℓ n : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    4 * n + 6 ≤ Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ n φ ∧
      281 * n + 156 ≤ Lax3Proofs.RamDriverCompose.coverPhaseCost n 0 ∧
      1600 * n + 650 ≤ Lax3Proofs.RamDriverCompose.orderPhaseCost n 0 0 := by
  refine ⟨?_, ?_, le_of_eq (orderPhaseCost_light_arena n).symm⟩
  · rw [baseCost_closed]
    have h : 1 ≤ Lax3Proofs.RamDriverBot.blockCost (tablesAt q_top cap mb φ ℓ) :=
      Lax3Proofs.RamDriverBot.one_le_blockCost _
    nlinarith
  · rw [coverPhaseCost_slotless]; omega

/-! ### §1 `hKbase` — the member-driven base

The landed walk is `RamDriver.baseCom = RamDriver.sweepCom` (R1.8-T4a
shed the representative scan; `Refine.BaseShed` is the ledger), whose
loop header is `.while (.lt (.var "z") (.var "n"))` — the carrier. The
member list it would walk instead already exists: `RamDriver.LevelPre`'s
sixteenth clause carries `RamDriver.MemEnum n mm Mem M` at every depth,
including `ℓ`.

Four things have to hold, and this section compiles all four.

* **§1.1** the member count is under the arena **weight**. This is the
  bridge the whole M class rides on and **it does not exist in the
  package**: `MemEnum.card_le` gives `mm ≤ n`, `MassWeight` gives
  `arenaSize ≤ arenaWeight`, and nothing joins them. §1.1 joins them,
  by `ArenaBlock.cnum_le_arenaSize`'s own argument at a shorter
  injection.
* **§1.2/§1.3** the proposed charge, and that it is `phaseM`-shaped with
  a constant empty-arena reading.
* **§1.4** it fits the base slot `g2m_exists` already grants
  (`∀ w, Cb·(w + 1) ≤ Kl ℓ w`), at `Cb = turnCost + 10` — which is
  `G2CostProbe.sweepCoeffA` on the nose, because the base pass and the
  retired sweep are literally the same `Com`.
* **§1.5** the contract move: the retyped `hbase` is **sufficient**.
* **§1.6** the two negative controls — accounting cannot (cost side),
  and the weakened post really is weaker (semantic side). -/

section Base

variable {n mm : ℕ} {Mem M : ℕ → ℕ}

/-! #### §1.1 The member count against the arena weight -/

/-- **A member list is no longer than the arena.** `MemEnum`'s second
clause makes `k ↦ Mem k` strictly increasing, hence injective, and its
third clause lands it in the mark set, so the list injects into the
alive set and `mm ≤ arenaSize n M`.

This is `Refine.ArenaBlock.cnum_le_arenaSize`'s argument with the `ord`
composition deleted — the member list is already a list of vertices, so
no `OrdersBy` inversion is needed. It is stated here because the
package has `MemEnum.card_le` (`mm ≤ n`, the *carrier* bound, useless
for the M class) and nothing else. -/
theorem memEnum_card_le_arenaSize (h : Lax3Proofs.RamDriver.MemEnum n mm Mem M) :
    mm ≤ Lax3Proofs.RamDriver.arenaSize n M := by
  classical
  rcases Nat.eq_zero_or_pos mm with rfl | hpos
  · exact Nat.zero_le _
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (h.1 0 hpos)
  set f : ℕ → Fin n := fun k => ⟨Mem k % n, Nat.mod_lt _ hn⟩ with hf
  have hfval : ∀ k, k < mm → ((f k : Fin n) : ℕ) = Mem k :=
    fun k hk => Nat.mod_eq_of_lt (h.1 k hk)
  have hmaps : ∀ k ∈ range mm,
      f k ∈ ({v : Fin n | M (v : ℕ) ≠ 0} : Set (Fin n)).toFinset := by
    intro k hk
    have hkc := mem_range.mp hk
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    rw [hfval k hkc]
    exact h.2.2.1 k hkc
  have hinj : ∀ k ∈ range mm, ∀ k' ∈ range mm, f k = f k' → k = k' := by
    intro k hk k' hk' he
    have hkc := mem_range.mp hk
    have hkc' := mem_range.mp hk'
    have hme : Mem k = Mem k' := by rw [← hfval k hkc, ← hfval k' hkc', he]
    rcases Nat.lt_trichotomy k k' with hl | hq | hg
    · exact absurd hme (Nat.ne_of_lt (h.2.1 k k' hl hkc'))
    · exact hq
    · exact absurd hme.symm (Nat.ne_of_lt (h.2.1 k' k hg hkc))
  have hcard := Finset.card_le_card_of_injOn f hmaps
    (fun k hk k' hk' he => hinj k (Finset.mem_coe.mp hk) k' (Finset.mem_coe.mp hk') he)
  rw [Finset.card_range] at hcard
  have hcards : ({v : Fin n | M (v : ℕ) ≠ 0} : Set (Fin n)).toFinset.card
      = Lax3Proofs.RamDriver.arenaSize n M := by
    rw [Lax3Proofs.RamDriver.arenaSize, Set.ncard_eq_toFinset_card']
  omega

/-- **…and no longer than the arena's WEIGHT**, which is the size
variable every G2 phase budget is read at. The second step is landed
(`MassWeight.arenaSize_le_arenaWeight`, at `graphW ≥ 1`). -/
theorem memEnum_card_le_arenaWeight (H : SimpleGraph (Fin n))
    (h : Lax3Proofs.RamDriver.MemEnum n mm Mem M) :
    mm ≤ Lax3Proofs.Refine.MassWeight.arenaWeight n H M :=
  le_trans (memEnum_card_le_arenaSize h)
    (Lax3Proofs.Refine.MassWeight.arenaSize_le_arenaWeight n H M)

/-- **The member walk never touches the pre-written domain.** `D` is a
set of *dead* vertices (`LevelImplementsD`'s own first hypothesis) and
every listed member is alive, so the two are disjoint: a member-driven
base cannot destroy the rows its caller wrote. This is the clause the
carrier walk supplied by overwriting `D` with the *same* values
(`DeadRow.sat_bot_of_dead`); the member walk supplies it by not writing
there at all. -/
theorem member_notMem_deadDomain {D : Set (Fin n)}
    (h : Lax3Proofs.RamDriver.MemEnum n mm Mem M)
    (hD : ∀ v : Fin n, v ∈ D → M (v : ℕ) = 0) {k : ℕ} (hk : k < mm) :
    (⟨Mem k, h.1 k hk⟩ : Fin n) ∉ D :=
  fun hmem => h.2.2.1 k hk (hD _ hmem)

end Base

/-! #### §1.2 The proposed charge -/

/-- **PROPOSED** base charge: the landed base pass with its loop header
at the member list. Nothing else about the pass changes — the turn is
`RamDriverBot.base_turn_spec` verbatim, parametric in the loop variable,
so the closed form is the landed one with `mm` in place of `n`. -/
noncomputable def baseCostM (q_top cap mb ℓ mm : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  (Lax3Proofs.RamDriverBot.turnCost q_top cap mb ℓ φ + 4) * mm + 6

/-- **The proposed charge IS the M-class shape** — `phaseM` at the
landed per-vertex coefficient, by `rfl`. -/
theorem baseCostM_eq_phaseM (q_top cap mb ℓ mm : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    baseCostM q_top cap mb ℓ mm φ
      = phaseM (Lax3Proofs.RamDriverBot.turnCost q_top cap mb ℓ φ + 4) 6 mm := rfl

/-- **The empty-arena reading is a constant** — the property
`OrderBlockProbe.nested_emptyCharge_floor` shows every solvable form
must have, and the landed charge does not. -/
theorem baseCostM_empty (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    baseCostM q_top cap mb ℓ 0 φ = 6 := by simp only [baseCostM]; omega

/-- **The landed charge at the same reading is `Ω(n)`** — the contrast,
in one line: the two costs agree at `mm = n` and diverge everywhere
else, which is exactly what "the header moved" means. -/
theorem baseCost_eq_baseCostM_at_carrier (q_top cap mb ℓ n : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ n φ = baseCostM q_top cap mb ℓ n φ := rfl

/-! #### §1.3 The coefficient -/

/-- **PROPOSED** base coefficient for the `hKbase` slot. It is
`G2CostProbe.sweepCoeffA` on the nose (`CbM_eq_sweepCoeffA`), which is
right and not a coincidence: since R1.8-T4a `RamDriver.baseCom` *is*
`RamDriver.sweepCom` (`DeadSweep.baseCost_eq`), so the base pass and the
retired dead sweep have one coefficient between them. -/
noncomputable def CbM (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  Lax3Proofs.RamDriverBot.turnCost q_top cap mb ℓ φ + 10

theorem CbM_eq_sweepCoeffA (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    CbM q_top cap mb ℓ φ = Lax3Proofs.Refine.G2CostProbe.sweepCoeffA q_top cap mb ℓ φ := rfl

/-- …and it is inside the design's own proposed base coefficient, which
still carries the twelve the representative scan's removal freed. -/
theorem CbM_le_baseCoeffA (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    CbM q_top cap mb ℓ φ ≤ Lax3Proofs.Refine.G2CostProbe.baseCoeffA q_top cap mb ℓ φ := by
  simp only [CbM, Lax3Proofs.Refine.G2CostProbe.baseCoeffA]
  omega

/-! #### §1.4 The fit -/

/-- **The proposed charge fits the slot the close already grants.** Any
`Kl` meeting `g2m_exists`' base clause at `Cb := CbM` pays the
member-driven base at the arena weight — the reading
`RamDriverCluster.levelImplements` takes its `hbase` at
(`Kl ℓ (wA M)`). The only new input is §1.1. -/
theorem baseSlot_paid {q_top cap mb ℓ n mm : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {Mem M : ℕ → ℕ} {Kl : ℕ → ℕ → ℕ} (H : SimpleGraph (Fin n))
    (hmem : Lax3Proofs.RamDriver.MemEnum n mm Mem M)
    (hKl : ∀ w, CbM q_top cap mb ℓ φ * (w + 1) ≤ Kl ℓ w) :
    baseCostM q_top cap mb ℓ mm φ
      ≤ Kl ℓ (Lax3Proofs.Refine.MassWeight.arenaWeight n H M) := by
  refine le_trans ?_ (hKl _)
  have hw := memEnum_card_le_arenaWeight H hmem
  have h1 : (Lax3Proofs.RamDriverBot.turnCost q_top cap mb ℓ φ + 4) * mm
      ≤ (Lax3Proofs.RamDriverBot.turnCost q_top cap mb ℓ φ + 4)
          * Lax3Proofs.Refine.MassWeight.arenaWeight n H M :=
    Nat.mul_le_mul_left _ hw
  simp only [baseCostM, CbM]
  nlinarith

/-- **`hKbase` fits, end to end.** The `g2m_exists` witness family,
instantiated at `Cb := CbM`, pays the member-driven base at the arena
weight and still closes to the same `(D + 1)^ℓ · (w + 1)` root shape.
This is the compiled answer to question 2 for this slot: **the target
shape fits the M-class slot, with no new interface**. -/
theorem base_fits_the_close (q_top cap mb ℓ n mm D R ao bo ac bc ad bd ct ksc : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (Ksc : ℕ → ℕ) (hKsc : ∀ j < ℓ, Ksc j ≤ ksc)
    {Mem M : ℕ → ℕ} (H : SimpleGraph (Fin n))
    (hmem : Lax3Proofs.RamDriver.MemEnum n mm Mem M) :
    ∃ Kl : ℕ → ℕ → ℕ,
      baseCostM q_top cap mb ℓ mm φ
          ≤ Kl ℓ (Lax3Proofs.Refine.MassWeight.arenaWeight n H M) ∧
        (∀ w, Kl 0 w ≤ (ℓ * g2M ao bo ac bc ad bd R ct ksc D + CbM q_top cap mb ℓ φ)
          * (D + 1) ^ ℓ * (w + 1)) := by
  obtain ⟨Ko, Kc, Kd, Ks, Kl, -, -, -, hbase, -, -, -, hcl⟩ :=
    g2m_exists ℓ D (CbM q_top cap mb ℓ φ) R ao bo ac bc ad bd ct ksc Ksc hKsc
  exact ⟨Kl, baseSlot_paid H hmem hbase, hcl⟩

/-! #### §1.5 The contract move, compiled

`RamDriverCluster.levelImplements` takes its `hbase` at
`RamDriver.LevelImplementsFull` — the carrier-wide obligation, which
since the flip only the bottom satisfies — and reads the base's
carrier-wide post down with `RamDriver.LevelPost.onD`. A member-driven
base cannot inhabit that type (§1.6). What it *can* inhabit is the
obligation below, and the point of this subsection is that the
obligation below is **enough**: the bottom case of `levelImplements`
closes from it with `Spec.pre` and nothing else, because the incoming
`RamDriver.TableInvOn … D` the flip put into `LevelImplementsD`'s
precondition is exactly the missing half.

So the semantic delta of wave T4b is: **one hypothesis retyped in
`RamDriverCluster.lean`, one `.onD` deleted, and `RamDriver.lean` gains
`BaseImplementsD` beside `BaseImplements`.** -/

/-- **PROPOSED** obligation for a member-driven base pass. It is
`RamDriver.BaseImplements` with three changes and no others:

* the post is `RamDriver.LevelPostD … D` — the alive rows the member
  walk writes, plus the caller's pre-written `D`;
* the pre gains `RamDriver.TableInvOn … D`, the clause that carries `D`
  across the pass (the walk does not touch it, §1.1's
  `member_notMem_deadDomain`);
* the hypothesis `2 ^ sigL cap mb ℓ < B` is dropped — R1.8-T4a's shed
  made it unused in `RamDriverCompose.baseImplements` already, and a
  weaker precondition is the honest statement.

The `masked G M = ⊥` hypothesis stays: it is what the bottom of the
recursion supplies (`eq_bot_of_playOk_full`) and what makes the depth's
`botCom` fragments compute the right truth values. -/
def BaseImplementsD (B q_top cap mb ns W ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (O T : ℕ → ℕ) (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (D : Set (Fin n)) (K : ℕ) : Prop :=
  ∀ {d : ℕ}, Lax3Proofs.RamDriver.WordBoundK B n d ns cap mb → masked G M = ⊥ →
  (∀ v : Fin n, v ∈ D → M (v : ℕ) = 0) →
  (∀ c < sigL cap mb ℓ, ∀ v < n, C c v ≤ 1) →
    Spec B (fun σ => Lax3Proofs.RamDriver.LevelPre B n cap mb ns W O T ℓ M Gm C σ ∧
        Lax3Proofs.RamDriver.TablesSized q_top cap mb φ n σ ∧
        Lax3Proofs.RamDriver.BaseArrs B q_top cap mb ℓ φ σ ∧
        Lax3Proofs.RamDriver.TableInvOn q_top cap mb φ G ℓ M C D σ)
      (Lax3Proofs.RamDriver.baseCom q_top cap mb ℓ φ)
      (fun σ σ' =>
        Lax3Proofs.RamDriver.LevelPostD B q_top cap mb φ G ns W O T ℓ M Gm C D σ σ' ∧
          σ'.out = σ.out) K

/-- **THE CONTRACT MOVE IS COMPLETE.** From the proposed obligation, the
level obligation at the bottom follows — at the same budget, for every
pre-written domain, with no clause of the bottom case needing the
carrier. Compare `RamDriverCluster.levelImplements`' zero branch: this
is that branch with `hpost.onD _` replaced by threading `hσ.2.2.2.2`
into the base's own precondition.

**What this compiles, and what it does not.** It compiles that the
retyped `hbase` slot is *sufficient* — the closing wave does not have to
discover a further clause. It does **not** compile that a member-driven
`baseCom` inhabits `BaseImplementsD`: that is the program-text half, and
it is `RamDriverBot.base_spec` re-run over a member header, which is
wave T4b's own work. -/
theorem levelImplementsD_bot {B q_top cap mb R ℓ W ns d K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {n : ℕ} {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {D : Set (Fin n)}
    (hB : Lax3Proofs.RamDriver.WordBoundK B n d ns cap mb) (hbot : masked G M = ⊥)
    (hbase : BaseImplementsD B q_top cap mb ns W ℓ φ G O T M Gm C D K) :
    Lax3Proofs.RamDriver.LevelImplementsD B q_top cap mb R ℓ W ns ℓ φ G O T M Gm C D K := by
  intro hDdead hbit
  rw [Lax3Proofs.RamDriver.driverAt_bot]
  exact (hbase hB hbot hDdead hbit).pre (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩)

/-- **And the landed obligation still implies the proposed one**, so the
retyping is a weakening of the slot and cannot break the current
discharge: whatever `RamDriverCompose.baseImplements` proves today
inhabits `BaseImplementsD` too, by `LevelPost.onD`. The move is
therefore safe to make *before* the member header exists — which is what
makes the two halves of T4b separable. -/
theorem baseImplementsD_of_baseImplements {B q_top cap mb ns W ℓ K : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {n : ℕ} {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {D : Set (Fin n)}
    (hpow : 2 ^ sigL cap mb ℓ < B)
    (h : Lax3Proofs.RamDriver.BaseImplements B q_top cap mb ns W ℓ φ G O T M Gm C K) :
    BaseImplementsD B q_top cap mb ns W ℓ φ G O T M Gm C D K := by
  intro d hB hbot _ hbit
  refine ((h hB hpow hbot hbit).pre (fun _ hσ => ⟨hσ.1, hσ.2.1, hσ.2.2.1⟩)).post ?_
  exact fun _ _ _ hq => ⟨hq.1.onD _, hq.2⟩

/-- **The retyped slot reproduces today's discharge.** §1.5 composed with
the weakening: the landed `RamDriverCompose.baseImplements` still closes
the bottom of the recursion *through the retyped `hbase`*, at the same
budget and at every pre-written domain.

So the contract move can land in one wave and the member header in the
next, with the package green in between — no flag day. That property is
the main reason this file calls `hKbase` the cheapest of the three. -/
theorem levelImplementsD_bot_of_landed {B q_top cap mb R ℓ W ns d K : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {n : ℕ} {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {D : Set (Fin n)}
    (hB : Lax3Proofs.RamDriver.WordBoundK B n d ns cap mb)
    (hpow : 2 ^ sigL cap mb ℓ < B) (hbot : masked G M = ⊥)
    (h : Lax3Proofs.RamDriver.BaseImplements B q_top cap mb ns W ℓ φ G O T M Gm C K) :
    Lax3Proofs.RamDriver.LevelImplementsD B q_top cap mb R ℓ W ns ℓ φ G O T M Gm C D K :=
  levelImplementsD_bot hB hbot (baseImplementsD_of_baseImplements hpow h)

/-! #### §1.6 The negative controls -/

/-- **Control (cost): accounting cannot.** The landed base charge
escapes its own proposed coefficient at the light arena, for every
formula and depth — `G2CostProbe.hKbase_gap_any` at `Cb := CbM`. So the
program text has to move: there is no re-attribution of the landed walk
that meets a weight-linear slot. -/
theorem landed_base_escapes_CbM (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∃ n : ℕ, ¬ (Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ n φ
      ≤ CbM q_top cap mb ℓ φ * (0 + 1)) :=
  Lax3Proofs.Refine.G2CostProbe.hKbase_gap_any (CbM q_top cap mb ℓ φ) q_top cap mb ℓ φ

/-- **Control (semantic): the weakened post really is weaker.** So a
member-driven base — which writes rows at the members only — cannot be
typed at `RamDriver.LevelImplementsFull`, and the contract move of §1.5
is *forced*, not a convenience. This is
`DeadRowDomain.tableInvOn_strictly_weaker` cited at the base's own
depth: at the all-dead mask the domain `alive ∪ ∅` is empty, so a junk
table satisfies `TableInvOn` and refutes `TableInv`. -/
theorem memberBase_cannot_meet_full (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (hlen : 0 < (tablesAt q_top cap mb φ ℓ).length) :
    ∃ (M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env),
      Lax3Proofs.RamDriver.TableInvOn q_top cap mb φ (⊥ : SimpleGraph (Fin 2)) ℓ M C
          ({v : Fin 2 | M (v : ℕ) ≠ 0} ∪ (∅ : Set (Fin 2))) σ ∧
        ¬ Lax3Proofs.RamDriver.TableInv q_top cap mb φ (⊥ : SimpleGraph (Fin 2)) ℓ M C σ :=
  Lax3Proofs.Refine.DeadRowDomain.tableInvOn_strictly_weaker q_top cap mb ℓ φ hlen

/-! #### §1.7 Falsification of the proposed charge, on numbers

`RamDriverBot.turnCost` is noncomputable (`tablesAt`), so the per-vertex
charge is a parameter `K` here, exactly as `Refine.BaseShed`'s own
falsification section does it. Both directions, and the undersized
control. -/

section BaseFalsification

/-- The proposed charge at per-turn charge `K` over `mm` members. -/
private def nbM (K mm : ℕ) : ℕ := (K + 4) * mm + 6

-- the charge, both directions
#guard nbM 10 100 = 1406
#guard ¬ (nbM 10 100 = 1405)
#guard ¬ (nbM 10 100 = 1407)

-- the empty-arena reading is the constant `6`, at every `K`
#guard nbM 10 0 = 6
#guard nbM 10000 0 = 6

-- the proposed coefficient pays …
#guard nbM 10 100 ≤ (10 + 10) * (100 + 1)
#guard nbM 10 1000000 ≤ (10 + 10) * (1000000 + 1)
-- … and an undersized one does not, so the coefficient is load-bearing
#guard ¬ (nbM 10 100 ≤ 13 * (100 + 1))
#guard ¬ (nbM 10 1000000 ≤ 13 * (1000000 + 1))

-- and the landed reading at the SAME arena inside a carrier of `10^6`
-- is five orders of magnitude larger: `mm = 2` against `n = 10^6`
#guard nbM 10 2 = 34
#guard nbM 10 1000000 = 14000006
#guard 34 * 100000 < 14000006

end BaseFalsification

/-! #### §1.8 The one trap in the program-text half -/

/-- **`baseCom` and the retired `sweepCom` are the same term**, by `rfl`
— which is R1.8-T4a's shed, and which is also a trap for wave T4b: a
member header written into `RamDriver.sweepCom` moves the *retired* dead
sweep with it and breaks `Refine.DeadSweep.sweepImplements`, kept in the
tree as the record of what the flip removed.

So the program-text half must give `RamDriver.baseCom` its **own** body —
one new `Com` in `RamDriver.lean`, beside the untouched `sweepCom` — and
the visible signal that the edit landed on the right declaration is that
`Refine.DeadSweep.baseCost_eq` stops being provable by `rfl`. That is a
one-line consequence for the closing wave, and it is exactly the kind of
coupling the scatter road discovered one wave too late four times. -/
theorem baseCom_is_sweepCom (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    Lax3Proofs.RamDriver.baseCom q_top cap mb ℓ φ
      = Lax3Proofs.RamDriver.sweepCom q_top cap mb ℓ φ := rfl

/-! ### §2 `hKc` — the cover phase

`Refine.CoverBlock` (wave E3a) landed the leaf side: the Σ-shaped centre
loop, the member copy at the true write pointer, and the export
`coverPhaseCostB_le_weight` at coefficient `kcov`. What is missing is
the composition, and this section compiles that the missing part is
**three blockers of three different classes**, in a forced order.

* **§2.3** the target shape fits: `kcov·(w + 1)` *is* a `phaseBudgetM`,
  so the close grants the slot.
* **§2.4(a)** the `12·n²` is an accounting loss — and the accounting fix
  does **not** finish: `CoverBlock.carrier_le_arena_of_coverOut` gives
  `n ≤ m`, so the export's third hypothesis `m ≤ D·(w + 1)` is a
  *carrier* bound wearing a weight bound's clothes. **Accounting, then
  program text.**
* **§2.4(b)** `RamCover.coverCost`'s `100·n²` is `n` centre turns each
  running a carrier-charged search. Two program deltas — the outer loop
  and the body. The body's engine is landed and unwired
  (`Refine.BfsBlock`/`BfsBlockCost`). **Program text.**
* **§2.4(c)** `RamCover.CoverOut.asg_lt` assigns *every carrier vertex*.
  **Semantic**, and it is §4's shared seam. -/

/-- **The `kcov` slot IS an M-class budget.** `CoverBlock.kcov`'s
`k·(w + 1)` is `phaseBudgetM k 0 0 w`, so the cover slot needs no new
interface: `g2m_exists`' cover clause already grants exactly this
shape. Question 2 for this slot answers **yes**, at the interface. -/
theorem kcov_is_phaseBudgetM (kc ka D w : ℕ) :
    Lax3Proofs.Refine.CoverBlock.kcov kc ka D * (w + 1)
      = phaseBudgetM (Lax3Proofs.Refine.CoverBlock.kcov kc ka D) 0 0 w := by
  simp only [phaseBudgetM]
  ring

/-- **…and the landed leaf export lands in it.** `E3a`'s
`coverPhaseCostB_le_weight`, restated at the M-class budget so that the
cover slot's fit is visible in the same vocabulary as the other two.
The three hypotheses are E3a's own; §2.4 is about the third. -/
theorem coverPhaseB_fits_M_slot {kc ka mlen mm D w : ℕ} {bw : ℕ → ℕ}
    (hmlen : mlen ≤ w) (hball : (∑ k ∈ range mlen, bw k) ≤ D * (w + 1))
    (hmm : mm ≤ D * (w + 1)) :
    Lax3Proofs.Refine.CoverBlock.coverPhaseCostB kc ka mlen bw mm
      ≤ phaseBudgetM (Lax3Proofs.Refine.CoverBlock.kcov kc ka D) 0 0 w := by
  rw [← kcov_is_phaseBudgetM]
  exact Lax3Proofs.Refine.CoverBlock.coverPhaseCostB_le_weight hmlen hball hmm

/-- **Blocker (a), compiled: the export's third hypothesis is a CARRIER
bound.** From the cover pass's own postcondition the arena is at least
the carrier (`CoverBlock.carrier_le_arena_of_coverOut`, which needs no
aliveness — a centre always lies in its own cluster), so any producer of
`m ≤ D·(w + 1)` has produced `n ≤ D·(w + 1)`.

That is the precise sense in which E3a's F-1 ("the `12·n²` is an
accounting loss") does not finish the slot: re-charging the copy at the
runtime pointer `m` is sound and free, and it leaves a bound that no
light arena inside a large carrier can satisfy. The repair has to be the
*alive prefix* (`CoverBlock.memCopy_alive_prefix_le_weight` costs it),
which is program text in `RamDriver.coverSave`. -/
theorem landed_copy_hmm_forces_carrier {n : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r m D w : ℕ}
    (hord : Lax3Proofs.RamCover.OrdersBy n π ord)
    (hout : Lax3Proofs.RamCover.CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hmm : m ≤ D * (w + 1)) : n ≤ D * (w + 1) :=
  le_trans (Lax3Proofs.Refine.CoverBlock.carrier_le_arena_of_coverOut hord hout) hmm

/-- …and a carrier bound is not a weight bound: the carrier is chosen
after `D` and `w`. The negative control for §2.4(a). -/
theorem carrier_bound_is_not_a_weight_bound (D w : ℕ) : ∃ n : ℕ, ¬ (n ≤ D * (w + 1)) :=
  ⟨D * (w + 1) + 1, by omega⟩

/-- **Blocker (a), the floor it leaves.** Even at the honest pointer
charge, the member copy costs at least `12·n + 6` at *every* level — so
no coefficient read at the arena weight pays it while the copy runs to
the write pointer. `CoverBlock.memCopyK_carrier_floor` is the landed
half; this is the consequence for the slot. -/
theorem landed_copy_no_weight_coeff {n : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r m k : ℕ}
    (hord : Lax3Proofs.RamCover.OrdersBy n π ord)
    (hout : Lax3Proofs.RamCover.CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hk : k < 12 * n + 6) :
    ¬ (Lax3Proofs.Refine.CoverBlock.memCopyK m ≤ k * (0 + 1)) := by
  have h := Lax3Proofs.Refine.CoverBlock.memCopyK_carrier_floor hord hout
  omega

/-- **Blocker (b), compiled: the pass itself is carrier-quadratic.** One
centre per carrier vertex, each running a carrier-charged search
(`RamCover.centreCost n ns = 100·n + 50·ns + 100`, carrier-charged
through `BfsBridge.bfsQCom_spec`). -/
theorem coverCost_quadratic_floor (n ns : ℕ) :
    100 * (n * n) ≤ Lax3Proofs.RamCover.coverCost n ns := by
  simp only [Lax3Proofs.RamCover.coverCost]
  nlinarith [Nat.zero_le (50 * n * ns), Nat.zero_le (200 * n)]

/-- …so no weight-read coefficient pays the pass either, at the light
arena. The negative control for §2.4(b): two program deltas — the outer
loop off the compacted list (`CoverBlock.centreLoopCom`'s shape, landed as
`centreLoop_spec`) and the body off the ball engine
(`BfsBlockCost.centreObligation_of_ballCost`, landed and unwired). -/
theorem coverCost_no_weight_coeff (k : ℕ) :
    ∃ n : ℕ, ¬ (Lax3Proofs.RamCover.coverCost n 0 ≤ k * (0 + 1)) := by
  refine ⟨k + 1, fun h => ?_⟩
  have hf := coverCost_quadratic_floor (k + 1) 0
  nlinarith

/-! ### §3 `hKo` — the order phase

The target is **measured**, not proposed: `Refine.OrderSigProbeM`
clocked a member-driven order-phase text at `68·m + 12` on the tower's
executable semantics, at three member counts and two carrier widths, and
`G2ExistsRevalidation.phaseClockK_eq_phaseM` ties that law to `phaseM`
by `rfl`. So question 1 and question 2 are already answered for this
slot, and the whole content is question 3.

`Refine.OrderEngineProbe` answered question 3 in 2026-07 with seven
coupling rows and a floor, **against the landed carrier engines**. Wave
E2 replaced those engines. This section re-asks the question against the
replacements. -/

/-- **The measured target, cited.** The law the member-driven text
clocks *is* the M-class shape. -/
theorem order_target_is_measured (m : ℕ) :
    Lax3Proofs.Refine.OrderSigProbeM.phaseClockK m = phaseM 68 12 m :=
  Lax3Proofs.Refine.G2ExistsRevalidation.phaseClockK_eq_phaseM m

/-- …and its empty-arena reading is the constant `12`, which is the
property `OrderBlockProbe.nested_emptyCharge_floor` proves every
solvable `hKo` form must have. -/
theorem order_target_empty : phaseM 68 12 0 = 12 := by simp only [phaseM]

/-! #### §3.3 The engine floor, discharged

`OrderEngineProbe` §1's floor is the one finding that "survives even a
FREE interior": at a fixed two-member arena the landed first
`RamElim.elimCom` call clocks `159·n + 276` — affine in the *carrier* —
and at `n = 800` it already exceeds `orderCostA (bsq 2 2 0) 0 4`, the
§2.1 budget at that arena's weight. Below: the same instance, against
the E2 engine's charge. -/

/-- The measured law of the landed engine's share of the phase clock,
`OrderEngineProbe` §1's four pinned points as a function. -/
def elimShareLaw (n : ℕ) : ℕ := 159 * n + 276

/-- The §2.1 order budget at `OrderEngineProbe` §1's own instance
(`d = D₁ = 2`, `R = 0`, arena weight `4`), pinned to the real budget by
the `#guard` below so the numeral cannot drift. -/
def ordBudget221 : ℕ := 103950

#guard Lax3Proofs.Refine.G2CostProbe.orderCostA
  (Lax3Proofs.Refine.G2CostProbe.bsq 2 2 0) 0 4 = ordBudget221

/-- **The landed engine share breaks the budget** — `OrderEngineProbe`
§1's floor, at its own carrier. -/
theorem elimShareLaw_exceeds_budget : ¬ (elimShareLaw 800 ≤ ordBudget221) := by
  simp only [elimShareLaw, ordBudget221]
  omega

/-- **The E2 engine at the SAME arena does not** — and, decisively, its
charge does not mention the carrier at all, so the statement holds at
every carrier at once. `OrderEngineProbe` §1's floor is therefore
**discharged**: it was a fact about `RamElim.elimCom` in context, not
about the order phase. -/
theorem elimCompact_inside_budget :
    Lax3Proofs.Refine.ElimCompact.elimCompactCost 2 4 ≤ ordBudget221 := by
  rw [Lax3Proofs.Refine.ElimCompact.elimCompactCost_eq]
  simp only [ordBudget221]
  omega

/-- **The E2 elimination fits the arena-weight budget, generically.** At
member count under the weight and slot reading under `D·(w + 1)` — the
two suppliers `MassWeight.mass_of_alive_compaction_weight` already
delivers for the cover — the compacted engine is weight-linear at
coefficient `900·D + 1300`. No carrier term enters. -/
theorem elimCompact_le_weight {mm w D wt : ℕ} (hmm : mm ≤ wt) (hw : w ≤ D * (wt + 1)) :
    Lax3Proofs.Refine.ElimCompact.elimCompactCost mm w ≤ (900 * D + 1300) * (wt + 1) := by
  rw [Lax3Proofs.Refine.ElimCompact.elimCompactCost_eq]
  have h1 : 900 * w ≤ 900 * (D * (wt + 1)) := Nat.mul_le_mul_left _ hw
  have h2 : 900 * mm ≤ 900 * wt := Nat.mul_le_mul_left _ hmm
  nlinarith

/-- **And so does the E2 symmetrization**, at coefficient `200·D + 700`.
Same two suppliers, same absence of `n`. -/
theorem symCompact_le_weight {mm cs D wt : ℕ} (hmm : mm ≤ wt) (hcs : cs ≤ D * (wt + 1)) :
    Lax3Proofs.Refine.SymCompact.symCompactCost mm cs ≤ (200 * D + 700) * (wt + 1) := by
  rw [Lax3Proofs.Refine.SymCompact.symCompactCost_eq]
  have h1 : 200 * cs ≤ 200 * (D * (wt + 1)) := Nat.mul_le_mul_left _ hcs
  have h2 : 300 * mm ≤ 300 * wt := Nat.mul_le_mul_left _ hmm
  nlinarith

/-- **The one E2 charge that is NOT weight-linear: the augmentation
round reads the allocation width.** `augCompactCost mm kd W` carries
`8000·W`, and `W` is an input-scaling parameter, so at a light arena the
round escapes every constant. This is not a defect of E2 — it is the
`TgtCoupling.chainWidth` → `G2CostProbe.chainWidthE` repair, design item
(ii-a), showing up at the engine. -/
theorem augCompact_no_weight_coeff (k : ℕ) :
    ∃ W : ℕ, ¬ (Lax3Proofs.Refine.AugCompact.augCompactCost 0 0 W ≤ k * (0 + 1)) := by
  refine ⟨k + 1, fun h => ?_⟩
  rw [Lax3Proofs.Refine.AugCompact.augCompactCost_eq] at h
  omega

/-- **…and it is out of scope for the C0 close, which runs at `R = 0`.**
At zero augmentation rounds the fold is `Com.skip` and the order phase's
cost is `orderPhaseCost` on the nose, so the width residue above is a
debt of the `R > 0` road (design item ii-a) and not of `hKo`'s close.
Landed: `RamDriverCompose.orderPhaseCostR_zero`. -/
theorem aug_out_of_scope_at_R_zero (n ns W : ℕ) :
    Lax3Proofs.RamDriverCompose.orderPhaseCostR n ns W 0
      = Lax3Proofs.RamDriverCompose.orderPhaseCost n ns W :=
  Lax3Proofs.RamDriverCompose.orderPhaseCostR_zero n ns W

/-! #### §3.4 The couplings, re-classified against the E2 engines

**This table is NOT COMPILED.** It is a reading of the landed E2
statements against `OrderEngineProbe`'s landed refutations, and each cell
names the landed clause it rests on so the reading can be checked
without re-deriving it. What *is* compiled is §3.3 (the floor the table's
last column would otherwise have to carry) and §4 (the one row that does
not clear). The zero-seam row's own gap is named as a `Prop` in §5.

`OrderEngineProbe`'s table has seven rows over the twelve probe passes.
Read against the compacted engines rather than the landed carrier ones:

| row (probe passes) | seam | against E2 |
|---|---|---|
| 1–2 saves, 6–7 restores | restore-seam §3 | **removed.** `SymCompact.symCompact_spec`'s conclusion pins the tail: `(σ''.arrs "off").drop (mm + 1) = (σ.arrs "off").drop (mm + 1)`. There is nothing off the prefix to restore, so the save/restore pair is a *prefix* pair. `SymCompact` §8 states this as removal, not repair. |
| 3 mask copy, 4–5 in-lists | read-seam §4 | **removed.** The compacted engine reads the *compact* CSR the member list builds (`ElimCompact.CompactInstalls`), not `alv` at every carrier vertex. |
| 8–9, 11–12 re-zeros | zero-seam §2 | **removed in the program, NOT YET STATED.** The engine runs at carrier `mm`, so its scratch flags live on `[0, mm)` and the re-zero is a prefix write. But `ElimCompact.elimCompact_spec`'s conclusion carries **no tail clause** — unlike its two siblings — so the fact that `OrderMem`'s carrier-wide zeroed-scratch clause survives is not available. §5's `ElimTailPinned` is that gap, named. |
| 10 `mordPass` | contract-seam §5 | **NOT removed.** §4. |

So the re-classification is: the twelve interior couplings are no longer
twelve. Six of the seven rows are removed by compaction (one of them
with a stated-but-unproved tail clause), and the seventh is a contract
that `hKc` shares. -/

/-! ### §4 The shared semantic seam

`OrderEngineProbe` §5 refuted the member inversion against
`RamCover.OrdersBy` on data. Below is the same fact as a statement about
the landed contracts, and the observation that makes this wave's report:
**`RamCover.OrdersBy` and `RamCover.CoverOut.asg_lt` are refuted by one
and the same condition**, so `hKo`'s surviving blocker and `hKc`'s
semantic blocker are one obligation. -/

/-- **The ordering contract is carrier-wide, both ways.** Every position
holds a genuine vertex, and every vertex occupies some position — so
`OrdersBy` determines the whole of `ord` on `[0, n)` and there is no
sub-carrier reading of it. Both halves are landed
(`RamCover.OrdersBy.lt`, and the definition itself for the onto half);
they are collected here because the two together are what forbids a
member-scale producer. -/
theorem ordersBy_carrier_wide {n : ℕ} {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ}
    (h : Lax3Proofs.RamCover.OrdersBy n π ord) :
    (∀ c, c < n → ord c < n) ∧ (∀ u, u < n → ∃ c, c < n ∧ ord c = u) :=
  ⟨fun _ hc => h.lt hc,
   fun u hu => ⟨((π ⟨u, hu⟩ : Fin n) : ℕ), (π ⟨u, hu⟩ : Fin n).isLt, h ⟨u, hu⟩⟩⟩

/-- **The contract-seam, generically.** A pass that leaves position `c`
holding a value that is not a vertex refutes `OrdersBy` — for every
permutation at once, so no choice of ordering repairs it. This is
`OrderEngineProbe` §5's data refutation (`¬ ordersByAt 4 …`) as a
statement, and it is what a member-scale inversion does at every
non-member position: the incoming array is scratch, and `LevelPre` says
nothing about its contents. -/
theorem ordersBy_refuted_off_members {n : ℕ} {ord : ℕ → ℕ} {c : ℕ}
    (hc : c < n) (hjunk : n ≤ ord c) :
    ∀ π : Equiv.Perm (Fin n), ¬ Lax3Proofs.RamCover.OrdersBy n π ord :=
  fun _ h => absurd (h.lt hc) (by omega)

/-- **The cover's assignment contract is refuted by the same
condition.** `RamCover.CoverOut.asg_lt` is "every vertex has been
assigned a centre position", quantified over the carrier — so a
member-scale cover leaves junk at the dead vertices and refutes the
cover's own postcondition, whatever its centres and blocks are. -/
theorem coverOut_refuted_off_members {n : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg : ℕ → ℕ} {r m w : ℕ}
    (hw : w < n) (hjunk : n ≤ asg w) :
    ∀ π : Equiv.Perm (Fin n),
      ¬ Lax3Proofs.RamCover.CoverOut G A₀ π ord r m Xoff Xmem asg :=
  fun _ h => absurd (h.asg_lt w hw) (by omega)

/-- **THE CROSS-SLOT FINDING, compiled.** One junk-off-the-members
condition at one position refutes *both* landed contracts at once: the
order phase's postcondition and the cover phase's. So `hKo`'s surviving
coupling (`OrderEngineProbe` §5) and `hKc`'s semantic blocker
(`CoverOut.asg_lt`) are not two leaves to be sequenced — they are one
obligation with two cost slots hanging off it, and any wave that
restates one contract at the members must restate the other in the same
breath.

Consequence for the wave order: **`hKc` and `hKo` cannot be separate
execution waves.** `OrderEngineProbe` §6 sequenced E2 before E3 before
E6 on the grounds that "E2 is coupled to E3 through the ordering
contract"; this theorem is that coupling, compiled, and it says the
coupling is symmetric. -/
theorem shared_contract_seam {n : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg : ℕ → ℕ} {r m c : ℕ} (hc : c < n)
    (hord : n ≤ ord c) (hasg : n ≤ asg c) :
    (∀ π : Equiv.Perm (Fin n), ¬ Lax3Proofs.RamCover.OrdersBy n π ord) ∧
      (∀ π : Equiv.Perm (Fin n),
        ¬ Lax3Proofs.RamCover.CoverOut G A₀ π ord r m Xoff Xmem asg) :=
  ⟨ordersBy_refuted_off_members hc hord, coverOut_refuted_off_members hc hasg⟩

/-- **The seam is not vacuous** — the refuting condition is satisfiable
at every carrier: an array that holds the sentinel `n` off the members
is exactly what `RamCover.initAsg` writes and what a member-scale pass
would leave. Negative control for §4. -/
theorem shared_seam_instance (n : ℕ) (hn : 0 < n) :
    ∀ π : Equiv.Perm (Fin n), ¬ Lax3Proofs.RamCover.OrdersBy n π (fun _ => n) :=
  ordersBy_refuted_off_members (c := 0) hn le_rfl

/-! ### §5 What this wave could not close

Everything below is an explicitly named opaque parameter or an
explicitly **not compiled** statement. None of them is a plugged
numeral. -/

/-- **OPAQUE — the cover phase's arena-driven residue `ka`.** Whatever
the composed cover phase pays per member beyond the centre loop and the
member copy. No wave has measured it; `C0CloseProbe.kaProbe = 20` is a
placeholder that appears only in `#guard`s. Every theorem of §2 carries
it as a parameter; this is the `hKc` coefficient with the measured
centre constant plugged (`C0CloseProbe.kcCov = 150`,
`CoverBlock.centreK_root_admissible`) and `ka` still free, so that the
one unmeasured number of the slot has a name here too. -/
def kcovOpen (ka D : ℕ) : ℕ :=
  Lax3Proofs.Refine.CoverBlock.kcov Lax3Proofs.Refine.C0CloseProbe.kcCov ka D

/-- …and it is `162·D + ka + 166` — one free number, linear in the cover
degree. Landed as `CoverBlock.kcov_root`. -/
theorem kcovOpen_eq (ka D : ℕ) : kcovOpen ka D = 162 * D + ka + 166 :=
  Lax3Proofs.Refine.CoverBlock.kcov_root ka D

/-- **NOT COMPILED — the elimination's missing tail clause.**
`SymCompact.symCompact_spec` and `AugCompact.augCompact_spec` both pin
the tail of the array they write off the compact prefix
(`(σ''.arrs "off").drop (mm + 1) = …`, `(σ''.arrs "alv").drop mm = …`).
`ElimCompact.elimCompact_spec`'s conclusion has no such clause, and
`ElimCompact.ElimMemPost` reads `"ork"` only at member positions and
says nothing about `"elm"`/`"bh"` at all.

That clause is exactly what turns `OrderEngineProbe`'s zero-seam
(rows 8–9 and 11–12: `RamDriver.OrderMem`'s carrier-wide zeroed-scratch
obligation) from *repaired* into *removed*. The generic machinery to
prove it is already in `ElimCompact` §3 (`padArrs`/`cutArrs`/`tailOf`
and `run_of_run_cutArrs`), so this is a statement gap and not a
mathematics gap — but it is a gap, and the E-order wave owns it.

This `Prop` is the statement, unproved, so that the wave has a name to
discharge. It is **not** used by any theorem above. -/
def ElimTailPinned (B mm : ℕ) (names : List String) : Prop :=
  ∀ (σ σ' : Env) (K : ℕ),
    Lax13Proofs.Reasoning.Run B Lax3Proofs.Refine.ElimCompact.elimCompactCore σ σ' K →
      ∀ a ∈ names, (σ'.arrs a).drop mm = (σ.arrs a).drop mm

/-- **NOT COMPILED — the member-restated ordering contract.** §4 says
the landed contract cannot be produced at member scale; it does not say
what replaces it. The replacement has to be a `RamCover.OrdersBy`-twin
quantified over the member list, together with the corresponding
weakening of `RamCover.CoverOut.asg_lt` and of
`RamDriverCluster.levelImplements`' partition step — the step that today
reads a turn's readback at *every* carrier vertex of a cluster. Whether
the partition step survives the weakening is the single open question of
the combined `hKc`/`hKo` wave, and this wave did not answer it: the
argument lives inside `levelImplements`' induction and is not stated
separately anywhere.

This `Prop` names the shape. It is **not** used by any theorem above. -/
def MemberOrderContract {n : ℕ} (mm : ℕ) (Mem : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord : ℕ → ℕ) : Prop :=
  ∀ k, k < mm → ∀ hk : Mem k < n, ord ((π ⟨Mem k, hk⟩ : Fin n) : ℕ) = Mem k

/-- **The member contract is strictly weaker than the landed one** — the
compiled half of the previous docstring, so that the replacement is
known to be a weakening and not a rename. -/
theorem memberOrderContract_of_ordersBy {n mm : ℕ} {Mem : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ}
    (h : Lax3Proofs.RamCover.OrdersBy n π ord) : MemberOrderContract mm Mem π ord :=
  fun _ _ hk => h ⟨_, hk⟩

/-- …and the converse fails: at an empty member list every array meets
the member contract, including the junk array §4 refutes. So the
weakening is real, and the whole question of the combined wave is what
the *consumers* need. -/
theorem memberOrderContract_not_ordersBy (n : ℕ) (hn : 0 < n) :
    MemberOrderContract 0 (fun _ => 0) (Equiv.refl (Fin n)) (fun _ => n) ∧
      ∀ π : Equiv.Perm (Fin n), ¬ Lax3Proofs.RamCover.OrdersBy n π (fun _ => n) :=
  ⟨fun _ hk => absurd hk (by omega), shared_seam_instance n hn⟩

/-! #### The three slots on one instance

A differential control in `Refine.CostShapeProbe`'s style: a two-member
arena inside a carrier of `10^6`, the landed three charges against the
proposed three, with the per-turn charge as a parameter `K` (the landed
`turnCost` is noncomputable). The proposed cover charge is read at the
E2 elimination's shape, since §2/§3 put the cover's centre body on the
same block engine.

The point of the instance is the *order*: the landed sum is quadratic in
the carrier, the proposed sum is linear in the members, and the ratio at
this instance is over `10^4` even after paying the proposed sum once per
carrier vertex. -/

section ThreeSlots

/-- The landed three, at per-turn charge `K` and carrier `n`. -/
private def landedThree (K n : ℕ) : ℕ :=
  ((K + 4) * n + 6) + (112 * (n * n) + 281 * n + 156) + (1600 * n + 650)

/-- The proposed three, at per-turn charge `K` and member count `mm`:
the member base, the compacted elimination at `mm` members and `mm`
slots, and the measured order clock. -/
private def proposedThree (K mm : ℕ) : ℕ :=
  ((K + 4) * mm + 6) + (900 * mm + 900 * mm + 400) + (68 * mm + 12)

#guard landedThree 10 1000000 = 112001895000812
#guard proposedThree 10 2 = 4182
#guard proposedThree 10 0 = 418
-- the proposed sum is `O(1)` on the empty arena; the landed one is not
#guard ¬ (landedThree 10 1000000 ≤ 418 * 1000000)
#guard proposedThree 10 2 * 1000000 < landedThree 10 1000000
-- and both directions on the two numerals, so neither can drift
#guard ¬ (landedThree 10 1000000 = 112001895000811)
#guard ¬ (proposedThree 10 2 = 4183)

end ThreeSlots

/-! ### Axioms -/

#print axioms baseCost_closed
#print axioms coverPhaseCost_closed
#print axioms coverPhaseCost_slotless
#print axioms orderPhaseCost_closed
#print axioms orderPhaseCost_light_arena
#print axioms all_three_read_the_carrier
#print axioms baseCostM_eq_phaseM
#print axioms baseCostM_empty
#print axioms baseCost_eq_baseCostM_at_carrier
#print axioms CbM_eq_sweepCoeffA
#print axioms CbM_le_baseCoeffA
#print axioms order_target_empty
#print axioms shared_seam_instance
#print axioms memEnum_card_le_arenaSize
#print axioms memEnum_card_le_arenaWeight
#print axioms member_notMem_deadDomain
#print axioms baseSlot_paid
#print axioms base_fits_the_close
#print axioms levelImplementsD_bot
#print axioms baseImplementsD_of_baseImplements
#print axioms levelImplementsD_bot_of_landed
#print axioms landed_base_escapes_CbM
#print axioms memberBase_cannot_meet_full
#print axioms baseCom_is_sweepCom
#print axioms kcov_is_phaseBudgetM
#print axioms coverPhaseB_fits_M_slot
#print axioms landed_copy_hmm_forces_carrier
#print axioms landed_copy_no_weight_coeff
#print axioms coverCost_quadratic_floor
#print axioms coverCost_no_weight_coeff
#print axioms order_target_is_measured
#print axioms elimShareLaw_exceeds_budget
#print axioms elimCompact_inside_budget
#print axioms elimCompact_le_weight
#print axioms symCompact_le_weight
#print axioms augCompact_no_weight_coeff
#print axioms aug_out_of_scope_at_R_zero
#print axioms ordersBy_carrier_wide
#print axioms ordersBy_refuted_off_members
#print axioms coverOut_refuted_off_members
#print axioms shared_contract_seam
#print axioms memberOrderContract_of_ordersBy
#print axioms memberOrderContract_not_ordersBy
#print axioms kcovOpen_eq

end Lax3Proofs.Refine.GapsDesign
