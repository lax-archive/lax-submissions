# ND-MC: the road to C0

Rev 1, 2026-08-08. Status: **PROPOSAL — not adopted.** Supersedes the road
sketch in `nd-mc-rebase-plan.md` §"the compiled residue" (`b02f83a`) and the
2026-08-08 session wrap's successor note; both are folded in below and neither
is contradicted except where flagged.

Assembled from eleven read-only audits against `aa6e681`, then attacked by
three adversarial reviews and two settling probes. Every claim below carries
either a file:line citation or an explicit ESTIMATE label. Where an audit and
an adversary disagreed, the disagreement was settled by re-reading the source,
and the settlement is recorded.

---

## §0 What this plan is not

A prior draft of this document opened with a phase of cost-ledger repairs — a
`rfl` completeness theorem for `turnCost`, seven "linkage" propositions tying
each ceiling-table constant to a driver cost, eight stale-constant fixes, and a
`DriverCost`/`Row` structure making non-driver constants unnameable. **All of
it is deleted, on evidence:**

- The `rfl` lemma is vacuous or impossible. Stated in `turnCost`'s own
  right-nested shape it proves `X = X`; stated flat it fails `rfl`
  (`Not a definitional equality`). What works is `rw [turnCost]; omega`, which
  is already the house pattern verbatim at `Refine/SlotSweep.lean:491-494`.
- The `#guard`s are impossible. `turnCost` is `noncomputable` — `killCost` and
  `rbCost` route through `tablesAt`, which is `Classical.choose`.
  `RamDriver.lean:150-152` says so: *"the program cannot be run by `#guard`"*.
  Only `descendCost`, `colourCost`, `killListCost` are guardable.
- The stale constants are all prose. The build is green at 3593 jobs and the
  `#guard`s are two-directional, so no stale numeral can sit anywhere that
  would fail. Repairing `16·n² → 24·n²` moves `level_cost_floor_sharp` from
  `128·n³` to `136·n³`: refuting harder something already refuted.
- The `Row` structure targets a real defect (*"the ceiling table answers 'is
  the number small enough', not 'is the number the driver's'"*) that is
  **already fully enumerated** at `nd-mc-rebase-plan.md:426-435`. The
  instrument that found it is a grep.
- The one argument for keeping a five-line restatement — that
  `hKs_carrier` goes dark when the size slot fills — is **void**. `b4-iface`
  cannot fill that slot (`G2CostProbe.hKs_gap:799` compiles that no
  `turnCostSizeA`-shaped budget pays a turn while `descendCost` opens with
  `24·n²`), and `Refine/SlotSweep.lean:6-7` is by definition the B7 re-run's
  opening leaf, so the restatement is owned.

`CLAUDE.md`: *the proof is the work; process exists only when it removes a
demonstrated risk.* The risk was already removed.

**Also not in this plan: any framework migration.** Five directions were
audited and each is refuted or dominated — index-set framing (additive and
cheap, but retrospectively break-even and it would *not* have bought back the
mask-support waves), sub-array ownership (rejected in writing at
`plans/word-ram/tower-expansion/p4.5-design.md:354-358`, no ND-MC demand), time
credits (zero consumers; `Amortization.lean` is not in ND-MC's import closure;
the load-bearing amortization is `Spec.while_potential`), asymptotic interfaces
(Lean blocks cross-declaration metavariables at two layers; symbolic constants
degrade the arithmetic from `omega` to hand-fed `calc`), and multi-currency
export (recoverable in ~15 lines at `Codegen/Cash.lean:314`, but it cannot
cross `embed` — IMP+ has one clock).

**And not in this plan: deleting the `pu` colour family.** The syntactic half
of the case is true, but the invariant is not provable as stated (depth-≥1
tables come from `Classical.choose` via `Assembly.locality`, whose conclusion
admits `distColorLt`), `isoPalette` indexes a `Fin` so the change is
type-level, it moves `hpow` — the word bound in `levelAt` — and it forces
removing `DistFO.distColorLt` from `concepts/`. Dropped.

---

## §1 Where the campaign actually stands

**The target is refuted through the current root, by the campaign's own
compiled theorem.** `Refine/SlotSweep.lean:600`
`driverRoot_decides_sentence_floored` takes `driverRoot_decides_sentence`'s
hypothesis list verbatim and returns its Spec **together with**
`128·n³ ≤ Kdec + (Kl 0 (n+ns) + Ksent)`; the `#guard` at `:713` exceeds C0's
ε = ½ budget by twelve orders. `G2CostProbe.hKs_gap:799` is universally
quantified in `ct`, `ksc`, `Kin`: **no constant closes the turn slot.**

**`turnCost` has eight summands and four are carrier-charged**
(`RamDriverRoot.lean:506-513`):

| summand | shape | owner |
|---|---|---|
| `descendCost n ns cap j` | `24n² + 98n + 61 + ballCost + batchCost` | §2.5 |
| `23·n + 12·mb + 30` | Θ(n) — **no cost-function name, no ledger row** | §2.5 |
| `colourCost n ns cap mb (sigL …)` | `(15n+6)L+(12n+6)+slotCost·(mb+L+1)+3` | §2.5 |
| `killCost` | carrier-blind ✓ | — |
| `killListCost` | carrier-blind ✓ | — |
| `Kin`, `Ksc` | slots | §2.1 |
| `rbCost q_top cap mb φ j n` | Θ(n) per turn | §2.2 |

The measured turn constant `ctTurn = 443` (`C0CloseProbe.lean:225`) covers two
of the eight, at one probe instance (`mb = 3`), plus a *proposal* for part of a
third. **No theorem anywhere bounds the whole turn** — every occurrence of
`turnCost` with `≤` on the right is a hypothesis; the only conclusions with it
on the right are floors.

**Good news, compiled:** `#guard gateHalf famHalfMeasured`
(`C0CloseProbe.lean:586-588`) — at every measured constant the ε = ½ close
clears, with 10⁴–10⁶ of headroom on every row but `ksc`, which was closed on
the carrier axis on 2026-08-08. **The algorithm is not a dead end. The gap is
shape, not headroom.**

**And the fidelity finding that reframes the work.** GKS charges each cluster
`O(|V(G_X)| + |E(G_X)|)` with `n_X ≤ |X|`, and the whole `n^{1+ε}` proof rests
on `Σ_X n_X ≤ n^{1+δ}` (`references/gks/nowheredense.tex:2745-2748`, eq.
`mt2`). Both disputed passes exist in the source **at the same frequency** —
once per cluster (`:2549-2560`, `:2605-2609`) — but on the cluster, not the
carrier. This is not a frequency bug. It is the campaign's own recurring scope
failure, and both work-sets are cluster-scoped **by necessity** and
carrier-scoped **only by contract**.

---

## §2 The road

Each item is a landing boundary: reviewable, landable, green in between.
Sizes are ESTIMATES calibrated on the measured rate — **~800 net lines and
~54 minutes per wave, one wave at a time** (2m-1 +898, 2m-2 +903, 2m-3 +600).

### §2.1 `b4-iface` — cash the three landed waves at the root

**Status 2026-08-10: landed on the campaign branch.** `Kb`/`Ki`/`Ksc` are
block-indexed through the root consumers, the carrier bridge is gone, and the
retired dead sweep has been removed semantically from both the root program
budget and the Σ recurrence.  The reduced interface and every downstream
probe pass the 3593-job `proofs` build.  The next dependency leaf is §2.2.

**First, because the campaign says so and because nothing else is true yet.**
`NIGHTLOG.md` session wrap: *"Where a successor starts: `b4-iface`."*

The 2026-08-08 waves (2m-1/2m-2/2m-3) are **not load-bearing at the root**:
`RamDriverRoot.lean:762-765` still reads `deadAtomK σs.β n n mb n ns n σs.t ≤ Kb`
— the carrier instantiation, verbatim. `scatterBnd_cluster` bridges the new
block reading back to it. `b4-iface` makes `Kb`/`Ki`/`Ksc` families of the
block reading, deletes `scatterBnd_cluster`, and takes the `hKd` slot with it.

Constrained by a compiled fact the brief must carry:
`ScatterDeadTurn.deadAtomKX_block_unbounded` — the block reading lives strictly
below `clusterStepAt`; nothing block-scale may touch `Ksc`.

**`hKd` is not a statement deletion and was already refused once.** On
2026-08-08 (`R1.8-T3-flip (c2b)`) a worker refused it: four *unowned* consumers
(`g2_plug`, `BridgeSeamProbe`, `BridgeCrossing`, `SlotSweep`) apply the root's
19-argument hypothesis list positionally. Worse, `Kd j m` appears inside
`hKl`'s **conclusion** (`RamDriverRoot.lean:783-785`), so removing the slot
reshapes the Σ-closure inequality — a semantic change. The recorded
consequence of the half-done attempt is the hazard to guard: *"the program's
cost fell and the stated budget did not."*

**Size: 4–5 sub-waves** (ESTIMATE) — the `levelAt`/`hKl`/`levelCost_of_sigma`/
root pair; the `DriverRootD` mirror; the probe files; the two bridge files.
Not one wave. Do not dispatch as one.

### §2.2 The readback block walk

**Status 2026-08-10: complete on the campaign branch.** `readbackCom` now walks
`[Xoff cur, Xoff (cur + 1))`, loads each row through `Xmem`, and retains the
assignment guard.  `RamDriverBase.readback_spec` is block-sized, its invariant
is indexed by block slots, and the readback's scalar/frame surface now includes
`z`, `zend`, and `rv`.  The proof no longer asks for a carrier-wide assignment
bound: `CoverOut.mem_lt` and `CoverOut.asg_lt` discharge the loaded member
pointwise. `ReadbackStep` is indexed by the static block centre, and the
cluster/root contracts now charge `rbCost` at that block's weight; the only
weakening is the proved `blockSize ≤ blockWeight` bridge. The restated root and
all downstream probes consume the new family, `turnCostSize_reads_size`
compiles that the slot is genuinely live, and the 3593-job `proofs` build
passes. `B4Design`'s surviving negative control is correspondingly narrowed:
the remaining floor comes from additive `Ksc`, not from readback blindness.
The next dependency leaf is §2.3.

**Landable now, against the LANDED contract, green in between.** The write set
only shrinks, and every new obligation follows a fortiori from clauses already
in hand (`hout.block c hcur`, `Compacted.alive`,
`MassAlive.inCluster_alive_iff` — used exactly this way at
`RamDriverDescend.lean:2577-2590`).

`readbackCom` (`RamDriver.lean:2206-2217`) is `while z < n` with the body
guarded by `asg[z] = cur`. The write set is *already* the block; only the walk
is the carrier. Replace with a walk of `[Xoff cur, Xoff (cur+1))` writing row
`Xmem p`, guard preserved.

Three payoffs, only one of which is on any current list:

1. `rbCost`'s Θ(n) per turn leaves `turnCost` — **`hKs` money the campaign has
   not counted.**
2. `hasgB : ∀ v < n, asg v < B` (`RamDriverBase.lean:876`) stops being a
   carrier-wide consumer as a side effect; the walk reads `Xmem p`, bounded by
   `mem_lt`. Same for the threaded-but-unconsumed `∀ z < n, ord z < n`.
3. It is the **prerequisite** for §2.6's contract wave — it is what replaces
   the dead branch `hdeadne` (`RamDriverCluster.lean:1840-1844`), whose
   consumption of `CoverOut.asg_cover` at a *dead* vertex is the one part of
   the partition step that does not survive member-weakening.

The alternative repair — an off-member sentinel pin on `asg` — is **rejected**:
establishing it needs a carrier-wide sentinel fill per level, reinstating an
Ω(n) init. That is the touched-only trap, and Wave C would inherit it.

Real cost: the loop invariant moves from a counter prefix to a block-index
prefix over a possibly-repeating `Xmem` (the body is idempotent, so repeats are
harmless, but the invariant must be restated); and `readbackCom`'s
`warrs`/`wvars` change, touching six frame lemmas at `RamDriverWrites.lean:683-691,
1585, 1631, 1696, 1758`. Frame breakage is this campaign's most-repeated defect
class — brief it explicitly.

**Size: 1–2 sub-waves** (ESTIMATE), ~700–1000 lines.

### §2.3 The `expandStep` tightening

**Status 2026-08-10: complete on the campaign branch.** `expandStep_spec` is
indexed by its static row and charges `24·rowLen z + 40`; the scan proof now
uses `ScanHit`'s live lower endpoint instead of discarding it with
`Nat.sub_le`. `expandCom_spec` uses `forRangeZeroSum`, and `sum_rowLen`
telescopes the row family to the exact bound `24·ns + 44·n + 6`.  The tighter
formula has propagated through both `slotCost` and `ballCost`, and the full
3593-job `proofs` build passes.  The next dependency leaf is §2.4.

`expandStep_spec` discharges its scan obligation at `RamDriverDescend.lean:1004-1009`
by `Nat.sub_le`, throwing away the row's start, with `hρ` bound and unused. The
tight fact is `ScanHit`'s fourth component (`RamDriverCluster.lean:448`,
`O z ≤ ρ.vars "j"`). The Σ-shaped loop rule is landed and already in scope:
`Refine/SigmaLoop.lean:47` `forRangeZeroSum`, with a per-iteration budget
`Kb : ℕ → ℕ`, already used with a varying budget at `RamDriverCluster.lean:1952`.
The closing lemma is landed: `RamBfs.lean:286` `sum_rowLen`.

Charge goes from `(24·ns + 44)·n + 6` to `24·ns + 44·n + 6`.

**What it buys is not a constant.** The loose `(24·ns+44)·n` is the *same
subexpression* in `ballCost` (`:2880`) and `slotCost` (`:1682`), so one `hK`
lambda plus a rule swap kills the `n·ns` product in `descendCost` **and**
`colourCost`. The plan of record prices this as engine work — *"re-walking
`ballCom_spec` and `batchCom_spec` at block scale"* — and at least the `n·ns`
half of it is accounting. It breaks no floor: `ballCost` carries no `n²`, and
`omega` never looks inside it.

**This is two edits, not a defect class.** 20 of 22 `Csr.rowScan_spec` sites in
ND-MC already carry the tight bound under one uniform house idiom; no
`ownerScan_spec`/`drain_spec` sites exist. The other loose site is
`clusterLoad`, and it is not an accounting fix — see §2.5.

**Size: 1 sub-wave** (ESTIMATE).

### §2.4 The `colourCost` re-association

**Status 2026-08-10: complete on the campaign branch.** `colourCost` now
retains `oldCom`'s exact flat-pass charge and applies `slotCost` only to the
batch and colour expansion profiles.  `colourCom_spec` proves the resulting
bound by normalising the three sequential run costs, with no monotonic
overcharge.  The targeted `RamDriverDescend` build passes.  The next
dependency leaf is §2.5.

`oldCom` runs **no expansion** (`RamDriver.lean:1502-1506`; its cost carries no
`cap` — `RamDriverDescend.lean:1651`) but `colourCost` bills it at
`slotCost·(L+1)`, rounded up at `:2076-2085`. Re-associating is free: the two
consumers (`RamDriverRoot.lean:509` as an addend, `:2213` as a hypothesis) are
both monotone in the value.

Not `rfl` and not `omega` — the goal atomises. It needs `ring`, and the `ring`
step is **already written** at `:2079-2082`.

Saving is `(L+1)/(2(L+1)+mb)`, tending to a half for `j ≥ 1`; at `j = 0`,
`sigL = 0` so it is `1/(2+mb)`.

**Size: 1 sub-wave** (ESTIMATE). Sequential after §2.3 — same file.

### §2.5 `E4c-descend` — the engine wave

**This is where the order changes, and it is not a swap.** `Refine/BlockLeaves.lean`
has **zero** `Spec B` and zero `Run`; its `Com` tokens are `Ir.Com`, not
`Imp.Com`. There is nothing to swap in. `G2CostProbe.lean:794-798` says so.

Contents:

1. **The import re-layer.** Four import drops — `ExpandSynth←RamDriverDescend`,
   `ArenaBlock←RamDriver`, `SigmaLoop←RamDriver`, `CoverBlock←RamDriverCompose`
   — verified three times independently to be exactly right, mutually
   necessary, and sufficient: all of `BlockLeaves`, `CoverBlock`, `MassWeight`,
   `ArenaBlock`, `SigmaLoop` reach zero driver files in closure. **The move
   list is eight declarations, not four**: `arenaSize` (`RamDriver.lean:1007`),
   `Compacted` + `Compacted.inj` (`:1084`, `:1108`), `markSet`
   (`RamDriverCluster.lean:289`), `expandVal` (`:386`),
   `expandVal_of_dead` (`RamDriverDescend.lean:823`), and from
   `RamDriverCompose`: `coverPhaseCost`, `xmem_ne_xmmName`, `copyPrefix_spec`.
   `SigmaLoop` needs `import Lax13Proofs.Reasoning` **added**, not merely the
   drop — its `Com`/`Spec` arrive transitively today.
   Precedent: `7a42ae7`, +96/−57, *"no mathematics"* — split into a new file
   **keeping the namespace**, so every qualified name resolves.
   Hazard: `markSet` has 177 uses across 20 files, 78 of them in
   `RamDriverDescend.lean` — the file this phase single-owner-locks. Sequence
   the move before the engine work or eat a merge conflict in 4568 lines.

   **Status 2026-08-10:** complete in `Refine/DriverPrelude.lean`. The actual
   elaborated closure also required moving the driver-independent primitives
   `xmmName`, `fillUpto`, `copyUpto`, `hit_eq_expandVal`, `forRangeZero'`, and
   `fillPrefix_spec`; leaving any one below its former driver made one of the
   five target closures cyclic. `BlockLeaves`, `CoverBlock`, `MassWeight`,
   `ArenaBlock`, and `SigmaLoop` now reach zero `RamDriver*` modules in a
   transitive source-import audit, and the full compose chain builds with one
   Lake job.

2. **`clusterLoad` at block scale.** `:2564-2568` bounds the block scan by
   `n*n`, syntactically discarding the `CluScan` invariant (`_`), whose third
   component (`:2338`) is `Xoff c ≤ ρ.vars "p"`. There is no counted loop here,
   so `forRangeZeroSum` does not apply: making the charge block-driven means
   making the cost a function of block size, which propagates into
   `turnCostSize`'s slot. That is why this is the engine wave, not §2.3.

   **Status 2026-08-10:** complete. `clusterLoad_spec` is fixed at an explicit
   centre and costs `24 * blockSize Xoff c + 11 * n + 26`;
   `DescendStep` carries that centre, `descendStep` pays the block size from
   `MassWeight.blockWeight`, and `turnCostSize` now reads the resulting
   size-indexed descent cost. The obsolete descent-based cubic floor in
   `SlotSweep` was retired, and the G2 negative control flipped positive.

3. **The four `BlockLeaves` leaves at `Com` + `Spec`**, and the walks re-done
   at block scale: `clusterLoad_spec` (264 lines), `ballCom_spec` (124),
   `ancestorStep_spec` (152), `batchCom_spec` (132), `descendStep` (516),
   `expandCom_spec` (35) — 1223 landed lines. `descendLeaves_le_turnSlot`
   requires **all four** leaves to reach `ctBlockLeaves = 200`; wiring only
   `bexpPass` cannot close it.
   Named debts `BlockLeaves` already owes: **N-1** the composed clear+load is
   not synthesized (tool timeout); **N-2** `degSum ≤ ns` unproved, so `bexpK`
   is honest but not summable.

**Two things break by design, and the brief must say so.**
`SlotSweep.descend_carrier:486` becomes **false**, not slack — `24·n²` is
`descendCost`'s only pure-`n²` summand — taking `turn_carrier`, `hKs_carrier`,
`level_cost_floor_cubic`, `level_cost_floor_sharp` and
`driverRoot_decides_sentence_floored` with it. That is the intended
demolition; the correct disposition is **retirement, not restatement**. Carry
`C0Probe.lean:161/215` on the same list — they route through the same `rfl` and
sit outside `SlotSweep`. And `G2CostProbe.lean:565`'s negative-control `#guard`
**flips and fails elaboration** once both §2.3 and this land; it needs
re-heading, not fixing.

Blast radius is otherwise small: `ballCom_spec`, `batchCom_spec` and
`clusterLoad_spec` have **no external code consumers**.

**Size: 5–8 sub-waves, 3000–5000 lines** (ESTIMATE). Single-owner on
`RamDriverDescend.lean` throughout. Build with `-j1` on that module: swap is at
19,828 of 19,889 MB.

Only after this does `turnCostSize` become fillable.

### §2.6 The contract chain — five boundaries, not one monolith

**`shared_contract_seam` does not compile the claim its docstring makes.** Its
two feeders are independent: `ordersBy_refuted_off_members` (`GapsDesign.lean:907`)
takes only `n ≤ ord c` and never mentions `asg`;
`coverOut_refuted_off_members` (`:917`) takes only `n ≤ asg w` and never
constrains `ord`. It is `A ∧ B` from `hA ∧ hB` — two independent junk
conditions in two different arrays read at the same index. There is **no shared
premise**, and the docstring's *"`hKc` and `hKo` cannot be separate execution
waves"* is not supported by the theorem it annotates.

The real coupling is one-way and compiled: `RamDriver.CoverImplements`
(`:3805-3811`) takes `RamCover.OrdersBy` as a **hypothesis**, fed at
`RamDriverCluster.lean:1799-1801`. Cover consumes order. That forces an
**order** — C before B — not a merge.

| wave | content | lines | sub-waves |
|---|---|---|---|
| **A** | `OrdersByM`/`CoverOutM` + `id`-bridges in a **new file importing `RamCover`** (not editing it — keeps the 71-module blast radius off); ~14 slot Props parameterized with `id`-instance re-derivations across ~21 files; `levelImplements` body re-walk; root shims keeping `levelAt` byte-identical | 900–1300 | 2 |
| **C** | block-driven cover: `coverCom` centre loop → `CoverBlock.centreLoopCom`, body `bfsBlockM_spec`; `CoverInv` at the list axis; `emitLoop`/`emitSlot` at block scale; `compactCom` → member scan; `coverSave` at the alive prefix | 3000–4500 | 4–6 |
| **B** | member-driven order text; wire `ElimCompact`/`SymCompact`/`AugCompact`; prove `ElimTailPinned` (`GapsDesign.lean:993`, a **statement gap, not missing mathematics**) | 2000–3500 | 3–5 |
| **D** | root re-instantiation at the real `Mem`/`cps`; `hKo`/`hKc` rows re-closed; two carrier dominations dropped from `g2_plug` | 800–1600 | 1–2 |

**11–17 sub-waves in four independently landable boundaries**, against 17–28 as
one monolith.

**Status 2026-08-12:** the concrete compact order and active cover now instantiate
the recursive `levelAtA` theorem, including an inductive write-set proof for the
nested driver and the centre-loop header.  Their costs are charged at the current
`arenaWeight`.  `ActiveRoot.driverRootActive_decides_sentence` now composes the
deduplicating decode, that concrete recursive driver, and sentence readback; the
active root has no abstract `hKo` or `hKc` phase slots.  Boundary D is therefore
through the executable root.  Its remaining boundary is to restate the sigma
recurrence plug at this root (retiring the two obsolete carrier dominations) and
close the surviving turn-cost row.

Two technical points the wave-A brief must carry:

- **`OrdersByM` is `MemberOrderContract` verbatim** and its bridge is an iff
  (← is compiled at `GapsDesign.lean:1018`; → is `Fin.eta`).
- **`CoverOutM` needs two lists, not one.** `CoverOut` is carrier-wide on two
  axes — centre *position* (`last`, `mono`, `block`, `block_inj`,
  `block_mono`) and *vertex* (`asg_lt`, `asg_cover`) — and the block clause
  names its centre `ord c`, not `c`. So `MemberOrderContract`'s vertex list
  cannot serve the cover half; the arena must be re-indexed by a **position
  list** `Pos`, with a new `pos_covers` clause. The re-indexing is **forced by
  a compiled cost fact**: `CoverBlock.carrier_le_arena_of_coverOut:315` proves
  `n ≤ m` from `OrdersBy` + `CoverOut` alone, so a `CoverOutM` that merely
  restricted quantifiers would inherit that floor and buy nothing.
- `hasgcps` survives member-weakening but **not verbatim** — it needs the new
  `pos_covers` clause and ~4 lines.

**The falsifier, to attack first under refute-before-prove:** if some consumer
needs `Xoff` addressed by carrier position *and* the arena shorter than the
carrier at once, `carrier_le_arena_of_coverOut` re-asserts `n ≤ m` and wave C
buys nothing. No such consumer was found by reading; every driver-side `Xoff`
read is either at the turn's own centre (`RamDriverDescend.lean:2577-2590`) or
offset arithmetic that re-indexes. This is the one assumption in the chain not
closed by reading.

Two file splits are prerequisites, both **file artifacts** verified by grep to
have no cross-references: `RamDriverCompose.lean` (helpers / cover half / order
half) and `RamDriverOrder.lean` (clean split at line 836). Precedent `7a42ae7`.
`RamDriverCluster.lean`'s lock is real but irrelevant — one declaration, owned
entirely by wave A.

### §2.7 B7 re-run → C0 → P5

`SlotSweep.lean` is the B7 re-run's opening leaf by construction
(`:6-7`). Unresolved and load-bearing: **which root C0 closes through** —
`Refine/DriverRootD.lean` restated the root and killed slots #6/#26/#12, but
nothing imports it except `G2ExistsRevalidation`, while the floors and
`g2_plug` are stated at the *landed* root. That decides whether B7 is a re-run
or an adoption.

---

## §3 Schedule, honestly

Measured: **54 min/wave, ~800 net lines/wave, one wave at a time, 4.1 sessions
per week.** Nominal for §2.1–§2.7: 38–61 waves ≈ one week of sessions.

But the measured multiplier from *plan item* to *actual waves* is **2–4×**:
`E4c` took eleven waves for one numbered item; `R1.8-T3-flip` took eight. The
campaign's own diagnosis (gaps-design): *"the scatter leaf took four execution
waves because each blocker surfaced only when the previous cleared."*

**Honest number: 76–180 waves, 7–15 sessions, 2–4 calendar weeks.** State this
to anyone who asks how long C0 takes.

---

## §4 Standing constraints

- **One worktree at a time.** 5.7 GB free on a 99%-full disk, 1.4 GB per
  seeded worktree, 4 cores — and swap at 19,828/19,889 MB, which is the tighter
  bound. Remove the worktree at every landing.
- **No phase may edit `word-ram`.** Thirteen lakefiles across six submissions
  pin `d35ba57`; `lax submit` requires fresh explicit consent from Jan. If a
  new `Reasoning` combinator is needed, that is a separate decision, not a
  wave.
- **`lax build` is a landing-boundary gate** run from the main checkout, never
  per-wave in a seeded worktree. Two waves paid ~an hour each learning this.
- **Check the import-order rule before scoping any wave.** It has bitten four.
- **Briefs state the obligation only.** Eleven mechanism prescriptions on this
  road have been overridden by the source.
- **The fallback is permanently discarded** (Jan, 2026-08-08): *"the full end
  to end result is what my community cares about."* No weaker headline, no
  citable-core provisional submission. Do not re-propose it; two audits
  reached for it independently.
- **JAN-FLAG 1 disposal stays blocked on G4** — 42,179 lines of superseded
  `Ram*.lean` still in the build.

---

## §5 Open decisions for Jan

1. **Adopt this road, or the plan-of-record's?** They differ in three places:
   this one puts the readback (§2.2) before the contract chain rather than
   inside it; it scopes `E4c-descend` to include the re-layer and
   `clusterLoad`; and it splits `hKc`+`hKo` into four boundaries on the finding
   that `shared_contract_seam` does not force one wave.
2. **`ka` is unmeasured** (`C0CloseProbe.lean:132`, ceiling 3.95·10⁷) and is
   the cover phase's whole arena residue. It decides whether wave C is four
   sub-waves or eight. Measuring it is a probe, not a wave. Schedule it before
   §2.6?
3. **The gate is verified at one `(ℓ, D)` point** — `famHalf` hard-wires
   `ℓ = 3`, `D = 8` (`C0CloseProbe.lean:581-585`), but `ℓ = N(2s+2)` is
   determined by the nowhere-dense class, not chosen. Re-run the gate at the
   class-forced `(ℓ, D)` before or after the road?

---

## §6 Evidence index

| finding | source |
|---|---|
| target refuted through the root | `Refine/SlotSweep.lean:600`, `:713` |
| no constant closes the turn slot | `Refine/G2CostProbe.lean:799` |
| `ctTurn` covers 2 of 8 summands | `Refine/C0CloseProbe.lean:225`, `Refine/KillListPass.lean:117-126` |
| ε = ½ clears at measured constants | `Refine/C0CloseProbe.lean:586-588` |
| source charges the cluster, not the carrier | `references/gks/nowheredense.tex:2549-2560`, `:2605-2609`, `:2745-2748` |
| 08-08 waves not load-bearing at the root | `RamDriverRoot.lean:762-765` |
| `hKd` refused once, and reshapes `hKl` | `NIGHTLOG.md` R1.8-T3-flip (c2b); `RamDriverRoot.lean:783-785` |
| readback provable against landed contract | `RamDriverDescend.lean:2577-2590`, `Refine/MassAlive.lean:145` |
| Σ-shaped loop rule landed and in scope | `Refine/SigmaLoop.lean:47`, `RamBfs.lean:286` |
| 20/22 scan sites already tight | sweep of `Csr.rowScan_spec` applications |
| `BlockLeaves` has no `Com`/`Spec` | token census; `Refine/G2CostProbe.lean:794-798` |
| re-layer: four drops, eight moves | three independent transitive-closure computations |
| `descend_carrier` becomes false | `24·n²` is `descendCost`'s only `n²` summand |
| `shared_contract_seam` proves `A ∧ B` from independent feeders | `Refine/GapsDesign.lean:907`, `:917`, `:938-944` |
| cover consumes order, one-way | `RamDriver.lean:3805-3811`, `RamDriverCluster.lean:1799-1801` |
| `CoverOutM` needs a position list | `Refine/CoverBlock.lean:315` |
| ownership locks 1 and 2 are file artifacts | grep: no cross-references either way |
| `turnCost` is noncomputable | `RamDriver.lean:150-152` |
| measured rate | `git diff --shortstat` on 2m-1/2m-2/2m-3; `NIGHTLOG.md` 2026-08-08 |

Stale-doc repairs to fold into whichever wave touches them (none worth a wave):
`Refine/ArenaBlock.lean:203-209` overstates the partition blocker — the landed
`levelImplements` is already split by aliveness; `Refine/SlotSweep.lean:446`
and `Refine/ClusterSynth.lean:1353` quote the pre-E-mem `16·n²`;
`Refine/G2CostProbe.lean:685`, `:794` the same; `C0CloseProbe.lean:567` quotes
`131·n` where the live floor is `122·n` (drifted twice); `:96` says "T4b
unstarted"; `KillListPass.lean:120` attributes `84` to the kill pass when it is
`DeadRowProbe.killClock` and the pass's charge at that instance is `75`.
