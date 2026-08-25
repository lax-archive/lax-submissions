import Lax3Proofs.SolveAugTrans
import Lax3Proofs.SolveAugFrat
import Lax3Proofs.TgtCoupling

/-!
# F6c12-5c-ii — `StepEmitIn`, the augmentation round body

The third and last of `CovAugAdjIn`'s split, and the one that closes a
greedy round: from an in-neighbour CSR of `D`, the two candidate
regions built beside it (`SolveAugTrans`'s `TransCsrAt`,
`SolveAugFrat`'s fraternity CSR) and the ranking `rk` in an array,
**emit the in-neighbour CSR of `greedyStep rk D`**
(`CoverRoutine.lean:212`).  The output is an in-CSR of an orientation,
i.e. exactly the shape of this pass's own input (`TrInCsr`), so the
next round consumes it unchanged.

## The divergence from the source, and why nothing is copied

NOdM's directed graphs *permit* two-cycles — "at most two arcs may
connect `x` and `y`, one in each direction" — while Lean's
`Orientation` forbids them (`Augmentation.lean:110`, the `asymm`
field).  `greedyStep`'s σ-arbitration and its `¬ D.Adjacent` filter
therefore have **no reference implementation** in BEII or GKS: the
paper's round never has to decide which of two directions to keep,
because it may keep both.  Everything below is read off the Lean
definition and nothing else.  Where the divergence bites is recorded
as Finding 1.

## The decision, split in two

`greedyStep rk D` adds `u → v` exactly when

    ¬ D.Adjacent u v ∧ (TransLink D u v ∨ FratLink D u v) ∧
      (rk u < rk v ∨ ¬ (TransLink D v u ∨ FratLink D v u)).

`FratLink` is symmetric (`Augmentation.lean:172`) and `TransLink` is
not, and that asymmetry is the whole content of the third clause.  It
splits the candidates at head `v` into two disjoint phases, each with
a decision the machine can take in `O(1)`:

* **the fraternal phase** — `u` with `(fratGraph D).Adj u v`, i.e.
  `u ≠ v ∧ FratLink D u v`.  Then `FratLink D v u` holds too, so the
  second disjunct of the arbitration is *false* and the decision
  collapses to `¬ D.Adjacent u v ∧ rk u < rk v` (`EmFratPick`).  A
  fraternal pair is tight-permissible both ways, so `rk` decides it
  outright.
* **the transitive phase** — `u` with `TransLink D u v` and
  `¬ (fratGraph D).Adj u v`.  Then `FratLink D u v` fails, hence
  `FratLink D v u` fails, and the decision is
  `¬ D.Adjacent u v ∧ (rk u < rk v ∨ ¬ TransLink D v u)`
  (`EmTransPick`).  The second disjunct is the **forced transitive
  direction**: `u → v` is demanded, the `rk`-order says no, and the
  opposite direction is not tight-permissible, so the arc goes against
  `rk`.

`emRow_eq_greedyStep` is that these two phases plus the old row are
**exactly** `(greedyStep rk D).inN v` — a finset equality, not a
containment — and `emRow_disjoint_*` that the three parts are pairwise
disjoint, so the emitted list is duplicate-free and the row length is
the sum of the three cards.

## The regions the pass consumes, and the two it still builds

Landed and reused verbatim:

* `TransCsrAt` (`SolveAugTrans.lean:509`) with `transCsrAt_decides`
  (`:1815`) — `TransLink D u v` is the cell `mk[v·n + u]` and
  `TransLink D v u` is the cell `mk[u·n + v]`, both `O(1)`, both in
  the *same* region.  That is precisely the two-direction test the
  arbitration needs, and it is why no transitive transpose is built.
  `transCsrAt_row` (`:1823`) is the head's candidate row.
* the fraternity CSR of `SolveAugFrat` (`csrPrefix_fratPref`, `:438`;
  `exists_fratCsr`, `:567`) — row `v` lists the `fratGraph D`
  neighbours of `v`, deduplicated, at most `fratPairCount D` slots in
  all (`fratNs_le`, `:527`).

Built here, and priced here:

* **the transpose** `outNbrs D` (`TgtCoupling.lean:144`), by counting
  sort, `O(n + arcCount D)` — `outOff_last` is that it has exactly
  `arcCount D` slots.  It exists for one reason: `D.Adjacent u v` is
  `u ∈ inN v ∨ v ∈ inN u`, **both** directions, and the second is not
  a row of the input CSR.
* **the adjacency stamp** — a row-stamped `n`-cell mark array over
  `adjSet D v = D.inN v ∪ outNbrs D v` (`mem_adjSet`), the
  `SolveCovLoad.lean:1290` pattern.  Stamping costs
  `|inN v| + |outNbrs v|` at head `v` and `2·arcCount D` in all
  (`sum_card_adjSet_le`), never a carrier scan per head and never a
  second `n²` window.
* **the seen stamp** — a second `n`-cell row-stamped array, written
  over the fraternal row of `v` during the fraternal phase and read as
  `(fratGraph D).Adj u v` during the transitive phase.  It is what
  makes the two phases disjoint on the machine, and it costs one store
  per fraternal candidate.

The emit itself needs no counting sort: heads are processed in
increasing order and a head's whole row is written before the next
head starts, so the output offsets are anchored per head off one
running write pointer — `trOuter`'s shape (`SolveAugTrans.lean:610`).

## The budget

    emK n a f T = 300·n + 300·a + 200·f + 240·T + 80

at `a = arcCount D`, `f = fratPairCount D`, `T = transPairCount D` —
the three counts `ProgCoverCharge.levelCharge` (`:150`) prices a
greedy round by, and at which `exists_chainCharge_le` (`:381`) already
closes the chain inside §7's `a·N^{1+2δ}`.  Term by term:

* `300` a **vertex**: the transpose's four carrier sweeps (zero the
  degrees, count, prefix-sum, scatter) and the emit loop's own header
  — anchor the output offset, load the four row bounds (input, out,
  fraternal, transitive), advance the stamp.  One turn per vertex of
  the carrier, isolated vertices included.
* `300` an **arc**: five passes over the arcs, all `arcCount D` long
  — the transpose's count and scatter sweeps, the two adjacency
  stamping sweeps (`inN v` and `outNbrs v`, whose sizes sum to
  `2·arcCount D`) and the old-arc copy into the output.
* `200` a **fraternal candidate**: the fraternal phase's turn — read
  the row slot, the adjacency test, the seen stamp, the two `rk`
  reads and the compare, and the emit.  Charged at
  `fratPairCount D`, which dominates the fraternity CSR's slot count
  (`fratNs_le`).
* `240` a **transitive candidate**: the transitive phase's turn — the
  same, plus the seen test and the `mk[u·n + v]` matrix read that
  decides the forced direction.  Charged at `transPairCount D`, which
  dominates the transitive region's slot count
  (`transCsrAt_slots_le`).

So the pass is `O(n + arcCount D + fratPairCount D + transPairCount D)`
and nothing else: no carrier scan inside a head's turn, no comparison
sort (the arbitration compares `rk u` against `rk v` only, one pair at
a time, and never orders a list), and no `n²` term — the one `n²`
window in sight is `TransCsrAt`'s, which this pass reads and does not
build.  `emK_le_levelCharge` is that the whole shape sits inside
`150·levelCharge D + 80`, and `emK_le` prices it at an in-degree bound.

`arcCount_greedyStep_le` is the matching **space** bound: the output
has at most `arcCount D + fratPairCount D + transPairCount D` slots,
so one allocation of the same envelope holds it.

## What is proved here, and what is not

**Proved** — the whole abstract layer, i.e. everything about *which*
data the pass leaves and everything about the counts:

* `emRow_eq_greedyStep` — the row equality, the σ-arbitration and the
  two-cycle cases included; `card_emRow`, `self_not_mem_emRow` and
  `emRow_asymm` — the row is duplicate-free and the result is an
  orientation, re-derived on the emitted rows rather than borrowed
  from `greedyStep`.
* `trInCsr_emit` — two arrays holding the offsets and the
  concatenated rows of *any* family that lists each `emRow D rk v`
  once **are** `TrInCsr o' t' (greedyStep rk D)`, on the nose: rows
  duplicate-free (`inj`), row membership exact in both directions
  (`sound`, `complete`), offsets anchored and stepping by the row
  card, every target a vertex.  This is `graphCsr_fratPref`'s role on
  this side of the split, and it is what leaves a discharger owing
  only the loop text.
* `emNs_eq` / `emNs_le` / `arcCount_greedyStep_le` — the output's slot
  count is the next round's `arcCount`, and it is inside this round's
  own envelope.
* `sum_card_fratNbrs_le`, `sum_card_trIn_le`, `sum_card_adjSet_le`,
  `outOff_last` — the four counts the budget's four constants
  multiply.
* `emK_le_levelCharge`, `emK_le` — the budget inside the pre-verified
  envelope, and priced at an in-degree bound.

**Not proved** — the concrete IMP+ program.  §10 names the residuals
`TransposeIn` and `StepEmitIn`, quantified over the command and its
budget (Finding 4).  No command text is asserted.

## Findings

1. **The two-cycle divergence is load-bearing three times, and each
   time in the Lean object's favour.**  `not_transLink_self`
   (`SolveAugTrans.lean:341`) makes `TransLink D v v` vacuous, so the
   transitive phase never sees `u = v` and owes no `u ≠ v` test;
   `emRow_asymm` is provable at all only because a pair demanded in
   both directions is arbitrated, which is the case NOdM does not
   have; and the `¬ D.Adjacent` filter — which in NOdM would be a
   one-directional "is this arc already present" test — has to consult
   the transpose.  A program transcribed from BEII would fail on all
   three.
2. **`FratLink D u v` with `u = v` is possible and is killed by the
   arbitration, not by the filter.**  `FratLink D v v` holds of any
   `v` with an out-neighbour, so the second clause of `greedyStep`'s
   `pick` does *not* exclude the diagonal; what excludes it is that
   `rk v < rk v` is false and `¬(TransLink D v v ∨ FratLink D v v)` is
   false as well.  `self_not_mem_emRow` proves that, and the fraternal
   phase's `u ≠ v` (from `fratGraph`'s own loopless clause) is what
   the machine tests instead.
3. **The postcondition is `TrInCsr` at `greedyStep rk D`** — the same
   structure this pass reads at `D`.  A round is therefore an
   endomorphism of the region shape, and `IsAugChain`'s rounds compose
   with no repacking.  `arcCount (greedyStep rk D)` is the next
   round's `ns`, and `arcCount_greedyStep_le` bounds it by this
   round's three counts.
4. **The concrete IMP+ program is a named residual, not a discharged
   `Spec`.**  `StepEmitIn` is quantified over the command and its
   budget in the shape `AdjBuildAt` (`SolveSweepBuild.lean:1864`)
   and `FratCsrAt` (`SolveAugFrat.lean:648`) established for a
   contract a program can actually meet: the figures in named scalar
   cells, since IMP+ reads no array length (`Imp.lean:158`).
   Everything about *which* finset each row holds, and everything
   about the counts, is proved below; what is open is the loop text.
   A program written but not verified is the failure mode this
   campaign has recorded three times, and it is not repeated here.
5. **The fraternal region's own slot bound is a precondition, not a
   consequence.**  `CsrPrefix fo ft (fratGraph D) nf` alone says
   nothing about how large `nf` is, so the `60·f` term of the budget
   would price nothing without it.  `FratCsrAt`'s postcondition does
   carry `ns' ≤ fratPairCount D` (`SolveAugFrat.lean:660`), so
   `StepEmitIn` asks for exactly that and no more.  The transitive
   side needs no such clause: `transCsrAt_slots_le` holds
   unconditionally.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (getD_eq_getElem)
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine
open Lax3Proofs.TgtCoupling

variable {n : ℕ}

/-! ## §1 The two phases of the arbitration

`greedyStep`'s `pick` filter is one conjunction; the machine takes it
in two disjoint passes over two different candidate rows.  These are
the predicates those passes test, and §2 is that they reassemble the
filter exactly. -/

/-- **The fraternal phase's decision** at head `v` on a candidate `u`
drawn from row `v` of the fraternity CSR.  `(fratGraph D).Adj u v`
already carries `u ≠ v` and `FratLink D u v`, hence `FratLink D v u`,
so `greedyStep`'s arbitration collapses to the plain `rk`-comparison —
a fraternal pair is tight-permissible in both directions. -/
def EmFratPick (D : Orientation n) (rk : Fin n → ℕ) (v u : Fin n) : Prop :=
  (fratGraph D).Adj u v ∧ ¬ D.Adjacent u v ∧ rk u < rk v

/-- **The transitive phase's decision** at head `v` on a candidate `u`
drawn from row `v` of `TransCsrAt`.  The `¬ (fratGraph D).Adj u v`
conjunct is the machine's seen-stamp test: it is what makes this phase
disjoint from the fraternal one, and it is what turns
`¬ (TransLink D v u ∨ FratLink D v u)` into the single matrix read
`¬ TransLink D v u` — the **forced transitive direction**. -/
def EmTransPick (D : Orientation n) (rk : Fin n → ℕ) (v u : Fin n) : Prop :=
  TransLink D u v ∧ ¬ (fratGraph D).Adj u v ∧ ¬ D.Adjacent u v ∧
    (rk u < rk v ∨ ¬ TransLink D v u)

/-- The fraternal phase's emissions at head `v`. -/
noncomputable def emFrat (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    Finset (Fin n) := pick (EmFratPick D rk v)

/-- The transitive phase's emissions at head `v`. -/
noncomputable def emTrans (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    Finset (Fin n) := pick (EmTransPick D rk v)

/-- **Row `v` of the output**: the old arcs, then the fraternal
phase's picks, then the transitive phase's picks — in the order the
pass writes them. -/
noncomputable def emRow (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    Finset (Fin n) := D.inN v ∪ emFrat D rk v ∪ emTrans D rk v

theorem mem_emFrat {D : Orientation n} {rk : Fin n → ℕ} {v u : Fin n} :
    u ∈ emFrat D rk v ↔ EmFratPick D rk v u := mem_pick

theorem mem_emTrans {D : Orientation n} {rk : Fin n → ℕ} {v u : Fin n} :
    u ∈ emTrans D rk v ↔ EmTransPick D rk v u := mem_pick

theorem mem_emRow {D : Orientation n} {rk : Fin n → ℕ} {v u : Fin n} :
    u ∈ emRow D rk v ↔
      u ∈ D.inN v ∨ EmFratPick D rk v u ∨ EmTransPick D rk v u := by
  rw [emRow, Finset.mem_union, Finset.mem_union, mem_emFrat, mem_emTrans, or_assoc]

/-! ## §2 The postcondition: a finset equality

Not a supergraph and not a multiset.  `pick` is a filter over a
decidable predicate, so `greedyStep`'s row is a *set*, and the pass
owes that set on the nose. -/

/-- **The pass's row is `greedyStep`'s row.**  The two phases of §1
plus the old arcs are exactly `(greedyStep rk D).inN v`.

Reading the four cases of the `←` direction is reading the whole
arbitration: a fraternal candidate is decided by `rk` because
`FratLink` is symmetric; a purely transitive one may go against `rk`
when the reverse link is absent; and the diagonal `u = v` — which
`FratLink` permits — is killed by the arbitration itself
(Finding 2). -/
theorem emRow_eq_greedyStep (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    emRow D rk v = (greedyStep rk D).inN v := by
  ext u
  rw [mem_emRow, mem_greedyStep]
  constructor
  · rintro (h | ⟨hadj, hnadj, hlt⟩ | ⟨htl, hnf, hnadj, hcase⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hnadj, Or.inr hadj.2, Or.inl hlt⟩
    · refine Or.inr ⟨hnadj, Or.inl htl, ?_⟩
      rcases hcase with hlt | hnt
      · exact Or.inl hlt
      · refine Or.inr ?_
        rintro (hr | hr)
        · exact hnt hr
        · exact hnf ⟨fun hc => not_transLink_self D v (hc ▸ htl), hr.symm⟩
  · rintro (h | ⟨hnadj, hlink, hcase⟩)
    · exact Or.inl h
    · by_cases hF : (fratGraph D).Adj u v
      · refine Or.inr (Or.inl ⟨hF, hnadj, ?_⟩)
        rcases hcase with hlt | hno
        · exact hlt
        · exact absurd (Or.inr hF.2.symm) hno
      · rcases hlink with htl | hfl
        · refine Or.inr (Or.inr ⟨htl, hF, hnadj, ?_⟩)
          rcases hcase with hlt | hno
          · exact Or.inl hlt
          · exact Or.inr fun hr => hno (Or.inl hr)
        · exfalso
          have hne : ¬ u ≠ v := fun hne => hF ⟨hne, hfl⟩
          rw [not_not] at hne
          subst hne
          rcases hcase with hlt | hno
          · exact absurd hlt (lt_irrefl _)
          · exact hno (Or.inr hfl)

/-! ## §3 The row is duplicate-free, and it is an orientation's row

The three parts of `emRow` are pairwise disjoint, so the pass writes
each target once and the row's length is the sum of the three sizes.
`not_mem_self` and `asymm` are re-established directly on `emRow`,
mirroring `greedyStep`'s own case analysis
(`CoverRoutine.lean:216-240`) — a consumer reading only the emitted
rows gets both without going through `greedyStep`. -/

theorem not_mem_inN_of_mem_emFrat {D : Orientation n} {rk : Fin n → ℕ}
    {v u : Fin n} (h : u ∈ emFrat D rk v) : u ∉ D.inN v :=
  fun hc => (mem_emFrat.1 h).2.1 (Or.inl hc)

theorem not_mem_inN_of_mem_emTrans {D : Orientation n} {rk : Fin n → ℕ}
    {v u : Fin n} (h : u ∈ emTrans D rk v) : u ∉ D.inN v :=
  fun hc => (mem_emTrans.1 h).2.2.1 (Or.inl hc)

theorem emRow_disjoint_inN_frat (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    Disjoint (D.inN v) (emFrat D rk v) :=
  Finset.disjoint_left.2 fun _ hu hc => not_mem_inN_of_mem_emFrat hc hu

theorem emRow_disjoint_frat_trans (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    Disjoint (D.inN v ∪ emFrat D rk v) (emTrans D rk v) := by
  refine Finset.disjoint_left.2 fun u hu hc => ?_
  rcases Finset.mem_union.1 hu with hu | hu
  · exact not_mem_inN_of_mem_emTrans hc hu
  · exact (mem_emTrans.1 hc).2.1 (mem_emFrat.1 hu).1

/-- **The row's size**: the old arcs plus the two phases' picks, with
no overlap.  This is the pass's per-head slot count. -/
theorem card_emRow (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    (emRow D rk v).card
      = (D.inN v).card + (emFrat D rk v).card + (emTrans D rk v).card := by
  rw [emRow, Finset.card_union_of_disjoint (emRow_disjoint_frat_trans D rk v),
    Finset.card_union_of_disjoint (emRow_disjoint_inN_frat D rk v)]

/-- **No loops**, re-established on the emitted row.  `v ∉ D.inN v` is
`not_mem_self`; `fratGraph` is loopless, so the fraternal phase never
emits `v`; and `TransLink D v v` is a two-cycle
(`not_transLink_self`), so neither does the transitive phase.  Note
that `FratLink D v v` may well hold — Finding 2. -/
theorem self_not_mem_emRow (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    v ∉ emRow D rk v := by
  rw [mem_emRow]
  rintro (h | h | h)
  · exact D.not_mem_self v h
  · exact h.1.ne rfl
  · exact not_transLink_self D v h.1

/-- **No two-cycles**, re-established on the emitted rows.  The three
crossing cases are the three ways the arbitration can be forced:
an old arc blocks the reverse by `¬ D.Adjacent`; two fraternal picks
would need `rk u < rk v` and `rk v < rk u`; and two transitive picks
would each have the reverse link present, so each would need the
`rk`-comparison, and again both ways.  Mixed fraternal/transitive is
impossible because `fratGraph` is symmetric and the transitive phase
tests its negation. -/
theorem emRow_asymm (D : Orientation n) (rk : Fin n → ℕ) (u v : Fin n)
    (h : u ∈ emRow D rk v) : v ∉ emRow D rk u := by
  rw [mem_emRow] at h ⊢
  rintro (h' | h' | h')
  · rcases h with h | h | h
    · exact D.asymm u v h h'
    · exact h.2.1 (Or.inr h')
    · exact h.2.2.1 (Or.inr h')
  · rcases h with h | h | h
    · exact h'.2.1 (Or.inr h)
    · exact absurd (h.2.2.trans h'.2.2) (lt_irrefl _)
    · exact h.2.1 h'.1.symm
  · rcases h with h | h | h
    · exact h'.2.2.1 (Or.inr h)
    · exact h'.2.1 h.1.symm
    · rcases h.2.2.2 with hlt | hnt
      · rcases h'.2.2.2 with hlt' | hnt'
        · exact absurd (hlt.trans hlt') (lt_irrefl _)
        · exact hnt' h.1
      · exact hnt h'.1

/-- The emitted rows *are* an orientation's rows, on the nose: the
orientation is `greedyStep rk D` and §2 is the equality. -/
theorem emRow_inN (D : Orientation n) (rk : Fin n → ℕ) :
    (greedyStep rk D).inN = emRow D rk :=
  funext fun v => (emRow_eq_greedyStep D rk v).symm

/-! ## §4 The counts: what the output costs in space

`emFrat` sits inside the fraternity graph's neighbourhood and
`emTrans` inside `trIn`, so the whole output is inside the three
figures `levelCharge` already prices. -/

/-- The `fratGraph`-neighbours of `v`, as a head's candidate row. -/
noncomputable def fratNbrs (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  pick (fun u => (fratGraph D).Adj u v)

theorem mem_fratNbrs {D : Orientation n} {u v : Fin n} :
    u ∈ fratNbrs D v ↔ (fratGraph D).Adj u v := mem_pick

theorem emFrat_subset (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    emFrat D rk v ⊆ fratNbrs D v :=
  fun _ hu => mem_fratNbrs.2 (mem_emFrat.1 hu).1

theorem emTrans_subset (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) :
    emTrans D rk v ⊆ trIn D v :=
  fun _ hu => mem_trIn.2 (mem_emTrans.1 hu).1

/-- A fraternal neighbour of `v` is an in-neighbour of an
out-neighbour of `v` — the enumeration BEII runs at the middle
vertex. -/
theorem fratNbrs_subset (D : Orientation n) (v : Fin n) :
    fratNbrs D v ⊆ (outNbrs D v).biUnion (fun w => D.inN w) := by
  intro u hu
  obtain ⟨-, w, hw1, hw2⟩ := mem_fratNbrs.1 hu
  exact Finset.mem_biUnion.2 ⟨w, mem_outNbrs.2 hw2, hw1⟩

theorem card_fratNbrs_le (D : Orientation n) (v : Fin n) :
    (fratNbrs D v).card ≤ ∑ w ∈ outNbrs D v, (D.inN w).card :=
  le_trans (Finset.card_le_card (fratNbrs_subset D v)) Finset.card_biUnion_le

/-- **The fraternal rows fit inside `fratPairCount D`.**  Double
counting at the middle vertex: `Σ_v Σ_{w ∈ outN v} |inN w|
= Σ_w |inN w|²`, which is `fratPairCount D` by definition
(`ProgCoverCharge.lean:134`). -/
theorem sum_card_fratNbrs_le (D : Orientation n) :
    ∑ v, (fratNbrs D v).card ≤ fratPairCount D := by
  classical
  refine le_trans (Finset.sum_le_sum fun v _ => card_fratNbrs_le D v) (le_of_eq ?_)
  rw [fratPairCount]
  calc ∑ v : Fin n, ∑ w ∈ outNbrs D v, (D.inN w).card
      = ∑ v : Fin n, ∑ w : Fin n, if v ∈ D.inN w then (D.inN w).card else 0 := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [outNbrs, Finset.sum_filter]
    _ = ∑ w : Fin n, ∑ v : Fin n, if v ∈ D.inN w then (D.inN w).card else 0 :=
        Finset.sum_comm
    _ = ∑ w : Fin n, (D.inN w).card * (D.inN w).card := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul]

/-- **The transitive rows fit inside `transPairCount D`** — the
landed bound, read at the row family. -/
theorem sum_card_trIn_le (D : Orientation n) :
    ∑ v, (trIn D v).card ≤ transPairCount D := by
  rw [transPairCount]
  exact Finset.sum_le_sum fun v _ => trIn_card_le D v

/-- **The output's slot count.**  A round's arcs are the old arcs plus
the two phases' picks, disjointly. -/
theorem arcCount_greedyStep (D : Orientation n) (rk : Fin n → ℕ) :
    arcCount (greedyStep rk D)
      = arcCount D + ∑ v, (emFrat D rk v).card + ∑ v, (emTrans D rk v).card := by
  show ∑ v, ((greedyStep rk D).inN v).card = _
  rw [arcCount, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by
    rw [← emRow_eq_greedyStep D rk v, card_emRow]

/-- **One allocation of the round's own envelope holds the output**:
`arcCount D + fratPairCount D + transPairCount D` cells of target
space are enough, which is exactly the sum of the three figures
`levelCharge` prices the round by. -/
theorem arcCount_greedyStep_le (D : Orientation n) (rk : Fin n → ℕ) :
    arcCount (greedyStep rk D)
      ≤ arcCount D + fratPairCount D + transPairCount D := by
  have hf : ∑ v, (emFrat D rk v).card ≤ fratPairCount D :=
    le_trans (Finset.sum_le_sum fun v _ =>
      Finset.card_le_card (emFrat_subset D rk v)) (sum_card_fratNbrs_le D)
  have ht : ∑ v, (emTrans D rk v).card ≤ transPairCount D :=
    le_trans (Finset.sum_le_sum fun v _ =>
      Finset.card_le_card (emTrans_subset D rk v)) (sum_card_trIn_le D)
  rw [arcCount_greedyStep D rk]
  omega

/-! ## §5 The output, read back

The counterpart of `graphCsr_fratPref` (`SolveAugFrat.lean:399`) on
this side of the split: **two arrays holding the offsets and the
concatenated rows of a family that lists each `emRow D rk v` once are
an in-neighbour CSR of `greedyStep rk D`** — every clause of
`TrInCsr`, on the nose.  The family is arbitrary, so a discharger
instantiates it with whatever its loops actually write and owes
nothing further about the *data*; §2's finset equality is what makes
the instantiation possible at all.

The list plumbing is `SolveAugFrat`'s §2, reused unchanged. -/

/-- The output target array up to row `k`: the emitted rows,
concatenated. -/
def emPref (E : ℕ → List ℕ) (k : ℕ) : List ℕ := (List.range k).flatMap E

/-- The output offsets: the partial lengths. -/
def emOff (E : ℕ → List ℕ) (k : ℕ) : ℕ := (emPref E k).length

/-- The output slot count. -/
def emNs (n : ℕ) (E : ℕ → List ℕ) : ℕ := emOff E n

theorem emOff_zero (E : ℕ → List ℕ) : emOff E 0 = 0 := rfl

theorem emOff_succ (E : ℕ → List ℕ) (k : ℕ) :
    emOff E (k + 1) = emOff E k + (E k).length := by
  rw [emOff, emOff, emPref, emPref, flatPref_succ, List.length_append]

/-- **The slot count is the next round's arc count.**  It is therefore
the `ns` of the CSR the next round reads, and
`arcCount_greedyStep_le` prices it. -/
theorem emNs_eq {n : ℕ} {D : Orientation n} {rk : Fin n → ℕ} {E : ℕ → List ℕ}
    (hnd : ∀ v : Fin n, (E (v : ℕ)).Nodup)
    (hE : ∀ (v : Fin n) (u : ℕ),
      u ∈ E (v : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ emRow D rk v) :
    emNs n E = arcCount (greedyStep rk D) := by
  have hlen : ∀ v : Fin n, (E (v : ℕ)).length = ((greedyStep rk D).inN v).card := by
    refine length_eq_card_of_rows (D := greedyStep rk D) hnd (fun v u => ?_)
    rw [hE v u, emRow_eq_greedyStep]
  rw [emNs, emOff, emPref, length_flatPref, arcCount,
    ← Fin.sum_univ_eq_sum_range (fun i => (E i).length) n]
  exact Finset.sum_congr rfl fun v _ => hlen v

/-- **The output, read back**: the two arrays *are* an in-neighbour
CSR of `greedyStep rk D`, in the windowed form the `≤`-sized
allocations force — `TrInCsr` is already stated at `≤ length`
(`SolveAugTrans.lean:127`), so unlike the fraternal side (its Finding
3) no separate prefix statement is needed here.

Row `v` is duplicate-free and lists exactly
`(greedyStep rk D).inN v`; that is `sound`, `complete` and `inj`
together, and §2 is why the finset is the right one. -/
theorem trInCsr_emit {o' t' : String} {n : ℕ} {D : Orientation n}
    {rk : Fin n → ℕ} {E : ℕ → List ℕ} {σ : Env}
    (hnd : ∀ v : Fin n, (E (v : ℕ)).Nodup)
    (hE : ∀ (v : Fin n) (u : ℕ),
      u ∈ E (v : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ emRow D rk v)
    (hoL : n + 1 ≤ (σ.arrs o').length)
    (htL : emNs n E ≤ (σ.arrs t').length)
    (hoG : ∀ i, i ≤ n → (σ.arrs o')[i]? = some (emOff E i))
    (htG : ∀ p, p < emNs n E → (σ.arrs t')[p]? = some ((emPref E n).getD p 0)) :
    TrInCsr o' t' (greedyStep rk D) (emNs n E) (emOff E)
      (fun p => (emPref E n).getD p 0) σ := by
  classical
  have hlen : ∀ v : Fin n, (E (v : ℕ)).length = ((greedyStep rk D).inN v).card := by
    refine length_eq_card_of_rows (D := greedyStep rk D) hnd (fun v u => ?_)
    rw [hE v u, emRow_eq_greedyStep]
  -- every target of the concatenation is a vertex
  have hlt : ∀ p, p < emNs n E → (emPref E n).getD p 0 < n := by
    intro p hp
    have hmem : (emPref E n).getD p 0 ∈ emPref E n := by
      rw [getD_eq_getElem hp]
      exact List.getElem_mem hp
    obtain ⟨i, hi, hy⟩ := (mem_flatPref E).mp hmem
    exact ((hE ⟨i, hi⟩ _).1 hy).1
  -- row `v` of the pair is `E v`
  have hrow : ∀ v : Fin n,
      Csr.row (emOff E) (fun p => (emPref E n).getD p 0) (v : ℕ) = E (v : ℕ) :=
    fun v => row_flatPref E v.isLt
  refine
    { zero := emOff_zero E
      step := fun v => by rw [emOff_succ, hlen v]
      last := rfl
      offLen := hoL
      tgtLen := htL
      offGet := hoG
      tgtGet := htG
      tgtLt := hlt
      sound := ?_
      complete := ?_
      inj := ?_ }
  · intro v p hp1 hp2 h
    have hmem : (emPref E n).getD p 0 ∈ E (v : ℕ) := by
      rw [← hrow v]
      exact mem_row_iff.2 ⟨p, hp1, hp2, rfl⟩
    obtain ⟨hu, hmem'⟩ := (hE v _).1 hmem
    have : (⟨(emPref E n).getD p 0, hu⟩ : Fin n) = ⟨(emPref E n).getD p 0, h⟩ := rfl
    rw [this, ← emRow_eq_greedyStep] at *
    exact hmem'
  · intro v u hu
    have hmem : (u : ℕ) ∈ E (v : ℕ) :=
      (hE v (u : ℕ)).2 ⟨u.isLt, by rw [emRow_eq_greedyStep]; simpa using hu⟩
    rw [← hrow v] at hmem
    exact mem_row_iff.1 hmem
  · -- distinct slots of one row hold distinct targets, since `E v` is nodup
    intro v p r hp1 hp2 hr1 hr2 hpr
    have hm : Csr.rowLen (emOff E) (v : ℕ) = (E (v : ℕ)).length := by
      show emOff E ((v : ℕ) + 1) - emOff E (v : ℕ) = (E (v : ℕ)).length
      rw [emOff_succ]; omega
    have hnd' : ((List.range (E (v : ℕ)).length).map
        (fun k => (emPref E n).getD (emOff E (v : ℕ) + k) 0)).Nodup := by
      have := hnd v
      rw [← hrow v, Csr.row, hm, arrOf] at this
      exact this
    have hinj := List.inj_on_of_nodup_map hnd'
    have h1 : p - emOff E (v : ℕ) ∈ List.range (E (v : ℕ)).length := by
      rw [List.mem_range]
      have : emOff E ((v : ℕ) + 1) = emOff E (v : ℕ) + (E (v : ℕ)).length :=
        emOff_succ E (v : ℕ)
      omega
    have h2 : r - emOff E (v : ℕ) ∈ List.range (E (v : ℕ)).length := by
      rw [List.mem_range]
      have : emOff E ((v : ℕ) + 1) = emOff E (v : ℕ) + (E (v : ℕ)).length :=
        emOff_succ E (v : ℕ)
      omega
    have h3 : emOff E (v : ℕ) + (p - emOff E (v : ℕ)) = p := by omega
    have h4 : emOff E (v : ℕ) + (r - emOff E (v : ℕ)) = r := by omega
    have := hinj h1 h2 (by rw [h3, h4]; exact hpr)
    omega

/-- **The output fits the allocation the round already pays for.** -/
theorem emNs_le {n : ℕ} {D : Orientation n} {rk : Fin n → ℕ} {E : ℕ → List ℕ}
    (hnd : ∀ v : Fin n, (E (v : ℕ)).Nodup)
    (hE : ∀ (v : Fin n) (u : ℕ),
      u ∈ E (v : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ emRow D rk v) :
    emNs n E ≤ arcCount D + fratPairCount D + transPairCount D := by
  rw [emNs_eq hnd hE]
  exact arcCount_greedyStep_le D rk

/-! ## §6 The adjacency test

`D.Adjacent u v` is `u ∈ inN v ∨ v ∈ inN u` — **both** directions.
Row `v` of the input CSR answers the first; the second needs the
transpose.  The pass stamps their union into one `n`-cell row-stamped
mark array at the start of head `v`'s turn, so the test is one array
read, and the stamping is paid for at `2·arcCount D` over the whole
carrier — never a carrier scan per head, and never a second `n²`
window. -/

/-- The vertices the machine stamps at head `v`: the in-neighbours and
the out-neighbours. -/
noncomputable def adjSet (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  D.inN v ∪ outNbrs D v

/-- **The stamp decides adjacency**, in both directions at once. -/
theorem mem_adjSet {D : Orientation n} {u v : Fin n} :
    u ∈ adjSet D v ↔ D.Adjacent u v := by
  rw [adjSet, Finset.mem_union, mem_outNbrs]
  exact Iff.rfl

/-- **The stamping is linear in the arcs**: `Σ_v (|inN v| + |outN v|)
= 2·arcCount D`, since the out-degrees add up to the in-degrees
(`TgtCoupling.sum_card_outNbrs`). -/
theorem sum_card_adjSet_le (D : Orientation n) :
    ∑ v, (adjSet D v).card ≤ 2 * arcCount D := by
  have hsum : ∑ v, (outNbrs D v).card = arcCount D := sum_card_outNbrs D
  calc ∑ v, (adjSet D v).card
      ≤ ∑ v, ((D.inN v).card + (outNbrs D v).card) :=
        Finset.sum_le_sum fun v _ => Finset.card_union_le _ _
    _ = (∑ v, (D.inN v).card) + ∑ v, (outNbrs D v).card := Finset.sum_add_distrib
    _ = arcCount D + arcCount D := by rw [hsum]; rfl
    _ = 2 * arcCount D := by ring

/-! ## §7 The transpose

An out-neighbour CSR of `D`, built by counting sort in
`O(n + arcCount D)`.  Its offsets are the out-degree prefix sums and
its extent is `arcCount D` on the nose — the transpose has exactly as
many slots as the input, which is why it costs the same envelope. -/

/-- The out-degree at a plain index, `0` off the carrier. -/
noncomputable def outDegAt (D : Orientation n) (v : ℕ) : ℕ :=
  if h : v < n then (outNbrs D ⟨v, h⟩).card else 0

/-- The transpose's offsets: the prefix sums of the out-degrees. -/
noncomputable def outOff (D : Orientation n) (v : ℕ) : ℕ :=
  ∑ a ∈ Finset.range v, outDegAt D a

theorem outOff_zero (D : Orientation n) : outOff D 0 = 0 := by simp [outOff]

theorem outOff_succ (D : Orientation n) (v : ℕ) :
    outOff D (v + 1) = outOff D v + outDegAt D v := Finset.sum_range_succ _ _

theorem outDegAt_coe (D : Orientation n) (v : Fin n) :
    outDegAt D (v : ℕ) = (outNbrs D v).card := by rw [outDegAt, dif_pos v.isLt]

/-- **The transpose has exactly `arcCount D` slots.** -/
theorem outOff_last (D : Orientation n) : outOff D n = arcCount D := by
  rw [outOff, ← Fin.sum_univ_eq_sum_range (fun v => outDegAt D v) n]
  rw [show ∑ v : Fin n, outDegAt D (v : ℕ) = ∑ v : Fin n, (outNbrs D v).card from
    Finset.sum_congr rfl fun v _ => outDegAt_coe D v]
  exact sum_card_outNbrs D

/-- **The out-neighbour CSR of `D`**, `TrInCsr`'s shape at the
transposed relation: row `v` lists `outNbrs D v`, the offsets are the
out-degree prefix sums, and the two regions may be longer than their
extents (the windowed convention). -/
structure OutCsrAt (qo qt : String) {n : ℕ} (D : Orientation n) (otF : ℕ → ℕ)
    (σ : Env) : Prop where
  /-- The offset region holds at least `n + 1` cells. -/
  qoLen : n + 1 ≤ (σ.arrs qo).length
  /-- The target region holds at least the slot count. -/
  qtLen : arcCount D ≤ (σ.arrs qt).length
  /-- Reading an offset. -/
  qoGet : ∀ i, i ≤ n → (σ.arrs qo)[i]? = some (outOff D i)
  /-- Reading a target. -/
  qtGet : ∀ p, p < arcCount D → (σ.arrs qt)[p]? = some (otF p)
  /-- Every target is a vertex. -/
  qtLt : ∀ p, p < arcCount D → otF p < n
  /-- Every slot of row `v` holds an out-neighbour of `v`. -/
  sound : ∀ (v : Fin n) (p : ℕ), outOff D (v : ℕ) ≤ p → p < outOff D ((v : ℕ) + 1) →
    ∀ h : otF p < n, (⟨otF p, h⟩ : Fin n) ∈ outNbrs D v
  /-- Every out-neighbour of `v` sits in a slot of row `v`. -/
  complete : ∀ (v u : Fin n), u ∈ outNbrs D v →
    ∃ p, outOff D (v : ℕ) ≤ p ∧ p < outOff D ((v : ℕ) + 1) ∧ otF p = (u : ℕ)
  /-- No two slots of one row hold the same target. -/
  inj : ∀ (v : Fin n) (p r : ℕ), outOff D (v : ℕ) ≤ p → p < outOff D ((v : ℕ) + 1) →
    outOff D (v : ℕ) ≤ r → r < outOff D ((v : ℕ) + 1) → otF p = otF r → p = r

/-! ## §8 The ranking, in an array

`greedyStep` is parameterized by `rk : Fin n → ℕ` and the arbitration
reads two of its values per candidate, so the machine holds it as an
`n`-cell array and every value must be a word. -/

/-- The ranking `rk`, cell by cell. -/
def RankAt (sg : String) {n : ℕ} (rk : Fin n → ℕ) (σ : Env) : Prop :=
  n ≤ (σ.arrs sg).length ∧ ∀ v : Fin n, (σ.arrs sg)[(v : ℕ)]? = some (rk v)

/-! ## §9 The budget -/

/-- **The pass's budget** at `(n, a, f, T)`, with `a = arcCount D`,
`f = fratPairCount D` and `T = transPairCount D` — the three figures
`ProgCoverCharge.levelCharge` (`:150`) prices a greedy round by.  The
module docstring has the command-by-command accounting; in one line,
`300` a carrier turn (the transpose's four sweeps and the emit
loop's header), `300` an arc (five arc-length passes: the transpose's
count and scatter, the two adjacency stampings, the old-arc copy),
`200` a fraternal candidate and `240` a transitive one (the extra is the
matrix read that decides the forced direction).

`Spec`'s budget is an upper bound, so a discharger may spend less; the
counts each constant multiplies are what is proved
(`sum_card_adjSet_le`, `outOff_last`, `sum_card_fratNbrs_le`,
`sum_card_trIn_le`). -/
def emK (n a f T : ℕ) : ℕ := 300 * n + 300 * a + 200 * f + 240 * T + 80

/-- **The budget sits inside the pre-verified envelope.**  One greedy
round is charged `levelCharge D = 3n + 2·arcCount + 4·fratPairCount +
2·transPairCount` (`ProgCoverCharge.lean:150`), and
`exists_chainCharge_le` (`:381`) already closes the chain built from
it inside §7's `a·N^{1+2δ}`.  This pass costs a *constant multiple* of
that charge, so it changes no exponent — only the `f` of the envelope
theorem. -/
theorem emK_le_levelCharge {n : ℕ} (D : Orientation n) :
    emK n (arcCount D) (fratPairCount D) (transPairCount D)
      ≤ 150 * levelCharge D + 80 := by
  simp only [emK, levelCharge]
  omega

/-- **The budget, priced by an in-degree bound**: at in-degree `≤ d`
one round body costs at most `n·(300 + 300·d + 440·d²) + 80`.  The
carrier enters linearly and never squared — the same
`d`-parameterization that keeps `n²` out of
`ProgCoverCharge.levelCharge_le`, and the same shape as the sibling
pass's `trK_le` (`SolveAugTrans.lean:1846`). -/
theorem emK_le {n : ℕ} {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    emK n (arcCount D) (fratPairCount D) (transPairCount D)
      ≤ n * (300 + 300 * d + 440 * (d * d)) + 80 := by
  have h1 := arcCount_le hd
  have h2 := fratPairCount_le hd
  have h3 := transPairCount_le hd
  calc emK n (arcCount D) (fratPairCount D) (transPairCount D)
      = 300 * n + 300 * arcCount D + 200 * fratPairCount D
          + 240 * transPairCount D + 80 := rfl
    _ ≤ 300 * n + 300 * (n * d) + 200 * (n * (d * d)) + 240 * (n * (d * d))
          + 80 := by omega
    _ = n * (300 + 300 * d + 440 * (d * d)) + 80 := by ring

/-! ## §10 The residuals: the two passes, at named figure cells

The shape is `AdjBuildAt`'s (`SolveSweepBuild.lean:1864`) and
`FratCsrAt`'s (`SolveAugFrat.lean:648`), for the reason recorded at
both: IMP+ reads no array length (`Imp.lean:158`), so the carrier size
and the slot counts must sit in named scalar cells, and every index
the pass forms — here including the matrix index `u·n + v` — must be a
word.  Both residuals are quantified over the command and its budget;
no command text is asserted, and none is verified (Finding 4). -/

/-- **The transpose, as a contract.**  From an in-neighbour CSR of `D`
with the carrier in `nN`, leave an out-neighbour CSR in `(qo, qt)`
with the input untouched.  A counting sort: zero the out-degrees,
count them over the input's slots, prefix-sum, scatter — four sweeps,
`O(n + arcCount D)`, which is what `kq` is asked for. -/
def TransposeIn (B : ℕ) (nN o t qo qt dg : String) (tpC : Com)
    (kq : ℕ → ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (D : Orientation n) (ns : ℕ) (off tgt : ℕ → ℕ),
    Spec B
      (fun σ => TrInCsr o t D ns off tgt σ ∧ σ.vars nN = n ∧
        n + arcCount D < B ∧
        n + 1 ≤ (σ.arrs qo).length ∧ arcCount D ≤ (σ.arrs qt).length ∧
        n ≤ (σ.arrs dg).length ∧ (∀ i, i < n → (σ.arrs dg).getD i 0 = 0))
      tpC
      (fun _ σ' => TrInCsr o t D ns off tgt σ' ∧
        ∃ otF, OutCsrAt qo qt D otF σ')
      (kq n (arcCount D))

/-- **`StepEmitIn`: the augmentation round body.**  From

* an in-neighbour CSR of `D` in `(o, t)` — the previous round's
  output, or `baseOr`'s at round `0`;
* the transitive region `(ro, rt, mk)` of `SolveAugTrans`, whose mark
  matrix decides `TransLink` in both directions in `O(1)`
  (`transCsrAt_decides`);
* the fraternity CSR `(fo, ft)` of `SolveAugFrat`, in the windowed
  form `CsrPrefix` its own residual delivers, with its slot count in
  `nF`;
* the ranking `rk` in `sg`;
* scratch: the transpose `(qo, qt)`, the adjacency stamps `ad`, the
  seen stamps `sd`, and the counting-sort degrees `dg`,

leave in `(o', t')` **an in-neighbour CSR of `greedyStep rk D`** — the
same structure the pass reads at `D`, so a round is an endomorphism of
the region shape (Finding 3) — with its slot count in `nO`, and every
input region unchanged.

The postcondition is a `TrInCsr`, whose `sound`/`complete`/`inj`
clauses pin each row to the finset `(greedyStep rk D).inN v` *exactly*
and duplicate-free: `emRow_eq_greedyStep` is that finset, `card_emRow`
its size, and `arcCount_greedyStep_le` the reason the stated
allocation suffices.  `kb` is the budget at the four figures
`levelCharge` prices a round by; `emK` is the concrete target. -/
def StepEmitIn (B : ℕ) (nN nF nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String)
    (emC : Com) (kb : ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (D : Orientation n) (rk : Fin n → ℕ) (ns nf : ℕ)
    (off tgt ttF : ℕ → ℕ),
    Spec B
      (fun σ =>
        -- the input orientation, its two candidate regions and the ranking
        TrInCsr o t D ns off tgt σ ∧ TransCsrAt ro rt mk D ttF σ ∧
        CsrPrefix fo ft (fratGraph D) nf σ ∧ RankAt sg rk σ ∧
        -- the figures, in named cells
        σ.vars nN = n ∧ σ.vars nF = nf ∧
        -- the fraternal region is inside the count its own pass promises
        -- (`FratCsrAt`'s last postcondition clause); without this the
        -- fraternal phase's `200·f` charge would price nothing
        nf ≤ fratPairCount D ∧
        -- every index and value the pass forms is a word
        n + n * n + arcCount D + fratPairCount D + transPairCount D < B ∧
        (∀ v : Fin n, rk v < B) ∧
        -- the output and scratch allocations
        n + 1 ≤ (σ.arrs o').length ∧
        arcCount D + fratPairCount D + transPairCount D ≤ (σ.arrs t').length ∧
        n + 1 ≤ (σ.arrs qo).length ∧ arcCount D ≤ (σ.arrs qt).length ∧
        n ≤ (σ.arrs ad).length ∧ n ≤ (σ.arrs sd).length ∧
        n ≤ (σ.arrs dg).length ∧
        (∀ i, i < n → (σ.arrs ad).getD i 0 = 0) ∧
        (∀ i, i < n → (σ.arrs sd).getD i 0 = 0) ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = 0))
      emC
      (fun σ σ' =>
        -- the inputs survive
        TrInCsr o t D ns off tgt σ' ∧ TransCsrAt ro rt mk D ttF σ' ∧
        CsrPrefix fo ft (fratGraph D) nf σ' ∧ RankAt sg rk σ' ∧
        -- and so does everything else: the pass writes only its output
        -- and its own scratch, so a round composes with the next
        (∀ b, b ≠ o' → b ≠ t' → b ≠ qo → b ≠ qt → b ≠ ad → b ≠ sd →
          b ≠ dg → σ'.arrs b = σ.arrs b) ∧
        -- the round's output: an in-CSR of the next orientation
        ∃ off' tgt' : ℕ → ℕ,
          TrInCsr o' t' (greedyStep rk D) (arcCount (greedyStep rk D))
            off' tgt' σ' ∧
          σ'.vars nO = arcCount (greedyStep rk D))
      (kb n (arcCount D) (fratPairCount D) (transPairCount D))

/-- **What a discharger of `StepEmitIn` owes, and what it does not.**
The output's slot count is inside the round's own envelope, so the
`t'` allocation the precondition asks for is enough — this is the one
clause of the contract that could have been unmeetable, and it is
not. -/
theorem stepEmitIn_slots_le {n : ℕ} (D : Orientation n) (rk : Fin n → ℕ) :
    arcCount (greedyStep rk D) ≤
      arcCount D + fratPairCount D + transPairCount D :=
  arcCount_greedyStep_le D rk

/-! ## §11 The axiom surface -/

#print axioms emRow_eq_greedyStep
#print axioms card_emRow
#print axioms self_not_mem_emRow
#print axioms emRow_asymm
#print axioms arcCount_greedyStep_le
#print axioms trInCsr_emit
#print axioms emNs_eq
#print axioms emNs_le
#print axioms mem_adjSet
#print axioms sum_card_adjSet_le
#print axioms outOff_last
#print axioms emK_le_levelCharge
#print axioms emK_le

end Lax3Proofs.Prog
