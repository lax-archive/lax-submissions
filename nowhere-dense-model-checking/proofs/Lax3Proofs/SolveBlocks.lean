import Lax13Proofs.Lib.Csr
import Lax3Proofs.ImplRestrict
import Lax3Proofs.ProgCodegenLayout

/-!
# F6c — the driver blocks on the machine, head: the per-frame state
contract

`ProgCodegen.SolveSpec` is the campaign's one remaining machine
obligation: from the parsed CSR (`CsrIn`), leave `unrolledMC`'s number
in `"verdict"`. Its decomposition plan (the skeleton's continuation
map, item 2) is `ProgDriver.driverProg`'s shape — `ℓ+1` static code
blocks, block `j`'s per-centre loop containing the one static copy of
block `j+1` (E10: the recursion is on the level index only). This file
is the head of that discharge: **the state contract every block is
specified against**, the level-indexed name mechanism that keeps the
`ℓ+1` copies of it apart inside one flat `mcLayout` extension, and the
bound lemmas that tie what the blocks store to `mcB`.

## The contract, in one sentence

*"The machine holds a depth-`j` arena"* is `ArenaSt (arenaNames j) hb
A σ`: the carrier size in the level's scalar cell, the arena's graph
as a CSR pair (`GraphCsr`: `Lib.Csr`'s relation plus the adjacency
semantics — row `v` lists exactly the neighbours of `v`, without
duplicates), the color rows as one row-major bit array (`ColBits`),
the root renaming as a plain array (`UpArr`), and D6's per-vertex
channel as a stride-`hb+1` length-prefixed region (`HistArr`). *"…and
its table region"* is `TableBits (arenaNames j).tab (levelFml S j) T
σ` on top: one bit per `(v, β)` with `β` running over the level's
schedule family `ℱ_j = F S j`. The arena record is `Impl.MArena` —
§4's machine arena, the record the landed `Impl.restrict`/`isolate`
functions transform — so every seam identity of `ImplRestrict`
(`restrict_G_eq_preG`, `childArena_G_eq_isolate_restrict`, …) applies
to the *contents* of two contract instances one level apart.
`DriverSt` is the same contract at a `Driver.Arena` through
`Impl.ofArena`, the form the block correctness statements quote
(`ProgDriver.driverProg` is stated at driver arenas; `htab` is a free
parameter there — it enters only the charge — so the contract takes
it as an argument).

## Judgment calls

* **`getD`-pointwise, not list-equal.** Every region predicate is "the
  array has this length, and position `p` reads `v`" rather than an
  `arrOf` equation: that is the form `evalB_get`/`Spec.store`
  obligations are stated in, so a routine's proof consumes the
  contract without a list-extensionality detour. (`Lib.Csr` keeps its
  own `arrOf` form internally; `GraphCsr` wraps it whole rather than
  re-proving its scan lemmas.)
* **`GraphCsr` is existential in the two index functions.** The seam
  quantifies them away so that two blocks agree on *what graph* the
  region holds without agreeing on slot order; a routine that scans
  rows `obtain`s the functions and works in `Lib.Csr`'s vocabulary
  (its `Pre`/`RowPre` are stated over the functions, deliberately).
  Row-`Nodup` and `off 0 = 0` are in the relation: they are true of
  every CSR the pipeline builds, and they are what pins the slot
  count to the degree sum (the cost side's `2M`).
* **`hist` is pinned by the contract even though the refinement never
  reads it** (`ProgDriver`: `htabF` is free, it enters only the
  charge): block `j+1`'s `restrict` *computes* the child's channel
  from the parent's, so the composition needs the parent region to
  hold definite lists — the contract states which.
* **Name mechanism: same-length bases, level by suffix length.**
  `lv s j` appends `j` copies of `'z'`; on bases of one common length
  the family is injective in `(s, j)` jointly (`lv_inj`), so the
  distinctness obligations of any two regions at any two levels are
  the two lemmas `lv_ne_of_base_ne`/`lv_ne_of_level_ne` — no string
  decoding. `arenaNames` fixes the canonical bases (all length 4);
  `levelScalars`/`levelArrays` are the `eS`/`eA` contribution of one
  level, `solveScalars`/`solveArrays` the flattened `ℓ+1`-level
  extension `mcLayout` receives.

## What rides on `mcB` (the stored-value hazard, discharged per class)

Everything a block stores is one of: a vertex name of some carrier
(`< N ≤ n₀`), a root name (`< n₀`), a CSR offset (`≤ ns = 2M ≤ n₀²`),
a bit, a BFS distance or round (`≤ r + 1`, a schedule constant), a
counter (`≤ N` or `≤ ns`), a table/hist index (`< N·|ℱ_j|` or
`< N·ℓp·(hb+1)`, schedule-constant multiples of `n₀`), or a scatter
count (`≤ t ≤ ‖β‖`, schedule data). `ArenaSt.N_le_root` pins
`N ≤ n₀`; with `n₀ ≤ |x|` (the encoding) every one of these is below
`mcB q x = q·(|x|+1)²` at a schedule constant `q` — the indices with
two carrier factors are exactly why `mcB` is quadratic
(`ProgCodegenLayout`'s design note). Discharged routine specs take the
bounds they need as explicit `< B` hypotheses; F7 instantiates them
from this arithmetic once.

## The blocks (division of labour, and the continuation map)

Owned here (`SolveBlocks*`): the `ℓ+1` driver blocks — per frame,
restrict → bfsSupports → recordProfiles(MS) → isolate → the next
block → guarded scatter → readback, and block `0`'s `botEval` route
(the edged fuel-`0` branch is dead on the class, `mkSetup_memLeaf_eq_bot`;
the compiled block implements the edgeless route only, its `Spec`
guarded by the invariant's edgeless hypothesis, exactly as
`ProgDriver.botProg`'s docstring plans). The sibling `SolveMat*` owns
the root materialization (CsrIn → the root `ArenaSt`), the root
evaluation and the `frameProgMS` reroute; nothing here depends on its
files — the contract is the reconciliation point.

Route decision, per routine: **direct `Spec`-kit IMP+**
(`ProgCodegenParse`'s route), not the Sepref descent — the landed
`Impl*` functions (`botEval`, `greedyScatter`, `restrictSweep`,
`isolate`) are first-order folds over concrete data, more legible than
their NREST wrappers, and the `Reasoning` kit's amortized loop rule is
exactly what the CSR sweeps need (`Lib/Csr`'s header records the same
verdict for the word-ram scans).

Status of the per-routine discharges:

1. `SolveBlocksScatter.lean` — **`greedyScatter`, discharged end to
   end**: the guarded early-stop sweep with the marking BFS-by-rounds
   inlined (`scatterCom_spec`, and `scatterCom_spec_graphCsr` at this
   file's seam: the count cell ends at `Impl.greedyScatter G r X t`
   exactly, from a CSR, a predicate bit array, and mark/distance
   scratch of the right length — the sweep cleans its own mark slate,
   so calls chain without a caller-side wipe and the `t = 0` guard
   stays free). Budget `scatterK = 41·N + (markK + 30)·t + 24`,
   `Impl.greedyScatterCost`'s `t·(n + W)` shape at the machine
   marking charge `W := markK ≤ 69·(r+1)·(N+ns+1)` (§6.5's
   `W := ‖A‖` at the schedule constant `r ≤ 2R`); envelope
   `scatterK_le : ≤ 130·(t+1)·(r+1)·(N+ns+1)` for F7.
2. `SolveBlocksBot.lean` — **block 0's schedule, abstract half
   discharged**: the representative table (`firsts` — first `K+1`
   vertices per packed row code; `mem_tableReps_iff` — at any
   environment of size `≤ K` the per-row `find?` is exactly
   `Impl.FirstRep`), and the table-scheduled evaluator `botEvalT`
   with `botEvalT_eq_botEval`/`botEvalT_eq_sat` — the value block 0's
   IMP+ table fill must produce, per (`v`, `β ∈ ℱ_j`) bit, with the
   per-entry work a constant of `(L, K, φ)`. Remaining for block 0:
   the IMP+ compilation itself — one `O(N·L)` table-build pass over
   `ColBits` into a `2^L`-strided region, then the structural
   recursion over the (compile-time) formula with an `env` scratch
   array, each `exU` a loop over `≤ k + 2^L·(K+1)` table candidates.
   Budget `botC`'s `(1 + |ℱ_j|)·‖A‖` shape.
3. isolate (one CSR sweep, `Impl.isolateCharge`), restrict
   (`restrictSweep`'s one-scratch-array discipline — the scratch is
   per *node*, cleared at the `|S|` touched entries, never a fresh
   array per child), supports (`chargeB0` + descend), profilesMS
   (`ImplMultiSource`, `profilesChargeMS`), the cover sweep
   (`sweepCharge`), readback — then the conditional frame-block
   composition (the per-centre `Spec.seq` chain + the centre loop,
   against `ProgFrame.frameProg_le_spec`'s shape), then the `ℓ+1`
   chain by induction on the level index mirroring
   `driverProg_le_spec`, closing `SolveSpec` with `Ks =` the block
   chain's total, reconciled against `ProgCharge.exists_mcChargeMS_T`
   by F7. Two seam facts the scatter discharge fixed for that
   composition: (a) a routine's `Spec` should clean the scratch it
   dirties (the sweep's own mark wipe) — the caller cannot afford a
   per-call wipe behind a cost guard, so self-cleanup is part of each
   routine's contract, not the block's; (b) the readback needs the
   per-centre guarded scatter *counts* stored (one small region,
   `|scatterAtoms|·|ℱ_j|` cells per centre's turn, reused per centre
   like the restrict scratch), and the cover slot must deliver the
   cluster *bit-vectors* alongside the order — the machine `π` as a
   rank array plus a per-centre membership region is the seam
   `ImplCover`'s discharge should be stated against.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3.ColoredGraphs (Coloring)
open Lax3.DistFO

/-! ## §1 Level-indexed names

`lv s j`: the base name `s`, tagged with level `j` by suffix length.
On bases of one common length the map `(s, j) ↦ lv s j` is injective,
which is the whole distinctness story for the `ℓ+1` copies of the
region family. -/

/-- The level tag: `j` copies of `'z'` appended to the base. -/
def lv (s : String) : ℕ → String
  | 0 => s
  | j + 1 => (lv s j).push 'z'

@[simp] theorem lv_zero (s : String) : lv s 0 = s := rfl

theorem lv_toList (s : String) (j : ℕ) :
    (lv s j).toList = s.toList ++ List.replicate j 'z' := by
  induction j with
  | zero => simp [lv]
  | succ j ih =>
    rw [lv, String.toList_push, ih, List.replicate_succ']
    simp

@[simp] theorem lv_length (s : String) (j : ℕ) : (lv s j).length = s.length + j := by
  induction j with
  | zero => simp [lv]
  | succ j ih => rw [lv, String.length_push, ih]; omega

/-- **Injectivity of the tagged family** over bases of one common
length: base and level are both recovered. -/
theorem lv_inj {s t : String} (hlen : s.length = t.length) {j k : ℕ}
    (h : lv s j = lv t k) : s = t ∧ j = k := by
  have hl : (lv s j).toList = (lv t k).toList := by rw [h]
  rw [lv_toList, lv_toList] at hl
  have hjk : j = k := by
    have := congrArg List.length hl
    simp only [List.length_append, List.length_replicate] at this
    have hs : s.toList.length = s.length := String.length_toList
    have ht : t.toList.length = t.length := String.length_toList
    omega
  subst hjk
  refine ⟨?_, rfl⟩
  rw [← String.toList_inj]
  exact (List.append_inj hl (by rw [String.length_toList, String.length_toList, hlen])).1

/-- Distinct bases of one length stay distinct at every pair of levels. -/
theorem lv_ne_of_base_ne {s t : String} (hlen : s.length = t.length)
    (hst : s ≠ t) (j k : ℕ) : lv s j ≠ lv t k :=
  fun h => hst (lv_inj hlen h).1

/-- Distinct levels stay distinct over any two bases of one length. -/
theorem lv_ne_of_level_ne {s t : String} (hlen : s.length = t.length)
    {j k : ℕ} (hjk : j ≠ k) : lv s j ≠ lv t k :=
  fun h => hjk (lv_inj hlen h).2

/-! ## §2 The region predicates

Each is "this array has this length, and reads back this data",
`getD`-pointwise (module docstring). All are plain `Prop`s over the
environment, so they sit directly in `Spec` pre- and postconditions. -/

open Classical in
/-- A bit array for a set of vertices: length `n`, entry `v` is `1`
exactly on members. -/
def FinBits (a : String) {n : ℕ} (X : Set (Fin n)) (σ : Env) : Prop :=
  (σ.arrs a).length = n ∧
    ∀ v : Fin n, (σ.arrs a).getD v 0 = if v ∈ X then 1 else 0

open Classical in
/-- The color rows, row-major: entry `v * Λ + c` is the bit of `v ∈
col c`. -/
def ColBits (a : String) {N Λ : ℕ} (col : Coloring N Λ) (σ : Env) : Prop :=
  (σ.arrs a).length = N * Λ ∧
    ∀ (v : Fin N) (c : Fin Λ),
      (σ.arrs a).getD (v * Λ + c) 0 = if v ∈ col c then 1 else 0

/-- The root renaming, as a plain array: entry `v` is the root name of
`v`. -/
def UpArr (a : String) {N n₀ : ℕ} (up : Fin N ↪ Fin n₀) (σ : Env) : Prop :=
  (σ.arrs a).length = N ∧ ∀ v : Fin N, (σ.arrs a).getD v 0 = up v

/-- D6's per-vertex channel, as a stride-`hb+1` length-prefixed
region: the `(v, p)` slot starts at `(v·ℓp + p)·(hb+1)`, its first
cell is the stored list's length (`≤ hb`), the next cells its names in
order. -/
def HistArr (a : String) {N : ℕ} (ℓp hb : ℕ)
    (hist : Fin N → Fin ℓp → List (Fin N)) (σ : Env) : Prop :=
  (σ.arrs a).length = N * ℓp * (hb + 1) ∧
    ∀ (v : Fin N) (p : Fin ℓp),
      (hist v p).length ≤ hb ∧
      (σ.arrs a).getD (((v : ℕ) * ℓp + p) * (hb + 1)) 0 = (hist v p).length ∧
      ∀ i : ℕ, ∀ hi : i < (hist v p).length,
        (σ.arrs a).getD (((v : ℕ) * ℓp + p) * (hb + 1) + 1 + i) 0
          = ((hist v p)[i] : ℕ)

open Classical in
/-- The table region: one bit per `(v, β)` with `β` running over the
level's schedule family, row-major — entry `v · |Fl| + i` is the bit
of `T v Fl[i]`. Only the family's entries are pinned: the table `T`
is a function, the machine holds its restriction to the schedule. -/
def TableBits (a : String) {N Λ : ℕ} (Fl : List (DistFO Λ 1))
    (T : Fin N → DistFO Λ 1 → Prop) (σ : Env) : Prop :=
  (σ.arrs a).length = N * Fl.length ∧
    ∀ (v : Fin N) (i : ℕ), ∀ hi : i < Fl.length,
      (σ.arrs a).getD ((v : ℕ) * Fl.length + i) 0 = if T v Fl[i] then 1 else 0

/-- **A graph in compressed-row form**: `Lib.Csr`'s relation (the two
arrays, monotone offsets, extent, target bound `N`), anchored at
`off 0 = 0`, with the adjacency semantics — row `v` lists exactly the
neighbours of `v`, without duplicates. The two index functions are
quantified away at the seam; a scanning routine `obtain`s them and
works in `Lib.Csr`'s own vocabulary. -/
def GraphCsr (o t : String) {N : ℕ} (G : SimpleGraph (Fin N)) (ns : ℕ)
    (σ : Env) : Prop :=
  ∃ off tgt : ℕ → ℕ,
    Csr o t N ns N off tgt σ ∧ off 0 = 0 ∧
    (∀ v : Fin N, (Csr.row off tgt v).Nodup) ∧
    ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩

/-- Membership of a row, in the slot-pointer form the scans read it:
`w` is in row `v` iff some slot of the row holds it. -/
theorem mem_row_iff {off tgt : ℕ → ℕ} {v w : ℕ} :
    w ∈ Csr.row off tgt v ↔
      ∃ p, off v ≤ p ∧ p < off (v + 1) ∧ tgt p = w := by
  simp only [Csr.row, Csr.rowLen, arrOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨off v + k, by omega, by omega, rfl⟩
  · rintro ⟨p, hlo, hhi, rfl⟩
    exact ⟨p - off v, by omega, by rw [Nat.add_sub_cancel' hlo]⟩

/-! ## §3 The canonical name family, and the layout extension -/

/-- The names of one level's arena region and its table. All bases have
length 4 (the `lv_inj` requirement); scalars and arrays live in
separate `Env` maps, so only names of the same kind need to differ. -/
structure ArenaNames where
  /-- Scalar: the carrier size `N`. -/
  nN : String
  /-- Scalar: the slot count `ns` of the CSR. -/
  nS : String
  /-- Array: the CSR offsets. -/
  off : String
  /-- Array: the CSR targets. -/
  tgt : String
  /-- Array: the color rows. -/
  col : String
  /-- Array: the root renaming. -/
  up : String
  /-- Array: the channel region. -/
  hist : String
  /-- Array: the table region. -/
  tab : String

/-- The canonical family at level `j`. -/
def arenaNames (j : ℕ) : ArenaNames where
  nN := lv "sv.n" j
  nS := lv "sv.m" j
  off := lv "sa.o" j
  tgt := lv "sa.t" j
  col := lv "sa.c" j
  up := lv "sa.u" j
  hist := lv "sa.h" j
  tab := lv "sa.b" j

/-- One level's contribution to the layout's scalar extension `eS`. -/
def levelScalars (j : ℕ) : List String := [(arenaNames j).nN, (arenaNames j).nS]

/-- One level's contribution to the layout's array extension `eA`. -/
def levelArrays (j : ℕ) : List String :=
  [(arenaNames j).off, (arenaNames j).tgt, (arenaNames j).col,
    (arenaNames j).up, (arenaNames j).hist, (arenaNames j).tab]

/-- The solve stages' scalar names for a depth-`ℓ` schedule: the
levels' cells, `0 … ℓ`. (The routines' scratch scalars are a fixed
finite list each satellite file declares; F7 appends them once.) -/
def solveScalars (ℓ : ℕ) : List String :=
  (List.range (ℓ + 1)).flatMap levelScalars

/-- The solve stages' array names for a depth-`ℓ` schedule. -/
def solveArrays (ℓ : ℕ) : List String :=
  (List.range (ℓ + 1)).flatMap levelArrays

/-- Arrays of different levels never collide — the mechanism lemma the
per-level frame conditions ride on. -/
theorem arenaNames_arrays_ne_of_level_ne {j k : ℕ} (hjk : j ≠ k)
    (a b : String) (ha : a ∈ levelArrays j) (hb : b ∈ levelArrays k) :
    a ≠ b := by
  simp only [levelArrays, arenaNames, List.mem_cons, List.not_mem_nil,
    or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact lv_ne_of_level_ne (by decide) hjk

/-- The scalar cells of different levels never collide. -/
theorem arenaNames_scalars_ne_of_level_ne {j k : ℕ} (hjk : j ≠ k)
    (a b : String) (ha : a ∈ levelScalars j) (hb : b ∈ levelScalars k) :
    a ≠ b := by
  simp only [levelScalars, arenaNames, List.mem_cons, List.not_mem_nil,
    or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    exact lv_ne_of_level_ne (by decide) hjk

/-- The six array bases of one level, in region order. -/
def arenaBases : List String := ["sa.o", "sa.t", "sa.c", "sa.u", "sa.h", "sa.b"]

theorem levelArrays_eq_map (j : ℕ) : levelArrays j = arenaBases.map (lv · j) := rfl

/-- Within one level, the six arrays are pairwise distinct. -/
theorem arenaNames_arrays_nodup (j : ℕ) : (levelArrays j).Nodup := by
  rw [levelArrays_eq_map]
  refine List.Nodup.map_on ?_ (by decide)
  intro s hs t ht h
  have hlen : ∀ u ∈ arenaBases, u.length = 4 := by decide
  exact (lv_inj (by rw [hlen s hs, hlen t ht]) h).1

/-! ## §4 The contract -/

/-- **The per-frame state contract** (this file's reason to exist):
the machine's level-`nm` region holds the arena `A` — the carrier size
in the scalar cell, the slot count in its cell, the graph as a CSR
pair, the color rows, the root renaming, and the channel at list bound
`hb`. Everything a block reads of its own level, and everything the
next block down is built from, is one of these five regions; the table
region (`TableBits` at the level's schedule family) is stated
separately, because the block *writes* it — a block's `Spec` is
`ArenaSt` in, `ArenaSt ∧ TableBits` out. -/
structure ArenaSt (nm : ArenaNames) {Λ n₀ ℓp : ℕ} (hb : ℕ)
    (A : Impl.MArena Λ n₀ ℓp) (σ : Env) : Prop where
  /-- The carrier size, in its cell. -/
  n_eq : σ.vars nm.nN = A.N
  /-- The graph, in compressed-row form at the slot count the cell
  holds. -/
  csr : GraphCsr nm.off nm.tgt A.G (σ.vars nm.nS) σ
  /-- The color rows. -/
  col : ColBits nm.col A.col σ
  /-- The root renaming. -/
  up : UpArr nm.up A.up σ
  /-- D6's channel. -/
  hist : HistArr nm.hist ℓp hb A.hist σ

/-- The contract at a driver arena (the form the block correctness
statements quote): the machine arena is `Impl.ofArena A htab`, with
the channel `htab` an argument — `ProgDriver`'s free parameter. -/
def DriverSt (nm : ArenaNames) {Λ n₀ : ℕ} {ℓp : ℕ} (hb : ℕ)
    (A : Driver.Arena Λ n₀) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (σ : Env) : Prop :=
  ArenaSt nm hb (Impl.ofArena A htab) σ

/-- Carriers never outgrow the root: the renaming embeds the carrier
in `Fin n₀`. This is the bound every stored vertex name rides to
`mcB` (module docstring: the stored-value hazard). -/
theorem ArenaSt.N_le_root {nm : ArenaNames} {Λ n₀ ℓp : ℕ} {hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (_ : ArenaSt nm hb A σ) :
    A.N ≤ n₀ := by
  have := Fintype.card_le_of_embedding A.up
  simpa using this

/-- The slot count is the degree sum (the rows tile the target zone,
each row exactly the neighbour list): `ns = Σ_v deg v` — the `2M` of
every cost statement, pinned by the contract. -/
theorem GraphCsr.ns_eq_sum_degree {o t : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {ns : ℕ} {σ : Env}
    (h : GraphCsr o t G ns σ) :
    ns = ∑ v : Fin N, G.degree v := by
  classical
  obtain ⟨off, tgt, hc, h0, hnd, hadj⟩ := h
  -- each row's length is the degree
  have hrow : ∀ v : Fin N, (Csr.rowLen off v) = G.degree v := by
    intro v
    have hlen : (Csr.row off tgt v).length = Csr.rowLen off v :=
      Csr.length_row off tgt v
    have hcard : (Csr.row off tgt v).toFinset.card = (Csr.row off tgt v).length :=
      List.toFinset_card_of_nodup (hnd v)
    have hset : (Csr.row off tgt v).toFinset
        = (G.neighborFinset v).map (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ) := by
      ext w
      simp only [List.mem_toFinset, hadj, Finset.mem_map,
        SimpleGraph.mem_neighborFinset, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hw, hAdj⟩
        exact ⟨⟨w, hw⟩, hAdj, rfl⟩
      · rintro ⟨u, hAdj, rfl⟩
        exact ⟨u.2, by simpa using hAdj⟩
    rw [← hlen, ← hcard, hset, Finset.card_map]
    rfl
  -- the rows tile the slots
  have htile : ∑ i ∈ Finset.range N, Csr.rowLen off i = off N - off 0 :=
    Csr.sum_rowLen hc N le_rfl
  have hlast : off N = ns := hc.last
  have : ∑ v : Fin N, G.degree v = ∑ i ∈ Finset.range N, Csr.rowLen off i := by
    rw [Finset.sum_range fun i => Csr.rowLen off i]
    exact Finset.sum_congr rfl fun v _ => (hrow v).symm
  omega

end Lax3Proofs.Prog
