import Lax3Proofs.DriverSchedule
import Lax3Proofs.CoverSpec
import Lax3Proofs.CoverCentres
import Lax3Proofs.ClusterPaths
import Lax3Proofs.SplitterWin
import Lax3Proofs.DriverBfsTree

/-!
# The abstract arena and the driver (E9, deliverable 2)

`algorithm-v2.md` §5's pseudocode over §4's interface, taken abstractly:
`SimpleGraph`/`Set`/functions instead of CSR arrays, every routine
consumed through its landed spec, and the two genuinely input-dependent
routines — the cover ordering and the scatter choice — as *parameters*
(`CoverSpec.OrderingRoutine`, `ScatterSentences.ScatterChoice`): the
driver is a function of the routines.

## The arena

An `Arena Λ n₀` is §4's structure with the machine-level fields
abstracted:

* `N`, `G`, `col` — the carrier, the edges, and the color rows, at the
  node's own palette `Λ` (the palette tower `Setup.pal` of the
  schedule).
* `up : Fin N ↪ Fin n₀` — the *composite* renaming to the ROOT carrier.
  §5 line 8 (E6): the game record lives at the root carrier and is never
  re-typed, so the arena carries the composite embedding rather than the
  one-step parent map. (The one-step map to the parent is recoverable:
  it is `childEquiv` composed with the cluster inclusion.)
* `hist` — D6's downward channel, abstracted: the list of
  `(connector, arena)` pairs of the ancestor rounds, at root names,
  newest first.
* `chan` — D6's downward channel *as the machine stores it*: per vertex
  and per ancestor round (indexed by `ℕ`, the round's column; only
  columns `< hist.length` carry a round), the recorded support names of
  that round's walk, **at this node's own carrier**. This is §4's
  per-vertex `hist` table, and it is what §5 line 19's batch is read
  off (`batchPar`).

  The field is what makes line 19 *computable*. Reading the batch off
  `SplitterWin.genSet` instead — the previous spelling — takes the
  support of a `Classical.choose`-picked walk, and the child-building
  pass must produce the batch **exactly** (`profilesCom_specW` requires
  the batch region to already hold `batchFn`'s values), so no program
  could ever hit it. The channel is the one thing the pass does compute:
  `supportsCom_specW` writes exactly one column per call, and
  `MArena.restrict` carries every other column down filtered. Hence
  `childArena`'s inherit-and-patch channel below.

`own` is not carried: abstractly the writing child of a vertex `v` is
*defined* to be the child of `centre v` (`ctr` of the cover layer), and
`ball_subset_cluster_ctr` puts `v` in that child — §5's "written exactly
once" is definitional here.

## One node of the recursion

At a node `A` at depth `j` with an edge left, with `π` the ordering the
cover routine returns:

* `cluster S A π u` — the wreach *fibre* at radius `2R` (`§6.2`);
  `centre S A π v` — the `π`-min of `wreach_R(v)` (`CoverCentres.ctr`).
* `childEquiv` — the compaction bijection of the cluster with
  `Fin (cluster.ncard)` (§5 step 3′; any bijection serves, and this one
  is `Classical`-chosen).
* `preG` — **`B₀` of §5 lines 16/20**: the induced graph on the cluster,
  renumbered. The profile colors of `childCol` are measured HERE —
  before isolation. Measuring them in the isolated graph would give `∅`
  for every distance `≥ 1` and the rewrite would be unsound, not lossy
  (the plan row's first hazard; `Isolate.lean:751-757`).
* `batchPar` — line 19's batch at the node's own names: the connector
  `u`, plus every name stored in `u`'s channel row at a round column;
  `batchRoot` is its image at root names, `batchSet` its trace on the
  child carrier; `batchFn` **pads it to exactly `width`** (`m`) by
  repeating the connector (the plan row's second hazard: the `iso`
  palette is sized by the schedule, not by the actual batch, and the
  `≤ 2R+1` channel-row bound + `m = ℓ(2R+1)` make the pad close the
  difference — `range_pad`, `batchSet_ncard_le`).
* `childArena` — carrier `Fin childN`, graph
  `deleteVerts preG (range batchFn)` (line 21, isolation *after* the
  profiles), colors `childCol` (marker = everything, since after
  compaction the cluster is the whole carrier; then the two profile slot
  families of the schedule's `isoEnc` layout), `up` composed through the
  cluster inclusion, `hist` extended by this round's
  `(up u, map up A.G)` pair, and `chan` **inherit-and-patch**: column
  `hist.length` — this round's — is the gradient-walk table
  `descendCol` of a BFS from `centreChild` in `preG` at radius `2R`
  (verbatim what `supportsCom_specW` leaves), every older column the
  parent's, filtered onto the cluster (verbatim what `MArena.restrict`
  leaves). One BFS per node, not one per round: the far ancestors'
  connectors are edge-isolated in the current arena, so recomputing
  their columns here would return `{u}` and nothing else.

## The driver

`tablesAux` is §5's `Tables`, with **structural fuel** as the honest
Lean spelling of termination (the semantic termination argument —
`ReachedS.reachedS_length_lt` — is the business of the invariant file
`DriverCorrect`, where it yields that at `j = ℓ` the arena is edgeless,
so the fuel never runs out on an arena with edges). At fuel `0` or on an
edgeless arena the driver returns `BotTables` *through its spec*: the
table's value at the leaf IS satisfaction in the edgeless arena, which
is what `Lax3Proofs.BotEval` shows a machine evaluates by row lookups.
Otherwise the entry at `(v, β)` is §5 line 28:
`eval(dec_j β, sub[v], sc)` — the chosen decomposition of the rewritten
`β`, its local atoms read from the child's table at `v`'s child name,
its scatter atoms evaluated by the (guarded) greedy scatter count over
the child's table (§5 lines 25–26). Entries at formulas outside the
schedule are `True` — §5 line 14's *uninitialised table*, never read.

`MC` is §5 lines 1–6: the root table, the root scatter counts, the
local sentence atoms of `top` evaluated as compile-time constants
(`localConst`, L1).

Everything is `noncomputable` (`Classical.choose` in the schedule and
in the compaction bijection); what this
file delivers is the *algorithm's structure* — which routine is called
where, on which data — with each routine consumed through its spec.
The correctness chain and the cost accounting are the satellite files
`DriverCorrect` and `DriverCost`.
-/

namespace Lax3Proofs.Driver

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.UniformQuasiWideness Lax12.ColoringNumbers
open Lax3Proofs.LocalityFun Lax3Proofs.WalkDistance

/-! ### Finite-set plumbing: the compaction bijection and the pad -/

/-- A bijection of `Fin X.ncard` with a set `X` of vertices — the
compaction bijection, **in ascending vertex order**. The compaction
transport (`Compaction.sat_compact_iff_satWithin`) asks nothing of the
order — any bijection serves (D3/E7) — but the machine layer can only
*compute* an order-pinned enumeration, so the sorted one is the pin
(F6c2's finding: the previous `equivFin` route was `Classical`-chosen
and no program could realize the abstract local names). -/
noncomputable def setEquiv {k : ℕ} (X : Set (Fin k)) : Fin X.ncard ≃ ↥X :=
  ((finCongr (Set.ncard_eq_toFinset_card X (Set.toFinite X))).trans
      ((Set.toFinite X).toFinset.orderIsoOfFin rfl).toEquiv).trans
    (Equiv.setCongr (Set.Finite.coe_toFinset (Set.toFinite X)))

/-- Padding a set to a fixed width: list its elements through `setEquiv`
and repeat the designated element `x₀` beyond them. -/
noncomputable def pad {k mb : ℕ} (X : Set (Fin k)) (x₀ : Fin k) : Fin mb → Fin k :=
  fun i => if h : (i : ℕ) < X.ncard then (setEquiv X ⟨(i : ℕ), h⟩ : Fin k) else x₀

theorem pad_mem {k mb : ℕ} {X : Set (Fin k)} {x₀ : Fin k} (hx : x₀ ∈ X) (i : Fin mb) :
    pad X x₀ i ∈ X := by
  unfold pad
  split
  · exact (setEquiv X _).2
  · exact hx

/-- The pad never leaves the set (the designated element belongs to it). -/
theorem range_pad_subset {k mb : ℕ} {X : Set (Fin k)} {x₀ : Fin k} (hx : x₀ ∈ X) :
    Set.range (pad (mb := mb) X x₀) ⊆ X := by
  rintro y ⟨i, rfl⟩
  exact pad_mem hx i

/-- **The pad is exact** (hazard 2): when the set fits the width, the
padded function enumerates exactly the set. -/
theorem range_pad {k mb : ℕ} {X : Set (Fin k)} {x₀ : Fin k} (hx : x₀ ∈ X)
    (hle : X.ncard ≤ mb) : Set.range (pad (mb := mb) X x₀) = X := by
  refine Set.eq_of_subset_of_subset (range_pad_subset hx) fun y hy => ?_
  refine ⟨⟨((setEquiv X).symm ⟨y, hy⟩ : Fin X.ncard),
    lt_of_lt_of_le ((setEquiv X).symm ⟨y, hy⟩).2 hle⟩, ?_⟩
  unfold pad
  rw [dif_pos (((setEquiv X).symm ⟨y, hy⟩)).2]
  have h : (⟨(((setEquiv X).symm ⟨y, hy⟩ : Fin X.ncard) : ℕ),
      ((setEquiv X).symm ⟨y, hy⟩).2⟩ : Fin X.ncard) = (setEquiv X).symm ⟨y, hy⟩ :=
    Fin.ext rfl
  rw [h, Equiv.apply_symm_apply]

/-- The designated element is hit by the pad whenever the set fits the
width (used for the descent's `hself`). -/
theorem mem_range_pad {k mb : ℕ} {X : Set (Fin k)} {x₀ : Fin k} (hx : x₀ ∈ X)
    (hle : X.ncard ≤ mb) : x₀ ∈ Set.range (pad (mb := mb) X x₀) :=
  (range_pad hx hle).symm ▸ hx

end Lax3Proofs.Driver

/-! ### The enumeration's partial inverse

`restrictEmb` and `toLocal` — §6.1's "rank `S` to get local names" and
its reverse index — were `ImplRestrict` §1a; they are here, **verbatim
and in their own namespace**, because `childArena`'s inherited channel
columns are `MArena.restrict`'s `filterMap (toLocal …)` on the nose and
the driver must now name them. Nothing changed but the position in the
import graph. -/

namespace Lax3Proofs.Impl

variable {n : ℕ}

/-- The enumeration embedding of §6.1's "rank `S` to get local names":
the local carrier `Fin S.ncard` into the parent carrier, through the
same `Driver.setEquiv` the driver's compaction bijection uses — so the
identities to `preG`/`childArena` below are definitional. -/
noncomputable def restrictEmb (S : Set (Fin n)) : Fin S.ncard ↪ Fin n :=
  (Driver.setEquiv S).toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem restrictEmb_apply (S : Set (Fin n)) (a : Fin S.ncard) :
    restrictEmb S a = ((Driver.setEquiv S) a : Fin n) := rfl

theorem restrictEmb_mem (S : Set (Fin n)) (a : Fin S.ncard) :
    restrictEmb S a ∈ S := ((Driver.setEquiv S) a).2

open Classical in
/-- The partial inverse of the enumeration: a parent name to its local
name if it has one — the reverse index the scratch array realizes. -/
noncomputable def toLocal (S : Set (Fin n)) (x : Fin n) : Option (Fin S.ncard) :=
  if h : x ∈ S then some ((Driver.setEquiv S).symm ⟨x, h⟩) else none

theorem toLocal_eq_none (S : Set (Fin n)) {x : Fin n} (hx : x ∉ S) :
    toLocal S x = none := by
  rw [toLocal, dif_neg hx]

theorem restrictEmb_toLocal (S : Set (Fin n)) {x : Fin n} (hx : x ∈ S)
    {a : Fin S.ncard} (h : toLocal S x = some a) : restrictEmb S a = x := by
  rw [toLocal, dif_pos hx] at h
  obtain rfl := Option.some_injective _ h
  show ((Driver.setEquiv S) ((Driver.setEquiv S).symm ⟨x, hx⟩) : Fin n) = x
  rw [Equiv.apply_symm_apply]

open Classical in
/-- The filtered list, read back at parent names, is exactly the stored
list's intersection with `S`, in order — "intersect the stored lists
with `S`" as a list identity. -/
theorem map_restrictEmb_filterMap_toLocal (S : Set (Fin n)) (l : List (Fin n)) :
    (l.filterMap (toLocal S)).map (fun b => (restrictEmb S b : Fin n))
      = l.filter fun x => decide (x ∈ S) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases hx : x ∈ S
    · have hsome : toLocal S x = some ((Driver.setEquiv S).symm ⟨x, hx⟩) := by
        rw [toLocal, dif_pos hx]
      rw [hsome, if_pos (by simpa using hx), List.map_cons, ih,
        restrictEmb_toLocal S hx hsome]
    · rw [toLocal_eq_none S hx, if_neg (by simpa using hx), ih]

/-- Filtering a channel row never lengthens it — with §4's `≤ 2R+1`
bound on the stored lists, the child's rows keep it. -/
theorem length_filterMap_toLocal_le (S : Set (Fin n)) (l : List (Fin n)) :
    (l.filterMap (toLocal S)).length ≤ l.length :=
  List.length_filterMap_le _ _

end Lax3Proofs.Impl

namespace Lax3Proofs.Driver

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.UniformQuasiWideness Lax12.ColoringNumbers
open Lax3Proofs.LocalityFun Lax3Proofs.WalkDistance

/-! ### The arena -/

variable {L : ℕ}

/-- §4's data structure, abstractly (module docstring for the field
discussion). `Λ` is the node's palette, `n₀` the ROOT carrier size. -/
structure Arena (Λ n₀ : ℕ) where
  /-- The number of vertices of this node's arena. -/
  N : ℕ
  /-- The edges of this node's arena. -/
  G : SimpleGraph (Fin N)
  /-- The color rows, at this node's palette. -/
  col : Coloring N Λ
  /-- This vertex's name at the ROOT (the composite of the `up` maps —
  the record is never re-typed, E6). -/
  up : Fin N ↪ Fin n₀
  /-- D6's downward channel, abstractly: the `(connector, arena)` pair
  of each ancestor round, at root names, newest first. -/
  hist : List (Fin n₀ × SimpleGraph (Fin n₀))
  /-- D6's downward channel, **as §4 stores it**: per vertex and per
  round column, that round's recorded walk-support names, at this
  node's own carrier. `ℕ`-indexed — only columns `< hist.length` carry
  a round, and the padding beyond is never read. -/
  chan : Fin N → ℕ → List (Fin N)

variable {n₀ : ℕ}

/-! ### One node of the recursion: cover, clusters, centres -/

/-- §6.2's cluster of the centre `u`: the wreach fibre at radius `2R`.
Membership of `w` is a walk `w → u` of length `≤ 2R` whose support is
`π`-above `u`. -/
def cluster (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N))
    (u : Fin A.N) : Set (Fin A.N) :=
  {w | u ∈ wreach A.G π (2 * S.R) w}

theorem self_mem_cluster (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : u ∈ cluster S A π u :=
  Lax3Proofs.ClusterPaths.self_mem_fiber A.G π (2 * S.R) u

/-- §4's `ctr`: the `π`-minimum of the weak `R`-reachability set — the
centre whose child answers for `v`. -/
noncomputable def centre (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (v : Fin A.N) : Fin A.N :=
  Lax3Proofs.CoverCentres.ctr A.G π S.R v

/-- Every vertex lies in the cluster of its centre (`ball_R(v) ⊆ X_{ctr v}`
at the ball's own centre) — §5's "written exactly once". -/
theorem mem_cluster_centre (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (v : Fin A.N) : v ∈ cluster S A π (centre S A π v) :=
  Lax3Proofs.CoverCentres.ball_subset_cluster_ctr A.G π S.R v
    (mem_ball_self A.G S.R v)

/-! ### The child of one centre -/

section Child

variable (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)

/-- The child carrier size: the cluster's cardinality. -/
noncomputable def childN : ℕ := (cluster S A π u).ncard

/-- The compaction bijection of the child carrier with the cluster
(§5 step 3′). -/
noncomputable def childEquiv : Fin (childN S A π u) ≃ ↥(cluster S A π u) :=
  setEquiv (cluster S A π u)

/-- The centre's own name on the child carrier. -/
noncomputable def centreChild : Fin (childN S A π u) :=
  (childEquiv S A π u).symm ⟨u, self_mem_cluster S A π u⟩

/-- **`B₀` of §5 lines 16/20**: the graph induced on the cluster,
renumbered onto the child carrier — the arena the profiles are measured
in, *before* isolation. -/
noncomputable def preG : SimpleGraph (Fin (childN S A π u)) :=
  SimpleGraph.comap (fun a => ((childEquiv S A π u) a : Fin A.N)) A.G

/-- The node's colors, pulled onto the child carrier. -/
noncomputable def childCol0 : Coloring (childN S A π u) Λ :=
  fun c => {a | ((childEquiv S A π u) a : Fin A.N) ∈ A.col c}

/-- The marker step: old colors at their old slots, the marker —
*everything*, since after compaction the cluster is the whole carrier —
at the appended slot. -/
noncomputable def childColR : Coloring (childN S A π u) (relPal Λ) :=
  relColoring (childCol0 S A π u) Set.univ

/-- **§5 line 19's batch, at the node's own names**: the connector `u`,
plus every name the channel stores in `u`'s row at a round column.
Columns `≥ hist.length` carry no round and are not read.

This is the set the machine's line 19 *computes*: the channel rows are
exactly the arrays `supportsCom_specW` writes and `MArena.restrict`
carries down. The previous spelling — `SplitterWin.genSet`, the union of
`Classical.choose`-picked walk supports — is the same *kind* of set
(one recorded walk-support per ancestor round) but no program can output
it, and `profilesCom_specW` needs the batch region to hold `batchFn`'s
values exactly. `genSet` remains live where it belongs, in `ReachedS`,
proving Splitter wins. -/
def batchPar : Set (Fin A.N) :=
  {u} ∪ {z | ∃ e < A.hist.length, z ∈ A.chan u e}

theorem self_mem_batchPar : u ∈ batchPar A u := Or.inl rfl

theorem chan_subset_batchPar {e : ℕ} (he : e < A.hist.length) {z : Fin A.N}
    (hz : z ∈ A.chan u e) : z ∈ batchPar A u := Or.inr ⟨e, he, hz⟩

/-- The batch at ROOT names — the shape the splitter record consumes. -/
def batchRoot : Set (Fin n₀) := ⇑A.up '' batchPar A u

/-- The batch's trace on the child carrier. -/
noncomputable def batchSet : Set (Fin (childN S A π u)) :=
  {a | A.up ((childEquiv S A π u) a : Fin A.N) ∈ batchRoot A u}

theorem centreChild_mem_batchSet : centreChild S A π u ∈ batchSet S A π u := by
  show A.up ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨u, _⟩) : Fin A.N)
      ∈ batchRoot A u
  rw [Equiv.apply_symm_apply]
  exact ⟨u, self_mem_batchPar A u, rfl⟩

/-- §5 line 19's `pad_m`: the batch as a function on exactly `width`
slots (hazard 2 — the `iso` palette is sized by the schedule, and the
pad repeats the connector to close the difference). -/
noncomputable def batchFn : Fin S.width → Fin (childN S A π u) :=
  pad (batchSet S A π u) (centreChild S A π u)

/-- **The child's colors** (§5 lines 20/22/23, semantically): the marker
palette, then the two profile families of the schedule's slot layout —
the batch-distance profiles and the color-distance profiles, both
*cumulative* (`WithinDist`, distance `≤ a`) and both measured in
**`preG`, before isolation** (hazard 1). These are `Isolate.sat_iso`'s
`hpd`/`hpu` equations, made definitional. -/
noncomputable def childCol : Coloring (childN S A π u) (isoPal (relPal Λ) S.width S.R) :=
  slotColoring (childColR S A π u)
    (fun j a => {z | WithinDist (preG S A π u) (a : ℕ) z (batchFn S A π u j)})
    (fun c b => {z | ∃ y ∈ childColR S A π u c, WithinDist (preG S A π u) (b : ℕ) z y})

open Classical in
/-- **The canonical ball table of this round's BFS**: the truncated
distance table from the centre's own child name in `B₀`, at radius
`2R`. `bfsCom` can leave no other table (`ballTable_eq_ballDist`), and
the radius is `2R` because the cluster is the wreach fibre at `2R`
(`SolveFrameStages.supportsCom_specW`: "the frame-step discharger
instantiates `2R` here, never `S.R`"). -/
noncomputable def childDist : Fin (childN S A π u) → ℕ :=
  Lax3Proofs.Prog.ballDist (preG S A π u) (centreChild S A π u) (2 * S.R)

open Classical in
/-- **The child's channel, inherit-and-patch** (§5 line 17/23): column
`hist.length` — this round's — is the gradient-walk table the supports
pass writes (`descendCol` of `childDist` in `B₀` at radius `2R`,
verbatim `supportsCom_specW`'s deliverable); every older column is the
parent's row at the parent name, filtered onto the cluster and
renumbered (verbatim `MArena.restrict`'s `hist` field).

One BFS per node, from `centreChild`, is all the pass can afford and
all it needs: `ClusterPaths.exists_walk_support_subset_fiber` puts
every child vertex within `2R` of the centre inside `B₀`, so this
column is a genuine `descend` at every vertex, never `[]`. Recomputing
the *ancestors'* columns here instead would return nothing — their
connectors are edge-isolated in the current arena — which is the
vacuity §5 ⟨A⟩ recorded. -/
noncomputable def childChan :
    Fin (childN S A π u) → ℕ → List (Fin (childN S A π u)) :=
  fun a e =>
    if e = A.hist.length then
      Lax3Proofs.Prog.descendCol (preG S A π u) (childDist S A π u) (2 * S.R) a
    else
      (A.chan ((childEquiv S A π u) a : Fin A.N) e).filterMap
        (Lax3Proofs.Impl.toLocal (cluster S A π u))

/-- **The child arena** of centre `u` (§5 lines 15–23): the cluster's
carrier, the restricted graph with the batch isolated, the profile
colors, the composite renaming, and the extended channel. -/
noncomputable def childArena : Arena (isoPal (relPal Λ) S.width S.R) n₀ where
  N := childN S A π u
  G := deleteVerts (preG S A π u) (Set.range (batchFn S A π u))
  col := childCol S A π u
  up := ((childEquiv S A π u).toEmbedding.trans
    (Function.Embedding.subtype _)).trans A.up
  hist := (A.up u, SimpleGraph.map A.up A.G) :: A.hist
  chan := childChan S A π u

@[simp] theorem childArena_N : (childArena S A π u).N = childN S A π u := rfl

@[simp] theorem childArena_G :
    (childArena S A π u).G = deleteVerts (preG S A π u) (Set.range (batchFn S A π u)) :=
  rfl

@[simp] theorem childArena_col : (childArena S A π u).col = childCol S A π u := rfl

@[simp] theorem childArena_hist :
    (childArena S A π u).hist = (A.up u, SimpleGraph.map A.up A.G) :: A.hist := rfl

@[simp] theorem childArena_chan :
    (childArena S A π u).chan = childChan S A π u := rfl

@[simp] theorem childArena_up_apply (a : Fin (childArena S A π u).N) :
    (childArena S A π u).up a = A.up ((childEquiv S A π u) a : Fin A.N) := rfl

open Classical in
theorem childChan_new (a : Fin (childN S A π u)) :
    childChan S A π u a A.hist.length
      = Lax3Proofs.Prog.descendCol (preG S A π u) (childDist S A π u) (2 * S.R) a :=
  if_pos rfl

open Classical in
theorem childChan_old {e : ℕ} (he : e ≠ A.hist.length) (a : Fin (childN S A π u)) :
    childChan S A π u a e
      = (A.chan ((childEquiv S A π u) a : Fin A.N) e).filterMap
          (Lax3Proofs.Impl.toLocal (cluster S A π u)) :=
  if_neg he

/-! #### The channel column's three facts

Everything `DriverCorrect` needs about `childChan`: the new column is a
real `descend` (so the batch is not degenerate), it fits the `2R+1`
schedule bound, and an inherited column is the parent's row cut down to
the cluster. -/

/-- **The cluster has radius `2R` inside `B₀`**: every child vertex is
within `2R` of the centre's own child name, *in `preG`* — cluster
path-closure (`ClusterPaths.exists_walk_induce_fiber`), transported
along the compaction bijection. This is what makes one BFS from
`centreChild` cover the whole child carrier. -/
theorem withinDist_preG_centreChild (a : Fin (childN S A π u)) :
    WithinDist (preG S A π u) (2 * S.R) (centreChild S A π u) a := by
  refine withinDist_symm ?_
  obtain ⟨q, hq⟩ := Lax3Proofs.ClusterPaths.exists_walk_induce_fiber
    (G := A.G) (π := π) (r := 2 * S.R) (u := u)
    (w := ((childEquiv S A π u) a : Fin A.N)) ((childEquiv S A π u) a).2
  have hadj : ∀ x y : ↥(cluster S A π u), (A.G.induce (cluster S A π u)).Adj x y →
      (preG S A π u).Adj ((childEquiv S A π u).symm x)
        ((childEquiv S A π u).symm y) := by
    intro x y hxy
    show A.G.Adj ((childEquiv S A π u) ((childEquiv S A π u).symm x) : Fin A.N)
      ((childEquiv S A π u) ((childEquiv S A π u).symm y) : Fin A.N)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hxy
  refine ⟨SimpleGraph.Walk.copy
    (q.map (⟨fun x => (childEquiv S A π u).symm x, fun {x y} h => hadj x y h⟩ :
      (A.G.induce (cluster S A π u)) →g preG S A π u))
    (by
      show (childEquiv S A π u).symm ((childEquiv S A π u) a) = a
      rw [Equiv.symm_apply_apply]) rfl, ?_⟩
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
  exact hq

open Classical in
/-- The centre's BFS reaches every child vertex within the horizon —
the `descendCol` guard is always satisfied. -/
theorem childDist_le (a : Fin (childN S A π u)) :
    childDist S A π u a ≤ 2 * S.R :=
  ((Lax3Proofs.Prog.ballDist_ballTable (preG S A π u) (centreChild S A π u)
    (2 * S.R)) a (2 * S.R) le_rfl).mpr (mem_ball.mpr (withinDist_preG_centreChild S A π u a))

open Classical in
/-- **The new column is a genuine recorded walk**, at every child
vertex: `descend`'s gradient list, which `Impl.descend_spec` certifies
is the support of a walk of length `≤ 2R` from the vertex to the
centre, inside `B₀`. -/
theorem exists_walk_childChan_new (a : Fin (childN S A π u)) :
    ∃ p : (preG S A π u).Walk a (centreChild S A π u),
      p.length ≤ 2 * S.R ∧
        p.support = childChan S A π u a A.hist.length := by
  obtain ⟨w, hwlen, hwsup⟩ :=
    Lax3Proofs.Impl.descend_spec
      (Lax3Proofs.Prog.ballDist_ballTable (preG S A π u) (centreChild S A π u)
        (2 * S.R)) a (childDist_le S A π u a)
  refine ⟨w, ?_, ?_⟩
  · rw [hwlen]; exact childDist_le S A π u a
  · rw [hwsup, childChan_new, Lax3Proofs.Prog.descendCol_of_reached
      (childDist_le S A π u a)]
    rfl

open Classical in
/-- **Every channel row fits `2R + 1`** — the new column by
`descendCol_length_le`, the inherited ones because filtering never
lengthens a list. -/
theorem childChan_length_le (hchan : ∀ (w : Fin A.N) (e : ℕ),
      (A.chan w e).length ≤ 2 * S.R + 1)
    (a : Fin (childN S A π u)) (e : ℕ) :
    (childChan S A π u a e).length ≤ 2 * S.R + 1 := by
  by_cases he : e = A.hist.length
  · subst he
    rw [childChan_new]
    exact Lax3Proofs.Prog.descendCol_length_le
      (Lax3Proofs.Prog.ballDist_ballTable (preG S A π u) (centreChild S A π u)
        (2 * S.R)) a
  · rw [childChan_old S A π u he]
    exact le_trans (Lax3Proofs.Impl.length_filterMap_toLocal_le _ _)
      (hchan _ e)

open Classical in
/-- **An inherited column is the parent's row cut down to the cluster**
— `MArena.restrict`'s `hist` field, read at parent names
(`map_restrictEmb_filterMap_toLocal`). -/
theorem mem_childChan_old_iff {e : ℕ} (he : e ≠ A.hist.length)
    (a : Fin (childN S A π u)) (x : Fin A.N) :
    (∃ b ∈ childChan S A π u a e, ((childEquiv S A π u) b : Fin A.N) = x)
      ↔ (x ∈ A.chan ((childEquiv S A π u) a : Fin A.N) e ∧ x ∈ cluster S A π u) := by
  classical
  have h := Lax3Proofs.Impl.map_restrictEmb_filterMap_toLocal
    (cluster S A π u) (A.chan ((childEquiv S A π u) a : Fin A.N) e)
  rw [childChan_old S A π u he]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hmem : ((childEquiv S A π u) b : Fin A.N) ∈
        (A.chan ((childEquiv S A π u) a : Fin A.N) e).filter
          (fun z => decide (z ∈ cluster S A π u)) := by
      rw [← h]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    exact ⟨(List.mem_filter.mp hmem).1, ((childEquiv S A π u) b).2⟩
  · rintro ⟨hx1, hx2⟩
    have hmem : x ∈ (A.chan ((childEquiv S A π u) a : Fin A.N) e).filter
        (fun z => decide (z ∈ cluster S A π u)) :=
      List.mem_filter.mpr ⟨hx1, decide_eq_true hx2⟩
    rw [← h, List.mem_map] at hmem
    exact hmem

/-- The child's root names are exactly the cluster's. -/
theorem range_childArena_up :
    Set.range ⇑(childArena S A π u).up = ⇑A.up '' cluster S A π u := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨((childEquiv S A π u) a : Fin A.N), ((childEquiv S A π u) a).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(childEquiv S A π u).symm ⟨y, hy⟩, by
      show A.up ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨y, hy⟩) : Fin A.N)
        = A.up y
      rw [Equiv.apply_symm_apply]⟩

end Child

/-! ### The driver -/

open Classical in
/-- **§5's `Tables`, abstractly.** Structural fuel spells the
termination; `tables` below ties it to `ℓ − j`. At fuel `0` or on an
edgeless arena, the leaf: `BotTables` through its spec — the table IS
satisfaction in the (edgeless) arena. Otherwise §5 lines 13–28: cover
the arena (`ord`), and the entry at `(v, β)` for a schedule formula `β`
is `eval(dec β, sub[v'], sc)` over the child of `v`'s centre — the
child's table at the local atoms, the guarded greedy scatter counts at
the scatter atoms. Entries at non-schedule formulas are `True` (line
14's uninitialised table, never read). -/
noncomputable def tablesAux (S : Setup L) (ord : CoverSpec.OrderingRoutine) :
    (fuel : ℕ) → (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → DistFO (S.pal j) 1 → Prop
  | 0, _, A => fun v β => Sat A.G A.col (fun _ => v) β
  | fuel + 1, j, A =>
    if A.G = ⊥ then fun v β => Sat A.G A.col (fun _ => v) β
    else fun v β =>
      let π := (ord A.N A.G).order
      let u := centre S A π v
      let B := childArena S A π u
      let vc : Fin B.N := (childEquiv S A π u).symm ⟨v, mem_cluster_centre S A π v⟩
      if h : IsLocal β ∧ DRank 1 (S.q - 1) β then
        (dec S (j := j) ⟨β, h.1, h.2⟩).eval
          (Sum.elim (fun ψ => tablesAux S ord fuel (j + 1) B vc ψ)
            (fun σ => σ.t ≤ S.choice.size B.G σ.r
              {a | tablesAux S ord fuel (j + 1) B a σ.β}))
      else True

/-- The table of a depth-`j` node: `Tables(A, j)`, at fuel `ℓ − j`. -/
noncomputable def tables (S : Setup L) (ord : CoverSpec.OrderingRoutine) (j : ℕ)
    (A : Arena (S.pal j) n₀) : Fin A.N → DistFO (S.pal j) 1 → Prop :=
  tablesAux S ord (S.depth - j) j A

/-- §5 line 2: the arena of the input graph — identity renaming, empty
channel, the input's own colors. -/
def rootArena {n : ℕ} (G : SimpleGraph (Fin n)) (col : Coloring n L) : Arena L n where
  N := n
  G := G
  col := col
  up := Function.Embedding.refl _
  hist := []
  chan := fun _ _ => []

/-- **§5's `MC`** (lines 1–6): evaluate `top` with its local sentence
atoms as compile-time constants (L1, `localConst`) and its scatter atoms
by the guarded greedy scatter count over the root table. -/
noncomputable def MC (S : Setup L) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) : Prop :=
  (top S).eval (Sum.elim (fun ψ => localConst ψ)
    (fun σ => σ.t ≤ S.choice.size G σ.r
      {v : Fin n | tables S ord 0 (rootArena G col) v σ.β}))

end Lax3Proofs.Driver
