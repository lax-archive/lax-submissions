import Lax3Proofs.DriverSchedule
import Lax3Proofs.CoverSpec
import Lax3Proofs.CoverCentres
import Lax3Proofs.ClusterPaths
import Lax3Proofs.SplitterWin

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
* `hist` — D6's downward channel, abstracted: per ancestor round, the
  connector together with the round's arena **restricted to the round's
  own cluster** (`histGraph` — §5 line 17's `B₀`, at root names),
  newest first. §4's per-vertex support lists are the *materialization*
  of this data (the supports of `SplitterWin.genSet`'s canonical
  gradient walks, computed in exactly these restricted graphs —
  F6c12p); the abstract driver reads the batch off `genSet` directly,
  which is the same set §5 line 19 computes (`algorithm-v2.md` §3, "the
  batch is legal, by a landed lemma").

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
* `batchRoot` — line 19's batch at root names:
  `genSet (2R) hist (up u)`, the connector plus one recorded
  walk-support per ancestor round; `batchSet` is its trace on the child
  carrier; `batchFn` **pads it to exactly `width`** (`m`) by repeating
  the connector (the plan row's second hazard: the `iso` palette is
  sized by the schedule, not by the actual batch, and
  `genSet_ncard_le` + `m = ℓ(2R+1)` make the pad close the difference —
  `range_pad`).
* `childArena` — carrier `Fin childN`, graph
  `deleteVerts preG (range batchFn)` (line 21, isolation *after* the
  profiles), colors `childCol` (marker = everything, since after
  compaction the cluster is the whole carrier; then the two profile slot
  families of the schedule's `isoEnc` layout), `up` composed through the
  cluster inclusion, `hist` extended by this round's
  `(up u, histGraph)` pair — the cluster-restricted round graph, the
  one §5 line 17's BFS walks in (F6c12p).

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

Everything is `noncomputable` (`Classical.choose` in the schedule; the
compaction bijection and `genSet`'s recorded walks are the order-pinned
canonical ones — noncomputable but extensionally determined, F6c2 and
F6c12p); what this
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

/-- **The sorted enumeration is strictly monotone** (F6c12p): the
machine-seam transport of the canonical batch walks
(`BatchCanon.pathList_map`) runs along order-embeddings, and this is
the per-level piece every `childArena.up` composes. -/
theorem setEquiv_coe_strictMono {k : ℕ} (X : Set (Fin k)) :
    StrictMono fun a => ((setEquiv X a : ↥X) : Fin k) := by
  intro a b hab
  have h := ((Set.toFinite X).toFinset.orderIsoOfFin rfl).strictMono
    (a := finCongr (Set.ncard_eq_toFinset_card X (Set.toFinite X)) a)
    (b := finCongr (Set.ncard_eq_toFinset_card X (Set.toFinite X)) b)
    (by rw [Fin.lt_def]; exact hab)
  exact Subtype.coe_lt_coe.mpr h

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
  /-- D6's downward channel, abstractly: per ancestor round, the
  connector together with the round's arena restricted to the round's
  own cluster (`histGraph` — the graph the recorded supports walk in),
  at root names, newest first. -/
  hist : List (Fin n₀ × SimpleGraph (Fin n₀))

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

/-- §5 line 19's batch, at ROOT names: the connector plus one recorded
walk-support per ancestor round. This is `SplitterWin.genSet`, which is
literally the set line 19 writes (`algorithm-v2.md` §3). -/
noncomputable def batchRoot : Set (Fin n₀) :=
  Lax3Proofs.SplitterWin.genSet (2 * S.R) A.hist (A.up u)

/-- The batch's trace on the child carrier. -/
noncomputable def batchSet : Set (Fin (childN S A π u)) :=
  {a | A.up ((childEquiv S A π u) a : Fin A.N) ∈ batchRoot S A u}

theorem centreChild_mem_batchSet : centreChild S A π u ∈ batchSet S A π u := by
  show A.up ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨u, _⟩) : Fin A.N)
      ∈ batchRoot S A u
  rw [Equiv.apply_symm_apply]
  exact Lax3Proofs.SplitterWin.self_mem_genSet _ _ _

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

/-- **§5 line 17's recorded round graph**: the round's arena restricted
to the round's own cluster, at ROOT names. This is the graph the
recorded supports walk in — one BFS from the centre inside `B₀ =
A[X_u]` computes them at cluster cost (D6's channel; wreach clusters
are path-closed, so every cluster vertex is within `2R` of the centre
HERE, not merely in the full arena), and a walk of this graph is a walk
of the round's full arena, which is all the game asks
(`reachedS_descend`). Recording the restricted graph — rather than the
full `map A.up A.G` the round is played in — is what makes the
canonical `pathSet` batch machine-computable at cluster cost (F6c12p;
`Lax3Proofs.BatchCanon`'s module docstring holds the investigation). -/
noncomputable def histGraph : SimpleGraph (Fin n₀) :=
  deleteVerts (SimpleGraph.map A.up A.G) ((⇑A.up '' cluster S A π u)ᶜ)

/-- The recorded round graph is the pushforward of `preG` along the
child's composite renaming — the machine seam: supports recorded at
level names in `B₀ = preG` map verbatim to the recorded root-name graph
(`BatchCanon.pathList_map` along `childArena_up_strictMono`). -/
theorem histGraph_eq_map :
    histGraph S A π u
      = SimpleGraph.map (((childEquiv S A π u).toEmbedding.trans
          (Function.Embedding.subtype _)).trans A.up) (preG S A π u) := by
  ext x y
  rw [histGraph, Lax3Proofs.SplitterBasics.deleteVerts_adj]
  constructor
  · rintro ⟨hadj, hx, hy⟩
    rw [Set.notMem_compl_iff] at hx hy
    obtain ⟨x', hx', hxe⟩ := hx
    obtain ⟨y', hy', hye⟩ := hy
    obtain ⟨a', b', hab, hax, hby⟩ := (SimpleGraph.map_adj _ _ _ _).mp hadj
    have hax' : a' = x' := A.up.injective (hax.trans hxe.symm)
    have hby' : b' = y' := A.up.injective (hby.trans hye.symm)
    subst hax'
    subst hby'
    refine (SimpleGraph.map_adj _ _ _ _).mpr
      ⟨(childEquiv S A π u).symm ⟨a', hx'⟩, (childEquiv S A π u).symm ⟨b', hy'⟩,
        ?_, ?_, ?_⟩
    · show A.G.Adj
        ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨a', hx'⟩) : Fin A.N)
        ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨b', hy'⟩) : Fin A.N)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hab
    · show A.up
        ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨a', hx'⟩) : Fin A.N) = x
      rw [Equiv.apply_symm_apply]
      exact hxe
    · show A.up
        ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨b', hy'⟩) : Fin A.N) = y
      rw [Equiv.apply_symm_apply]
      exact hye
  · intro h
    obtain ⟨a, b, hab, hax, hby⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
    have hax' : A.up ((childEquiv S A π u) a : Fin A.N) = x := hax
    have hby' : A.up ((childEquiv S A π u) b : Fin A.N) = y := hby
    have hadj : A.G.Adj ((childEquiv S A π u) a : Fin A.N)
        ((childEquiv S A π u) b : Fin A.N) := hab
    refine ⟨(SimpleGraph.map_adj _ _ _ _).mpr ⟨_, _, hadj, hax', hby'⟩, ?_, ?_⟩
    · rw [Set.notMem_compl_iff]
      exact ⟨_, ((childEquiv S A π u) a).2, hax'⟩
    · rw [Set.notMem_compl_iff]
      exact ⟨_, ((childEquiv S A π u) b).2, hby'⟩

/-- **The child arena** of centre `u` (§5 lines 15–23): the cluster's
carrier, the restricted graph with the batch isolated, the profile
colors, the composite renaming, and the extended channel — the channel
entry records the round's connector together with `histGraph`, the
cluster-restricted round graph its supports walk in (F6c12p). -/
noncomputable def childArena : Arena (isoPal (relPal Λ) S.width S.R) n₀ where
  N := childN S A π u
  G := deleteVerts (preG S A π u) (Set.range (batchFn S A π u))
  col := childCol S A π u
  up := ((childEquiv S A π u).toEmbedding.trans
    (Function.Embedding.subtype _)).trans A.up
  hist := (A.up u, histGraph S A π u) :: A.hist

@[simp] theorem childArena_N : (childArena S A π u).N = childN S A π u := rfl

@[simp] theorem childArena_G :
    (childArena S A π u).G = deleteVerts (preG S A π u) (Set.range (batchFn S A π u)) :=
  rfl

@[simp] theorem childArena_col : (childArena S A π u).col = childCol S A π u := rfl

@[simp] theorem childArena_hist :
    (childArena S A π u).hist = (A.up u, histGraph S A π u) :: A.hist := rfl

/-- The child's composite renaming is strictly monotone whenever the
node's is: the sorted compaction enumeration into the subtype
inclusion, then the node's own map (F6c12p — the machine-seam
transport `BatchCanon.pathList_map` runs along these). -/
theorem childArena_up_strictMono (hA : StrictMono A.up) :
    StrictMono (childArena S A π u).up := fun _ _ hab =>
  hA (setEquiv_coe_strictMono (cluster S A π u) hab)

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

/-- The root renaming is strictly monotone — it is the identity
(F6c12p: the base of the `up`-chain the machine-seam transport runs
along; `childArena_up_strictMono` is the step). -/
theorem rootArena_up_strictMono {n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) : StrictMono (rootArena G col).up :=
  fun _ _ h => h

/-- **§5's `MC`** (lines 1–6): evaluate `top` with its local sentence
atoms as compile-time constants (L1, `localConst`) and its scatter atoms
by the guarded greedy scatter count over the root table. -/
noncomputable def MC (S : Setup L) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) : Prop :=
  (top S).eval (Sum.elim (fun ψ => localConst ψ)
    (fun σ => σ.t ≤ S.choice.size G σ.r
      {v : Fin n | tables S ord 0 (rootArena G col) v σ.β}))

end Lax3Proofs.Driver
