import Lax3Proofs.SolveSweepMdPeel

/-!
# F6c12 (residual 4) — the GKS peeling sweep, split at the seam its own output draws

`SolveSweepStep` splits `CovSweepIn` at the deletable structure's seam
and names two residuals; `SolveSweepBuild` discharged the first
(`CovAdjBuildIn`). This file owns the second, **`CovPeelIn`**
(`SolveSweepStep.lean:127`): from the built region, GKS's own sweep —
in ascending `OrdArr` order, per centre one frontier-queue BFS at
radius `2R` inside the current structure, the row and the first-hit
`ctr` marks emitted, then the centre deleted — landing
`CoverStageSpec`'s exact postcondition.

It does **not** write the sweep's program. It splits `CovPeelIn` at
the one seam the *output shape* forces, names the two halves at
budgets in GKS's own currency, proves the verbatim residual from them
(`covPeelIn_of_sweep_group`), and then proves the thing this leaf
exists to establish: **that this budget closes inside the `a·N^{1+2δ}`
envelope §7 charges the cover at** (§5).

## Finding 1 — the sweep cannot emit `ClusterCsr` directly

`ClusterCsr` (`SolveChainCover.lean:63`) anchors its offsets in
**carrier order** — `offC (u+1) = offC u + |X_u|` over `u : Fin N` —
and its rows in **ascending vertex order**
(`Impl.restrictEmb (Xf u) t` is the `t`-th smallest member, the value
the restrict stage reads). The sweep visits centres in ascending `π`,
which is a different order, and a BFS enumerates its ball in level
order, which is a different order again. Neither can be repaired
inside the sweep:

* the row of `u` cannot be written at `offC u` before `|X_{u'}|` is
  known for every carrier-earlier `u'`, and those clusters are
  computed at their own `π`-positions, later in the sweep;
* sorting a row by a per-centre pass over the carrier is `Θ(N)` a
  centre, i.e. `Θ(N²)` — the exact envelope break `SolveCovStep`'s
  Finding 3 records, and the one wave 23 repeated in the ordering
  pass.

So the sweep emits its rows in **peel order, unsorted** — a log
(`ClusterLog`, §1) — and a second pass turns the log into
`ClusterCsr`. That pass is two stable counting sorts (by member, then
by centre), `O(N + Σ_u |X_u|)` and no per-centre carrier pass: the
seam is what keeps both halves linear in the mass.

## The budget, and what it counts (§2)

Three figures, all functions of the arena and the ordering alone:

* `A.N` — the per-centre overhead (read `od[i]`, start and finish the
  BFS, the counting sorts' two carrier scans);
* `clusterMass S A π = Σ_u |X_u|` — the per-reached-vertex work (the
  queue push, the `ctr` test, the log append, the two scatter passes,
  and — by `curDeg_at_deletion_le_cluster` — the deletion's own
  `54·d + 5`, since `d ≤ |X_u|` at `u`'s deletion);
* `peelEdgeWork S A π = Σ_u Σ_{w ∈ X_u} d_<(w)` — the per-scanned-cell
  work of the BFS, in **GKS's own currency** (tex:1488-1496: "we can
  count the edges of `G'` by counting the sum of `d_<(v)` over all
  `v ∈ V(G')`").

Both residuals are stated at the **affine** budget
`peelK a b c = a·N + b·mass + c·edge`, with the constants left to
their dischargers (a program not yet written cannot honestly pin
them) but the *shape* fixed: a residual at a budget function of the
discharger's free choice would have been no budget at all. So
`CovPeelIn` is concluded at

    Kpl j A = peelK (asw + agr) (bsw + bgr) csw S A π

(`peelK_add`), and §5 proves of that very expression

    peelK a b c ≤ a·N + b·(N·D) + c·(N·D·D)

under the cover-degree hypothesis `∀ x, |wreach_{2R}(x)| ≤ D`
(`peelBudget_le`) — i.e. `O(N·D²)`, which is §7's `a·N^{1+2δ}` at
`D = ⌈c_D·N^δ⌉` — and, against the landed abstract account,

    peelK a b c ≤ a·N + (b+c)·sweepCharge

(`peelBudget_le_sweepCharge`; and `A.N ≤ mass` by
`card_le_clusterMass`, so the linear term is not a fourth figure).
Both need `1 ≤ S.R`, which is Hazard 4: `d_<(v) ≤ |wreach_{2R}(v)|`
and `N_>(v) ⊆ X_v` each charge a length-`1` walk against the radius
and are false at `R = 0`. It is stated, never hidden.

## Finding 2 — why the BFS budget is `Σ_{w ∈ X_u} d_<(w)` and not the
degree sum

The frontier BFS at `u` reads the live prefix of `w`'s row for every
`w` it *expands*. If it expands the vertices at distance `< 2R` only —
**it must not expand the final level** — then every cell it reads is
an edge of the current graph with *both* endpoints inside `X_u`, and
`sum_induced_deg_le_two_sum_dlt` (§5) bounds those, for any subgraph
`H ≤ G` and any set `s`, by `2·Σ_{w ∈ s} d_<(w)`: each such edge is
counted once, in the `N_<`-list of its `π`-later endpoint. A BFS that
expands the last level too reads cells whose far endpoint is outside
`X_u` and is *not* covered by this bound; a BFS that resets an
`N`-cell visited array per centre is `Θ(N²)` outright — it must clear
its marks by re-walking its own reached list. Both are real
constraints on the discharger of `PeelSweepIn`, recorded here because
neither is visible in its statement.

A third, smaller one: `CovPeelIn`'s precondition offers `ca` as a bare
allocation, with no initial contents, so the sweep owes one carrier
pass writing a sentinel (`A.N`, a word since `A.N < mcB q x`) before
the marking can test "not yet assigned". That pass is `O(N)` and sits
inside the budget's `a·N` term.

## What this file proves

* `ClusterLog` (§1) — the peel-order log, its frame fact
  (`of_eq`), its pigeonhole (`row_injOn`: soundness + completeness +
  the count force a row to be a duplicate-free enumeration, so no
  no-dup clause is carried — the landed `DelAdjSt.slot_injOn` idiom)
  and its size (`total`: the log is exactly `mass` cells);
* `PeelSweepIn`, `PeelGroupIn` (§3) — the two named residuals;
* `covPeelIn_of_sweep_group` (§4) — **`CovPeelIn`, verbatim**, from
  the two, at the summed affine budget;
* §5 — the cost envelope: `sum_induced_deg_le_two_sum_dlt` and its
  assembly over the sweep (`sum_bfsCells_le`),
  `sum_curDeg_le_clusterMass`, `card_le_clusterMass`,
  `clusterMass_le`, `peelEdgeWork_le_mass_mul`,
  `clusterMass_le_sweepCharge`, `peelEdgeWork_le_sweepCharge`,
  `peelBudget_le`, `peelBudget_le_sweepCharge`;
* §6 — a control that `ClusterLog` is satisfiable, so the seam is not
  a vacuous one.

What it does **not** prove: either residual. Neither the frontier BFS
nor the two counting sorts is written here. The leaf's judgement is
that a quadratic program at the wrong budget would have been worth
less than these two names at the right one.

Everything stays **parametric in `ord`**: no clause mentions how the
ordering was produced.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax12.ColoringNumbers
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The peel-order cluster log

The seam of Finding 1: the sweep's own output shape. Row `i` is the
cluster of the vertex of rank `i` — the centre the sweep processes
`i`-th — in **whatever order the BFS reached it**. Offsets are the
running mass in peel order, so the sweep appends and never seeks.

Soundness and completeness are carried; duplicate-freeness is derived
(`row_injOn`), exactly as `DelAdjSt` carries neither a no-duplicates
clause nor a per-row enumeration. -/

/-- **The peel-order cluster log**: `lo` holds the `N + 1` running
offsets in peel order, `lm` the appended rows. Row `i` — at
`[offL i, offL (i+1))` — enumerates `Xf (π.symm i)`, the cluster of
the rank-`i` vertex, in an unspecified order. -/
def ClusterLog (lo lm : String) {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (σ : Env) : Prop :=
  ∃ offL : ℕ → ℕ,
    offL 0 = 0 ∧
    N + 1 ≤ (σ.arrs lo).length ∧
    (∀ i, i ≤ N → (σ.arrs lo).getD i 0 = offL i) ∧
    (∀ i : Fin N, offL ((i : ℕ) + 1) = offL (i : ℕ) + (Xf (π.symm i)).ncard) ∧
    offL N ≤ (σ.arrs lm).length ∧
    (∀ i : Fin N, ∀ t : ℕ, t < (Xf (π.symm i)).ncard →
      ∃ z : Fin N, z ∈ Xf (π.symm i) ∧
        (σ.arrs lm).getD (offL (i : ℕ) + t) 0 = (z : ℕ)) ∧
    (∀ i : Fin N, ∀ z : Fin N, z ∈ Xf (π.symm i) →
      ∃ t : ℕ, t < (Xf (π.symm i)).ncard ∧
        (σ.arrs lm).getD (offL (i : ℕ) + t) 0 = (z : ℕ))

/-- The log reads exactly two arrays: it transports along agreement on
them (the frame fact a composed pass applies). -/
theorem ClusterLog.of_eq {lo lm : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {Xf : Fin N → Set (Fin N)} {σ σ' : Env} (h : ClusterLog lo lm π Xf σ)
    (hlo : σ'.arrs lo = σ.arrs lo) (hlm : σ'.arrs lm = σ.arrs lm) :
    ClusterLog lo lm π Xf σ' := by
  rw [ClusterLog, hlo, hlm]
  exact h

/-- **A log row has no duplicates** (pigeonhole): completeness makes
the cluster's values a subset of the row's image and the count equates
the cardinalities, so the row is an *enumeration* of the cluster. The
grouping pass's counting sort consumes exactly this: it moves
`Σ_i |X_{π.symm i}|` entries and must not move a member twice. -/
theorem ClusterLog.row_injOn {lo lm : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {Xf : Fin N → Set (Fin N)} {σ : Env} (h : ClusterLog lo lm π Xf σ) :
    ∃ offL : ℕ → ℕ,
      offL 0 = 0 ∧
      (∀ i : Fin N, offL ((i : ℕ) + 1) = offL (i : ℕ) + (Xf (π.symm i)).ncard) ∧
      ∀ i : Fin N, Set.InjOn (fun t => (σ.arrs lm).getD (offL (i : ℕ) + t) 0)
        {t | t < (Xf (π.symm i)).ncard} := by
  obtain ⟨offL, h0, -, -, hstep, -, -, hcomp⟩ := h
  refine ⟨offL, h0, hstep, fun i => ?_⟩
  -- the cluster's values sit inside the image of the row
  have h1 : (Fin.val '' (Xf (π.symm i))) ⊆
      ↑((Finset.range ((Xf (π.symm i)).ncard)).image
        (fun t => (σ.arrs lm).getD (offL (i : ℕ) + t) 0)) := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨t, ht, hval⟩ := hcomp i z hz
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, hval⟩)
  have h2 : (Xf (π.symm i)).ncard ≤
      ((Finset.range ((Xf (π.symm i)).ncard)).image
        (fun t => (σ.arrs lm).getD (offL (i : ℕ) + t) 0)).card :=
    calc (Xf (π.symm i)).ncard
        = (Fin.val '' (Xf (π.symm i))).ncard :=
          (Set.ncard_image_of_injective _ Fin.val_injective).symm
      _ ≤ _ := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((Finset.range ((Xf (π.symm i)).ncard)).image
      (fun t => (σ.arrs lm).getD (offL (i : ℕ) + t) 0)).card
        = (Finset.range ((Xf (π.symm i)).ncard)).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_range]; exact h2)
  have hinj := Finset.injOn_of_card_image_eq h3
  have hset : ({t | t < (Xf (π.symm i)).ncard} : Set ℕ)
      = ↑(Finset.range ((Xf (π.symm i)).ncard)) := by
    rw [Finset.coe_range]
    rfl
  rw [hset]
  exact hinj

/-- **The log occupies exactly the cluster mass**: the running offsets
close at `Σ_u |X_u|` cells (the peel order is a permutation of the
carrier, so the peel-order sum is the carrier-order sum). This is the
figure the sweep's appends and the grouping's two counting sorts are
each linear in, and the allocation the grouping pass's scratch owes
for `cm`. -/
theorem ClusterLog.total {lo lm : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {Xf : Fin N → Set (Fin N)} {σ : Env} (h : ClusterLog lo lm π Xf σ) :
    ∃ offL : ℕ → ℕ,
      (∀ i, i ≤ N → (σ.arrs lo).getD i 0 = offL i) ∧
      offL N = ∑ u : Fin N, (Xf u).ncard ∧
      offL N ≤ (σ.arrs lm).length := by
  obtain ⟨offL, h0, -, hread, hstep, hlen, -, -⟩ := h
  refine ⟨offL, hread, ?_, hlen⟩
  have hpre : ∀ k, k ≤ N → offL k
      = ∑ i ∈ Finset.range k,
          if hi : i < N then (Xf (π.symm ⟨i, hi⟩)).ncard else 0 := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
        intro hk
        have hkN : k < N := hk
        rw [Finset.sum_range_succ, ← ih (by omega), dif_pos hkN]
        exact hstep ⟨k, hkN⟩
  rw [hpre N le_rfl,
    Finset.sum_range fun i => if hi : i < N then (Xf (π.symm ⟨i, hi⟩)).ncard else 0]
  have hdif : ∑ i : Fin N,
      (if hi : (i : ℕ) < N then (Xf (π.symm ⟨(i : ℕ), hi⟩)).ncard else 0)
        = ∑ i : Fin N, (Xf (π.symm i)).ncard :=
    Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt, Fin.eta]
  rw [hdif]
  exact Fintype.sum_equiv π.symm (fun i => (Xf (π.symm i)).ncard)
    (fun u => (Xf u).ncard) (fun _ => rfl)

/-! ## §2 The budget's three figures -/

/-- **The cluster mass** `Σ_u |X_u|` — GKS's own aggregate
(tex:1509-1513), and the figure both halves of the sweep are linear
in: the log is exactly this many cells, the counting sorts move
exactly this many entries, and the deletions cost at most this many
turns (`curDeg_at_deletion_le_cluster`). -/
noncomputable def clusterMass (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) : ℕ :=
  ∑ u : Fin A.N, (cluster S A π u).ncard

open Classical in
/-- **The BFS's edge work**, in GKS's currency: `Σ_u Σ_{w ∈ X_u}
d_<(w)`. By `sum_induced_deg_le_two_sum_dlt` (§5) this bounds — up to
the factor `2` a budget function absorbs — the number of adjacency
cells the frontier BFS at `u` reads, provided it expands only the
vertices at distance `< 2R` (Finding 2). -/
noncomputable def peelEdgeWork (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) : ℕ :=
  ∑ u : Fin A.N, ∑ w ∈ Finset.univ.filter (fun w => w ∈ cluster S A π u),
    Impl.dlt A.G π w

/-- **The budget shape**: affine in the three figures. The two
residuals of §3 are stated at this shape with the constants left to
their dischargers — a program not yet written cannot honestly pin
them — but the *shape* is pinned, and it is the shape §5 proves closes
inside §7's envelope. A budget function of the discharger's free choice
would have been no budget at all. -/
noncomputable def peelK (a b c : ℕ) (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) : ℕ :=
  a * A.N + b * clusterMass S A π + c * peelEdgeWork S A π

/-- Two affine budgets in sequence are one affine budget: the peel's
own is the sweep's plus the grouping's. -/
theorem peelK_add (a b c a' b' c' : ℕ) (S : Setup L) {Λ : ℕ}
    (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) :
    peelK a b c S A π + peelK a' b' c' S A π
      = peelK (a + a') (b + b') (c + c') S A π := by
  simp only [peelK]
  ring

/-! ## §3 The two named residuals -/

/-- **Named residual (4-i): the sweep** — per admissible level arena
at the word bound of every admissible input, from `CovPeelIn`'s exact
precondition, run GKS's ascending peel: per centre one frontier-queue
BFS at radius `2R` in the current structure, the first-hit `ctr` marks
(`centre_eq_of_hit_first`), the cluster row appended to the log, then
the centre's deletion (`AdjDeleteInW`'s account, `54·d + 5` in the
*current* degree). It leaves the arena intact, `CtrArr` at
`Driver.centre`, the order region, the log at `Driver.cluster`, the
`co` allocation and the grouping pass's scratch.

Budget `peelK asw bsw csw` (§2). The frontier is `Lax13Proofs`'
`Lib.Queue` (`push`/`front`/`advance` under the `drain` loop); the
adjacency reads are the live prefixes of `DelAdjSt`, and the deletion
is the landed `delAdjCom` at **`AdjDeleteInW`** — not the landed
`AdjDeleteIn`, which `not_adjDeleteIn` refutes for every `B`, program
and budget. The BFS must expand only the
vertices at distance `< 2R` and must clear its visited marks by
walking its own reached list, never by a carrier pass (Finding 2). -/
def PeelSweepIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od lo lm : ℕ → String) (Spl Sgr : ℕ → Env → Prop)
    (swC : ℕ → Com) (asw bsw csw : ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          RankArr (ra j) ((ord A.N A.G).order) σ ∧
          OrdArr (od j) ((ord A.N A.G).order) σ ∧
          DelAdjSt (ao j) (aj j) (dg j) (mt j) A.G ∅ σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Spl j σ)
        (swC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          CtrArr (ca j) (centre (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ' ∧
          OrdArr (od j) ((ord A.N A.G).order) σ' ∧
          ClusterLog (lo j) (lm j) ((ord A.N A.G).order)
            (cluster (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) σ' ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Sgr j σ')
        (peelK asw bsw csw (Headline.headlineSetup C hC φ) A
          ((ord A.N A.G).order))

/-- **Named residual (4-ii): the grouping** — from the peel-order log
and the order region, deliver `ClusterCsr`: offsets anchored in
**carrier** order, rows in **ascending vertex** order
(`Impl.restrictEmb`'s enumeration, the restrict stage's
`ClusterList`). The route is two stable counting sorts over the log —
by member, then by centre (`od[i]` names the centre of log row `i`) —
each a carrier scan plus a pass over the mass, so the pass is
`O(N + mass)` and never touches the carrier once per centre
(Finding 1). The arena and the assignment region pass through
untouched.

Budget `peelK agr bgr 0` (§2): no edge term — the grouping never
reads the graph. `ClusterLog.total` is the fact that both sorts move
exactly `mass` entries, and `Impl.restrictEmb` is `Driver.setEquiv`,
which is `Finset.orderIsoOfFin` — the ascending enumeration, checked,
so the ascending-row demand is what the second (stable) sort
delivers. -/
def PeelGroupIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (od lo lm : ℕ → String) (Sgr : ℕ → Env → Prop)
    (grC : ℕ → Com) (agr bgr : ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          CtrArr (ca j) (centre (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ ∧
          OrdArr (od j) ((ord A.N A.G).order) σ ∧
          ClusterLog (lo j) (lm j) ((ord A.N A.G).order)
            (cluster (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) σ ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Sgr j σ)
        (grC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          CtrArr (ca j) (centre (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ' ∧
          ClusterCsr (co j) (cm j) (cluster (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ')
        (peelK agr bgr 0 (Headline.headlineSetup C hC φ) A
          ((ord A.N A.G).order))

/-! ## §4 The glue: the verbatim residual from the two passes -/

open Classical in
/-- **F6c12 residual 4, reduced to its two passes**: `CovPeelIn` holds
— verbatim — of the sequenced program `swC j ; grC j` at the summed
budget, from the two named residuals. The composition is `Spec.seq`:
the sweep's postcondition *is* the grouping's precondition (the same
six conjuncts in the same order), and the grouping's postcondition is
`CoverStageSpec`'s. -/
theorem covPeelIn_of_sweep_group (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od lo lm : ℕ → String) (Spl Sgr : ℕ → Env → Prop)
    (swC grC : ℕ → Com) (asw bsw csw agr bgr : ℕ)
    (hsw : PeelSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
      ao aj dg mt od lo lm Spl Sgr swC asw bsw csw)
    (hgr : PeelGroupIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm
      od lo lm Sgr grC agr bgr) :
    CovPeelIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra
      ao aj dg mt od Spl
      (fun j => .seq (swC j) (grC j))
      (fun _ A => peelK (asw + agr) (bsw + bgr) csw
        (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) := by
  intro x hx j hj A hAdm hbot
  refine (Spec.seq (hsw x hx j hj A hAdm hbot)
    (hgr x hx j hj A hAdm hbot) ?_ ?_).mono ?_
  · -- the sweep lands in the grouping's precondition
    rintro σ σ' - ⟨hA', hctr, hod', hlog, hco', hSgr⟩
    exact ⟨hA', hctr, hod', hlog, hco', hSgr⟩
  · -- the grouping's postcondition is the peel's
    rintro σ σ' σ'' - - hq
    exact hq
  · -- the two affine budgets sum to one
    rw [peelK_add]
    simp

/-! ## §5 The cost envelope

The reason this leaf exists. §7 charges the whole cover routine at
`a·N^{1+2δ}` (`algorithm-v2.md` §7, line 798), which is the only place
`δ` enters the design; the sweep is the routine that spends it. -/

/-- Counting a set of vertices as a `Finset` of the carrier. -/
theorem ncard_eq_card_univ_filter {N : ℕ} (s : Set (Fin N))
    [DecidablePred (· ∈ s)] :
    s.ncard = (Finset.univ.filter (fun z => z ∈ s)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

open Classical in
/-- **The BFS's edge budget is GKS's `d_<` sum** (tex:1488-1491: "we
can count the edges of `G'` by counting the sum of `d_<(v)` over all
`v ∈ V(G')`"), formalized for an arbitrary subgraph `H ≤ G` and an
arbitrary vertex set `s`: the number of `H`-edges with both endpoints
in `s`, counted from both ends, is at most `2·Σ_{v ∈ s} d_<(v)` —
each such edge is charged once, in the `N_<`-list of its `π`-later
endpoint.

This is what prices the frontier BFS at `u` by `peelEdgeWork`'s
summand: with `H` the current (peeled) graph and `s = X_u`, the cells
the BFS reads are exactly the live rows of the vertices it expands,
and if it expands only the vertices at distance `< 2R` then every cell
read is an `H`-edge inside `X_u` (Finding 2). -/
theorem sum_induced_deg_le_two_sum_dlt {N : ℕ} {G H : SimpleGraph (Fin N)}
    (hHG : H ≤ G) (π : Equiv.Perm (Fin N)) (s : Finset (Fin N)) :
    ∑ v ∈ s, (s.filter (fun z => H.Adj v z)).card
      ≤ 2 * ∑ v ∈ s, Impl.dlt G π v := by
  classical
  -- split each row at the `π`-position of its far endpoint
  have hsplit : ∀ v ∈ s, (s.filter (fun z => H.Adj v z)).card ≤
      (s.filter (fun z => H.Adj v z ∧ π z < π v)).card
        + (s.filter (fun z => H.Adj v z ∧ π v < π z)).card := by
    intro v _
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases hadj : H.Adj v z
    · have hne : π z ≠ π v := fun hc => (H.ne_of_adj hadj) (π.injective hc).symm
      rcases lt_or_gt_of_ne hne with h1 | h1
      · simp [hadj, h1, not_lt.mpr (le_of_lt h1)]
      · simp [hadj, h1, not_lt.mpr (le_of_lt h1)]
    · simp [hadj]
  -- the earlier half is the `N_<`-list of the row's own vertex
  have hA : ∑ v ∈ s, (s.filter (fun z => H.Adj v z ∧ π z < π v)).card
      ≤ ∑ v ∈ s, Impl.dlt G π v := by
    refine Finset.sum_le_sum fun v _ => Finset.card_le_card fun z hz => ?_
    obtain ⟨-, hadj, hlt⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_neighborFinset _ _ _ |>.mpr (hHG hadj), hlt⟩
  -- the later half is the `N_<`-list of the far endpoint, after the swap
  have hB : ∑ v ∈ s, (s.filter (fun z => H.Adj v z ∧ π v < π z)).card
      ≤ ∑ v ∈ s, Impl.dlt G π v := by
    have hswap : ∑ v ∈ s, (s.filter (fun z => H.Adj v z ∧ π v < π z)).card
        = ∑ z ∈ s, (s.filter (fun v => H.Adj v z ∧ π v < π z)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    refine Finset.sum_le_sum fun z _ => Finset.card_le_card fun v hv => ?_
    obtain ⟨-, hadj, hlt⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_neighborFinset _ _ _ |>.mpr (hHG hadj).symm, hlt⟩
  calc ∑ v ∈ s, (s.filter (fun z => H.Adj v z)).card
      ≤ ∑ v ∈ s, ((s.filter (fun z => H.Adj v z ∧ π z < π v)).card
          + (s.filter (fun z => H.Adj v z ∧ π v < π z)).card) :=
        Finset.sum_le_sum hsplit
    _ = ∑ v ∈ s, (s.filter (fun z => H.Adj v z ∧ π z < π v)).card
        + ∑ v ∈ s, (s.filter (fun z => H.Adj v z ∧ π v < π z)).card :=
        Finset.sum_add_distrib
    _ ≤ (∑ v ∈ s, Impl.dlt G π v) + ∑ v ∈ s, Impl.dlt G π v := add_le_add hA hB
    _ = 2 * ∑ v ∈ s, Impl.dlt G π v := by ring

variable {Λ : ℕ}

open Classical in
/-- **The sweep's whole BFS cell count is `2·peelEdgeWork`** — §5's
bound assembled over the sweep. For each centre `u`, `s` its cluster
and `H` the graph at `u`'s own peel state (`cluster_eq_ball_peelSet`:
that graph's `2R`-ball at `u` *is* the cluster), the cells the BFS
reads are the live rows of the vertices it expands, and each is an
`H`-edge inside the cluster provided the last level is not expanded
(Finding 2). Summing the §5 bound gives the sweep's total in the
figure `peelEdgeWork` names. -/
theorem sum_bfsCells_le (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) :
    ∑ u : Fin A.N,
        ∑ v ∈ Finset.univ.filter (fun z => z ∈ cluster S A π u),
          ((Finset.univ.filter (fun z => z ∈ cluster S A π u)).filter
            (fun z => (deleteVerts A.G (peelSet π (π u : ℕ))).Adj v z)).card
      ≤ 2 * peelEdgeWork S A π := by
  rw [peelEdgeWork, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  exact sum_induced_deg_le_two_sum_dlt
    (Lax3Proofs.WalkDistance.deleteVerts_le A.G _) π _

/-- **The deletions ride inside the mass**: at the moment the sweep
deletes `u` its current degree is at most `|X_u|`
(`curDeg_at_deletion_le_cluster`), so the whole peel — `54·d + 5` a
deletion under `AdjDeleteInW` — costs at most `54·mass + 5·N`, with no
figure of its own. Hazard 4's `1 ≤ S.R` is spent here (`N_>(v) ⊆ X_v`
charges a length-`1` walk against the radius). -/
theorem sum_curDeg_le_clusterMass (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (hr : 1 ≤ S.R) :
    ∑ u : Fin A.N, ((deleteVerts A.G (peelSet π (π u : ℕ))).neighborSet u).ncard
      ≤ clusterMass S A π := by
  rw [clusterMass]
  exact Finset.sum_le_sum fun u _ => curDeg_at_deletion_le_cluster S A π hr u

/-- Every cluster holds its own centre, so the carrier term never
exceeds the mass term: an affine budget's `a·N` is not a fourth
figure. -/
theorem card_le_clusterMass (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) : A.N ≤ clusterMass S A π := by
  rw [clusterMass]
  calc A.N = ∑ _u : Fin A.N, 1 := by simp
    _ ≤ ∑ u : Fin A.N, (cluster S A π u).ncard :=
        Finset.sum_le_sum fun u _ =>
          (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, self_mem_cluster S A π u⟩

/-- **The mass is GKS's `Σ_v |X_v| ≤ n·n^δ`** — the landed
`Impl.sum_sweepCluster_ncard_le` at the driver's cluster family. -/
theorem clusterMass_le (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {D : ℕ}
    (hD : ∀ x, (wreach A.G π (2 * S.R) x).ncard ≤ D) :
    clusterMass S A π ≤ A.N * D := by
  rw [clusterMass]
  calc ∑ u : Fin A.N, (cluster S A π u).ncard
      = ∑ u : Fin A.N, (Impl.sweepCluster A.G π S.R u).ncard :=
        Finset.sum_congr rfl fun u _ => by rw [Impl.sweepCluster_eq_cluster]
    _ ≤ A.N * D := Impl.sum_sweepCluster_ncard_le hD

open Classical in
/-- **The edge work is the mass times the degree bound**: `d_<(w) ≤ D`
for every `w` (`Impl.dlt_le_of_wreach`, where `1 ≤ 2R` is spent), so
each centre's summand is at most `|X_u|·D` — GKS's own per-BFS
estimate. -/
theorem peelEdgeWork_le_mass_mul (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {D : ℕ} (hr : 1 ≤ S.R)
    (hD : ∀ x, (wreach A.G π (2 * S.R) x).ncard ≤ D) :
    peelEdgeWork S A π ≤ clusterMass S A π * D := by
  have h2r : 1 ≤ 2 * S.R := by omega
  rw [peelEdgeWork, clusterMass, Finset.sum_mul]
  refine Finset.sum_le_sum fun u _ => ?_
  calc ∑ w ∈ Finset.univ.filter (fun w => w ∈ cluster S A π u), Impl.dlt A.G π w
      ≤ (Finset.univ.filter (fun w => w ∈ cluster S A π u)).card * D :=
        Impl.sum_dlt_le h2r hD _
    _ = (cluster S A π u).ncard * D := by
        rw [← ncard_eq_card_univ_filter]

open Classical in
/-- The mass rides inside the landed abstract account (at `1 ≤ D`,
which the cover-degree bound gives since every cluster contains its own
centre). -/
theorem clusterMass_le_sweepCharge (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {D : ℕ} (hD1 : 1 ≤ D) :
    clusterMass S A π ≤ Impl.sweepCharge A.G π S.R D := by
  rw [clusterMass, Impl.sweepCharge]
  refine Finset.sum_le_sum fun u _ => ?_
  have h : (cluster S A π u).ncard = (Impl.sweepCluster A.G π S.R u).ncard := by
    rw [Impl.sweepCluster_eq_cluster]
  rw [h]
  have := Nat.le_mul_of_pos_right (Impl.sweepCluster A.G π S.R u).ncard hD1
  omega

open Classical in
/-- The edge work rides inside the landed abstract account: it is at
most `Σ_u |X_u|·D`, which is `sweepCharge`'s first summand. -/
theorem peelEdgeWork_le_sweepCharge (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {D : ℕ} (hr : 1 ≤ S.R)
    (hD : ∀ x, (wreach A.G π (2 * S.R) x).ncard ≤ D) :
    peelEdgeWork S A π ≤ Impl.sweepCharge A.G π S.R D := by
  refine le_trans (peelEdgeWork_le_mass_mul S A π hr hD) ?_
  rw [clusterMass, Impl.sweepCharge, Finset.sum_mul]
  refine Finset.sum_le_sum fun u _ => ?_
  have h : (cluster S A π u).ncard = (Impl.sweepCluster A.G π S.R u).ncard := by
    rw [Impl.sweepCluster_eq_cluster]
  rw [h]
  omega

open Classical in
/-- **The envelope** (deliverable): every budget affine in the three
figures of §2 closes at `O(N·D²)` — `a·N + b·(N·D) + c·(N·D·D)` —
under the cover-degree hypothesis `∀ x, |wreach_{2R}(x)| ≤ D`. At
`D = ⌈c_D·N^δ⌉` that is §7's `a·N^{1+2δ}`, and it is the *whole* of
the sweep: no term is a carrier pass per centre.

`1 ≤ S.R` is Hazard 4 — GKS assume it silently and it is false at
`R = 0`; the design's `R ≥ 1` supplies it. -/
theorem peelBudget_le (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {D : ℕ} (a b c : ℕ) (hr : 1 ≤ S.R)
    (hD : ∀ x, (wreach A.G π (2 * S.R) x).ncard ≤ D) :
    peelK a b c S A π ≤ a * A.N + b * (A.N * D) + c * (A.N * D * D) := by
  rw [peelK]
  have hm : clusterMass S A π ≤ A.N * D := clusterMass_le S A π hD
  have he : peelEdgeWork S A π ≤ A.N * D * D :=
    le_trans (peelEdgeWork_le_mass_mul S A π hr hD)
      (Nat.mul_le_mul_right D hm)
  have h1 : b * clusterMass S A π ≤ b * (A.N * D) := Nat.mul_le_mul_left b hm
  have h2 : c * peelEdgeWork S A π ≤ c * (A.N * D * D) := Nat.mul_le_mul_left c he
  omega

open Classical in
/-- **The envelope against the landed abstract account**: every budget
affine in the three figures is at most `a·N + (b+c)·sweepCharge`, so
the machine's own account never exceeds GKS's own by more than a
constant factor and a linear term. With `Impl.sweepCharge_le` this is
again `O(N·D²)`. -/
theorem peelBudget_le_sweepCharge (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {D : ℕ} (a b c : ℕ) (hr : 1 ≤ S.R)
    (hD1 : 1 ≤ D) (hD : ∀ x, (wreach A.G π (2 * S.R) x).ncard ≤ D) :
    peelK a b c S A π
      ≤ a * A.N + (b + c) * Impl.sweepCharge A.G π S.R D := by
  rw [peelK]
  have hm : clusterMass S A π ≤ Impl.sweepCharge A.G π S.R D :=
    clusterMass_le_sweepCharge S A π hD1
  have he : peelEdgeWork S A π ≤ Impl.sweepCharge A.G π S.R D :=
    peelEdgeWork_le_sweepCharge S A π hr hD
  have h1 : b * clusterMass S A π ≤ b * Impl.sweepCharge A.G π S.R D :=
    Nat.mul_le_mul_left b hm
  have h2 : c * peelEdgeWork S A π ≤ c * Impl.sweepCharge A.G π S.R D :=
    Nat.mul_le_mul_left c he
  have h3 : (b + c) * Impl.sweepCharge A.G π S.R D
      = b * Impl.sweepCharge A.G π S.R D + c * Impl.sweepCharge A.G π S.R D := by
    ring
  omega

/-! ## §6 Control: the seam is satisfiable

Not mathematics; a check that `ClusterLog`'s conjunction — soundness,
completeness and the running offsets together — is realizable, so the
split of §3 is not a vacuous one. The smallest instance with two
rows: two singleton clusters at the identity ordering. -/

section Control

/-- The control state: offsets `[0,1,2]`, rows `[0]` and `[1]`. -/
private def logEnv : Env :=
  { vars := fun _ => 0
    arrs := fun a =>
      if a = "c.lo" then [0, 1, 2]
      else if a = "c.lm" then [0, 1]
      else []
    inp := []
    out := [] }

/-- **The log is satisfiable**: the two singleton clusters of the
identity ordering, appended in peel order. -/
private theorem ctrl_clusterLog :
    ClusterLog "c.lo" "c.lm" (Equiv.refl (Fin 2)) (fun u => {u}) logEnv := by
  have hlo : logEnv.arrs "c.lo" = [0, 1, 2] := rfl
  have hlm : logEnv.arrs "c.lm" = [0, 1] := rfl
  refine ⟨id, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlo]; simp
  · intro i hi
    rw [hlo]
    interval_cases i <;> rfl
  · intro i
    simp
  · rw [hlm]; simp
  · intro i t ht
    simp only [Set.ncard_singleton] at ht
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    refine ⟨(Equiv.refl (Fin 2)).symm i, rfl, ?_⟩
    rw [hlm]
    fin_cases i <;> rfl
  · intro i z hz
    have hz' : z = (Equiv.refl (Fin 2)).symm i := hz
    refine ⟨0, by simp, ?_⟩
    rw [hlm, hz']
    fin_cases i <;> rfl

end Control

/-! The leaf's axiom profile. The cost envelope of §5 uses nothing but
the three of the ambient logic; the glue's statement quotes
`Headline.headlineSetup`, so — exactly like the landed
`covSweepIn_of_build_peel` it feeds — it additionally carries Lax12's
endorsed `uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms peelBudget_le

#print axioms peelBudget_le_sweepCharge

#print axioms covPeelIn_of_sweep_group

end Lax3Proofs.Prog
