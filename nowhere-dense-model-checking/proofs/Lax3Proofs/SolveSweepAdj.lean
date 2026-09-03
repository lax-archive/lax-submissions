import Lax3Proofs.SolveCovStep

/-!
# F6c11b (part 1) — the deletable adjacency region

`SolveCovStep`'s Finding 3 pins the route for the peeling sweep
(`CovSweepIn`): GKS's own frontier-queue BFS over a **mutable adjacency
structure with peeling** (tex:1459-1520) — every full-pass-per-round
BFS variant busts the `2·D²·N` budget, because its per-round cost is
the whole slot array rather than the frontier's own edges. This file
owns the new machinery that route needs: the **deletable adjacency
region**, its invariant against `deleteVerts`, and the named contracts
of its two mutating passes. The composition of the sweep from these
contracts is `SolveSweepStep.lean`; the machine programs themselves are
the residuals named there and here.

## The representation: compacting swap-delete rows

Four arrays over the fixed CSR slot space of the *base* graph `G`
(`offF` the degree-sum offsets, so row `v` owns slots
`[offF v, offF (v+1))`):

* `ao` — the offsets, `ao[i] = offF i` (never mutated; a discharger may
  alias it to the arena's own CSR offset region, which no sweep pass
  writes);
* `aj` — the adjacency slots: the **live prefix** `aj[offF v .. offF v
  + dg[v])` of row `v` enumerates exactly the current neighbours of
  `v`, i.e. its neighbours in `deleteVerts G S`;
* `dg` — the live row lengths: `dg[v]` is `v`'s current degree, and `0`
  for a deleted vertex;
* `mt` — the mate pointers: the slot holding the copy `v → w` of a live
  edge points at the slot holding the copy `w → v`, and back.

**Why this shape and not doubly-linked slot lists**: iteration over the
current neighbours of `w` is a *contiguous prefix read* of `dg[w]`
cells — exactly the unit the BFS budget charges (`Impl.sweepCharge`'s
`|X_v| · D` summand prices the queue BFS at its current-edge budget) —
and deletion is `O(1)` per removed edge copy: unlink `v` from `w`'s row
by swapping `w`'s last live slot into the vacated one and shrinking
`dg[w]`, with `mt` repaired through the swap. Deleting `v` therefore
costs `O(1 + dg[v])`, which the sweep absorbs (`N_>(v) ⊆ X_v`,
`ImplCover.card_Ngt_le_cluster`) — *cheaper* than GKS's own
`Σ_{w ∈ N_>(v)} d_<(w)` account for searching linked `N_<`-lists, so
the landed `sweepCharge` bound stays an upper envelope for this
machine.

## The invariant (`DelAdjSt`)

Stated against the *abstract* deleted set `S`: degrees are the
`deleteVerts G S` degrees, every live slot holds a current neighbour
with a consistent mate, and every current neighbour appears in the live
prefix. Soundness + completeness + the degree clause force the live
prefix to enumerate the current neighbourhood without duplicates
(`DelAdjSt.slot_injOn`, by pigeonhole — no separate no-dup clause is
carried through the mutating passes).

## What the peel loop's invariant consumes (§4)

The sweep processes vertices in ascending `π`-order, deleting as it
goes, so the deleted set after `i` steps is the rank prefix
`peelSet π i` (§1). §4 closes the loop against the landed abstract
sweep: the cluster of `u` is the `2R`-ball at `u`'s own peel state
(`cluster_eq_ball_peelSet`, via `Impl.sweepCluster_eq_peeledBall`), and
the first `π`-ascending centre whose `R`-ball reaches `v` *is*
`Driver.centre` (`centre_eq_of_hit_first`, via `ctr`'s two
characterising properties) — the "first assignment wins" discipline of
GKS's Remark (tex:1522-1538), in the form a marking pass's invariant
discharges.

## The named contracts (§3)

`AdjBuildIn` (build the region from a `GraphCsr`, empty deleted set)
and `AdjDeleteIn` (delete the vertex named by a scalar, at cost affine
in its *current* degree) are the insert/delete Specs of the structure;
iteration needs no command of its own — it is the invariant's
completeness clause read over the live prefix, priced by the degree
clause. Both are contracts for the machine wave; nothing here proves a
program. `Lib.Queue` (Lax67) supplies the BFS frontier the peel pass
composes next to these.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax3.ColoredGraphs (ball)
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.SplitterBasics (deleteVerts_adj)
open Lax3Proofs.Driver

/-! ## §1 The peel prefix -/

/-- The deleted set after `i` steps of the `π`-ascending peel: the
vertices of rank `< i`. -/
def peelSet {N : ℕ} (π : Equiv.Perm (Fin N)) (i : ℕ) : Set (Fin N) :=
  {x | (π x : ℕ) < i}

@[simp] theorem peelSet_zero {N : ℕ} (π : Equiv.Perm (Fin N)) :
    peelSet π 0 = ∅ := by
  ext x; simp [peelSet]

/-- One peel step: the prefix grows by the vertex of rank `i`. -/
theorem peelSet_succ {N : ℕ} (π : Equiv.Perm (Fin N)) {i : ℕ} (hi : i < N) :
    peelSet π (i + 1) = peelSet π i ∪ {π.symm ⟨i, hi⟩} := by
  ext x
  simp only [peelSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
    Equiv.eq_symm_apply]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Fin.ext h)
  · rintro (h | h)
    · exact Nat.lt_succ_of_lt h
    · rw [h]
      exact Nat.lt_succ_self i

/-- The prefix at `v`'s own rank is the strictly-`π`-earlier set — the
peeled set of the abstract sweep (`ImplCover` §2). -/
theorem peelSet_rank {N : ℕ} (π : Equiv.Perm (Fin N)) (v : Fin N) :
    peelSet π (π v : ℕ) = {x | π x < π v} := by
  ext x
  simp only [peelSet, Set.mem_setOf_eq, Fin.lt_def]

/-- After all `N` steps everything is deleted. -/
theorem peelSet_last {N : ℕ} (π : Equiv.Perm (Fin N)) :
    peelSet π N = Set.univ := by
  ext x
  simp [peelSet]

/-! ## §2 The two regions -/

/-- **The order region**: entry `i` holds the vertex of rank `i` — the
inverse of `RankArr`, the form the ascending peel reads (`ascList` as
an array: `Impl.ascList_getElem`). Windowed convention, like every
chain region. -/
def OrdArr (od : String) {N : ℕ} (π : Equiv.Perm (Fin N)) (σ : Env) : Prop :=
  N ≤ (σ.arrs od).length ∧
    ∀ i : Fin N, (σ.arrs od).getD (i : ℕ) 0 = ((π.symm i : Fin N) : ℕ)

/-- **The deletable adjacency region** (module docstring): offsets of
the *base* graph `G` in `ao`; live row prefixes in `aj` of lengths
`dg`, enumerating exactly the `deleteVerts G S` neighbourhoods; mate
pointers in `mt`, involutive across live slots. Deleted vertices have
live length `0`.

The clauses, in order: the offset function (anchored, degree-sum
steps), the offset region, the two slot allocations, the degree
region's allocation, the dead rows, the degree clause, per-slot
soundness with a consistent mate, and completeness. Duplicate-freeness
of a live prefix is *derived* (`slot_injOn`), not carried. -/
def DelAdjSt (ao aj dg mt : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Set (Fin N)) (σ : Env) : Prop :=
  ∃ offF : ℕ → ℕ,
    offF 0 = 0 ∧
    (∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) ∧
    N + 1 ≤ (σ.arrs ao).length ∧
    (∀ i, i ≤ N → (σ.arrs ao).getD i 0 = offF i) ∧
    offF N ≤ (σ.arrs aj).length ∧
    offF N ≤ (σ.arrs mt).length ∧
    N ≤ (σ.arrs dg).length ∧
    (∀ v : Fin N, v ∈ S → (σ.arrs dg).getD (v : ℕ) 0 = 0) ∧
    (∀ v : Fin N, v ∉ S →
      (σ.arrs dg).getD (v : ℕ) 0 = ((deleteVerts G S).neighborSet v).ncard) ∧
    (∀ v : Fin N, v ∉ S → ∀ t : ℕ, t < (σ.arrs dg).getD (v : ℕ) 0 →
      ∃ w : Fin N, (deleteVerts G S).Adj v w ∧
        (σ.arrs aj).getD (offF (v : ℕ) + t) 0 = (w : ℕ) ∧
        ∃ s : ℕ, s < (σ.arrs dg).getD (w : ℕ) 0 ∧
          (σ.arrs mt).getD (offF (v : ℕ) + t) 0 = offF (w : ℕ) + s ∧
          (σ.arrs aj).getD (offF (w : ℕ) + s) 0 = (v : ℕ) ∧
          (σ.arrs mt).getD (offF (w : ℕ) + s) 0 = offF (v : ℕ) + t) ∧
    (∀ v : Fin N, v ∉ S → ∀ w : Fin N, (deleteVerts G S).Adj v w →
      ∃ t : ℕ, t < (σ.arrs dg).getD (v : ℕ) 0 ∧
        (σ.arrs aj).getD (offF (v : ℕ) + t) 0 = (w : ℕ))

/-- The region reads exactly four arrays: it transports along agreement
on them (the frame fact every composed pass applies). -/
theorem DelAdjSt.of_eq {ao aj dg mt : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {S : Set (Fin N)} {σ σ' : Env}
    (h : DelAdjSt ao aj dg mt G S σ)
    (hao : σ'.arrs ao = σ.arrs ao) (haj : σ'.arrs aj = σ.arrs aj)
    (hdg : σ'.arrs dg = σ.arrs dg) (hmt : σ'.arrs mt = σ.arrs mt) :
    DelAdjSt ao aj dg mt G S σ' := by
  rw [DelAdjSt, hao, haj, hdg, hmt]
  exact h

/-- Deletion only shrinks a neighbourhood: the current degree is at
most the base degree — the slack every slot-range side condition
spends. -/
theorem ncard_neighborSet_deleteVerts_le {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Set (Fin N)) (v : Fin N) :
    ((deleteVerts G S).neighborSet v).ncard ≤ (G.neighborSet v).ncard :=
  Set.ncard_le_ncard
    (fun _ hw => (deleteVerts_le G S) hw) (Set.toFinite _)

/-- The anchor and the steps determine the offset function on
`[0, N]` — the alignment fact a consumer of two `DelAdjSt`s (or of a
`DelAdjSt` next to the arena's own CSR at exact degrees) applies to
identify their existentials. -/
theorem offF_unique {N : ℕ} {G : SimpleGraph (Fin N)} {offF offF' : ℕ → ℕ}
    (h0 : offF 0 = 0) (h0' : offF' 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    (hstep' : ∀ v : Fin N, offF' ((v : ℕ) + 1) = offF' (v : ℕ) + (G.neighborSet v).ncard) :
    ∀ i, i ≤ N → offF i = offF' i := by
  intro i
  induction i with
  | zero => intro _; rw [h0, h0']
  | succ k ih =>
      intro hk
      have hkN : k < N := hk
      rw [hstep ⟨k, hkN⟩, hstep' ⟨k, hkN⟩, ih (by omega)]

/-- The offset function is monotone below `N` (the row extents tile). -/
theorem offF_mono {N : ℕ} {G : SimpleGraph (Fin N)} {offF : ℕ → ℕ}
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    ∀ j, j ≤ N → ∀ i, i ≤ j → offF i ≤ offF j := by
  intro j
  induction j with
  | zero =>
      intro _ i hi
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact le_rfl
  | succ k ih =>
      intro hk i hi
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exact le_rfl
      · refine le_trans (ih (by omega) i (by omega)) ?_
        have hkN : k < N := by omega
        have h' : offF (k + 1) = offF k + (G.neighborSet ⟨k, hkN⟩).ncard :=
          hstep ⟨k, hkN⟩
        rw [h']
        omega

/-- A live slot of row `v` lies inside the slot space: the range side
condition of every load and store on the live prefix. -/
theorem slot_lt {N : ℕ} {G : SimpleGraph (Fin N)} {S : Set (Fin N)}
    {σ : Env} {dg : String} {offF : ℕ → ℕ}
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    (hdeg : ∀ v : Fin N, v ∉ S →
      (σ.arrs dg).getD (v : ℕ) 0 = ((deleteVerts G S).neighborSet v).ncard)
    {v : Fin N} (hv : v ∉ S) {t : ℕ} (ht : t < (σ.arrs dg).getD (v : ℕ) 0) :
    offF (v : ℕ) + t < offF N := by
  have hlt : offF (v : ℕ) + t < offF ((v : ℕ) + 1) := by
    rw [hstep v]
    have hle := ncard_neighborSet_deleteVerts_le G S v
    rw [hdeg v hv] at ht
    omega
  exact lt_of_lt_of_le hlt (offF_mono hstep N le_rfl ((v : ℕ) + 1) v.isLt)

/-- **The live prefix has no duplicates** (pigeonhole): the slot map of
a live row is injective on `[0, dg v)` — completeness makes the current
neighbourhood's values a subset of the image, and the degree clause
equates the cardinalities. What an iterating consumer reads is
therefore an *enumeration* of the current neighbourhood. -/
theorem DelAdjSt.slot_injOn {ao aj dg mt : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {S : Set (Fin N)} {σ : Env}
    (h : DelAdjSt ao aj dg mt G S σ) {v : Fin N} (hv : v ∉ S) :
    ∃ offF : ℕ → ℕ,
      offF 0 = 0 ∧
      (∀ u : Fin N, offF ((u : ℕ) + 1) = offF (u : ℕ) + (G.neighborSet u).ncard) ∧
      Set.InjOn (fun t => (σ.arrs aj).getD (offF (v : ℕ) + t) 0)
        {t | t < (σ.arrs dg).getD (v : ℕ) 0} := by
  obtain ⟨offF, h0, hstep, -, -, -, -, -, -, hdeg, -, hcomp⟩ := h
  refine ⟨offF, h0, hstep, ?_⟩
  have hdv := hdeg v hv
  -- the current neighbourhood's values sit inside the image of the
  -- live prefix
  have h1 : (Fin.val '' ((deleteVerts G S).neighborSet v)) ⊆
      ↑((Finset.range ((σ.arrs dg).getD (v : ℕ) 0)).image
        (fun t => (σ.arrs aj).getD (offF (v : ℕ) + t) 0)) := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨t, ht, hval⟩ := hcomp v hv w hw
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, hval⟩)
  -- so the image has full cardinality
  have h2 : (σ.arrs dg).getD (v : ℕ) 0 ≤
      ((Finset.range ((σ.arrs dg).getD (v : ℕ) 0)).image
        (fun t => (σ.arrs aj).getD (offF (v : ℕ) + t) 0)).card :=
    calc (σ.arrs dg).getD (v : ℕ) 0
        = ((deleteVerts G S).neighborSet v).ncard := hdv
      _ = (Fin.val '' ((deleteVerts G S).neighborSet v)).ncard :=
          (Set.ncard_image_of_injective _ Fin.val_injective).symm
      _ ≤ _ := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((Finset.range ((σ.arrs dg).getD (v : ℕ) 0)).image
      (fun t => (σ.arrs aj).getD (offF (v : ℕ) + t) 0)).card =
        (Finset.range ((σ.arrs dg).getD (v : ℕ) 0)).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_range]; exact h2)
  have hinj := Finset.injOn_of_card_image_eq h3
  have hset : ({t | t < (σ.arrs dg).getD (v : ℕ) 0} : Set ℕ) =
      ↑(Finset.range ((σ.arrs dg).getD (v : ℕ) 0)) := by
    rw [Finset.coe_range]
    rfl
  rw [hset]
  exact hinj

/-! ## §3 The named contracts of the two mutating passes -/

/-- **The build contract**: from a `GraphCsr` of the base graph and raw
allocations for the four regions, establish the region at the empty
deleted set, preserving the CSR. `kb` is the pass's budget at
`(N, ns)` — one scan of the carrier and one of the slot space (the
mate pass is the standard counting trick), `O(N + ns)`. The insert
Spec of the structure: the only insertion the sweep ever does is this
bulk one. -/
def AdjBuildIn (B : ℕ) (o t ao aj dg mt : String) (bldC : Com)
    (kb : ℕ → ℕ → ℕ) : Prop :=
  ∀ {N : ℕ} (G : SimpleGraph (Fin N)) (ns : ℕ),
    Spec B
      (fun σ => GraphCsr o t G ns σ ∧
        N + 1 ≤ (σ.arrs ao).length ∧ ns ≤ (σ.arrs aj).length ∧
        N ≤ (σ.arrs dg).length ∧ ns ≤ (σ.arrs mt).length)
      bldC
      (fun _ σ' => GraphCsr o t G ns σ' ∧ DelAdjSt ao aj dg mt G ∅ σ')
      (kb N ns)

/-- **The delete contract**: with the region at `S` and the live vertex
`v` named in the scalar `vx`, remove `v` — the region moves to
`S ∪ {v}` — at a cost affine in `v`'s *current* degree (the swap-delete
account: `O(1)` per removed edge copy). Iteration needs no contract of
its own: reading the live prefix is the invariant's completeness
clause, priced by the degree clause. -/
def AdjDeleteIn (B : ℕ) (ao aj dg mt vx : String) (delC : Com)
    (kd : ℕ → ℕ) : Prop :=
  ∀ {N : ℕ} (G : SimpleGraph (Fin N)) (S : Set (Fin N)) (v : Fin N),
    v ∉ S →
    Spec B
      (fun σ => DelAdjSt ao aj dg mt G S σ ∧ σ.vars vx = (v : ℕ))
      delC
      (fun _ σ' => DelAdjSt ao aj dg mt G (S ∪ {v}) σ')
      (kd (((deleteVerts G S).neighborSet v).ncard))

/-! ## §4 What the peel loop's invariant consumes -/

variable {L n₀ : ℕ}

/-- **The cluster at the peel state** — the abstract identity the
emitted row is checked against: the cluster of `u` is the `2R`-ball of
`u` in the graph with `u`'s own rank prefix deleted, which is exactly
the reached set of the BFS the sweep runs at the moment it processes
`u`. `Impl.sweepCluster_eq_peeledBall` at the prefix form. -/
theorem cluster_eq_ball_peelSet (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    cluster S A π u =
      ball (deleteVerts A.G (peelSet π (π u : ℕ))) (2 * S.R) u := by
  rw [← Impl.sweepCluster_eq_cluster S A π u, Impl.sweepCluster_eq_peeledBall,
    peelSet_rank]

/-- **First assignment wins** — GKS's Remark as the marking pass's exit
fact: if the `R`-ball of `u` at `u`'s own peel state reaches `v` and no
`π`-earlier centre's did, then `u` *is* `Driver.centre` of `v`. The
peel loop's `ctr`-invariant ("entry `v` holds the first centre whose
`R`-levels reached `v`, sentinel otherwise") discharges its
postcondition through this. -/
theorem centre_eq_of_hit_first (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {u v : Fin A.N}
    (hu : v ∈ ball (deleteVerts A.G (peelSet π (π u : ℕ))) S.R u)
    (hprev : ∀ u' : Fin A.N, π u' < π u →
      v ∉ ball (deleteVerts A.G (peelSet π (π u' : ℕ))) S.R u') :
    centre S A π v = u := by
  rw [peelSet_rank] at hu
  have hmem : u ∈ wreach A.G π S.R v :=
    Impl.mem_wreach_iff_mem_peeledBall.mpr hu
  -- the centre is the `π`-minimum of the wreach set, and `u` is a member
  have hle : π (centre S A π v) ≤ π u :=
    Lax3Proofs.CoverCentres.ctr_le_of_mem_wreach hmem
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- then the centre itself is an earlier hit
    exfalso
    refine hprev _ hlt ?_
    rw [peelSet_rank]
    exact Impl.mem_wreach_iff_mem_peeledBall.mp
      (Lax3Proofs.CoverCentres.ctr_mem_wreach A.G π S.R v)
  · exact π.injective heq

open Classical in
/-- At the moment the sweep deletes `u`, its current neighbours are
exactly its `π`-later neighbours — GKS's `N_>` (`Impl.Ngt`). -/
theorem neighborSet_deleteVerts_peelSet_self {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (u : Fin N) :
    (deleteVerts G (peelSet π (π u : ℕ))).neighborSet u = ↑(Impl.Ngt G π u) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨hadj, -, hwp⟩ := deleteVerts_adj.mp hw
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Set.mem_toFinset.mpr hadj, ?_⟩)
    have hne : π u ≠ π w := fun hc => G.ne_of_adj hadj (π.injective hc)
    have hwp' : ¬ ((π w : ℕ) < (π u : ℕ)) := hwp
    exact Fin.lt_def.mpr
      (lt_of_le_of_ne (not_lt.mp hwp') fun hc => hne (Fin.ext hc))
  · intro hw
    obtain ⟨hnb, hlt⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    have hadj : G.Adj u w := Set.mem_toFinset.mp hnb
    refine deleteVerts_adj.mpr ⟨hadj, ?_, ?_⟩
    · simp [peelSet]
    · intro hc
      have hc' : (π w : ℕ) < (π u : ℕ) := hc
      have hlt' : (π u : ℕ) < (π w : ℕ) := Fin.lt_def.mp hlt
      omega

/-- **The deletion account closes into the cluster mass**: the current
degree of `u` at its own deletion — `AdjDeleteIn`'s cost argument in
the sweep's peel loop — is at most `u`'s own cluster size, so the
sweep's total deletion cost rides inside `Impl.sweepCharge`'s first
summand (`Σ_v |X_v| · D`, already at `D ≥ 1`). -/
theorem curDeg_at_deletion_le_cluster (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (hr : 1 ≤ S.R) (u : Fin A.N) :
    ((deleteVerts A.G (peelSet π (π u : ℕ))).neighborSet u).ncard ≤
      (cluster S A π u).ncard := by
  classical
  rw [neighborSet_deleteVerts_peelSet_self, Set.ncard_coe_finset,
    ← Impl.sweepCluster_eq_cluster S A π u]
  exact Impl.card_Ngt_le_cluster hr u

/-- The cluster of a live centre is live: no vertex of the emitted ball
is `π`-earlier than its centre (the emitted row never mentions deleted
vertices — the well-formedness fact the row write consumes). -/
theorem not_peeled_of_mem_cluster (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {u w : Fin A.N} (hw : w ∈ cluster S A π u) :
    w ∉ peelSet π (π u : ℕ) := by
  rw [cluster_eq_ball_peelSet] at hw
  obtain ⟨q, -⟩ := mem_ball.mp hw
  intro hwS
  have hu : u ∉ peelSet π (π u : ℕ) := by
    simp [peelSet]
  exact Impl.not_mem_of_mem_support_deleteVerts q hu w q.end_mem_support hwS

/-! ## §5 Control: the invariant is satisfiable

Not mathematics; a check that `DelAdjSt`'s conjunction — the mate
clause in particular — is realizable, so the contracts of §3 are not
vacuously undischargeable. The smallest instance with a real mate:
`K₂`, both edge copies live, each slot the other's mate. -/

section Control

/-- The `K₂` control environment: offsets `[0,1,2]`, both slots live,
mates crossed. -/
private def ctrlEnv : Env :=
  { vars := fun _ => 0
    arrs := fun a =>
      if a = "c.ao" then [0, 1, 2]
      else if a = "c.aj" then [1, 0]
      else if a = "c.dg" then [1, 1]
      else if a = "c.mt" then [1, 0]
      else []
    inp := []
    out := [] }

private theorem ctrl_neighborSet_ncard (v : Fin 2) :
    ((⊤ : SimpleGraph (Fin 2)).neighborSet v).ncard = 1 := by
  fin_cases v
  · show ((⊤ : SimpleGraph (Fin 2)).neighborSet 0).ncard = 1
    have h : (⊤ : SimpleGraph (Fin 2)).neighborSet 0 = {1} := by
      ext w
      fin_cases w <;> simp
    rw [h, Set.ncard_singleton]
  · show ((⊤ : SimpleGraph (Fin 2)).neighborSet 1).ncard = 1
    have h : (⊤ : SimpleGraph (Fin 2)).neighborSet 1 = {0} := by
      ext w
      fin_cases w <;> simp
    rw [h, Set.ncard_singleton]

/-- **The invariant is satisfiable** (with the mate clause exercised on
a real edge): `K₂`'s deletable region at the empty deleted set. -/
private theorem ctrl_delAdjSt :
    DelAdjSt "c.ao" "c.aj" "c.dg" "c.mt" (⊤ : SimpleGraph (Fin 2)) ∅
      ctrlEnv := by
  have harrs_ao : ctrlEnv.arrs "c.ao" = [0, 1, 2] := rfl
  have harrs_aj : ctrlEnv.arrs "c.aj" = [1, 0] := rfl
  have harrs_dg : ctrlEnv.arrs "c.dg" = [1, 1] := rfl
  have harrs_mt : ctrlEnv.arrs "c.mt" = [1, 0] := rfl
  refine ⟨id, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simp [ctrl_neighborSet_ncard v]
  · rw [harrs_ao]; simp
  · intro i hi
    rw [harrs_ao]
    interval_cases i <;> rfl
  · rw [harrs_aj]; simp
  · rw [harrs_mt]; simp
  · rw [harrs_dg]; simp
  · intro v hv
    simp at hv
  · intro v _
    rw [harrs_dg, Impl.deleteVerts_empty, ctrl_neighborSet_ncard v]
    fin_cases v <;> rfl
  · intro v _ t ht
    rw [harrs_dg] at ht
    fin_cases v
    · obtain rfl : t = 0 := by simpa using Nat.lt_one_iff.mp ht
      refine ⟨1, ?_, rfl, 0, ?_, rfl, rfl, rfl⟩
      · rw [Impl.deleteVerts_empty]
        simp
      · rw [harrs_dg]
        simp
    · obtain rfl : t = 0 := by simpa using Nat.lt_one_iff.mp ht
      refine ⟨0, ?_, rfl, 0, ?_, rfl, rfl, rfl⟩
      · rw [Impl.deleteVerts_empty]
        simp
      · rw [harrs_dg]
        simp
  · intro v _ w hw
    rw [Impl.deleteVerts_empty] at hw
    fin_cases v <;> fin_cases w
    · simp at hw
    · exact ⟨0, by rw [harrs_dg]; simp, rfl⟩
    · exact ⟨0, by rw [harrs_dg]; simp, rfl⟩
    · simp at hw

end Control

end Lax3Proofs.Prog
