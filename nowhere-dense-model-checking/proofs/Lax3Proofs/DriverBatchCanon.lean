import Lax3Proofs.WalkDistance
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Lattice

/-!
# F6c12p — the ⟨D⟩ batch, canonicalized: the choice-free walk kit

## The finding this file repairs

`Driver.batchRoot` is `SplitterWin.genSet (2R) hist (up u)`, and
`SplitterWin.pathSet` was `(withinDist_iff.mp h).choose.support` — a
`Classical.choose`-picked walk. `childArena.G = deleteVerts preG (range
batchFn)` and `childCol` depend on it, so the machine child-building
pass (residual `ChildLoadPartsAll`, `SolveMachPrep`) could never be
proved to output the child arena: no program provably outputs a
choice-picked set. The design (`algorithm-v2.md` §5 l.17–19, D6) always
meant recorded, derivable supports; the formalization re-chose. This
file is the choice-free kit; `SplitterWin.pathSet` is redefined on it,
and `DriverArena`'s channel records the graph the walks live in.

## The investigation, and the decision

**(α′) — walks in the current graph — fails on a real obstruction.**
`ReachedS.step`'s walk clause is guarded by `WithinDist e.arena r e.vtx
v` — distance in the ROUND's arena — and the extraction can only arm it
that way: `pairS_walk` derives the guard from the legality clause of
the rounds played after `e` (`mem_res_of_roundS` + `resS_subset_ball`),
which yields round-arena distance and nothing smaller. Under that guard
a walk in the CURRENT graph need not exist at all: every recorded
connector is in its own round's generating set (`selfS`), hence
edge-isolated in every later arena (`isolatedS`), so at positive
distance the connector end of the required walk carries no current
edge. Weakening `reachedS_descend`'s `hwalk` to accept walks in
subgraphs of `e.arena` is sound but empty — such walks transfer into
`e.arena` support-for-support — and weakening the guard would weaken
the landed extraction. Round-graph walks stay.

**(α) at the full round graph is provable but cost-dead.** Redefining
`pathSet` as the canonical gradient walk of the FULL round graph keeps
every consumer verbatim (`hwalk` untouched, this kit supplies the
walk), but the machine could then realize the batch only by one BFS
from the connector in the node's FULL graph per child — `Σ_children
O(‖A‖)` per node, which is exactly the cost shape `algorithm-v2.md` D6
rejects ("one carrier-wide BFS per ancestor per turn" was the deleted
driver's principal cost) and §6/§7 cannot absorb (the child-building
column is budgeted at `Σ_u O(‖A[X_u]‖)`, cluster-sized). The design
computes the recorded walks at §5 line 17 by ONE BFS from the centre
**inside `B₀ = A[X_u]`**, before isolation, and its ⟨B⟩ audit block
proves why that suffices: wreach clusters are path-closed
(`ClusterPaths.exists_walk_support_subset_fiber`), so `dist_{A[X_u]}(u,
w) ≤ 2R` for every `w ∈ X_u`, and every descendant carrier lies in
`X_u`. A walk of `B₀` IS a walk of the round's arena, which is all the
game asks (`reachedS_descend`: "the program owes no equation between
the walk it found and any other walk").

**The decision: canonicalize the walk AND record the graph it lives
in.** `pathSet G r u v` becomes the support of the canonical min-parent
gradient walk of `G` (`pathList` below) — choice-free, extensionally
determined. The channel entry a descent pushes becomes `(A.up u,
histGraph)` with `histGraph = deleteVerts (map A.up A.G) (A.up ''
cluster)ᶜ` — the round's arena restricted to the round's own cluster,
at root names (`DriverArena`), which is `map childUp preG`
(`histGraph_eq_map`): exactly the graph §5 line 17's BFS runs in. The
correctness linkage (`Driver.Inv`) ties each recorded round `e` of the
`ReachedS` record to the channel pair `(e.vtx, deleteVerts e.arena
e.resᶜ)` — a function of the round's own data, no existential — plus
the path-closure fact that every current carrier vertex is within `2R`
of the connector in that restricted graph; `inv_child` then discharges
`hwalk` verbatim from `pathSet_spec` + `Walk.transfer`. The five
statements the chain consumes — `pathSet_spec`, `pathSet_ncard_le`,
`self_mem_genSet`, `pathSet_subset_genSet`, `genSet_ncard_le` — keep
their statements byte-identical; `ReachedS`, `SplitterWin(Rec)`'s games
and `reachedS_descend` are untouched; `Unroll` consumes `Inv` opaquely
and re-elaborates verbatim.

## The kit, and why it is a mirror

`cdist`/`cparents`/`cdescend` are formula-for-formula the machine
layer's own canonical kit — `Prog.ballDist` (`SolveMachPrep`),
`Impl.parents`/`Impl.descend` (`ImplBfs`) — made generic (`[Fintype]`/
`[LinearOrder]` carrier instead of `Fin n`, classical decidability
instead of `DecidableRel`). They are mirrored, not imported: `pathSet`
sits upstream of the whole abstract chain, and importing `ImplBfs`
there would pull the IMP+ probe tower under the splitter game. The seam
lemmas (`cdist = Prog.ballDist`, `cdescend = Impl.descend` at `Fin n`,
one filter-decidability transport each) are one well-founded induction
apiece and belong to the machine-pass leaf that consumes them;
`isBallTable_eq_cdist` is the uniqueness that makes any valid BFS run
land on the same table, mirrored here so the abstract side states it
too.

## The transport lemma (the machine seam's other half)

The batch is read at ROOT names — `pathSet` in the recorded root-name
graph — while every machine region lives at level names. `pathList_map`:
for a strictly monotone embedding `f`, the canonical list in `map f G`
between mapped endpoints is the `f`-image of the canonical list in `G`
(no edge of a pushforward leaves the range, distances between range
vertices are blind to `f`, and `min'` commutes with monotone images).
The `up` maps of every reachable arena ARE strictly monotone — root
`Embedding.refl`, each level the sorted `setEquiv` enumeration composed
with a subtype inclusion — `setEquiv_coe_strictMono`/
`childArena_up_strictMono`/`rootArena_up_strictMono` (in `DriverArena`,
their DAG-forced home). So the machine computes at level names and the
abstract batch at root names is its verbatim image.

## How the machine computes the batch (the story the residual
`ChildLoadPartsAll`'s discharger follows)

Per descent at centre `u`, at level names:
* **new round's column**: one BFS from the centre at cap `2R` in `B₀ =
  preG` (`bfsCom` — the table is forced: `isBallTable_eq_cdist`), one
  gradient pass (`supportsCom` — the stored list IS `cdescend`), cost
  `O(‖B₀‖ + (2R+1)·|X_u|)`, summed over centres within the cover
  budget; path-closure makes every cluster vertex reached;
* **old rounds' columns**: no BFS — filter each inherited list to the
  cluster and rename through the sorted compaction
  (`Impl.MArena.restrict` already does exactly this), `O(j·(2R+1))` per
  vertex; restriction loses nothing the batch reads, because carrier
  images only descend;
* **the batch**: `{u} ∪ ⋃_e column_e(u)` traced on the cluster, padded
  by the connector to width `m` through the sorted enumeration
  (`range_pad`); this is the trace of the root-name `genSet` by
  `pathList_map` down the strictly monotone `up` chain.
-/

namespace Lax3Proofs.BatchCanon

open Lax3.ColoredGraphs
open Lax12.UniformQuasiWideness
open Lax3Proofs.WalkDistance

variable {V : Type*}

/-! ### §1 The canonical truncated distance

The formula of `Prog.ballDist` (`SolveMachPrep`), generic: the least
radius reaching `v` from `s`, or `d + 1` beyond the horizon. -/

open Classical in
/-- **The canonical truncated distance** from `s` at cap `d`: the least
radius reaching `v`, or `d + 1` beyond the horizon — `Prog.ballDist`'s
formula, the unique table a capped BFS can leave
(`isBallTable_eq_cdist`). -/
noncomputable def cdist (G : SimpleGraph V) (s : V) (d : ℕ) (v : V) : ℕ :=
  if v ∈ ball G d s then sInf {k | v ∈ ball G k s} else d + 1

/-- A correct truncated distance table: below the cap, the table bound
is membership in the ball of that radius — `Impl.BallTable`'s clause,
generic. -/
def IsBallTable (G : SimpleGraph V) (s : V) (d : ℕ) (D : V → ℕ) : Prop :=
  ∀ v : V, ∀ k ≤ d, (D v ≤ k ↔ v ∈ ball G k s)

open Classical in
/-- The canonical table respects the horizon bound. -/
theorem cdist_le (G : SimpleGraph V) (s : V) (d : ℕ) (v : V) :
    cdist G s d v ≤ d + 1 := by
  rw [cdist]
  by_cases hv : v ∈ ball G d s
  · rw [if_pos hv]
    exact le_trans (Nat.sInf_le hv) (Nat.le_succ d)
  · rw [if_neg hv]

open Classical in
/-- The canonical table is a correct table. -/
theorem isBallTable_cdist (G : SimpleGraph V) (s : V) (d : ℕ) :
    IsBallTable G s d (cdist G s d) := by
  intro v k hk
  by_cases hv : v ∈ ball G d s
  · rw [cdist, if_pos hv]
    constructor
    · intro hle
      have hmem : v ∈ ball G (sInf {k | v ∈ ball G k s}) s :=
        Nat.sInf_mem (⟨d, hv⟩ : {k | v ∈ ball G k s}.Nonempty)
      exact ball_mono_radius G s hle hmem
    · intro hkm
      exact Nat.sInf_le hkm
  · rw [cdist, if_neg hv]
    constructor
    · intro h
      exact absurd hk (by omega)
    · intro hkm
      exact absurd (ball_mono_radius G s hk hkm) hv

open Classical in
/-- **Uniqueness**: any correct table with the horizon bound — verbatim
what a capped BFS leaves — IS the canonical table. This is what makes a
stored channel independent of the run that produced it. -/
theorem isBallTable_eq_cdist {G : SimpleGraph V} {s : V} {d : ℕ}
    {D : V → ℕ} (hD : IsBallTable G s d D) (hle : ∀ v, D v ≤ d + 1) :
    D = cdist G s d := by
  funext v
  by_cases hv : v ∈ ball G d s
  · rw [cdist, if_pos hv]
    have h1 : D v ≤ d := (hD v d le_rfl).mpr hv
    have h2 : v ∈ ball G (D v) s := (hD v (D v) h1).mp le_rfl
    have h3 : sInf {k | v ∈ ball G k s} ≤ D v := Nat.sInf_le h2
    have hmem : v ∈ ball G (sInf {k | v ∈ ball G k s}) s :=
      Nat.sInf_mem (⟨d, hv⟩ : {k | v ∈ ball G k s}.Nonempty)
    have h4 : D v ≤ sInf {k | v ∈ ball G k s} :=
      (hD v _ (le_trans h3 h1)).mpr hmem
    omega
  · rw [cdist, if_neg hv]
    have h1 : ¬ D v ≤ d := fun h => hv ((hD v d le_rfl).mp h)
    have h2 := hle v
    omega

/-! ### §2 The canonical parent and the gradient walk

`Impl.parents`/`Impl.descend`'s recursion (`ImplBfs`), generic: from
`v`, descend the distance gradient to the source, taking the least
parent at each step. -/

section Kit

variable [Fintype V]

open Classical in
/-- **The canonical parent candidates**: the strictly-closer neighbours
of `v` — `Impl.parents`' formula. -/
noncomputable def cparents (G : SimpleGraph V) (D : V → ℕ) (v : V) :
    Finset V :=
  Finset.univ.filter fun u => G.Adj u v ∧ D u < D v

/-- A reached vertex of positive distance has a strictly closer
neighbour: peel the first edge of its witness walk. -/
theorem cparents_nonempty {G : SimpleGraph V} {s : V} {d : ℕ}
    {D : V → ℕ} (hD : IsBallTable G s d D) {v : V} (hvd : D v ≤ d)
    (hv : 0 < D v) : (cparents G D v).Nonempty := by
  classical
  obtain ⟨w, hw⟩ : WithinDist G (D v) v s :=
    withinDist_symm (mem_ball.mp ((hD v (D v) hvd).mp le_rfl))
  cases w with
  | nil =>
      have : D s ≤ 0 :=
        (hD s 0 (Nat.zero_le d)).mpr (mem_ball_self G 0 s)
      omega
  | cons hadj p =>
      rename_i u
      have hp : p.length ≤ D v - 1 := by
        simp only [SimpleGraph.Walk.length_cons] at hw
        omega
      have hu : D u ≤ D v - 1 :=
        (hD u (D v - 1) (by omega)).mpr (mem_ball.mpr (withinDist_symm ⟨p, hp⟩))
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj.symm, by omega⟩⟩

variable [LinearOrder V]

open Classical in
/-- **The canonical gradient walk, as its support list**: from `v`,
descend to the least parent until none is left — `Impl.descend`'s
recursion. Under `IsBallTable` this list is the support of a walk of
length exactly `D v` (`cdescend_spec`). -/
noncomputable def cdescend (G : SimpleGraph V) (D : V → ℕ) (v : V) :
    List V :=
  if h : (cparents G D v).Nonempty then
    v :: cdescend G D ((cparents G D v).min' h)
  else [v]
termination_by D v
decreasing_by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.2

/-- **The support is a walk's support** — the correctness of
`cdescend`: at every reached vertex there is a walk to the source of
length exactly `D v` whose support is precisely the canonical list. -/
theorem cdescend_spec {G : SimpleGraph V} {s : V} {d : ℕ} {D : V → ℕ}
    (hD : IsBallTable G s d D) (v : V) (hvd : D v ≤ d) :
    ∃ w : G.Walk v s, w.length = D v ∧ w.support = cdescend G D v := by
  classical
  rcases Nat.eq_zero_or_pos (D v) with h0 | hpos
  · -- the source itself: the empty walk
    obtain ⟨w, hw⟩ : WithinDist G 0 s v :=
      mem_ball.mp ((hD v 0 (Nat.zero_le d)).mp (le_of_eq h0))
    cases w with
    | nil =>
        have hemp : ¬ (cparents G D s).Nonempty := by
          rintro ⟨u, hu⟩
          have := (Finset.mem_filter.mp hu).2.2
          omega
        refine ⟨.nil, by simpa using h0.symm, ?_⟩
        rw [SimpleGraph.Walk.support_nil, cdescend, dif_neg hemp]
    | cons hadj p => simp at hw
  · -- one step down the gradient, then the recursive walk
    have hne := cparents_nonempty hD hvd hpos
    set u := (cparents G D v).min' hne with hu
    have hmem := (cparents G D v).min'_mem hne
    rw [← hu, cparents, Finset.mem_filter] at hmem
    obtain ⟨-, hadj, hlt⟩ := hmem
    obtain ⟨w', hw'len, hw'sup⟩ := cdescend_spec hD u (by omega)
    refine ⟨.cons hadj.symm w', ?_, ?_⟩
    · have hle : D v ≤ D u + 1 := by
        refine (hD v (D u + 1) (by omega)).mpr (mem_ball.mpr ?_)
        exact withinDist_symm ⟨.cons hadj.symm w', by simp [hw'len]⟩
      simp only [SimpleGraph.Walk.length_cons, hw'len]
      omega
    · rw [SimpleGraph.Walk.support_cons, hw'sup]
      conv_rhs => rw [cdescend]
      rw [dif_pos hne, ← hu]
termination_by D v
decreasing_by exact hlt

/-- The canonical list has exactly `D v + 1` names. -/
theorem length_cdescend {G : SimpleGraph V} {s : V} {d : ℕ} {D : V → ℕ}
    (hD : IsBallTable G s d D) {v : V} (hv : D v ≤ d) :
    (cdescend G D v).length = D v + 1 := by
  obtain ⟨w, hwlen, hwsup⟩ := cdescend_spec hD v hv
  rw [← hwsup, SimpleGraph.Walk.length_support, hwlen]

/-! ### §3 The canonical path list

The choice-free replacement for the strategy's chosen walk: the
canonical gradient walk of the canonical distance table, from the
target back to the source, when the target is within reach — the list a
BFS-and-supports pass stores, and the list `SplitterWin.pathSet` now
reads its support off. -/

open Classical in
/-- **The canonical path list** from `u` to `v` at radius `r`: the
canonical gradient walk of `cdist G u r` at `v` when `v` is within
distance `r` of `u`, and the empty list otherwise. -/
noncomputable def pathList (G : SimpleGraph V) (r : ℕ) (u v : V) :
    List V :=
  if WithinDist G r u v then cdescend G (cdist G u r) v else []

open Classical in
theorem pathList_of_not {G : SimpleGraph V} {r : ℕ} {u v : V}
    (h : ¬ WithinDist G r u v) : pathList G r u v = [] := if_neg h

open Classical in
/-- The canonical path is the support of a genuine walk of length at
most `r` whenever there is one — the discharge of
`SplitterWin.pathSet_spec`. -/
theorem pathList_spec {G : SimpleGraph V} {r : ℕ} {u v : V}
    (h : WithinDist G r u v) :
    ∃ p : G.Walk u v, p.length ≤ r ∧
      {z | z ∈ pathList G r u v} = {z | z ∈ p.support} := by
  classical
  have hD := isBallTable_cdist G u r
  have hvd : cdist G u r v ≤ r := (hD v r le_rfl).mpr (mem_ball.mpr h)
  obtain ⟨w, hwlen, hwsup⟩ := cdescend_spec hD v hvd
  refine ⟨w.reverse, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_reverse, hwlen]
    exact hvd
  · rw [pathList, if_pos h, ← hwsup, SimpleGraph.Walk.support_reverse]
    ext z
    simp

open Classical in
/-- The canonical path has at most `r + 1` names. -/
theorem pathList_length_le (G : SimpleGraph V) (r : ℕ) (u v : V) :
    (pathList G r u v).length ≤ r + 1 := by
  classical
  by_cases h : WithinDist G r u v
  · have hD := isBallTable_cdist G u r
    have hvd : cdist G u r v ≤ r := (hD v r le_rfl).mpr (mem_ball.mpr h)
    rw [pathList, if_pos h, length_cdescend hD hvd]
    omega
  · rw [pathList_of_not h]
    simp

end Kit

/-! ### §4 Transport along an embedding

The walk lemmas of `ArenaTransport`, generic (that file sits downstream
of the game, so they are re-proved here in their dozen lines each): no
edge of a pushforward leaves the range, so walks push and pull at the
same length and balls transport exactly. -/

section Transport

variable {W : Type*} (f : V ↪ W) {G : SimpleGraph V}

/-- A walk pushes through an embedding edge by edge, at the same
length. -/
theorem exists_walk_push {u v : V} (p : G.Walk u v) :
    ∃ q : (G.map f).Walk (f u) (f v), q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hqlen⟩ := ih
    exact ⟨.cons (SimpleGraph.map_adj_apply.mpr hab) q, by simp [hqlen]⟩

/-- A walk of the pushforward starting in the range pulls back, at the
same length; the far endpoint is produced, not assumed. -/
theorem exists_walk_pull {x y : W} (q : (G.map f).Walk x y) {a : V}
    (hax : f a = x) :
    ∃ (b : V) (p : G.Walk a b), f b = y ∧ p.length = q.length := by
  induction q generalizing a with
  | nil => exact ⟨a, .nil, hax, rfl⟩
  | @cons x c y hxc q ih =>
    obtain ⟨a₁, c', hac, ha₁, hc'⟩ := (SimpleGraph.map_adj f G x c).mp hxc
    obtain rfl : a₁ = a := f.injective (ha₁.trans hax.symm)
    obtain ⟨b, p, hby, hlen⟩ := ih hc'
    exact ⟨b, .cons hac p, hby, by simp [hlen]⟩

/-- Distance bounds between range vertices are blind to the
embedding. -/
theorem withinDist_map_iff {d : ℕ} {u v : V} :
    WithinDist (G.map f) d (f u) (f v) ↔ WithinDist G d u v := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨b, p, hb, hlen⟩ := exists_walk_pull f q rfl
    obtain rfl : b = v := f.injective hb
    exact ⟨p, hlen.trans_le hq⟩
  · rintro ⟨p, hp⟩
    obtain ⟨q, hqlen⟩ := exists_walk_push f p
    exact ⟨q, hqlen.trans_le hp⟩

/-- The ball of a pushforward around an image vertex is exactly the
image of the ball: no walk leaves the range. -/
theorem ball_map (G : SimpleGraph V) (d : ℕ) (v : V) :
    ball (G.map f) d (f v) = f '' ball G d v := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := mem_ball.mp hx
    obtain ⟨b, p, hb, hlen⟩ := exists_walk_pull f q rfl
    exact ⟨b, mem_ball.mpr ⟨p, hlen.trans_le hq⟩, hb⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨p, hp⟩ := mem_ball.mp hu
    obtain ⟨q, hqlen⟩ := exists_walk_push f p
    exact mem_ball.mpr ⟨q, hqlen.trans_le hp⟩

/-- The canonical distance is blind to the embedding. -/
theorem cdist_map (G : SimpleGraph V) (s : V) (d : ℕ) (v : V) :
    cdist (G.map f) (f s) d (f v) = cdist G s d v := by
  classical
  have hball : ∀ k, f v ∈ ball (G.map f) k (f s) ↔ v ∈ ball G k s := by
    intro k
    rw [ball_map]
    exact ⟨fun ⟨a, ha, hav⟩ => f.injective hav ▸ ha, fun h => ⟨v, h, rfl⟩⟩
  rw [cdist, cdist]
  by_cases h : v ∈ ball G d s
  · rw [if_pos ((hball d).mpr h), if_pos h]
    congr 1
    ext k
    exact hball k
  · rw [if_neg (fun hc => h ((hball d).mp hc)), if_neg h]

variable [Fintype V] [Fintype W]

/-- The canonical parent set of a mapped vertex is the image of the
canonical parent set: no edge of the pushforward leaves the range. -/
theorem cparents_map [DecidableEq W] {D : V → ℕ} {Dm : W → ℕ}
    (hDm : ∀ a : V, Dm (f a) = D a) (v : V) :
    cparents (G.map f) Dm (f v) = (cparents G D v).image f := by
  classical
  ext w
  simp only [cparents, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨hadj, hlt⟩
    obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj f G w (f v)).mp hadj
    have hbv : b = v := f.injective hb
    rw [hbv] at hab
    refine ⟨a, ⟨hab, ?_⟩, ha⟩
    rw [← hDm a, ← hDm v, ha]
    exact hlt
  · rintro ⟨a, ⟨hab, hlt⟩, rfl⟩
    refine ⟨(SimpleGraph.map_adj f G _ _).mpr ⟨a, v, hab, rfl, rfl⟩, ?_⟩
    rw [hDm a, hDm v]
    exact hlt

variable [LinearOrder V] [LinearOrder W]

open Classical in
/-- **The canonical walk transports**: along a strictly monotone
embedding, the canonical gradient list at a mapped vertex is the image
of the canonical gradient list — min-index parents commute with
order-embeddings (the `min'` of an image under a monotone map is the
image of the `min'`). -/
theorem cdescend_map (hf : StrictMono f) {D : V → ℕ} {Dm : W → ℕ}
    (hDm : ∀ a : V, Dm (f a) = D a) (v : V) :
    cdescend (G.map f) Dm (f v) = (cdescend G D v).map f := by
  have hpar := cparents_map (G := G) f hDm (D := D) (Dm := Dm) v
  by_cases h : (cparents G D v).Nonempty
  · have hm : (cparents (G.map f) Dm (f v)).Nonempty := by
      rw [hpar]
      exact h.image f
    have hmin : (cparents (G.map f) Dm (f v)).min' hm
        = f ((cparents G D v).min' h) := by
      apply le_antisymm
      · apply Finset.min'_le
        rw [hpar]
        exact Finset.mem_image_of_mem f ((cparents G D v).min'_mem h)
      · apply Finset.le_min'
        intro y hy
        rw [hpar] at hy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
        exact hf.monotone ((cparents G D v).min'_le a ha)
    conv_lhs => rw [cdescend]
    conv_rhs => rw [cdescend]
    rw [dif_pos h, dif_pos hm, List.map_cons, hmin]
    congr 1
    exact cdescend_map hf hDm ((cparents G D v).min' h)
  · have hm : ¬ (cparents (G.map f) Dm (f v)).Nonempty := by
      rw [hpar, Finset.image_nonempty]
      exact h
    conv_lhs => rw [cdescend]
    conv_rhs => rw [cdescend]
    rw [dif_neg hm, dif_neg h, List.map_cons, List.map_nil]
termination_by D v
decreasing_by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.2

/-- **The canonical path list transports** along a strictly monotone
embedding: the machine computes at level names, and the batch at root
names is its verbatim image. -/
theorem pathList_map (hf : StrictMono f) (G : SimpleGraph V) (r : ℕ)
    (u v : V) :
    pathList (G.map f) r (f u) (f v) = (pathList G r u v).map f := by
  classical
  by_cases h : WithinDist G r u v
  · have hm : WithinDist (G.map f) r (f u) (f v) :=
      (withinDist_map_iff f).mpr h
    rw [pathList, pathList, if_pos h, if_pos hm]
    exact cdescend_map f hf (fun a => cdist_map f G u r a) v
  · have hm : ¬ WithinDist (G.map f) r (f u) (f v) := fun hc =>
      h ((withinDist_map_iff f).mp hc)
    rw [pathList, pathList, if_neg h, if_neg hm, List.map_nil]

end Transport

end Lax3Proofs.BatchCanon
