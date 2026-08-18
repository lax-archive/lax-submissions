import Lax3Proofs.DriverArena

/-!
# The cover sweep and the computed `ctr` (E12c, §6.2 ⟨B⟩)

GKS's own cluster-computation routine (`references/gks/nowheredense.tex`
:1459-1520), the one `algorithm-v2.md` §6.2 ⟨B⟩ says the design's
ordering section is *not*: given the ordering `π`, process the vertices
in **ascending `π`**, from each `v` run `2r` BFS levels in the *peeled*
graph — the strictly `π`-earlier vertices deleted — emit the reached set
as the cluster `X_v`, then delete `v`.  Alongside, their Remark
(tex:1522-1538): `ctr v` is read off the same sweep at no extra cost, as
the first (`π`-minimal) `u` whose radius-`r` levels reach `v`.

## §1 The correctness crux: peeled ball = wreach fibre

GKS's Claim (tex:1468-1471), `X_{2r}[G,<,v] = N_{2r}^{G∖S(v)}(v)`, in
this repo's vocabulary and at a general radius:

    {w | v ∈ wreach G π r w} = ball (deleteVerts G {x | π x < π v}) r v

(`fiber_eq_peeledBall`).  The two minimality conventions meet exactly:
`wreach`'s clause is *non-strict about the endpoint* over the whole
support (`π v ≤ π y` for every support vertex `y`), and the peeled set
`S(v)` is the *strictly* earlier vertices — so "the support survives the
peeling" and "`v` is `π`-minimal on the support" are the same condition,
`¬(π y < π v)`.  Both inclusions hold with **no side condition**: a
wreach witness walk never meets `S(v)`, hence survives `deleteVerts`
verbatim (`exists_walk_deleteVerts`); conversely a walk of the peeled
graph starting at `v ∉ S(v)` has its whole support outside `S(v)`
(`deleteVerts` isolates, so a non-nil walk touches no isolated vertex,
and the nil walk's support is `{v}`), which is `wreach`'s clause read
backwards.

## §2 The sweep

`sweepAux` is the fold: peeled graph in the accumulator, one emitted
`2r`-ball and one `deleteVerts {v}` per step.  `sweepClusters G π r`
runs it over the `π`-ascending vertex list; `sweepCluster G π r v` is
the entry the sweep emits for `v`.  The state invariant
(`sweepAux_getElem`) closes the accumulated singleton deletions into the
peeled set `{x | π x < π v}`, and §1 turns the emitted ball into the
wreach fibre (`sweepCluster_eq_fiber`) — i.e. into `Driver.cluster` at
that ordering (`sweepCluster_eq_cluster`).

## §3 The computed `ctr`

`sweepCtr G π r v` is GKS's Remark as a function: `find?` over the same
`π`-ascending list for the first `u` whose *radius-`r`* peeled ball
contains `v` — the `r`-level cut of the BFS the sweep already runs; the
clusters stay at `2r` (`CoverCentres`' two radii are distinct and stay
so).  By §1 that predicate is `u ∈ wreach G π r v`, so the first hit is
the `π`-minimum of `wreach G π r v` — `CoverCentres.ctr` by its two
characterising properties (`sweepCtr_eq_ctr`), hence `Driver.centre`
(`sweepCtr_eq_centre`).

## §4 The accounting — `(★)` as GKS's identity

The `N_<`/`N_>` split representation: `Nlt`/`Ngt` are the neighbours at
strictly earlier/later positions, `dlt` the back-degree `d_<`.
`sweepCharge G π r D` is GKS's own per-vertex account (tex:1502-1517):

    Σ_v (|X_v| · D  +  Σ_{w ∈ N_>(v)} d_<(w))

— per `v`, the BFS inside the peeled graph charged at its edge budget
(`Σ_{w ∈ X_v} d_<(w) ≤ |X_v| · D`, `sum_dlt_le`), plus the overhead of
deleting `v` from the adjacency lists of its later neighbours (`d_<(w)`
each, since only the `N_<`-list of `w` can contain `v`).  Under the
degree hypothesis `∀ x, |wreach_{2r}(x)| ≤ D` — the shape
`CoverSpec.wreach_degree_of_isCoverOrdering` supplies at
`D = ⌈c·N^δ⌉₊` — it closes as GKS close it:
`d_<(v) ≤ |wreach_{2r}(v)| ≤ D` (`dlt_le_of_wreach`) and
`N_>(v) ⊆ X_v` (`card_Ngt_le_cluster`), so

    sweepCharge ≤ 2·D·Σ_v |X_v| ≤ 2·D·(N·D)

(`sweepCharge_le_clusterMass`, `sweepCharge_le`) — §4's
`O(‖A‖^{1+2δ})` at `D = ⌈c_D‖A‖^δ⌉`, the mass bound being
`CoverDegree.sum_ncard_le_mul`.

**One side condition, GKS's implicitly**: the closing step needs
`1 ≤ r`.  Both `d_<(v) ≤ |wreach_{2r}(v)|` and `N_>(v) ⊆ X_v` charge a
length-`1` walk against radius `2r`, which fails at `r = 0` (`wreach`
at radius `0` is `{v}`, but `d_<` counts real neighbours).  The design
only ever calls the cover at its fixed radius `R ≥ 1`, but the
hypothesis is genuine and is stated, not hidden.  The §1 fibre identity
and the §2/§3 sweep identities need no such condition.

The peeling sweep *mutates* the arena (§6.2 ⟨B⟩'s note); here that
mutation is the accumulator of a fold, and the charge is a value — no
tower program is built this run.
-/

namespace Lax3Proofs.Impl

open Lax3.ColoredGraphs (WithinDist ball)
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.CoverConstruction (mem_wreach_iff)
open Lax3Proofs.SplitterBasics (deleteVerts_adj)
open Lax3Proofs.CoverCentres (ctr ctr_mem_wreach ctr_le_of_mem_wreach)

variable {n : ℕ}

/-! ### §0 `deleteVerts` plumbing -/

/-- Isolating nothing changes nothing. -/
theorem deleteVerts_empty {V : Type*} (G : SimpleGraph V) :
    deleteVerts G (∅ : Set V) = G := by
  ext u v
  rw [deleteVerts_adj]
  simp

/-- Two isolations compose into one: the sweep's accumulated singleton
deletions close into the peeled set. -/
theorem deleteVerts_deleteVerts {V : Type*} (G : SimpleGraph V) (S T : Set V) :
    deleteVerts (deleteVerts G S) T = deleteVerts G (S ∪ T) := by
  ext u v
  rw [deleteVerts_adj, deleteVerts_adj, deleteVerts_adj]
  simp only [Set.mem_union]
  tauto

/-- A walk of the isolated graph starting outside the isolated set never
touches it: `deleteVerts` removes every edge into `S`, and the nil
walk's support is its start. -/
theorem not_mem_of_mem_support_deleteVerts {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b : V} (q : (deleteVerts G S).Walk a b) (ha : a ∉ S) :
    ∀ y ∈ q.support, y ∉ S := by
  induction q with
  | nil =>
      intro y hy
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      exact hy ▸ ha
  | @cons a c b hadj q ih =>
      intro y hy
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ha
      · exact ih (deleteVerts_adj.mp hadj).2.2 y hy

/-- A walk of a subgraph is a walk of the graph — with the same length
*and the same support*, which is what transferring `wreach`'s
minimality clause needs. -/
theorem exists_walk_of_le_support {V : Type*} {G G' : SimpleGraph V} (hle : G ≤ G')
    {a b : V} (p : G.Walk a b) :
    ∃ q : G'.Walk a b, q.length = p.length ∧ q.support = p.support := by
  induction p with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | cons hadj p ih =>
      obtain ⟨q, hq1, hq2⟩ := ih
      exact ⟨.cons (hle hadj) q, by simp [hq1], by simp [hq2]⟩

/-! ### §1 The correctness crux: peeled ball = wreach fibre -/

/-- **GKS's Claim (tex:1468-1471), membership form.**  `v` is weakly
`r`-reachable from `w` iff `w` lies in the `r`-ball of `v` in the graph
with the strictly `π`-earlier vertices peeled.  `wreach`'s non-strict
endpoint-minimality over the whole support and the strictness of the
peeled set are the same condition `¬(π y < π v)`; no side condition. -/
theorem mem_wreach_iff_mem_peeledBall {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    {r : ℕ} {v w : Fin n} :
    v ∈ wreach G π r w ↔ w ∈ ball (deleteVerts G {x | π x < π v}) r v := by
  constructor
  · intro h
    obtain ⟨p, hp, hmin⟩ := mem_wreach_iff.mp h
    obtain ⟨q, hq⟩ :=
      exists_walk_deleteVerts p fun x hx => not_lt.mpr (hmin x hx)
    exact mem_ball.mpr (withinDist_symm ⟨q, le_of_eq_of_le hq hp⟩)
  · intro h
    obtain ⟨q, hq⟩ := mem_ball.mp h
    have hsup : ∀ y ∈ q.support, y ∉ {x | π x < π v} :=
      not_mem_of_mem_support_deleteVerts q (by simp)
    obtain ⟨p, hplen, hpsup⟩ :=
      exists_walk_of_le_support (deleteVerts_le G _) q.reverse
    refine mem_wreach_iff.mpr ⟨p, ?_, fun y hy => ?_⟩
    · rw [hplen, SimpleGraph.Walk.length_reverse]
      exact hq
    · rw [hpsup, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy
      exact not_lt.mp (hsup y hy)

/-- **The peeled-ball = wreach-fibre identity**, set form: the cluster
the design defines (the wreach fibre over `v`) is the set the sweep's
BFS computes (the `r`-ball of `v` in the peeled graph).  Stated at a
general radius; the sweep instantiates `2r`, the `ctr` assignment `r`. -/
theorem fiber_eq_peeledBall (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) :
    {w | v ∈ wreach G π r w} = ball (deleteVerts G {x | π x < π v}) r v :=
  Set.ext fun _ => mem_wreach_iff_mem_peeledBall

/-! ### §2 The sweep -/

/-- **The sweep's fold** (GKS tex:1475-1478): peeled graph in the
accumulator; per vertex, emit the `2r`-ball in the current graph, then
delete the vertex. -/
def sweepAux (r : ℕ) : SimpleGraph (Fin n) → List (Fin n) → List (Set (Fin n))
  | _, [] => []
  | H, v :: vs => ball H (2 * r) v :: sweepAux r (deleteVerts H {v}) vs

@[simp] theorem sweepAux_nil (r : ℕ) (H : SimpleGraph (Fin n)) :
    sweepAux r H [] = [] := rfl

@[simp] theorem sweepAux_cons (r : ℕ) (H : SimpleGraph (Fin n)) (v : Fin n)
    (vs : List (Fin n)) :
    sweepAux r H (v :: vs) = ball H (2 * r) v :: sweepAux r (deleteVerts H {v}) vs := rfl

@[simp] theorem length_sweepAux (r : ℕ) (H : SimpleGraph (Fin n)) (l : List (Fin n)) :
    (sweepAux r H l).length = l.length := by
  induction l generalizing H with
  | nil => rfl
  | cons v vs ih => simp [ih]

/-- **The state invariant of the fold**: at position `i` the accumulated
singleton deletions are exactly the processed prefix, and the emitted
set is the `2r`-ball of the `i`-th vertex in the graph with that prefix
peeled. -/
theorem sweepAux_getElem (r : ℕ) (l : List (Fin n)) :
    ∀ (H : SimpleGraph (Fin n)) (i : ℕ) (hi : i < l.length),
      (sweepAux r H l)[i]'(by rw [length_sweepAux]; exact hi) =
        ball (deleteVerts H {x | x ∈ l.take i}) (2 * r) (l[i]'hi) := by
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons v vs ih =>
      intro H i hi
      match i with
      | 0 =>
          simp only [sweepAux_cons, List.getElem_cons_zero, List.take_zero]
          have : {x : Fin n | x ∈ ([] : List (Fin n))} = (∅ : Set (Fin n)) := by
            ext x; simp
          rw [this, deleteVerts_empty]
      | j + 1 =>
          have hj : j < vs.length := by simpa using hi
          have h := ih (deleteVerts H {v}) j hj
          simp only [sweepAux_cons, List.getElem_cons_succ]
          rw [h, deleteVerts_deleteVerts]
          congr 2
          ext x
          simp [List.take_succ_cons]

/-- The `π`-ascending vertex list: position `i` holds `π.symm i`. -/
def ascList (π : Equiv.Perm (Fin n)) : List (Fin n) :=
  (List.finRange n).map π.symm

@[simp] theorem length_ascList (π : Equiv.Perm (Fin n)) : (ascList π).length = n := by
  simp [ascList]

theorem ascList_getElem (π : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) :
    (ascList π)[i]'(by rw [length_ascList]; exact hi) = π.symm ⟨i, hi⟩ := by
  simp [ascList]

/-- The processed prefix of the ascending list is exactly the set of
strictly `π`-earlier positions. -/
theorem mem_take_ascList {π : Equiv.Perm (Fin n)} {i : ℕ} {x : Fin n} :
    x ∈ (ascList π).take i ↔ (π x : ℕ) < i := by
  constructor
  · intro hx
    obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take, length_ascList] at hj
    rw [List.getElem_take, ascList_getElem π (lt_min_iff.mp hj).2] at hxj
    have : π x = ⟨j, (lt_min_iff.mp hj).2⟩ := ((Equiv.symm_apply_eq π).mp hxj).symm
    rw [this]
    exact (lt_min_iff.mp hj).1
  · intro hx
    have hxn : (π x : ℕ) < n := (π x).isLt
    refine List.mem_iff_getElem.mpr ⟨(π x : ℕ), ?_, ?_⟩
    · rw [List.length_take, length_ascList]
      exact lt_min hx hxn
    · rw [List.getElem_take, ascList_getElem π hxn, Fin.eta]
      exact π.symm_apply_apply x

/-- **The sweep**: GKS's routine — the fold run over the `π`-ascending
vertex list, emitting the clusters in ascending order of their
centres. -/
def sweepClusters (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ) :
    List (Set (Fin n)) :=
  sweepAux r G (ascList π)

@[simp] theorem length_sweepClusters (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) : (sweepClusters G π r).length = n := by
  simp [sweepClusters]

/-- The cluster the sweep emits for `v`: the entry at `v`'s position. -/
def sweepCluster (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : Set (Fin n) :=
  (sweepClusters G π r)[(π v : ℕ)]'(by rw [length_sweepClusters]; exact (π v).isLt)

/-- What the sweep computes for `v`, read off the state invariant: the
`2r`-ball of `v` in the graph with the strictly `π`-earlier vertices
peeled. -/
theorem sweepCluster_eq_peeledBall (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) :
    sweepCluster G π r v = ball (deleteVerts G {x | π x < π v}) (2 * r) v := by
  have hset : {x : Fin n | x ∈ (ascList π).take (π v : ℕ)} = {x : Fin n | π x < π v} := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_take_ascList, Fin.lt_def]
  have hidx : (ascList π)[(π v : ℕ)]'(by rw [length_ascList]; exact (π v).isLt) = v := by
    rw [ascList_getElem π (π v).isLt, Fin.eta, π.symm_apply_apply]
  calc sweepCluster G π r v
      = ball (deleteVerts G {x | x ∈ (ascList π).take (π v : ℕ)}) (2 * r)
          ((ascList π)[(π v : ℕ)]'(by rw [length_ascList]; exact (π v).isLt)) :=
        sweepAux_getElem r (ascList π) G (π v : ℕ) _
    _ = ball (deleteVerts G {x | π x < π v}) (2 * r) v := by
        simp only [hset, hidx]

/-- **The sweep is correct** (deliverable 2): the emitted set is the
wreach fibre — the cluster of `algorithm-v2.md` §6.2 — via the §1
identity. -/
theorem sweepCluster_eq_fiber (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) :
    sweepCluster G π r v = {w | v ∈ wreach G π (2 * r) w} := by
  rw [sweepCluster_eq_peeledBall, ← fiber_eq_peeledBall]

/-- The sweep's emitted set **is** the driver's cluster at that
ordering: the identity the abstract layer consumes. -/
theorem sweepCluster_eq_cluster {L n₀ Λ : ℕ} (S : Driver.Setup L)
    (A : Driver.Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) (v : Fin A.N) :
    sweepCluster A.G π S.R v = Driver.cluster S A π v :=
  sweepCluster_eq_fiber A.G π S.R v

/-! ### §3 The computed `ctr` -/

/-- `find?` returns the first hit: if position `i` satisfies the
predicate and every earlier position fails it, the search returns the
element at `i`. -/
private theorem find?_eq_some_getElem {α : Type*} {p : α → Bool} :
    ∀ {l : List α} {i : ℕ} (hi : i < l.length), p (l[i]'hi) = true →
      (∀ j (hj : j < i), p (l[j]'(Nat.lt_trans hj hi)) = false) →
      l.find? p = some (l[i]'hi) := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
      intro i hi hp hprev
      match i with
      | 0 => exact List.find?_cons_of_pos (by simpa using hp)
      | j + 1 =>
          have ha : p a = false := by simpa using hprev 0 (Nat.succ_pos j)
          rw [List.getElem_cons_succ,
            List.find?_cons_of_neg (by simp [ha])]
          exact ih (by simpa using hi) (by simpa using hp)
            fun k hk => by simpa using hprev (k + 1) (by omega)

open scoped Classical in
/-- **The `ctr` assignment of GKS's Remark (tex:1522-1538)**: sweep the
`π`-ascending list and assign to `v` the *first* `u` whose radius-`r`
levels — the `r`-cut of the BFS the sweep already runs — reach `v`.
The clusters stay at radius `2r`; the assignment probes at `r`. -/
noncomputable def sweepCtr (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : Option (Fin n) :=
  (ascList π).find? fun u => decide (v ∈ ball (deleteVerts G {x | π x < π u}) r u)

/-- **The sweep's assignment is `ctr`** (deliverable 3): the first `u`
in ascending order whose peeled `r`-ball reaches `v` is the `π`-minimum
of `wreach G π r v` — `CoverCentres.ctr`, by its two characterising
properties, through the §1 identity.  In particular the search always
succeeds. -/
theorem sweepCtr_eq_ctr (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : sweepCtr G π r v = some (ctr G π r v) := by
  classical
  have hidx : ((π (ctr G π r v) : ℕ)) < (ascList π).length := by
    rw [length_ascList]; exact (π _).isLt
  have hget : (ascList π)[(π (ctr G π r v) : ℕ)]'hidx = ctr G π r v := by
    rw [ascList_getElem π (π _).isLt, Fin.eta, π.symm_apply_apply]
  rw [sweepCtr, find?_eq_some_getElem hidx ?_ ?_, hget]
  · rw [hget, decide_eq_true_eq]
    exact mem_wreach_iff_mem_peeledBall.mp (ctr_mem_wreach G π r v)
  · intro j hj
    have hjn : j < n := lt_trans hj (π _).isLt
    rw [ascList_getElem π hjn, decide_eq_false_iff_not]
    intro hu
    have humem : π.symm ⟨j, hjn⟩ ∈ wreach G π r v :=
      mem_wreach_iff_mem_peeledBall.mpr hu
    have hle := ctr_le_of_mem_wreach humem
    rw [π.apply_symm_apply] at hle
    have : (π (ctr G π r v) : ℕ) ≤ j := by simpa [Fin.le_def] using hle
    omega

/-- The sweep's assignment **is** the driver's `centre` at that
ordering: `Driver.centre` is `ctr` at the schedule's radius `R`. -/
theorem sweepCtr_eq_centre {L n₀ Λ : ℕ} (S : Driver.Setup L)
    (A : Driver.Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) (v : Fin A.N) :
    sweepCtr A.G π S.R v = some (Driver.centre S A π v) :=
  sweepCtr_eq_ctr A.G π S.R v

/-! ### §4 The accounting — `(★)` as GKS's identity -/

section Accounting

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (π : Equiv.Perm (Fin n))

/-- `N_<(v)`: the neighbours of `v` at strictly earlier positions — one
half of GKS's split representation (tex:1481-1487). -/
def Nlt (v : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v).filter fun u => π u < π v

/-- `N_>(v)`: the neighbours of `v` at strictly later positions. -/
def Ngt (v : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v).filter fun u => π v < π u

/-- `d_<(v)`, the back-degree of the split representation. -/
def dlt (v : Fin n) : ℕ := (Nlt G π v).card

variable {G π}

/-- A strictly earlier neighbour is weakly reachable at any positive
radius: the length-`1` walk, on whose two-vertex support the earlier
endpoint is minimal.  GKS tex:1486-1487, `d_<(v) ≤ |wreach_{2r}(v)|` —
**this is where `1 ≤ r` is spent**. -/
theorem coe_Nlt_subset_wreach {r : ℕ} (hr : 1 ≤ r) (v : Fin n) :
    ↑(Nlt G π v) ⊆ wreach G π r v := by
  intro u hu
  rw [Finset.mem_coe, Nlt, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu
  refine mem_wreach_iff.mpr ⟨.cons hu.1 .nil, by simpa using hr, fun y hy => ?_⟩
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact le_of_lt hu.2
  · exact le_rfl

/-- `d_<(v) ≤ D` under the wreach-degree bound — the split
representation's row budget. -/
theorem dlt_le_of_wreach {r D : ℕ} (hr : 1 ≤ r)
    (hD : ∀ x, (wreach G π r x).ncard ≤ D) (v : Fin n) : dlt G π v ≤ D :=
  calc dlt G π v = (↑(Nlt G π v) : Set (Fin n)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (wreach G π r v).ncard :=
        Set.ncard_le_ncard (coe_Nlt_subset_wreach hr v) (Set.toFinite _)
    _ ≤ D := hD v

/-- A strictly later neighbour of `v` lies in `v`'s cluster: the
length-`1` walk back to `v`, on whose support `v` is minimal.  GKS
tex:1494-1496 ("the number of such vertices `w` is `d_>(v)`, which is
bounded by `|X_v|`") — the other place `1 ≤ r` is spent. -/
theorem mem_fiber_of_mem_Ngt {r : ℕ} (hr : 1 ≤ r) {v w : Fin n}
    (hw : w ∈ Ngt G π v) : v ∈ wreach G π (2 * r) w := by
  rw [Ngt, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw
  refine mem_wreach_iff.mpr ⟨.cons hw.1.symm .nil, by simp; omega, fun y hy => ?_⟩
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact le_of_lt hw.2
  · exact le_rfl

/-- `d_>(v) ≤ |X_v|`: at the moment `v` is deleted, its surviving
neighbours are exactly its later neighbours, and all of them were
reached by `v`'s own BFS. -/
theorem card_Ngt_le_cluster {r : ℕ} (hr : 1 ≤ r) (v : Fin n) :
    (Ngt G π v).card ≤ (sweepCluster G π r v).ncard := by
  rw [sweepCluster_eq_fiber]
  calc (Ngt G π v).card = (↑(Ngt G π v) : Set (Fin n)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ {w | v ∈ wreach G π (2 * r) w}.ncard :=
        Set.ncard_le_ncard (fun w hw => mem_fiber_of_mem_Ngt hr (Finset.mem_coe.mp hw))
          (Set.toFinite _)

/-- GKS tex:1488-1491: the edges of any subgraph are counted by summing
`d_<` over its vertices — each edge is in exactly one `N_<`-list.  This
is the budget that prices one BFS at `|X_v| · D`. -/
theorem sum_dlt_le {r D : ℕ} (hr : 1 ≤ r) (hD : ∀ x, (wreach G π r x).ncard ≤ D)
    (s : Finset (Fin n)) : ∑ w ∈ s, dlt G π w ≤ s.card * D :=
  calc ∑ w ∈ s, dlt G π w ≤ ∑ _w ∈ s, D :=
        Finset.sum_le_sum fun w _ => dlt_le_of_wreach hr hD w
    _ = s.card * D := by rw [Finset.sum_const, smul_eq_mul]

variable (G π)

/-- **`(★)` as GKS's accounting identity** (tex:1502-1506): the sweep's
cost — per vertex, the BFS inside the peeled graph at its edge budget
`|X_v| · D`, plus the overhead `Σ_{w ∈ N_>(v)} d_<(w)` of deleting `v`
from the adjacency lists of its later neighbours. -/
noncomputable def sweepCharge (r D : ℕ) : ℕ :=
  ∑ v : Fin n, ((sweepCluster G π r v).ncard * D + ∑ w ∈ Ngt G π v, dlt G π w)

variable {G π}

/-- **GKS's closing estimate** (tex:1507-1514): under the wreach-degree
bound, the deletion overhead is absorbed — `d_<(w) ≤ D` and
`N_>(v) ⊆ X_v` — and the whole charge closes to `2·D·Σ_v |X_v|`. -/
theorem sweepCharge_le_clusterMass {r D : ℕ} (hr : 1 ≤ r)
    (hD : ∀ x, (wreach G π (2 * r) x).ncard ≤ D) :
    sweepCharge G π r D ≤ 2 * D * ∑ v : Fin n, (sweepCluster G π r v).ncard := by
  have h2r : 1 ≤ 2 * r := by omega
  have hterm : ∀ v : Fin n,
      (sweepCluster G π r v).ncard * D + ∑ w ∈ Ngt G π v, dlt G π w ≤
        2 * D * (sweepCluster G π r v).ncard := by
    intro v
    have hover : ∑ w ∈ Ngt G π v, dlt G π w ≤ (sweepCluster G π r v).ncard * D :=
      calc ∑ w ∈ Ngt G π v, dlt G π w ≤ (Ngt G π v).card * D := sum_dlt_le h2r hD _
        _ ≤ (sweepCluster G π r v).ncard * D :=
            Nat.mul_le_mul_right D (card_Ngt_le_cluster hr v)
    calc (sweepCluster G π r v).ncard * D + ∑ w ∈ Ngt G π v, dlt G π w
        ≤ (sweepCluster G π r v).ncard * D + (sweepCluster G π r v).ncard * D :=
          Nat.add_le_add_left hover _
      _ = 2 * D * (sweepCluster G π r v).ncard := by ring
  calc sweepCharge G π r D ≤ ∑ v : Fin n, 2 * D * (sweepCluster G π r v).ncard :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = 2 * D * ∑ v : Fin n, (sweepCluster G π r v).ncard := by
        rw [Finset.mul_sum]

omit [DecidableRel G.Adj] in
/-- The cluster mass of the sweep's output: `Σ_v |X_v| ≤ N·D` — the
degree hypothesis double-counted, `CoverDegree.sum_ncard_le_mul` at the
fibre family. -/
theorem sum_sweepCluster_ncard_le {r D : ℕ}
    (hD : ∀ x, (wreach G π (2 * r) x).ncard ≤ D) :
    ∑ v : Fin n, (sweepCluster G π r v).ncard ≤ n * D := by
  have h : ∀ v : Fin n, sweepCluster G π r v = {w | v ∈ wreach G π (2 * r) w} :=
    sweepCluster_eq_fiber G π r
  calc ∑ v : Fin n, (sweepCluster G π r v).ncard
      = ∑ v : Fin n, {w | v ∈ wreach G π (2 * r) w}.ncard :=
        Finset.sum_congr rfl fun v _ => by rw [h]
    _ ≤ n * D :=
        Lax3Proofs.CoverDegree.sum_ncard_le_mul
          (fun u => {w | u ∈ wreach G π (2 * r) w}) D fun w => hD w

/-- **The sweep's total** (deliverable 4, GKS tex:1514-1517): under the
degree hypothesis the whole sweep is charged at `2·D·(N·D)` — §4's
`O(‖A‖^{1+2δ})` shape at `D = ⌈c_D·‖A‖^δ⌉`. -/
theorem sweepCharge_le {r D : ℕ} (hr : 1 ≤ r)
    (hD : ∀ x, (wreach G π (2 * r) x).ncard ≤ D) :
    sweepCharge G π r D ≤ 2 * D * (n * D) :=
  le_trans (sweepCharge_le_clusterMass hr hD)
    (Nat.mul_le_mul_left (2 * D) (sum_sweepCluster_ncard_le hD))

end Accounting

end Lax3Proofs.Impl
