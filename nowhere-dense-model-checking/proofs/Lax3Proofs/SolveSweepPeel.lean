import Lax3Proofs.SolveSweepStep
import Lax3Proofs.SolveBfs

/-!
# F6c12 — `CovPeelIn`: the GKS peeling sweep, discharged

`SolveSweepStep` names `CovPeelIn`: from the built deletable adjacency
region (`DelAdjSt` at `∅`), the order region (`OrdArr`), the rank
region (`RankArr`) and the two output allocations, run GKS's peel —
per rank one frontier-queue BFS at radius `2R` over the **live
prefixes** of the deletable structure, emit the ball, write first-hit
centre marks, delete the centre at `O(1)` per removed edge copy — and
land `CoverStageSpec`'s exact postcondition (`CtrArr` at
`Driver.centre`, `ClusterCsr` at `Driver.cluster`).  This file is that
discharge: `covPeelIn_peelCom` concludes the verbatim residual at the
concrete program `peelCom` and the closed budget `peelK`.

## The machine

One program (`peelCom`), five phases:

* **Prologue** — one `O(N)` pass: distance region to the sentinel
  `2R+1`, assignment region to the sentinel `N` (`ca[v] = N` means
  "unassigned"), stream cursor and segment anchor to `0`.
* **The sweep** — for rank `i` ascending, `u := od[i]`:
  a *frontier-queue* BFS from `u` in the current structure — the queue
  is the emitted segment of the member stream `pc.r` itself, walked by
  head/tail cursors; a popped vertex is expanded only when its stored
  level is `< 2R`, and expansion reads exactly the **live prefix**
  `aj[ao[z] .. ao[z]+dg[z])` (the w20 finding: never a full pass).
  Discovery writes the level, appends to the segment, and lays the
  first-hit `ctr` mark (`ca[w] := u` when the level is `≤ R` and
  `ca[w]` still holds the sentinel).  After the BFS the touched
  distance cells are re-sentineled by walking the emitted segment
  (`O(|X_u|)`, the E11 discipline — never `O(N)` per centre), the
  segment end is recorded (`pc.e[i+1] := tail`), and `u` is deleted:
  per live copy, swap-remove through the mate pointer at `O(1)`, then
  `dg[u] := 0`.
* **Correctness anchors** (`SolveSweepAdj` §4): the emitted segment is
  `cluster S A π u` (`cluster_eq_ball_peelSet` through the exactness
  of the truncated level table, re-derived from soundness + the
  relaxation closure by `d_complete`); the first-hit marks are
  `Driver.centre` (`centre_eq_of_hit_first`'s content, in the
  invariant form `π (ctr v) < i → ca[v] = ctr v`); the deleted set
  walks the rank prefixes (`peelSet_zero/succ`).
* **The regroup** — `ClusterCsr` wants each row **ascending**
  (`restrictEmb`'s enumeration).  Discovery order is not sorted, so
  the sweep's segments are regrouped globally at `O(N + M)`,
  `M = Σ|X_u|`: count per-member occurrences (`pc.z`), prefix-sum to
  inverse offsets (`pc.o`), scatter the (centre, member) pairs into
  member-major buckets (`pc.v`), prefix-sum the row lengths into the
  offsets `co` (via the rank array: row `u`'s segment is `ra[u]`),
  then one member-ascending placement pass: each bucket `z` appends
  `z` to the next slot (`pc.f`) of each containing row — rows fill in
  ascending member order, which *is* `restrictEmb`'s order.
* **Budget** — the BFS is priced by a queue potential whose weight at
  `z` is its live degree when `z` can be expanded (`dist < 2R`) plus a
  constant; the deletion at `u`'s current degree rides inside the
  cluster mass (`curDeg_at_deletion_le_cluster`).  The closed budget
  `peelK` is `Σ_i (peelDeg + peelNc) + O(N)` in shape;
  `peelK_le_sweepCharge` closes it against a constant multiple of the
  landed `Impl.sweepCharge` account under the wreach-degree bound —
  the scanned edges live inside the ball, and each is charged to the
  back-degree `dlt` of its later endpoint (GKS tex:1488-1491).

## The intermediate structure

Deletion is proved against `PAdj` — `DelAdjSt`'s clauses with the
current graph `H` an explicit parameter and an exemption set for the
row being dismantled (`delStar H u T` is `H` minus the `u`–`T` star).
`DelAdjSt G S = PAdj G (deleteVerts G S) S ∅` definitionally-tightly
(`delAdjSt_iff_pAdj`), and one swap-remove moves
`PAdj … (delStar H u T) … {u}` to `T ∪ {w}` (`the delete turn`).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.SplitterBasics (deleteVerts_adj)

/-! ## §1 Names and the scratch descriptor -/

/-- Distance region (levels; sentinel `2R+1`). -/
def plDd : String := "pc.d"
/-- The member stream: the emitted segments, in rank order — also the
BFS queue of the segment being emitted. -/
def plRw : String := "pc.r"
/-- Segment ends: `pc.e[i]` is the stream offset where rank `i`'s
segment begins (`pc.e[N]` the total mass). -/
def plRe : String := "pc.e"
/-- Inverse counts: per member, the number of containing clusters. -/
def plDz : String := "pc.z"
/-- Inverse offsets: prefix sums of `pc.z`. -/
def plIo : String := "pc.o"
/-- Inverse cursors (scatter fill). -/
def plCu : String := "pc.c"
/-- The inverse stream: member-major buckets of containing centres. -/
def plIv : String := "pc.v"
/-- Row fill cursors of the placement pass. -/
def plFl : String := "pc.f"

/-- The eight scratch arrays of the peel pass. -/
def plArrNames : List String := [plDd, plRw, plRe, plDz, plIo, plCu, plIv, plFl]

/-- **The peel's scratch descriptor `Spl`** — length-only, as the frame
seam demands: the eight scratch allocations at the carrier bound `n`,
and the membership allocation `cm` at the mass bound `n²` (the one
allocation `CovPeelIn`'s precondition does not carry). -/
def peelScr (n : ℕ) (cm : ℕ → String) (_j : ℕ) (σ : Env) : Prop :=
  n ≤ (σ.arrs plDd).length ∧ n * n ≤ (σ.arrs plRw).length ∧
  n + 1 ≤ (σ.arrs plRe).length ∧ n ≤ (σ.arrs plDz).length ∧
  n + 1 ≤ (σ.arrs plIo).length ∧ n ≤ (σ.arrs plCu).length ∧
  n * n ≤ (σ.arrs plIv).length ∧ n ≤ (σ.arrs plFl).length ∧
  n * n ≤ (σ.arrs (cm 0)).length

/-! ## §2 The program -/

/-- One turn of the expansion scan over `z`'s live prefix: read the
slot; on an undiscovered target, set its level, lay the first-hit mark
when within radius `R`, and append it to the queue. -/
def peelExpandB (R : ℕ) (ca aj : String) : Com :=
  .seq (.assign "pl.w" (.get aj (.add (.var "pl.a") (.var "pl.j"))))
    (.seq
      (.ite (.eq (.get plDd (.var "pl.w")) (.lit (2 * R + 1)))
        (.seq (.store plDd (.var "pl.w") (.add (.var "pl.d") (.lit 1)))
          (.seq
            (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
              .skip
              (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
                (.store ca (.var "pl.w") (.var "pl.u"))
                .skip))
            (.seq (.store plRw (.var "pl.t") (.var "pl.w"))
              (.assign "pl.t" (.add (.var "pl.t") (.lit 1))))))
        .skip)
      (.assign "pl.j" (.add (.var "pl.j") (.lit 1))))

/-- One BFS pop: read the head vertex and its level; when the level is
below `2R`, scan its live prefix; advance the head. -/
def peelPopB (R : ℕ) (ca ao aj dg : String) : Com :=
  .seq (.assign "pl.z" (.get plRw (.var "pl.h")))
    (.seq (.assign "pl.d" (.get plDd (.var "pl.z")))
      (.seq
        (.ite (.lt (.var "pl.d") (.lit (2 * R)))
          (.seq (.assign "pl.a" (.get ao (.var "pl.z")))
            (.seq (.assign "pl.g" (.get dg (.var "pl.z")))
              (.seq (.assign "pl.j" (.lit 0))
                (.while (.lt (.var "pl.j") (.var "pl.g"))
                  (peelExpandB R ca aj)))))
          .skip)
        (.assign "pl.h" (.add (.var "pl.h") (.lit 1)))))

/-- The seed: the centre off the order region, level `0`, the segment
anchor, the self mark, the two cursors. -/
def peelSeedB (ca od : String) : Com :=
  .seq (.assign "pl.u" (.get od (.var "pl.i")))
    (.seq (.assign "pl.b" (.var "pl.m"))
      (.seq (.store plDd (.var "pl.u") (.lit 0))
        (.seq (.store plRw (.var "pl.m") (.var "pl.u"))
          (.seq
            (.ite (.eq (.get ca (.var "pl.u")) (.var "pl.n"))
              (.store ca (.var "pl.u") (.var "pl.u"))
              .skip)
            (.seq (.assign "pl.h" (.var "pl.m"))
              (.assign "pl.t" (.add (.var "pl.m") (.lit 1))))))))

/-- The touched-cell reset: walk the emitted segment, re-sentinel the
level of each member — `O(|X_u|)`, never `O(N)`. -/
def peelResetB (R : ℕ) : Com :=
  .seq (.assign "pl.k" (.var "pl.b"))
    (.while (.lt (.var "pl.k") (.var "pl.t"))
      (.seq (.store plDd (.get plRw (.var "pl.k")) (.lit (2 * R + 1)))
        (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))

/-- One swap-remove: `u`'s copy at slot `pl.a + pl.j` names the mate
slot `m` inside `w`'s row; move `w`'s last live slot into `m`, repair
the moved copy's mate, shrink `w`'s live prefix. -/
def peelDelTurnB (ao aj dg mt : String) : Com :=
  .seq (.assign "pl.w" (.get aj (.add (.var "pl.a") (.var "pl.j"))))
    (.seq (.assign "pl.p" (.get mt (.add (.var "pl.a") (.var "pl.j"))))
      (.seq (.assign "pl.k"
          (.sub (.add (.get ao (.var "pl.w")) (.get dg (.var "pl.w"))) (.lit 1)))
        (.seq (.assign "pl.y" (.get aj (.var "pl.k")))
          (.seq (.assign "pl.s" (.get mt (.var "pl.k")))
            (.seq (.store aj (.var "pl.p") (.var "pl.y"))
              (.seq (.store mt (.var "pl.p") (.var "pl.s"))
                (.seq (.store mt (.var "pl.s") (.var "pl.p"))
                  (.seq (.store dg (.var "pl.w")
                      (.sub (.get dg (.var "pl.w")) (.lit 1)))
                    (.assign "pl.j" (.add (.var "pl.j") (.lit 1)))))))))))

/-- Delete the centre: one swap-remove per live copy, then kill the
row. -/
def peelDelB (ao aj dg mt : String) : Com :=
  .seq (.assign "pl.a" (.get ao (.var "pl.u")))
    (.seq (.assign "pl.g" (.get dg (.var "pl.u")))
      (.seq (.assign "pl.j" (.lit 0))
        (.seq
          (.while (.lt (.var "pl.j") (.var "pl.g")) (peelDelTurnB ao aj dg mt))
          (.store dg (.var "pl.u") (.lit 0)))))

/-- One rank of the sweep: seed, BFS, reset, segment end, delete. -/
def peelStepB (R : ℕ) (ca ao aj dg mt od : String) : Com :=
  .seq (peelSeedB ca od)
    (.seq (.while (.lt (.var "pl.h") (.var "pl.t")) (peelPopB R ca ao aj dg))
      (.seq (peelResetB R)
        (.seq (.store plRe (.add (.var "pl.i") (.lit 1)) (.var "pl.t"))
          (.seq (.assign "pl.m" (.var "pl.t"))
            (peelDelB ao aj dg mt)))))

/-- The prologue: `N` off the carrier cell, one fused sentinel pass,
the stream anchors. -/
def peelInitB (R : ℕ) (nNs ca : String) : Com :=
  .seq (.assign "pl.n" (.var nNs))
    (.seq (.assign "pl.i" (.lit 0))
      (.seq
        (.while (.lt (.var "pl.i") (.var "pl.n"))
          (.seq (.store plDd (.var "pl.i") (.lit (2 * R + 1)))
            (.seq (.store ca (.var "pl.i") (.var "pl.n"))
              (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))))
        (.seq (.assign "pl.m" (.lit 0))
          (.store plRe (.lit 0) (.lit 0)))))

/-- The sweep loop over the ranks. -/
def peelSweepB (R : ℕ) (ca ao aj dg mt od : String) : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (peelStepB R ca ao aj dg mt od)
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 1: zero the inverse counts. -/
def peelP1B : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.store plDz (.var "pl.i") (.lit 0))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 2: count occurrences over the whole stream. -/
def peelP2B : Com :=
  .seq (.assign "pl.k" (.lit 0))
    (.while (.lt (.var "pl.k") (.var "pl.m"))
      (.seq (.store plDz (.get plRw (.var "pl.k"))
          (.add (.get plDz (.get plRw (.var "pl.k"))) (.lit 1)))
        (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))

/-- Regroup pass 3: prefix-sum the counts into the inverse offsets. -/
def peelP3B : Com :=
  .seq (.store plIo (.lit 0) (.lit 0))
    (.seq (.assign "pl.i" (.lit 0))
      (.while (.lt (.var "pl.i") (.var "pl.n"))
        (.seq (.store plIo (.add (.var "pl.i") (.lit 1))
            (.add (.get plIo (.var "pl.i")) (.get plDz (.var "pl.i"))))
          (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))))

/-- Regroup pass 3b: cursors to the bucket starts. -/
def peelP3bB : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.store plCu (.var "pl.i") (.get plIo (.var "pl.i")))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 4: scatter each segment's pairs into the member-major
buckets — outer loop over ranks, inner over the segment. -/
def peelP4B (od : String) : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.assign "pl.u" (.get od (.var "pl.i")))
        (.seq (.assign "pl.k" (.get plRe (.var "pl.i")))
          (.seq (.assign "pl.g" (.get plRe (.add (.var "pl.i") (.lit 1))))
            (.seq
              (.while (.lt (.var "pl.k") (.var "pl.g"))
                (.seq (.assign "pl.z" (.get plRw (.var "pl.k")))
                  (.seq (.store plIv (.get plCu (.var "pl.z")) (.var "pl.u"))
                    (.seq (.store plCu (.var "pl.z")
                        (.add (.get plCu (.var "pl.z")) (.lit 1)))
                      (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))))
              (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))))))

/-- Regroup pass 5: the output offsets — row `u`'s length is its
segment's, found through the rank region. -/
def peelP5B (co ra : String) : Com :=
  .seq (.store co (.lit 0) (.lit 0))
    (.seq (.assign "pl.i" (.lit 0))
      (.while (.lt (.var "pl.i") (.var "pl.n"))
        (.seq (.assign "pl.k" (.get ra (.var "pl.i")))
          (.seq (.store co (.add (.var "pl.i") (.lit 1))
              (.add (.get co (.var "pl.i"))
                (.sub (.get plRe (.add (.var "pl.k") (.lit 1)))
                  (.get plRe (.var "pl.k")))))
            (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))))

/-- Regroup pass 6: row fill cursors to the row starts. -/
def peelP6B (co : String) : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.store plFl (.var "pl.i") (.get co (.var "pl.i")))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 7: the member-ascending placement — bucket `z` puts
`z` into the next slot of every containing row; rows fill sorted. -/
def peelP7B (cm : String) : Com :=
  .seq (.assign "pl.z" (.lit 0))
    (.while (.lt (.var "pl.z") (.var "pl.n"))
      (.seq (.assign "pl.k" (.get plIo (.var "pl.z")))
        (.seq (.assign "pl.g" (.get plIo (.add (.var "pl.z") (.lit 1))))
          (.seq
            (.while (.lt (.var "pl.k") (.var "pl.g"))
              (.seq (.assign "pl.u" (.get plIv (.var "pl.k")))
                (.seq (.store cm (.get plFl (.var "pl.u")) (.var "pl.z"))
                  (.seq (.store plFl (.var "pl.u")
                      (.add (.get plFl (.var "pl.u")) (.lit 1)))
                    (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))))
            (.assign "pl.z" (.add (.var "pl.z") (.lit 1)))))))

/-- **The peel program**: prologue, sweep, regroup. -/
def peelCom (R : ℕ) (nNs ca co cm ra ao aj dg mt od : String) : Com :=
  .seq (peelInitB R nNs ca)
    (.seq (peelSweepB R ca ao aj dg mt od)
      (.seq peelP1B
        (.seq peelP2B
          (.seq peelP3B
            (.seq peelP3bB
              (.seq (peelP4B od)
                (.seq (peelP5B co ra)
                  (.seq (peelP6B co) (peelP7B cm)))))))))

/-! ## §3 Cell algebra -/

/-- Reading through a store, `getD`-pointwise. -/
theorem getD_set (l : List ℕ) {i : ℕ} (v j : ℕ) (hi : i < l.length) :
    (l.set i v).getD j 0 = if j = i then v else l.getD j 0 := by
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
    rfl
  · rw [if_neg hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (fun h => hj h.symm)]

private theorem evalB_incr {B : ℕ} {x : String} {σ : Env}
    (hx : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var x) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hx)
  simpa using h

/-! ## §4 The star deletion, and the parametric region -/

/-- `H` minus the `u`–`T` star: the graph after the copies of `u`'s
edges into `T` are unlinked.  The deletion loop walks `T` up `u`'s
frozen live prefix. -/
def delStar {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N) (T : Set (Fin N)) :
    SimpleGraph (Fin N) where
  Adj v w := H.Adj v w ∧ ¬(v = u ∧ w ∈ T) ∧ ¬(w = u ∧ v ∈ T)
  symm := by
    intro v w h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    exact ⟨fun v h => H.irrefl h.1⟩

theorem delStar_adj {N : ℕ} {H : SimpleGraph (Fin N)} {u : Fin N}
    {T : Set (Fin N)} {v w : Fin N} :
    (delStar H u T).Adj v w ↔
      H.Adj v w ∧ ¬(v = u ∧ w ∈ T) ∧ ¬(w = u ∧ v ∈ T) := Iff.rfl

theorem delStar_le {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N)
    (T : Set (Fin N)) : delStar H u T ≤ H := by
  intro v w h
  exact h.1

@[simp] theorem delStar_empty {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N) :
    delStar H u (∅ : Set (Fin N)) = H := by
  ext v w
  simp [delStar_adj]

open Classical in
/-- Away from `u`, the star deletion only removes the `u`-edge (when
the row is in `T`). -/
theorem delStar_neighborSet_ne {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N)
    (T : Set (Fin N)) {v : Fin N} (hv : v ≠ u) :
    (delStar H u T).neighborSet v =
      if v ∈ T then H.neighborSet v \ {u} else H.neighborSet v := by
  by_cases hvT : v ∈ T
  · rw [if_pos hvT]
    ext w
    simp only [SimpleGraph.mem_neighborSet, delStar_adj, Set.mem_diff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      refine ⟨h1, fun hw => h3 ⟨hw, hvT⟩⟩
    · rintro ⟨h1, hw⟩
      exact ⟨h1, fun hc => hv hc.1, fun hc => hw hc.1⟩
  · rw [if_neg hvT]
    ext w
    simp only [SimpleGraph.mem_neighborSet, delStar_adj]
    constructor
    · rintro ⟨h1, -, -⟩; exact h1
    · intro h1
      exact ⟨h1, fun hc => hv hc.1, fun hc => hvT hc.2⟩

/-- At `u`, the star deletion removes exactly `T`. -/
theorem delStar_neighborSet_self {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N)
    (T : Set (Fin N)) :
    (delStar H u T).neighborSet u = H.neighborSet u \ T := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, delStar_adj, Set.mem_diff]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, fun hw => h2 ⟨trivial, hw⟩⟩
  · rintro ⟨h1, hw⟩
    refine ⟨h1, fun hc => hw hc.2, fun hc => ?_⟩
    exact H.irrefl (hc.1 ▸ h1)

/-- Killing the whole current star is deleting the vertex. -/
theorem delStar_neighborSet_eq_deleteVerts {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Set (Fin N)) (u : Fin N) {T : Set (Fin N)}
    (hT : ∀ w, (deleteVerts G S).Adj u w → w ∈ T) :
    delStar (deleteVerts G S) u T = deleteVerts G (S ∪ {u}) := by
  ext v w
  rw [delStar_adj, deleteVerts_adj, deleteVerts_adj]
  constructor
  · rintro ⟨⟨hadj, hv, hw⟩, h2, h3⟩
    refine ⟨hadj, ?_, ?_⟩
    · intro hc
      rcases (Set.mem_union _ _ _).mp hc with h | h
      · exact hv h
      · obtain rfl := Set.mem_singleton_iff.mp h
        exact h2 ⟨rfl, hT w ⟨hadj, hv, hw⟩⟩
    · intro hc
      rcases (Set.mem_union _ _ _).mp hc with h | h
      · exact hw h
      · obtain rfl := Set.mem_singleton_iff.mp h
        exact h3 ⟨rfl, hT v ⟨hadj.symm, hw, hv⟩⟩
  · rintro ⟨hadj, hv, hw⟩
    refine ⟨⟨hadj, fun h => hv (Set.mem_union_left _ h),
      fun h => hw (Set.mem_union_left _ h)⟩, ?_, ?_⟩
    · rintro ⟨rfl, -⟩
      exact hv (Set.mem_union_right _ rfl)
    · rintro ⟨rfl, -⟩
      exact hw (Set.mem_union_right _ rfl)

/-- **The parametric region, function level**: `DelAdjSt`'s live-data
clauses over the `getD`-read functions, with the current graph `H`
explicit and the rows of `ex` suspended (their cells hold whatever the
suspension's owner maintains by hand).  `dead` rows are empty; live,
unsuspended rows are exact live prefixes of `H` with consistent
mates. -/
def PAdjF {N : ℕ} (H : SimpleGraph (Fin N)) (dead ex : Set (Fin N))
    (offF AJ MT DG : ℕ → ℕ) : Prop :=
  (∀ v : Fin N, v ∈ dead → DG (v : ℕ) = 0) ∧
  (∀ v : Fin N, v ∉ dead → v ∉ ex → DG (v : ℕ) = (H.neighborSet v).ncard) ∧
  (∀ v : Fin N, v ∉ dead → v ∉ ex → ∀ t : ℕ, t < DG (v : ℕ) →
    ∃ w : Fin N, H.Adj v w ∧ AJ (offF (v : ℕ) + t) = (w : ℕ) ∧
      ∃ s : ℕ, s < DG (w : ℕ) ∧ MT (offF (v : ℕ) + t) = offF (w : ℕ) + s ∧
        AJ (offF (w : ℕ) + s) = (v : ℕ) ∧
        MT (offF (w : ℕ) + s) = offF (v : ℕ) + t) ∧
  (∀ v : Fin N, v ∉ dead → v ∉ ex → ∀ w : Fin N, H.Adj v w →
    ∃ t : ℕ, t < DG (v : ℕ) ∧ AJ (offF (v : ℕ) + t) = (w : ℕ))

/-- **The parametric region, at a pinned offset function**: the offset
head (anchor, degree-sum steps, the `ao` region, the allocations) plus
the function-level clauses at the `getD` reads. -/
def PAdjOff (ao aj dg mt : String) {N : ℕ} (G H : SimpleGraph (Fin N))
    (dead ex : Set (Fin N)) (offF : ℕ → ℕ) (σ : Env) : Prop :=
  offF 0 = 0 ∧
  (∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) ∧
  N + 1 ≤ (σ.arrs ao).length ∧
  (∀ i, i ≤ N → (σ.arrs ao).getD i 0 = offF i) ∧
  offF N ≤ (σ.arrs aj).length ∧
  offF N ≤ (σ.arrs mt).length ∧
  N ≤ (σ.arrs dg).length ∧
  PAdjF H dead ex offF (fun c => (σ.arrs aj).getD c 0)
    (fun c => (σ.arrs mt).getD c 0) (fun c => (σ.arrs dg).getD c 0)

/-- The landed region is the parametric one at `deleteVerts` and no
suspension. -/
theorem delAdjSt_iff_pAdj {ao aj dg mt : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {S : Set (Fin N)} {σ : Env} :
    DelAdjSt ao aj dg mt G S σ ↔
      ∃ offF, PAdjOff ao aj dg mt G (deleteVerts G S) S ∅ offF σ := by
  constructor
  · rintro ⟨offF, h0, hstep, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨offF, h0, hstep, h1, h2, h3, h4, h5, h6,
      fun v hv _ => h7 v hv, fun v hv _ => h8 v hv, fun v hv _ => h9 v hv⟩
  · rintro ⟨offF, h0, hstep, h1, h2, h3, h4, h5, ⟨h6, h7, h8, h9⟩⟩
    exact ⟨offF, h0, hstep, h1, h2, h3, h4, h5, h6,
      fun v hv => h7 v hv (Set.notMem_empty v),
      fun v hv => h8 v hv (Set.notMem_empty v),
      fun v hv => h9 v hv (Set.notMem_empty v)⟩

section PAdjFacts

variable {N : ℕ} {G H : SimpleGraph (Fin N)}
  {dead ex : Set (Fin N)} {offF AJ MT DG : ℕ → ℕ}

/-- A live, unsuspended row enumerates without duplicates —
`DelAdjSt.slot_injOn`'s pigeonhole, at the parametric region. -/
theorem PAdjF.rowInj (h : PAdjF H dead ex offF AJ MT DG)
    {v : Fin N} (hv : v ∉ dead) (hv' : v ∉ ex) {s s' : ℕ}
    (hs : s < DG (v : ℕ)) (hs' : s' < DG (v : ℕ))
    (heq : AJ (offF (v : ℕ) + s) = AJ (offF (v : ℕ) + s')) : s = s' := by
  obtain ⟨-, hdeg, -, hcomp⟩ := h
  have hdv := hdeg v hv hv'
  have h1 : (Fin.val '' (H.neighborSet v)) ⊆
      ↑((Finset.range (DG (v : ℕ))).image
        (fun t => AJ (offF (v : ℕ) + t))) := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨t, ht, hval⟩ := hcomp v hv hv' w hw
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, hval⟩)
  have h2 : DG (v : ℕ) ≤
      ((Finset.range (DG (v : ℕ))).image
        (fun t => AJ (offF (v : ℕ) + t))).card :=
    calc DG (v : ℕ)
        = (H.neighborSet v).ncard := hdv
      _ = (Fin.val '' (H.neighborSet v)).ncard :=
          (Set.ncard_image_of_injective _ Fin.val_injective).symm
      _ ≤ _ := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((Finset.range (DG (v : ℕ))).image
      (fun t => AJ (offF (v : ℕ) + t))).card =
        (Finset.range (DG (v : ℕ))).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_range]; exact h2)
  have hinj := Finset.injOn_of_card_image_eq h3
  exact hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr hs))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hs')) heq

/-- Slot-space room: a slot below a row bound that is itself below the
base degree lands inside the slot space. -/
theorem slot_lt_of_le {v : Fin N} {t : ℕ}
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    (hle : t < (G.neighborSet v).ncard) :
    offF (v : ℕ) + t < offF N := by
  have hlt : offF (v : ℕ) + t < offF ((v : ℕ) + 1) := by
    rw [hstep v]
    omega
  exact lt_of_lt_of_le hlt (offF_mono hstep N le_rfl ((v : ℕ) + 1) v.isLt)

end PAdjFacts

/-! ## §5 The deletion loop's state -/

/-- The processed star: the first `t` values of the frozen prefix. -/
def Tset {N : ℕ} (wfun : ℕ → ℕ) (t : ℕ) : Set (Fin N) :=
  {x | ∃ s, s < t ∧ (x : ℕ) = wfun s}

@[simp] theorem Tset_zero {N : ℕ} (wfun : ℕ → ℕ) :
    Tset (N := N) wfun 0 = ∅ := by
  ext x
  simp [Tset]

theorem mem_Tset_succ {N : ℕ} {wfun : ℕ → ℕ} {t : ℕ} {x : Fin N} :
    x ∈ Tset wfun (t + 1) ↔ x ∈ Tset wfun t ∨ (x : ℕ) = wfun t := by
  constructor
  · rintro ⟨s, hs, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | rfl
    · exact Or.inl ⟨s, h, hx⟩
    · exact Or.inr hx
  · rintro (⟨s, hs, hx⟩ | hx)
    · exact ⟨s, by omega, hx⟩
    · exact ⟨t, by omega, hx⟩

/-- One more processed value refines the star-deleted adjacency by the
single edge `u`–`wfun t`. -/
theorem delStar_Tset_succ_adj {N : ℕ} {H₀ : SimpleGraph (Fin N)} {u : Fin N}
    {wfun : ℕ → ℕ} {t : ℕ} {v x : Fin N} :
    (delStar H₀ u (Tset wfun (t + 1))).Adj v x ↔
      (delStar H₀ u (Tset wfun t)).Adj v x ∧
        ¬(v = u ∧ (x : ℕ) = wfun t) ∧ ¬(x = u ∧ (v : ℕ) = wfun t) := by
  rw [delStar_adj, delStar_adj]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun hc => h2 ⟨hc.1, mem_Tset_succ.mpr (Or.inl hc.2)⟩,
      fun hc => h3 ⟨hc.1, mem_Tset_succ.mpr (Or.inl hc.2)⟩⟩,
      fun hc => h2 ⟨hc.1, mem_Tset_succ.mpr (Or.inr hc.2)⟩,
      fun hc => h3 ⟨hc.1, mem_Tset_succ.mpr (Or.inr hc.2)⟩⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    refine ⟨h1, ?_, ?_⟩
    · rintro ⟨rfl, hmem⟩
      rcases mem_Tset_succ.mp hmem with h | h
      · exact h2 ⟨rfl, h⟩
      · exact h4 ⟨rfl, h⟩
    · rintro ⟨rfl, hmem⟩
      rcases mem_Tset_succ.mp hmem with h | h
      · exact h3 ⟨rfl, h⟩
      · exact h5 ⟨rfl, h⟩

/-- **The `u`-row clauses of the deletion loop**: the still-unprocessed
slots of the frozen prefix read their original values, and each still
carries a consistent mate into its target's live prefix. -/
def URowF {N : ℕ} (u : Fin N) (offF wfun AJ MT DG : ℕ → ℕ)
    (dgu t : ℕ) : Prop :=
  ∀ s : ℕ, t ≤ s → s < dgu →
    AJ (offF (u : ℕ) + s) = wfun s ∧
    ∃ s' : ℕ, s' < DG (wfun s) ∧
      MT (offF (u : ℕ) + s) = offF (wfun s) + s' ∧
      AJ (offF (wfun s) + s') = (u : ℕ) ∧
      MT (offF (wfun s) + s') = offF (u : ℕ) + s

section DeleteTurn

variable {N : ℕ} {G : SimpleGraph (Fin N)} {dead : Set (Fin N)} {u : Fin N}
  {offF wfun AJ MT DG : ℕ → ℕ} {dgu t : ℕ}

/-- A neighbourhood inside `Fin N` has at most `N` members. -/
theorem ncard_neighborSet_le_card {H : SimpleGraph (Fin N)} (v : Fin N) :
    (H.neighborSet v).ncard ≤ N := by
  calc (H.neighborSet v).ncard ≤ (Set.univ : Set (Fin N)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = N := by simp [Set.ncard_univ]

/-- The whole slot space is at most `N²`. -/
theorem offF_le_sq (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    offF N ≤ N * N := by
  suffices h : ∀ i, i ≤ N → offF i ≤ i * N from h N le_rfl
  intro i
  induction i with
  | zero => intro _; simp [h0]
  | succ k ih =>
      intro hk
      have hkN : k < N := hk
      rw [hstep ⟨k, hkN⟩]
      have hval : ((⟨k, hkN⟩ : Fin N) : ℕ) = k := rfl
      rw [hval]
      have h1 := ih (by omega)
      have h2 := ncard_neighborSet_le_card (H := G) ⟨k, hkN⟩
      have : (k + 1) * N = k * N + N := by ring
      omega

/-- Distinct rows occupy disjoint slot ranges. -/
theorem offF_row_ne
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    {v v' : Fin N} (hne : v ≠ v') {a a' : ℕ}
    (ha : a < (G.neighborSet v).ncard) (ha' : a' < (G.neighborSet v').ncard) :
    offF (v : ℕ) + a ≠ offF (v' : ℕ) + a' := by
  have key : ∀ x x' : Fin N, (x : ℕ) < (x' : ℕ) → ∀ {b b' : ℕ},
      b < (G.neighborSet x).ncard → b' < (G.neighborSet x').ncard →
      offF (x : ℕ) + b ≠ offF (x' : ℕ) + b' := by
    intro x x' hlt b b' hb hb'
    have h1 : offF (x : ℕ) + b < offF ((x : ℕ) + 1) := by
      rw [hstep x]; omega
    have h2 : offF ((x : ℕ) + 1) ≤ offF (x' : ℕ) :=
      offF_mono hstep (x' : ℕ) (le_of_lt x'.isLt) ((x : ℕ) + 1) (by omega)
    omega
  rcases Nat.lt_trichotomy (v : ℕ) (v' : ℕ) with h | h | h
  · exact key v v' h ha ha'
  · exact absurd (Fin.ext h) hne
  · exact fun hc => key v' v h ha' ha hc.symm

/-- **The delete turn**: with the region suspended at `u` and the
`u`-row clauses at position `t < dgu`, one swap-remove — read the mate
`p` of `u`'s copy `t`, move the target row's last live slot into `p`,
repair the moved copy's mate, shrink the row — advances the processed
star by `wfun t`.  The machine's five reads are named and bounded, and
the three stores' pointwise effect is exactly the update functions the
conclusion carries. -/
theorem peel_delete_turn
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    (hwN : ∀ s, s < dgu → wfun s < N)
    (hwadj : ∀ s, (hs : s < dgu) → (deleteVerts G dead).Adj u ⟨wfun s, hwN s hs⟩)
    (hwinj : ∀ s, s < dgu → ∀ s', s' < dgu → wfun s = wfun s' → s = s')
    (hdguG : dgu ≤ (G.neighborSet u).ncard)
    (hP : PAdjF (delStar (deleteVerts G dead) u (Tset wfun t)) dead {u} offF AJ MT DG)
    (hU : URowF u offF wfun AJ MT DG dgu t)
    (hdgu : DG (u : ℕ) = dgu)
    (ht : t < dgu) :
    ∃ pv gv yv ysv : ℕ,
      MT (offF (u : ℕ) + t) = pv ∧
      AJ (offF (u : ℕ) + t) = wfun t ∧
      DG (wfun t) = gv ∧ 1 ≤ gv ∧ gv ≤ N ∧
      AJ (offF (wfun t) + (gv - 1)) = yv ∧
      MT (offF (wfun t) + (gv - 1)) = ysv ∧
      pv < offF N ∧ ysv < offF N ∧ offF (wfun t) + (gv - 1) < offF N ∧
      yv < N ∧ (u : ℕ) ≠ wfun t ∧ wfun t < N ∧ pv ≠ ysv ∧
      offF (wfun t) ≤ pv ∧
      PAdjF (delStar (deleteVerts G dead) u (Tset wfun (t + 1))) dead {u} offF
        (fun c => if c = pv then yv else AJ c)
        (fun c => if c = ysv then pv else if c = pv then ysv else MT c)
        (fun c => if c = wfun t then gv - 1 else DG c) ∧
      URowF u offF wfun
        (fun c => if c = pv then yv else AJ c)
        (fun c => if c = ysv then pv else if c = pv then ysv else MT c)
        (fun c => if c = wfun t then gv - 1 else DG c) dgu (t + 1) := by
  classical
  have hP' := hP
  obtain ⟨hdead, hdeg, hsound, hcomp⟩ := hP'
  set H₀ := deleteVerts G dead with hH₀
  set Ht := delStar H₀ u (Tset wfun t) with hHt
  set W : Fin N := ⟨wfun t, hwN t ht⟩ with hW
  have hWval : (W : ℕ) = wfun t := rfl
  have huW : u ≠ W := (hwadj t ht).ne
  have hWu : W ≠ u := huW.symm
  have hne_ut : (u : ℕ) ≠ wfun t := fun h => huW (Fin.ext h)
  have hvalW : ∀ {v : Fin N}, (v : ℕ) = wfun t → v = W :=
    fun {v} h => Fin.ext (h.trans hWval.symm)
  have hWdead : W ∉ dead := ((deleteVerts_adj).mp (hwadj t ht)).2.2
  have hudead : u ∉ dead := ((deleteVerts_adj).mp (hwadj t ht)).2.1
  have hWex : W ∉ ({u} : Set (Fin N)) := by
    simp only [Set.mem_singleton_iff]
    exact hWu
  have hWT : W ∉ Tset wfun t := by
    rintro ⟨s, hs, hval⟩
    have := hwinj t ht s (by omega) (by exact hval)
    omega
  -- degrees below the base graph
  have hHtG : ∀ {a b : Fin N}, Ht.Adj a b → G.Adj a b := by
    intro a b h
    exact (deleteVerts_le G dead) ((delStar_le H₀ u _) h)
  have hHtdead : ∀ {a b : Fin N}, Ht.Adj a b → b ∉ dead := by
    intro a b h
    exact ((deleteVerts_adj).mp ((delStar_le H₀ u _) h)).2.2
  have hDGle : ∀ v : Fin N, v ∉ dead → v ≠ u →
      DG (v : ℕ) ≤ (G.neighborSet v).ncard := by
    intro v hv hv'
    rw [hdeg v hv (by simpa using hv')]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro w hw
    exact hHtG hw
  have hrne : ∀ (a b : Fin N), a ≠ b → ∀ {c c' : ℕ},
      c < (G.neighborSet a).ncard → c' < (G.neighborSet b).ncard →
      offF (a : ℕ) + c ≠ offF (b : ℕ) + c' :=
    fun a b hab {c c'} hc hc' => offF_row_ne hstep hab hc hc'
  -- the mate of u's copy t
  obtain ⟨hAJut, s', hs'g, hMTut, hAJp, hMTp⟩ := hU t le_rfl ht
  set gv := DG (wfun t) with hgv
  have hg1 : 1 ≤ gv := by omega
  have hgleG : gv ≤ (G.neighborSet W).ncard := hDGle W hWdead hWu
  have hgN : gv ≤ N := le_trans hgleG (ncard_neighborSet_le_card W)
  have hs'G : s' < (G.neighborSet W).ncard := lt_of_lt_of_le hs'g hgleG
  set pv := offF (wfun t) + s' with hpv
  -- the last live slot of W's row and its data
  have hlastg : gv - 1 < gv := by omega
  have hlastG : gv - 1 < (G.neighborSet W).ncard := lt_of_lt_of_le hlastg hgleG
  have hWTsucc : W ∈ Tset wfun (t + 1) := mem_Tset_succ.mpr (Or.inr rfl)
  obtain ⟨y, hHtWy, hAJlast, s'', hs''lt, hMTlast, hAJys, hMTys⟩ :=
    hsound W hWdead hWex (gv - 1) (by omega)
  set lastv := offF (wfun t) + (gv - 1) with hlastv
  set ysv := offF (y : ℕ) + s'' with hysv
  have hydead : y ∉ dead := hHtdead hHtWy
  have hyW : y ≠ W := (SimpleGraph.Adj.ne hHtWy).symm
  have hyWv : (y : ℕ) ≠ wfun t := fun h => hyW (hvalW h)
  -- range facts
  have hpvlt : pv < offF N := by
    rw [hpv, ← hWval]
    exact slot_lt_of_le hstep hs'G
  have hlastlt' : lastv < offF N := by
    rw [hlastv, ← hWval]
    exact slot_lt_of_le hstep hlastG
  have hs''G : s'' < (G.neighborSet y).ncard := by
    by_cases hyu : y = u
    · subst hyu
      rw [hdgu] at hs''lt
      exact lt_of_lt_of_le hs''lt hdguG
    · exact lt_of_lt_of_le hs''lt (hDGle y hydead hyu)
  have hysvlt : ysv < offF N := by
    rw [hysv]
    exact slot_lt_of_le hstep hs''G
  have hyvN : AJ lastv < N := by
    rw [hAJlast]
    exact y.isLt
  have hpvne_ysv : pv ≠ ysv := by
    rw [hpv, hysv, ← hWval]
    exact hrne W y hyW.symm hs'G hs''G
  -- the mate of u's copy t sits in W's live row
  have hpv_lo : offF (wfun t) ≤ pv := by
    rw [hpv]
    omega
  -- abbreviations for the update functions
  set AJ' : ℕ → ℕ := fun c => if c = pv then AJ lastv else AJ c with hAJ'
  set MT' : ℕ → ℕ := fun c => if c = ysv then pv else if c = pv then ysv else MT c
    with hMT'
  set DG' : ℕ → ℕ := fun c => if c = wfun t then gv - 1 else DG c with hDG'
  -- membership of the refined star, and the refined neighbourhoods
  have hTT : ∀ {v : Fin N}, v ≠ W →
      (v ∈ Tset wfun (t + 1) ↔ v ∈ Tset wfun t) := by
    intro v hv
    constructor
    · intro h
      exact (mem_Tset_succ.mp h).resolve_right fun hc => hv (hvalW hc)
    · intro h
      exact mem_Tset_succ.mpr (Or.inl h)
  have hnb_ne : ∀ {v : Fin N}, v ≠ u → v ≠ W →
      (delStar H₀ u (Tset wfun (t + 1))).neighborSet v = Ht.neighborSet v := by
    intro v hvu hvW
    rw [hHt, delStar_neighborSet_ne H₀ u _ hvu, delStar_neighborSet_ne H₀ u _ hvu,
      if_congr (hTT hvW) rfl rfl]
  have hnbW : (delStar H₀ u (Tset wfun (t + 1))).neighborSet W =
      H₀.neighborSet W \ {u} := by
    rw [delStar_neighborSet_ne H₀ u _ hWu, if_pos hWTsucc]
  have hnbWt : Ht.neighborSet W = H₀.neighborSet W := by
    rw [hHt, delStar_neighborSet_ne H₀ u _ hWu, if_neg hWT]
  have huWmem : u ∈ H₀.neighborSet W := (hwadj t ht).symm
  have hdegW : gv = (H₀.neighborSet W).ncard := by
    rw [hgv, ← hWval, hdeg W hWdead hWex, hnbWt]
  have hdegW' : ((delStar H₀ u (Tset wfun (t + 1))).neighborSet W).ncard =
      gv - 1 := by
    rw [hnbW, Set.ncard_diff_singleton_of_mem huWmem, ← hdegW]
  -- the refined adjacency, forward and backward
  have hadj_succ : ∀ {v x : Fin N},
      (delStar H₀ u (Tset wfun (t + 1))).Adj v x ↔
        Ht.Adj v x ∧ ¬(v = u ∧ (x : ℕ) = wfun t) ∧ ¬(x = u ∧ (v : ℕ) = wfun t) :=
    fun {v x} => delStar_Tset_succ_adj
  -- ===== the case split: is the mate slot the last slot? =====
  refine ⟨pv, gv, AJ lastv, ysv, hMTut, hAJut, rfl, hg1, hgN, rfl, hMTlast,
    hpvlt, hysvlt, hlastlt', hyvN, hne_ut, hwN t ht, hpvne_ysv, hpv_lo, ?_, ?_⟩
  all_goals sorry

end DeleteTurn

end Lax3Proofs.Prog
