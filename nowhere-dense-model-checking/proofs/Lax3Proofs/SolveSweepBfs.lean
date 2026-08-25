import Lax3Proofs.SolveSweepRun

/-!
# F6c12 (residual 4-i-a) — one centre's frontier BFS

`SolveSweepRun` reduces the peel sweep to a single named residual,
`PeelBfsIn` (`SolveSweepRun.lean:554`): one centre's turn, at the loop
state's two consecutive mark indices. This file owns that turn's
*program* and the accounting that prices it.

## The two program constraints, and how the shape enforces them

Both are invisible in `PeelBfsIn`'s `Spec` and are the reason the
budget closes at all (`SolveSweepPeel`'s Finding 2, restated on the
residual):

1. **The BFS must not expand its final level.** The edge summand is
   `cbf·Σ_{w ∈ X_u} d_<(w)`, which by `sum_induced_deg_le_two_sum_dlt`
   pays for the edges *inside* `X_u` and for nothing else; expanding a
   vertex at distance exactly `2R` reads rows whose far endpoint may
   leave `X_u`. Here the constraint is **structural, not a guard**:
   `bfsTurnCom` is `2·R` sequential level passes
   (`iterCom S.R (bfsLevelCom … true)` then
   `iterCom S.R (bfsLevelCom … false)`), so a vertex discovered at
   distance `2R` is discovered *by* the last pass and there is no pass
   left to expand it. `bfsCells_le_edgeTerm` (§3) is the price of the
   passes that do run, and it is stated at exactly the hypothesis the
   shape gives: every expanded vertex lies in `ball H r u` with
   `r + 1 ≤ 2·R`.
2. **Visited marks are cleared by re-walking the pass's own reached
   list.** `bfsClearCom` (§4) walks `lm[b .. b + cnt)` — the row the
   pass has just emitted, which *is* its reached list — and zeroes
   `co` at each entry, at `14·cnt + 6`. No carrier pass: the sweep's
   one permitted `Θ(N)` pass is `sweepInitCom`, spent once, before the
   loop.

Unrolling the level count also removes a word-bound obligation that a
level *counter* would have created: `2·S.R` is a constant of the
setup, and nothing in `mcD`/`mcB` bounds it by the input's length, so
`.lit (2 * S.R)` could not be evaluated at `mcB q x`. The unrolled
program's only literals are `0` and `1`.

## Where the marks and the row live

`SweepSt` carries `co` as an allocation and *nothing else*
(`A.N + 1 ≤ |co|`), so the visited marks go there and the pass owes
their clean-up to itself: the scratch descriptor `Ssc` a discharger
picks is where "`co` is clean" belongs (Hazard 6 — an allocation
clause in a state is a binding requirement, and here it is also the
only free space). The reached list is not a separate queue: it is the
log row itself, `lm[b .. b + cnt)` with `b = lo["sw.i"]`, and the
frontier's head is an index into it. That is why `Lib.Queue` is not
used — its relation pins the *whole* backing array (`Queue.arr`), and
`lm` holds every earlier row below `b`.

## What is proved here

* **§2** the program: `bfsPushCom`, `bfsScanCom`, `bfsLevelCom`,
  `iterCom`, `bfsInitCom`, `bfsEmitCom`, `bfsClearCom`, `bfsTurnCom`.
* **§3** `bfsCells_le_edgeTerm` — **the `cbf` term, and it is the
  frontier's own edge budget**: if every expanded vertex lies within
  `r` of the centre in the current structure and `r + 1 ≤ 2·R`, the
  live rows those vertices read total at most
  `2·Σ_{w ∈ X_u} d_<(w)`, which is `peelTurn`'s third summand at
  `cbf = 2·(cost of one cell)`. Nothing here is fitted: the `2` is
  `sum_induced_deg_le_two_sum_dlt`'s, charging each induced edge in
  the `N_<`-list of its `π`-later endpoint. `ball_succ` and
  `cluster_eq_expand_of_ball` turn the first program constraint into
  an identity — the cluster **is** the one-step expansion of the set
  the passes expand — and `bfsExpanded_le_edgeTerm` is the bill for
  that set, with `1 ≤ S.R` (Hazard 3) its only input.
* **§4** `bfsClear_spec` — the clean-up walk, with its accounting, at
  `14·cnt + 6`.
* **§5** `ctrPart_succ_of_ball`, `logPart_succ_of_row`,
  `sweepSt_step_of_bfs` — the state step. From the pass's exit data
  (which cells of the `R`-ball it wrote, the row's contents, the two
  offsets) the loop state moves from mark index `i` to `i + 1`, one
  obligation per clause, through `centre_eq_iff_first_hit`,
  `ctrPart_succ` and `logPart_succ`. `bfsRow_fits` is Hazard 6's
  concrete clause (`peelOff (i+1) ≤ |lm|`) and `bfsEmit_spec` the
  offset write, which happens for the empty ball too.
* **§6** `bfsTurn_warrs`, `bfsTurn_wvars` — the turn's frame. It
  writes four arrays (`ca`, `co`, `lo`, `lm`) and ten scalars, all in
  the `bf.` family; in particular it does **not** write `"sw.i"` or
  `"sw.v"`, which `PeelBfsIn`'s postcondition demands back unchanged,
  nor the adjacency region, which is what leaves `DelAdjSt` standing.
* **§7** `BfsClean`, `bfsClean_hSsc` — the scratch descriptor, and the
  check that it satisfies `peelSweepIn_of_bfs`'s `hSsc` verbatim. The
  choice of `Ssc` is a design decision here, not an integration debt.

## The three constants, and what they are not

Read off the program text at the `Run` cost model — a `store` is
`1 + |index| + |value|`, an `assign` `1 + |value|`, a loop turn
`1 + |test| + body`:

* `abf = 12·R + 44` — the initial push (`29`), `2·R` level-pass
  prologues and exits (`6` each), the two `iterCom` tails (`2`), the
  offset write (`7`), the clean-up's constant (`6`).
* `bbf = 39` — `25` per expanded vertex (its row read, the head bump,
  the level loop's turn) and `14` per reached vertex in the clean-up.
  A vertex at distance exactly `2·R` pays only the `14`.
* `cbf = 76 = 2·38` — `38` is one adjacency cell in a *marking* level
  pass (the neighbour read `5`, the visited test and its push `25`,
  the cursor bump `4`, the loop's turn `4`); a plain pass costs `31`
  and the marking figure is the one taken. The `2` is §3's.

**These are the figures the shape yields, not a proved bound**: the
loop that would discharge them is not written, so nothing in this file
asserts `PeelBfsIn` at them. `bfsClear_spec`'s `14·cnt + 6` is the one
of them that *is* proved, against its own program.

## What remains

The frontier loop's own `Spec`: that `bfsInitCom` followed by
`iterCom R (bfsLevelCom … true)` and `iterCom R (bfsLevelCom … false)`
leaves `bf.c` at `|X_u|`, `lm[b .. b + cnt)` enumerating
`ball H (2R) u` — which is `X_u` by `cluster_eq_ball_peelSet` — with
`co` set exactly on it and the first-hit marks written into the cells
of `ball H R u` that failed the stamp test. Everything that loop must
*produce* is pinned by §5, everything it may *spend* by §3 and §4, and
its frame by §6; what is missing is the induction over levels that
identifies the reached list with the ball, and with it the
duplicate-freeness (a vertex is pushed only when `co` reads `0`) that
makes `cnt = |X_u|` rather than merely `≥`. `PeelBfsIn` is therefore
**not** discharged here.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax12.ColoringNumbers
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.WalkDistance

/-! ## §1 Reading a cell that is in range

`evalB_get` asks for `l[k]? = some v`; every region in play states its
contents with `getD`. -/

/-- An in-range `getD` read as the `getElem?` the evaluator wants. -/
theorem getElem?_of_lt {l : List ℕ} {k : ℕ} (h : k < l.length) :
    l[k]? = some (l.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-! ## §2 The program

Scratch scalars, all four characters and all in the `bf.` family so
that no landed pass's frame condition has to be re-read: `bf.b` the
row's base offset, `bf.c` the reached count, `bf.h` the frontier head,
`bf.e` the current level's end, `bf.v` the vertex being expanded,
`bf.o` and `bf.n` its live row's offset and length, `bf.t` the cursor
into that row, `bf.w` the neighbour, `bf.k` the clean-up cursor.

`"sw.i"` (the rank) and `"sw.v"` (the centre) are the sweep's own and
are read, never written. -/

/-- **A push**: mark the vertex in `bf.w` visited, append it to the
row, and — in a *marking* level pass only — claim it for the centre if
it is not already claimed.

The claim test is `ca[w] < nn`, `CtrPart.lt_iff`'s exact stamp test
(Hazard 5: no disequality, so the sentinel `A.N` and the sharpened
"every cell `≤ A.N`" invariant are what make an order test a
"has this been claimed?" test). Its *true* branch is `skip`: an
already-claimed cell is left alone, which is first-assignment-wins
(`centre_eq_iff_first_hit`) as one line of program. -/
def bfsPushCom (ca co lm nn : String) (mark : Bool) : Com :=
  .seq (.store co (.var "bf.w") (.lit 1))
    (.seq (.store lm (.add (.var "bf.b") (.var "bf.c")) (.var "bf.w"))
      (.seq (.assign "bf.c" (.add (.var "bf.c") (.lit 1)))
        (if mark then
            .ite (.lt (.get ca (.var "bf.w")) (.var nn)) .skip
              (.store ca (.var "bf.w") (.var "sw.v"))
          else .skip)))

/-- **One vertex's expansion**: read the live row of `bf.v` — offset
`ao[v]`, length `dg[v]`, `DelAdjSt`'s live prefix — and push every
neighbour not already visited. `co[w] < 1` is the visited test, exact
against the invariant "every `co` cell is `0` or `1`". -/
def bfsScanCom (ca co ao aj dg lm nn : String) (mark : Bool) : Com :=
  .seq (.assign "bf.o" (.get ao (.var "bf.v")))
    (.seq (.assign "bf.n" (.get dg (.var "bf.v")))
      (.seq (.assign "bf.t" (.lit 0))
        (.while (.lt (.var "bf.t") (.var "bf.n"))
          (.seq (.assign "bf.w" (.get aj (.add (.var "bf.o") (.var "bf.t"))))
            (.seq (.ite (.lt (.get co (.var "bf.w")) (.lit 1))
                    (bfsPushCom ca co lm nn mark) .skip)
              (.assign "bf.t" (.add (.var "bf.t") (.lit 1))))))))

/-- **One level pass**: freeze the current level's end at the reached
count, then expand every vertex from the head to that end. Vertices
pushed during the pass land above `bf.e` and are therefore *not*
expanded by it — that is the level discipline, and it is why the last
pass discovers distance `2R` without reading its rows. -/
def bfsLevelCom (ca co ao aj dg lm nn : String) (mark : Bool) : Com :=
  .seq (.assign "bf.e" (.var "bf.c"))
    (.while (.lt (.var "bf.h") (.var "bf.e"))
      (.seq (.assign "bf.v" (.get lm (.add (.var "bf.b") (.var "bf.h"))))
        (.seq (bfsScanCom ca co ao aj dg lm nn mark)
          (.assign "bf.h" (.add (.var "bf.h") (.lit 1))))))

/-- `k` copies of a command in sequence. The level count is a constant
of the setup, so the passes are unrolled rather than counted; see the
module docstring for the word-bound reason. -/
def iterCom : ℕ → Com → Com
  | 0, _ => .skip
  | (k + 1), c => .seq c (iterCom k c)

@[simp] theorem iterCom_zero (c : Com) : iterCom 0 c = .skip := rfl

@[simp] theorem iterCom_succ (k : ℕ) (c : Com) :
    iterCom (k + 1) c = .seq c (iterCom k c) := rfl

/-- **The initial push**: anchor the row at `lo["sw.i"]`, empty the
frontier, and push the centre itself as the level-`0` frontier. The
centre is at distance `0 ≤ R`, so its push marks. -/
def bfsInitCom (ca co lo lm nn : String) : Com :=
  .seq (.assign "bf.b" (.get lo (.var "sw.i")))
    (.seq (.assign "bf.c" (.lit 0))
      (.seq (.assign "bf.h" (.lit 0))
        (.seq (.assign "bf.w" (.var "sw.v"))
          (bfsPushCom ca co lm nn true))))

/-- **The offset write**: row `i` ends where it started plus what was
reached, and that is row `i + 1`'s anchor. Emitted for *every* centre,
the empty ball included — `LogPart`'s offsets are anchored per rank,
not per nonempty rank. -/
def bfsEmitCom (lo : String) : Com :=
  .store lo (.add (.var "sw.i") (.lit 1)) (.add (.var "bf.b") (.var "bf.c"))

/-- **The clean-up**: re-walk the row just emitted and zero `co` at
each of its entries. This is the second program constraint in one
loop — the marks are cleared from the pass's own reached list, never
by a pass over the carrier. -/
def bfsClearCom (co lm : String) : Com :=
  .seq (.assign "bf.k" (.lit 0))
    (.while (.lt (.var "bf.k") (.var "bf.c"))
      (.seq (.store co (.get lm (.add (.var "bf.b") (.var "bf.k"))) (.lit 0))
        (.assign "bf.k" (.add (.var "bf.k") (.lit 1)))))

/-- **One centre's turn.** The initial push, `R` marking level passes,
`R` plain level passes, the offset write, the clean-up.

`2·R` passes and no more: the vertices at distance `2R` are pushed by
the last plain pass and expanded by nobody. The adjacency region is
read and never written — the delete that follows in the same turn is
`sweepBodyCom`'s business, not this pass's. -/
def bfsTurnCom (R : ℕ) (ca co ao aj dg lo lm nn : String) : Com :=
  .seq (bfsInitCom ca co lo lm nn)
    (.seq (iterCom R (bfsLevelCom ca co ao aj dg lm nn true))
      (.seq (iterCom R (bfsLevelCom ca co ao aj dg lm nn false))
        (.seq (bfsEmitCom lo) (bfsClearCom co lm))))

/-! ## §3 The edge term — what `cbf` buys

The frontier BFS reads exactly the live rows of the vertices it
expands. §3 prices those rows in `peelTurn`'s own third figure, and
the hypothesis it needs is precisely the first program constraint:
every expanded vertex is within `r` of the centre in the current
structure, with `r + 1 ≤ 2·R`. `bfsTurnCom` gives it by construction —
there are `2·R` level passes, so the deepest vertex any of them
expands sits at distance `2·R - 1`. -/

variable {L n₀ Λ : ℕ}

open Classical in
/-- **The pass's adjacency cells are the frontier's own edge budget.**
With `H` the current (peeled) structure at `u`'s rank and `E` any set
of vertices each within `r` of `u`, `r + 1 ≤ 2·R`, the live rows of
`E` total at most `2·Σ_{w ∈ X_u} d_<(w)` — `peelTurn`'s third summand
at `c = 2`.

Two steps and no slack in either. The neighbours of an expanded vertex
are within `r + 1 ≤ 2·R`, so every cell read is an `H`-edge with
*both* endpoints in `X_u` (`cluster_eq_ball_peelSet`: the `2R`-ball
**is** the cluster); and an induced edge set counted from both ends is
`sum_induced_deg_le_two_sum_dlt`, which charges each edge once in the
`N_<`-list of its `π`-later endpoint. The factor `2` is that lemma's
and is the only one.

This is the hypothesis the *program* discharges structurally: a
guard-free `2·R`-fold unrolling cannot expand distance `2R`. Were the
last level expanded, `r + 1 ≤ 2·R` would fail and the cells of edges
leaving `X_u` would be unpaid — there is no term in `peelK` for
them. -/
theorem bfsCells_le_edgeTerm (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (E : Finset (Fin A.N)) (r : ℕ)
    (hr : r + 1 ≤ 2 * S.R)
    (hE : ∀ v ∈ E,
      v ∈ ball (deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))) r u) :
    ∑ v ∈ E,
        ((deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))).neighborSet v).ncard
      ≤ 2 * ∑ w ∈ Finset.univ.filter (fun w => w ∈ cluster S A π u),
          Impl.dlt A.G π w := by
  classical
  set H := deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ)) with hHdef
  set X : Finset (Fin A.N) :=
    Finset.univ.filter (fun z => z ∈ cluster S A π u) with hXdef
  have hball : cluster S A π u = ball H (2 * S.R) u :=
    cluster_eq_ball_peelSet S A π u
  -- an expanded vertex is itself in the cluster
  have hEX : E ⊆ X := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hball]
    exact ball_mono_radius H u (by omega) (hE v hv)
  -- and so is every current neighbour of one
  have hnb : ∀ v ∈ E, ∀ z : Fin A.N, H.Adj v z → z ∈ cluster S A π u := by
    intro v hv z hz
    rw [hball]
    exact withinDist_mono_radius hr
      (withinDist_trans (mem_ball.mp (hE v hv)) (withinDist_of_adj hz))
  -- so a live row is exactly the induced row inside the cluster
  have hrow : ∀ v ∈ E,
      (H.neighborSet v).ncard = (X.filter (fun z => H.Adj v z)).card := by
    intro v hv
    rw [ncard_eq_card_univ_filter]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hXdef,
      SimpleGraph.mem_neighborSet]
    exact ⟨fun hz => ⟨hnb v hv z hz, hz⟩, fun hz => hz.2⟩
  calc ∑ v ∈ E, (H.neighborSet v).ncard
      = ∑ v ∈ E, (X.filter (fun z => H.Adj v z)).card :=
        Finset.sum_congr rfl hrow
    _ ≤ ∑ v ∈ X, (X.filter (fun z => H.Adj v z)).card :=
        Finset.sum_le_sum_of_subset hEX
    _ ≤ 2 * ∑ v ∈ X, Impl.dlt A.G π v :=
        sum_induced_deg_le_two_sum_dlt (deleteVerts_le A.G _) π X

open Classical in
/-- **`cbf = 2·f`**, where `f` is what one adjacency cell costs the
scan. The edge summand of `peelTurn S A π abf bbf (2·f) i` is exactly
`f` times the cells `bfsCells_le_edgeTerm` counts, so the constant is
read off the program's inner body and nothing is fitted. -/
theorem bfsCells_cost_le_edgeTerm (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (E : Finset (Fin A.N)) (r f : ℕ)
    (hr : r + 1 ≤ 2 * S.R)
    (hE : ∀ v ∈ E,
      v ∈ ball (deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))) r u) :
    f * ∑ v ∈ E,
        ((deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))).neighborSet v).ncard
      ≤ (2 * f) * ∑ w ∈ Finset.univ.filter (fun w => w ∈ cluster S A π u),
          Impl.dlt A.G π w := by
  calc f * ∑ v ∈ E, _ ≤ f * (2 * ∑ w ∈ Finset.univ.filter
          (fun w => w ∈ cluster S A π u), Impl.dlt A.G π w) :=
        Nat.mul_le_mul_left _ (bfsCells_le_edgeTerm S A π u E r hr hE)
    _ = (2 * f) * ∑ w ∈ Finset.univ.filter (fun w => w ∈ cluster S A π u),
          Impl.dlt A.G π w := by ring

/-! ### The level identity, and the last level

One level pass is exactly one radius: the reached set after `k + 1`
passes is the reached set after `k` together with the neighbours of
what `k` reached. So `bfsTurnCom`'s `2·R` passes reach
`ball H (2·R) u`, which is the cluster, while the vertices they
*expand* are `ball H (2·R - 1) u` — one radius short. That gap is the
first program constraint, and `cluster_eq_expand_of_ball` states it as
an identity rather than a side condition: the cluster **is** the
one-step expansion of the expanded set, so a pass that expanded the
last level would be reading rows for a level nobody needs. -/

/-- **One level pass is one radius.** -/
theorem ball_succ {V : Type*} (H : SimpleGraph V) (k : ℕ) (u : V) :
    ball H (k + 1) u = ball H k u ∪ {z | ∃ v ∈ ball H k u, H.Adj v z} := by
  ext z
  simp only [Set.mem_union, Set.mem_setOf_eq, mem_ball]
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := withinDist_symm hz
    cases p with
    | nil => exact Or.inl (withinDist_refl H k _)
    | cons h q =>
        exact Or.inr ⟨_, withinDist_symm ⟨q, by simpa using hp⟩, h.symm⟩
  · rintro (h | ⟨v, hv, hadj⟩)
    · exact withinDist_mono_radius (Nat.le_succ k) h
    · exact withinDist_trans hv (withinDist_of_adj hadj)

/-- **The cluster is the expansion of what the pass expands.** At
`1 ≤ S.R` (Hazard 3 — `S.R = 0` makes `2·R - 1` and `2·R` collide, and
the identity is then false), the emitted `2R`-ball is the `2R-1`-ball
together with its neighbours. The program expands the second set and
emits the first; the vertices of the difference are pushed by the last
level pass and read by nobody. -/
theorem cluster_eq_expand_of_ball {L n₀ Λ : ℕ} (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (hR : 1 ≤ S.R) :
    cluster S A π u =
      ball (deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))) (2 * S.R - 1) u ∪
        {z | ∃ v ∈ ball (deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ)))
          (2 * S.R - 1) u,
          (deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))).Adj v z} := by
  rw [cluster_eq_ball_peelSet]
  obtain ⟨r, hr⟩ : ∃ r, 2 * S.R = r + 1 := ⟨2 * S.R - 1, by omega⟩
  have hrv : 2 * S.R - 1 = r := by omega
  rw [hrv, hr, ball_succ]

open Classical in
/-- **The pass's own bill.** The set `bfsTurnCom` expands is
`ball H (2R-1) u`, and §3 prices exactly that set: the live rows it
reads total at most `2·Σ_{w ∈ X_u} d_<(w)`, `peelTurn`'s third summand
at `c = 2`. This is `cbf`'s justification with no hypothesis left
open — `1 ≤ S.R` is the only input, and it is already an explicit
hypothesis upstream (`peelSweepIn_of_bfs`'s `hR`). -/
theorem bfsExpanded_le_edgeTerm {L n₀ Λ : ℕ} (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (hR : 1 ≤ S.R) :
    ∑ v ∈ Finset.univ.filter (fun v => v ∈
        ball (deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))) (2 * S.R - 1) u),
        ((deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))).neighborSet v).ncard
      ≤ 2 * ∑ w ∈ Finset.univ.filter (fun w => w ∈ cluster S A π u),
          Impl.dlt A.G π w :=
  bfsCells_le_edgeTerm S A π u _ (2 * S.R - 1) (by omega)
    (fun _ hv => (Finset.mem_filter.mp hv).2)

/-! ## §4 The clean-up, and its accounting

The second program constraint. `co` arrives clean, is set on exactly
the reached vertices, and must leave clean — `SweepSt` carries `co` as
an allocation with no content clause, so the *pass* owns the marks
from end to end and cannot borrow a clean array from the loop. Clearing
them by a carrier pass would be `Θ(N)` per centre and `Θ(N²)` over the
sweep, and `peelK` has no such term; so the walk is over the pass's own
reached list, which is the row it has just written.

The invariant is the one that makes that work: a cell is either already
zero or still owed by an entry the cursor has not passed. At the exit
the cursor is at the count, no entry is left, and every cell is zero —
without any statement about which cells were ever set, and in
particular without a second pass to find them. -/

/-- **The clean-up walk's invariant.** `row` names the entries of the
emitted row; the last clause is the accounting: every `co` cell is
zero *or* is claimed by an entry at or above the cursor. -/
def BfsClearInv (co lm : String) (N base cnt : ℕ) (row : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "bf.b" = base ∧ σ.vars "bf.c" = cnt ∧ σ.vars "bf.k" ≤ cnt ∧
  N ≤ (σ.arrs co).length ∧
  (∀ k, k < cnt →
    base + k < (σ.arrs lm).length ∧ (σ.arrs lm).getD (base + k) 0 = row k) ∧
  (∀ k, k < cnt → row k < N) ∧
  (∀ v, v < N → (σ.arrs co).getD v 0 = 0 ∨
    ∃ k, σ.vars "bf.k" ≤ k ∧ k < cnt ∧ row k = v)

/-- **The clean-up walk.** From the invariant with the cursor zeroed —
which is what "the marks stand on the row's entries and nowhere else"
comes to — `bfsClearCom` leaves every carrier cell of `co` at zero, at
`14·cnt + 6`.

Linear in the count and in nothing else: this is the whole of the
second constraint, and `cnt = |X_u|` rides in `peelTurn`'s mass
summand `bbf·|X_u|` with `14` of `bbf`. A carrier clear would have
asked for a term in `A.N` per centre, which is `peelK`'s missing
`N²`. -/
theorem bfsClear_spec {co lm : String} (hne : co ≠ lm) {B N base cnt : ℕ}
    {row : ℕ → ℕ} (hNB : N < B) (hbc : base + cnt < B) (h1B : 1 < B) :
    Spec B (fun σ => BfsClearInv co lm N base cnt row (σ.setVar "bf.k" 0))
      (bfsClearCom co lm)
      (fun _ σ' => (∀ v, v < N → (σ'.arrs co).getD v 0 = 0) ∧
        BfsClearInv co lm N base cnt row σ' ∧ σ'.vars "bf.k" = cnt)
      (14 * cnt + 6) := by
  -- the body: zero the cell named by the entry under the cursor, bump
  have hbody : Spec B
      (fun σ => BfsClearInv co lm N base cnt row σ ∧ σ.vars "bf.k" < cnt)
      (.seq (.store co (.get lm (.add (.var "bf.b") (.var "bf.k"))) (.lit 0))
        (.assign "bf.k" (.add (.var "bf.k") (.lit 1))))
      (fun σ σ' => BfsClearInv co lm N base cnt row σ' ∧
        σ'.vars "bf.k" = σ.vars "bf.k" + 1) 10 := by
    have hst : Spec B
        (fun σ => BfsClearInv co lm N base cnt row σ ∧ σ.vars "bf.k" < cnt)
        (.store co (.get lm (.add (.var "bf.b") (.var "bf.k"))) (.lit 0))
        (fun σ σ' => σ' = σ.setArr co (row (σ.vars "bf.k")) 0) (1 + 4 + 1) := by
      refine Spec.store (idx := fun σ => row (σ.vars "bf.k")) (f := fun _ => 0)
        (fun σ hσ => ?_) (fun _ _ => evalB_lit (by omega)) (fun σ hσ => ?_)
      · obtain ⟨⟨hb, hc, hkle, hcolen, hlm, hrowN, -⟩, hk⟩ := hσ
        obtain ⟨hlen, hval⟩ := hlm _ hk
        refine evalB_get (k := base + σ.vars "bf.k") ?_ ?_ ?_
        · have := evalB_bin (B := B) (op := .add) (evalB_var (x := "bf.b")
            (σ := σ) (by omega)) (evalB_var (x := "bf.k") (σ := σ) (by omega))
            (show σ.vars "bf.b" + σ.vars "bf.k" < B by omega)
          rw [hb] at this
          exact this
        · rw [getElem?_of_lt hlen, hval]
        · exact lt_trans (hrowN _ hk) hNB
      · obtain ⟨⟨-, -, -, hcolen, -, hrowN, -⟩, hk⟩ := hσ
        exact lt_of_lt_of_le (hrowN _ hk) hcolen
    have has : Spec B (fun τ => τ.vars "bf.k" + 1 < B)
        (.assign "bf.k" (.add (.var "bf.k") (.lit 1)))
        (fun τ τ' => τ' = τ.setVar "bf.k" (τ.vars "bf.k" + 1)) (1 + 3) :=
      Spec.assign (fun _ hτ =>
        evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hτ))
    refine (Spec.seq hst has ?_ ?_).mono (by omega)
    · rintro σ σ' ⟨hI, hk⟩ rfl
      show (σ.setArr co (row (σ.vars "bf.k")) 0).vars "bf.k" + 1 < B
      rw [vars_setArr]
      omega
    · rintro σ σ' σ'' ⟨hI, hk⟩ rfl rfl
      obtain ⟨hb, hc, hkle, hcolen, hlm, hrowN, hmark⟩ := hI
      simp only [vars_setArr]
      set j := σ.vars "bf.k" with hj
      have hvco : ((σ.setArr co (row j) 0).setVar "bf.k" (j + 1)).arrs co
          = (σ.arrs co).set (row j) 0 := by
        rw [arrs_setVar, arrs_setArr_self]
      have hvlm : ((σ.setArr co (row j) 0).setVar "bf.k" (j + 1)).arrs lm
          = σ.arrs lm := by
        rw [arrs_setVar, arrs_setArr_ne _ _ _ (Ne.symm hne)]
      have hvk : ((σ.setArr co (row j) 0).setVar "bf.k" (j + 1)).vars "bf.k"
          = j + 1 := by rw [vars_setVar, if_pos rfl]
      have hvb : ((σ.setArr co (row j) 0).setVar "bf.k" (j + 1)).vars "bf.b"
          = base := by rw [vars_setVar, if_neg (by decide), vars_setArr, hb]
      have hvc : ((σ.setArr co (row j) 0).setVar "bf.k" (j + 1)).vars "bf.c"
          = cnt := by rw [vars_setVar, if_neg (by decide), vars_setArr, hc]
      refine ⟨⟨hvb, hvc, by rw [hvk]; omega, ?_, ?_, hrowN, ?_⟩, by rw [hvk]⟩
      · rw [hvco, List.length_set]; exact hcolen
      · intro k hk'; rw [hvlm]; exact hlm k hk'
      · intro v hv
        rw [hvco, hvk]
        by_cases hveq : v = row j
        · left
          subst hveq
          exact getD_set_self (lt_of_lt_of_le (hrowN _ hk) hcolen)
        · rw [getD_set_of_ne hveq]
          rcases hmark v hv with h0 | ⟨k, hk1, hk2, hk3⟩
          · exact Or.inl h0
          · refine Or.inr ⟨k, ?_, hk2, hk3⟩
            rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt
            · exact absurd hk3.symm hveq
            · omega
  -- the scan, and its exit
  have hscan := Spec.forRangeZero (B := B) "bf.k" "bf.c"
    (BfsClearInv co lm N base cnt row) cnt 10
    (lt_of_le_of_lt (Nat.le_add_left _ _) hbc)
    (fun _ hσ => hσ.2.2.1) (fun _ hσ => hσ.2.1) hbody
  refine hscan.post ?_
  rintro σ σ' - ⟨hI, hk⟩
  refine ⟨fun v hv => ?_, hI, hk⟩
  rcases hI.2.2.2.2.2.2 v hv with h0 | ⟨k, hk1, hk2, -⟩
  · exact h0
  · rw [hk] at hk1; omega

/-! ## §5 The state step

What the frontier loop has to *produce*, one clause at a time. §8 of
`SolveSweepRun` hands down the two region steps and the first-hit
equivalence; here they are restated in the terms the pass actually has
— a ball, a stamp test, a row and an offset — so that the loop's exit
obligation is a list of facts about cells rather than a re-derivation
of the invariant.

The marking step is the one with content. A pass that writes its
centre into the *unclaimed* cells of the `R`-ball and touches nothing
else moves `CtrPart` up one rank, and both halves of
`centre_eq_iff_first_hit` are spent: sufficiency says every cell it
writes really does hold `Driver.centre`, and the converse — `ctr`'s
minimality — says the cells it *declines* to write are exactly the
ones an earlier centre already owns. Without the converse a marking
pass could be sound and still mark a vertex that a later, nearer
centre should have taken. -/

/-- **The marking step, in the pass's own terms.** `M` is the `R`-ball
of the current centre in the current structure; the pass writes the
centre into the cells of `M` that fail the stamp test `ca[v] < A.N`
and leaves every other cell — members that pass the test, and
non-members — alone. That is `CtrPart` at rank `i + 1`.

The two hypotheses are the program's two branches. `hhit` is the
`else` branch of `bfsPushCom`'s marking `ite`; `hkeep` covers both the
`then` branch (a member already claimed) and every cell the pass never
reaches. Nothing is asked about the order of the visits, and nothing
about the cells outside `M` beyond their being untouched. -/
theorem ctrPart_succ_of_ball {L n₀ Λ : ℕ} (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {ca : String} {i : ℕ} (hi : i < A.N)
    {σ σ' : Env} (h : CtrPart ca (centre S A π) π i σ)
    (hlen : A.N ≤ (σ'.arrs ca).length)
    (hhit : ∀ v : Fin A.N,
      v ∈ ball (deleteVerts A.G (peelSet π i)) S.R (π.symm ⟨i, hi⟩) →
      ¬ ((σ.arrs ca).getD (v : ℕ) 0 < A.N) →
      (σ'.arrs ca).getD (v : ℕ) 0 = ((π.symm ⟨i, hi⟩ : Fin A.N) : ℕ))
    (hkeep : ∀ v : Fin A.N,
      (v ∈ ball (deleteVerts A.G (peelSet π i)) S.R (π.symm ⟨i, hi⟩) →
        (σ.arrs ca).getD (v : ℕ) 0 < A.N) →
      (σ'.arrs ca).getD (v : ℕ) 0 = (σ.arrs ca).getD (v : ℕ) 0) :
    CtrPart ca (centre S A π) π (i + 1) σ' := by
  set u : Fin A.N := π.symm ⟨i, hi⟩ with hu
  have hπu : ((π u : Fin A.N) : ℕ) = i := by rw [hu, Equiv.apply_symm_apply]
  refine ctrPart_succ hi h hlen (fun v hv => ?_) (fun v hv => ?_)
  · -- `v` is claimed by this centre: it is a member, and it was unclaimed
    obtain ⟨hmem, -⟩ := (centre_eq_iff_first_hit S A π u v).mp hv
    rw [hπu] at hmem
    refine hhit v hmem ?_
    rw [h.2 v, hv, hπu, if_neg (by omega)]
    omega
  · -- `v` is not claimed by this centre: either it is no member, or an
    -- earlier centre already owns it, and either way the pass passed
    refine hkeep v (fun hmem => ?_)
    obtain ⟨-, hmin⟩ := (centre_eq_iff_first_hit S A π (centre S A π v) v).mp rfl
    have hle : ¬ (π u < π (centre S A π v)) := by
      intro hlt
      exact hmin u hlt (by rw [hπu]; exact hmem)
    have hne : π (centre S A π v) ≠ π u := fun hc => hv (π.injective hc)
    have hlt : ((π (centre S A π v) : Fin A.N) : ℕ) < i := by
      rw [← hπu]
      have := lt_of_le_of_ne (not_lt.mp hle) hne
      exact this
    rw [h.2 v, if_pos hlt]
    exact Fin.isLt _

/-- **The log step, in the pass's own terms.** The row is written at
the anchor the invariant already holds (`lo[i] = peelOff i`), it
enumerates the cluster, and `lo[i+1]` is the anchor plus the count.
`peelOff_step` is the only arithmetic: the named offset function's
step *is* `base + cnt`.

The empty ball is not a special case — `cnt = 0` satisfies both row
clauses vacuously and `lo[i+1] := lo[i]` is still written, which is
what `LogPart`'s per-rank anchoring demands. -/
theorem logPart_succ_of_row {L n₀ Λ : ℕ} (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {lo lm : String} {i : ℕ} (hi : i < A.N)
    {σ σ' : Env} {base cnt : ℕ}
    (h : LogPart lo lm π (cluster S A π) i σ)
    (hbase : base = peelOff π (cluster S A π) i)
    (hcnt : cnt = (cluster S A π (π.symm ⟨i, hi⟩)).ncard)
    (hlolen : A.N + 1 ≤ (σ'.arrs lo).length)
    (holdoff : ∀ k, k ≤ i → (σ'.arrs lo).getD k 0 = (σ.arrs lo).getD k 0)
    (hnewoff : (σ'.arrs lo).getD (i + 1) 0 = base + cnt)
    (hlmlen : base + cnt ≤ (σ'.arrs lm).length)
    (holdrow : ∀ m, m < base → (σ'.arrs lm).getD m 0 = (σ.arrs lm).getD m 0)
    (hsnd : ∀ t, t < cnt → ∃ z : Fin A.N, z ∈ cluster S A π (π.symm ⟨i, hi⟩) ∧
      (σ'.arrs lm).getD (base + t) 0 = (z : ℕ))
    (hcmp : ∀ z : Fin A.N, z ∈ cluster S A π (π.symm ⟨i, hi⟩) →
      ∃ t, t < cnt ∧ (σ'.arrs lm).getD (base + t) 0 = (z : ℕ)) :
    LogPart lo lm π (cluster S A π) (i + 1) σ' := by
  have hstep : peelOff π (cluster S A π) (i + 1) = base + cnt := by
    have := peelOff_step π (cluster S A π) (⟨i, hi⟩ : Fin A.N)
    rw [this, hbase, hcnt]
  subst hbase
  refine logPart_succ hi h hlolen holdoff (by rw [hnewoff, hstep])
    (by rw [hstep]; exact hlmlen) holdrow ?_ ?_
  · intro t ht
    exact hsnd t (by rw [hcnt]; exact ht)
  · intro z hz
    obtain ⟨t, ht, hval⟩ := hcmp z hz
    exact ⟨t, by rw [← hcnt]; exact ht, hval⟩

/-- **The turn's state step.** The pass writes `ca`, `co`, `lo` and
`lm` and reads everything else, so every clause of `SweepSt` but the
two regions transports along agreement, the deletable region included
— the delete is `sweepBodyCom`'s half of the turn, not this pass's,
and the region is left at the same rank prefix `i` it arrived at.

This is `PeelBfsIn`'s postcondition reduced to exactly what the
frontier loop has to know: two region steps and a list of frame
facts. -/
theorem sweepSt_step_of_bfs {L n₀ Λ : ℕ} {S : Setup L} {j ℓp hb : ℕ}
    {A : Arena Λ n₀} {htab : Fin A.N → Fin ℓp → List (Fin A.N)}
    {π : Equiv.Perm (Fin A.N)} {ca co ao aj dg mt od lo lm : String}
    {Ssc : Env → Prop} {i : ℕ} {σ σ' : Env}
    (h : SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc i i σ)
    (hoff : σ'.arrs (arenaNames j).off = σ.arrs (arenaNames j).off)
    (htgt : σ'.arrs (arenaNames j).tgt = σ.arrs (arenaNames j).tgt)
    (hcol : σ'.arrs (arenaNames j).col = σ.arrs (arenaNames j).col)
    (hup : σ'.arrs (arenaNames j).up = σ.arrs (arenaNames j).up)
    (hhis : σ'.arrs (arenaNames j).hist = σ.arrs (arenaNames j).hist)
    (hnN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN)
    (hnS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS)
    (hodA : σ'.arrs od = σ.arrs od)
    (haoA : σ'.arrs ao = σ.arrs ao) (hajA : σ'.arrs aj = σ.arrs aj)
    (hdgA : σ'.arrs dg = σ.arrs dg) (hmtA : σ'.arrs mt = σ.arrs mt)
    (hcoL : (σ'.arrs co).length = (σ.arrs co).length)
    (hlmL : n₀ * n₀ ≤ (σ'.arrs lm).length)
    (hS : Ssc σ')
    (hctr : CtrPart ca (centre S A π) π (i + 1) σ')
    (hlog : LogPart lo lm π (cluster S A π) (i + 1) σ') :
    SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc i (i + 1) σ' := by
  obtain ⟨hA, hordr, hco, -, -, hdel, -, -⟩ := h
  exact ⟨arenaStW_of_eq hA hnN hnS hoff htgt hcol hup hhis,
    hordr.of_eq hodA, by rw [hcoL]; exact hco, hlmL, hS,
    hdel.of_eq haoA hajA hdgA hmtA, hctr, hlog⟩

/-! ## §6 The turn's frame

`sweepSt_step_of_bfs` asks for agreement on eleven arrays and two
scalars; `Spec.frame` supplies exactly that from the syntax, once the
syntax is known. So the frame is computed here, once, rather than by
whoever composes.

The scalar half is the load-bearing one: `PeelBfsIn`'s postcondition
repeats `σ'.vars "sw.i" = i` and `σ'.vars "sw.v" = …`, so the pass must
not write the sweep's own two cells. It does not — every scalar it
touches is in the `bf.` family. -/

theorem iterCom_warrs (k : ℕ) (c : Com) (b : String) (h : b ∉ c.warrs) :
    b ∉ (iterCom k c).warrs := by
  induction k with
  | zero => simp
  | succ m ih =>
      simp only [iterCom_succ, Com.warrs, List.mem_append, not_or]
      exact ⟨h, ih⟩

theorem iterCom_wvars (k : ℕ) (c : Com) (y : String) (h : y ∉ c.wvars) :
    y ∉ (iterCom k c).wvars := by
  induction k with
  | zero => simp
  | succ m ih =>
      simp only [iterCom_succ, Com.wvars, List.mem_append, not_or]
      exact ⟨h, ih⟩

/-- **The turn writes four arrays**: the marks, the visited flags, the
log's offsets and the log's cells. The adjacency region — `ao`, `aj`,
`dg`, `mt` — and the arena are read only, which is what leaves
`DelAdjSt` standing at the rank prefix it arrived at. -/
theorem bfsTurn_warrs (R : ℕ) (ca co ao aj dg lo lm nn : String) {b : String}
    (h1 : b ≠ ca) (h2 : b ≠ co) (h3 : b ≠ lo) (h4 : b ≠ lm) :
    b ∉ (bfsTurnCom R ca co ao aj dg lo lm nn).warrs := by
  have hlvl : ∀ mk : Bool, b ∉ (bfsLevelCom ca co ao aj dg lm nn mk).warrs := by
    intro mk
    cases mk <;>
      simp [bfsLevelCom, bfsScanCom, bfsPushCom, Com.warrs, h1, h2, h4]
  simp only [bfsTurnCom, Com.warrs, List.mem_append, not_or]
  refine ⟨?_, iterCom_warrs _ _ _ (hlvl true), iterCom_warrs _ _ _ (hlvl false),
    ?_, ?_⟩
  · simp [bfsInitCom, bfsPushCom, Com.warrs, h1, h2, h4]
  · simp [bfsEmitCom, Com.warrs, h3]
  · simp [bfsClearCom, Com.warrs, h2]

/-- **The turn writes ten scalars, all its own.** In particular it
leaves `"sw.i"` and `"sw.v"` — the rank and the centre, which
`PeelBfsIn` demands back unchanged — and the delete's `"dl.*"`
family. -/
theorem bfsTurn_wvars (R : ℕ) (ca co ao aj dg lo lm nn : String) {y : String}
    (h1 : y ≠ "bf.b") (h2 : y ≠ "bf.c") (h3 : y ≠ "bf.h") (h4 : y ≠ "bf.e")
    (h5 : y ≠ "bf.v") (h6 : y ≠ "bf.o") (h7 : y ≠ "bf.n") (h8 : y ≠ "bf.t")
    (h9 : y ≠ "bf.w") (h10 : y ≠ "bf.k") :
    y ∉ (bfsTurnCom R ca co ao aj dg lo lm nn).wvars := by
  have hlvl : ∀ mk : Bool, y ∉ (bfsLevelCom ca co ao aj dg lm nn mk).wvars := by
    intro mk
    cases mk <;>
      simp [bfsLevelCom, bfsScanCom, bfsPushCom, Com.wvars, h2, h3, h4, h5, h6,
        h7, h8, h9]
  simp only [bfsTurnCom, Com.wvars, List.mem_append, not_or]
  refine ⟨?_, iterCom_wvars _ _ _ (hlvl true), iterCom_wvars _ _ _ (hlvl false),
    ?_, ?_⟩
  · simp [bfsInitCom, bfsPushCom, Com.wvars, h1, h2, h3, h9]
  · simp [bfsEmitCom, Com.wvars]
  · simp [bfsClearCom, Com.wvars, h10]

/-! ### The row's allocation, and the offset write

Two small facts the loop's exit needs and neither region states.

The first is Hazard 6 in its concrete form: `LogPart` demands
`peelOff (i+1) ≤ |lm|`, and *nothing in the contract text says who owes
that allocation*. `peelSweepIn_of_bfs` pays it with `n·n ≤ |lm|` in
its scratch descriptor and `peelOff_le_sq`; `bfsRow_fits` is the step
of that argument the turn itself performs, and it is why the row write
is in range. -/

/-- **The row fits.** Every prefix of the log is at most `A.N²` wide,
the carrier is at most the input's, and the descriptor allocates
`n₀²`. So writing row `i` never leaves the array. -/
theorem bfsRow_fits {N n₀ : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) {i : ℕ} (hi : i < N) (hNn : N ≤ n₀)
    {lm : String} {σ : Env} (hlm : n₀ * n₀ ≤ (σ.arrs lm).length) :
    peelOff π Xf (i + 1) ≤ (σ.arrs lm).length :=
  le_trans (le_trans (peelOff_le_sq π Xf (by omega)) (Nat.mul_le_mul hNn hNn)) hlm

/-- **The offset write.** `lo[i+1] := lo[i] + cnt` — a single store, and
it happens on *every* turn, the empty ball included: `LogPart`'s
offsets are anchored per rank, so a centre whose current ball is empty
still writes `lo[i+1] = lo[i]`. Skipping it for an empty row is the
way `ClusterCsr`'s per-centre anchoring silently breaks. -/
theorem bfsEmit_spec {lo : String} {B i base cnt : ℕ}
    (hiB : i + 1 < B) (h1B : 1 < B) (hbcB : base + cnt < B) :
    Spec B
      (fun σ => σ.vars "sw.i" = i ∧ σ.vars "bf.b" = base ∧
        σ.vars "bf.c" = cnt ∧ i + 1 < (σ.arrs lo).length)
      (bfsEmitCom lo)
      (fun σ σ' => σ' = σ.setArr lo (i + 1) (base + cnt)) 7 := by
  have h : Spec B
      (fun σ => σ.vars "sw.i" = i ∧ σ.vars "bf.b" = base ∧
        σ.vars "bf.c" = cnt ∧ i + 1 < (σ.arrs lo).length)
      (bfsEmitCom lo)
      (fun σ σ' => σ' = σ.setArr lo (i + 1) (base + cnt)) (1 + 3 + 3) := by
    refine Spec.store (idx := fun _ => i + 1) (f := fun _ => base + cnt)
      (fun σ hσ => ?_) (fun σ hσ => ?_) (fun _ hσ => hσ.2.2.2)
    · have := evalB_bin (B := B) (op := .add)
        (evalB_var (x := "sw.i") (σ := σ) (by omega)) (evalB_lit (n := 1) h1B)
        (show σ.vars "sw.i" + 1 < B by rw [hσ.1]; omega)
      rw [hσ.1] at this
      exact this
    · have := evalB_bin (B := B) (op := .add)
        (evalB_var (x := "bf.b") (σ := σ) (by omega))
        (evalB_var (x := "bf.c") (σ := σ) (by omega))
        (show σ.vars "bf.b" + σ.vars "bf.c" < B by rw [hσ.2.1, hσ.2.2.1]; omega)
      rw [hσ.2.1, hσ.2.2.1] at this
      exact this
  exact h.mono (by omega)

/-! ## §7 The scratch descriptor

`SweepSt` offers `co` as an allocation and says nothing about its
contents, so "the visited flags are clear" has to live in `Ssc` — the
free scratch predicate `PeelBfsIn` carries and a discharger chooses.
This is the choice, and the check that it meets the frame condition
`peelSweepIn_of_bfs` asks of any such choice: `co` is not one of the
six arrays the sweep's other phases may write, so the sentinel pass and
the delete both preserve it. -/

/-- **The visited flags are clear**: the scratch descriptor for the
sweep's `Ssc`. Consumed and re-established by every turn — the
clean-up of §4 is what re-establishes it. -/
def BfsClean (co : String) (N : ℕ) (σ : Env) : Prop :=
  ∀ v, v < N → (σ.arrs co).getD v 0 = 0

theorem bfsClean_of_eq {co : String} {N : ℕ} {σ σ' : Env}
    (h : BfsClean co N σ) (heq : σ'.arrs co = σ.arrs co) : BfsClean co N σ' := by
  intro v hv
  rw [heq]
  exact h v hv

/-- **`BfsClean` meets `peelSweepIn_of_bfs`'s `hSsc`** — verbatim, at
the one hypothesis it needs: the flag array is none of the six the
sweep's other phases write. Without this the choice of `Ssc` would
have been an integration debt rather than a design decision. -/
theorem bfsClean_hSsc {ca co lo lm aj dg mt : ℕ → String} {N : ℕ}
    (hne : ∀ j, co j ≠ ca j ∧ co j ≠ lo j ∧ co j ≠ lm j ∧ co j ≠ aj j ∧
      co j ≠ dg j ∧ co j ≠ mt j) :
    ∀ (j : ℕ) (σ σ' : Env),
      (∀ b : String, b ≠ ca j → b ≠ lo j → b ≠ lm j → b ≠ aj j → b ≠ dg j →
        b ≠ mt j → σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ≠ "sw.i" → y ≠ "sw.v" → y ≠ "dl.i" → y ≠ "dl.w" →
        y ≠ "dl.p" → y ≠ "dl.l" → y ≠ "dl.u" → y ≠ "dl.q" →
        σ'.vars y = σ.vars y) →
      BfsClean (co j) N σ → BfsClean (co j) N σ' := by
  intro j σ σ' harr _ _ hcl
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hne j
  exact bfsClean_of_eq hcl (harr _ k1 k2 k3 k4 k5 k6)

/-! The leaf's axiom profile. Everything here is about the ambient
logic, the walk metric and the two landed regions; nothing quotes
`Headline.headlineSetup`, so the endorsed Lax12 axiom does not appear
— it will enter only with the discharge of `PeelBfsIn` itself, which
is stated against that setup. -/

#print axioms bfsCells_le_edgeTerm

#print axioms ball_succ

#print axioms cluster_eq_expand_of_ball

#print axioms bfsExpanded_le_edgeTerm

#print axioms bfsClear_spec

#print axioms bfsEmit_spec

#print axioms bfsClean_hSsc

#print axioms ctrPart_succ_of_ball

#print axioms sweepSt_step_of_bfs

#print axioms bfsTurn_wvars

end Lax3Proofs.Prog
