import Lax3Proofs.SolveSweepPeel
import Lax3Proofs.SolveMachPrepRun

/-!
# F6c12 (residual 4-ii) — `PeelGroupIn`, the sweep's grouping half

`SolveSweepPeel` splits `CovPeelIn` at the seam its own output shape
forces and names two residuals. This file discharges the second,
**`PeelGroupIn`** (`SolveSweepPeel.lean:380`), with a concrete `Com`
and the budget the split pinned: `peelK agr bgr 0` — **no edge term**,
because the grouping never reads the graph.

## Why the log exists

`ClusterCsr` (`SolveChainCover.lean:63`) anchors its offsets in
**carrier** order and its rows in **ascending vertex** order — after
the `setEquiv` repin, `Impl.restrictEmb`'s enumeration, which is
`Finset.orderIsoOfFin`'s. The sweep visits centres in `π` order and a
BFS enumerates a ball in level order; sorting a row by a carrier pass
per centre is `Θ(N²)`, the envelope break the whole campaign avoids.
So the sweep emits its rows **in peel order, unsorted** — the log
`ClusterLog` — and this pass turns the log into `ClusterCsr` by two
stable counting sorts, by member and then by centre, each a carrier
scan plus a pass over the mass.

## The program: six passes, `O(N + mass)`

Nothing here is a pass per centre over the carrier, and nothing reads
an array length (Hazard 3): the carrier size is the arena's own `nN`
cell and the mass is `lo[nN]`, the log's last offset — the transpose's
`ns = off n` idiom (`SolveAugEmitCom` Finding 1) at a second seam.

* `grLenCom` — one turn a *rank*: `cur[od[i]] := lo[i+1] − lo[i]`, so
  `cur` ends holding `|X_u|` at every carrier position. The order
  region is what turns a rank-indexed log into a carrier-indexed
  count, and it is why no zeroing pass is owed for `cur`: `od` is a
  bijection, so every cell is written.
* `grOffCom` — the carrier prefix sum: `co[u] := acc`, `cur[u] := acc`
  (the offsets become the second sort's cursor, the transpose's
  in-place trick), `cnt[u] := 0` (the first sort's counters, zeroed
  here rather than in a pass of their own), then `co[nN] := acc`.
  **`co` is written at every `u ≤ N`, empty centres included**
  (Hazard 1): the offsets are anchored per centre, not per nonempty
  centre.
* `grCntCom` — the first sort's count, one turn a log cell:
  `cnt[lm[p]] += 1`.
* `grMoffCom` — the first sort's prefix sum, one turn a member.
* `grScatCom` — the first sort's scatter, one outer turn a rank and
  one inner turn a log cell: the centre `od[i]` goes to
  `sb[cnt[lm[p]]]`. `sb` is then the log's centres **grouped by
  member, ascending**.
* `grEmitCom` — the second sort's scatter, one outer turn a member and
  one inner turn a cell of its bucket: `cm[cur[sb[q]]] := v`. The
  members arrive in ascending order and each row is appended to, so
  each row comes out ascending — which is the stability the split's
  Finding 1 asks for, delivered by the scan order and not by a
  comparison. The outer bucket bound is `cnt[v]`, which the scatter
  left holding the bucket's *end*, and the bucket's start is the
  running pointer `gp.q` — so the pass owes no second offset array.

`grK N ms = 104·N + 61·ms + 49` — two carrier scans at `24` a vertex,
a member prefix sum at `18`, a log scan at `17` a cell, and the two
scatters at `23`/`15` a vertex and `22` a cell apiece.  The constant
folds into the carrier term (`1 ≤ N`, from `¬ A.G = ⊥`), so the
residual is concluded at **`peelK 153 61 0`** — `peelBudget_le` then
puts it inside §7's `a·N^{1+2δ}`.  Nothing is charged per centre
against the carrier and no term reads the graph.

## What is carried, and what is derived

The two scatters carry an **address, not a set** (`SolveAugEmitCom`
Finding 2): `GrpScatSt.fill` says *where* a centre lands
(`spos u z`, §1), and `GrpEmitSt.fill` says the member `z` of row `u`
sits at `offC u + |{y ∈ X_u : y < z}|`. The second is `ClusterCsr`'s
clause on the nose, because `ncard_lt_setEquiv` says that count *is*
the local name — so the ascending-row demand needs no sortedness
invariant and no pigeonhole at the end.

Duplicate-freeness of a log row is not assumed: it is derived
(`GrpLog.row_injOn`, the `DelAdjSt.slot_injOn` idiom the split's §1
already used), and it is what makes `logPos` — the log position of
member `z` of centre `u` — well defined.

## Findings

1. **The mass needs no cell, and the scratch needs no contents.**
   `PeelGroupIn` hands the pass `Sgr`, a level predicate that cannot
   mention the arena, so no allocation length can be stated in `A.N`
   or in the mass. Both are nevertheless available: the mass is
   `lo[nN]` at run time, and at proof time `Sgr` states the four
   scratch lengths **against the log's own two arrays**
   (`|lm| ≤ |cm|`, `|lm| ≤ |sb|`, `|co| ≤ |cnt|`, `|co| ≤ |cur|`),
   which is arena-free and exactly strong enough. No clause about
   scratch *contents* is asked for: `grOffCom` zeroes `cnt` itself and
   `grLenCom` overwrites `cur` outright.
2. **The order region is load-bearing twice.** It is the only way the
   pass learns which centre a log row belongs to, and — because it is
   a bijection — the reason the carrier count needs no zeroing pass.
   `PeelGroupIn` does not carry `RankArr`, so the pass can only scan
   ranks and scatter into the carrier, never the reverse.
3. **`ClusterCsr` pins no exact length** — Hazard 4, checked at the
   contract rather than assumed. Both its allocation clauses are
   inequalities (`N + 1 ≤ |co|`, `offC N ≤ |cm|`), so meeting it lays
   no invisible binding requirement on whoever establishes the
   precondition. What *is* such a requirement, and is stated here so
   that it is visible, is `Sgr`: the sweep half must hand the grouping
   a state in which the four length inequalities of Finding 1 hold.
   They mention no array the sweep writes and IMP+ stores never change
   a length, so they survive the sweep once the allocations are made —
   but they have to be made.
4. **`SolveBlocksRestrict`'s Finding 1 is stale.** It records that
   `Driver.setEquiv` is `Classical`-chosen and flags the repin to
   `Finset.orderIsoOfFin` as future work. The repin landed (F6c2,
   `DriverArena.lean:140`), and `setEquiv_strictMono` /
   `ncard_lt_setEquiv` (`SolveMachPrepRun` §2) are the theorems that
   say so — this file consumes them, and they are the whole reason the
   ascending-row demand is discharged by a scan order rather than by a
   comparison sort. The docstring should be corrected; nothing in the
   *theorems* is wrong.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

/-! ## §0 Small array and run helpers

The shapes the six passes are built from, each with its value
obligations named and its cost computed once — `SolveSweepBuild`'s §0
and `SolveAugEmitCom`'s, which are `private` there. -/

private theorem gsetD_self {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem gsetD_ne {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

private theorem gget? (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem gvar {B : ℕ} {y : String} {σ : Env} {c : ℕ} (hy : σ.vars y = c)
    (hc : c < B) : (Expr.var y).evalB B σ = some c := by
  rw [← hy] at hc ⊢; exact evalB_var hc

private theorem glit {B c : ℕ} {σ : Env} (hc : c < B) :
    (Expr.lit c).evalB B σ = some c := evalB_lit hc

private theorem gadd {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (hab : a + b < B) :
    (Expr.add e f).evalB B σ = some (a + b) := evalB_bin he hf (by simpa using hab)

private theorem gsub {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (hab : a - b < B) :
    (Expr.sub e f).evalB B σ = some (a - b) := evalB_bin he hf (by simpa using hab)

private theorem gget {B : ℕ} {a : String} {i : Expr} {σ : Env} {q c : ℕ}
    (hi : i.evalB B σ = some q) (hq : (σ.arrs a)[q]? = some c) (hc : c < B) :
    (Expr.get a i).evalB B σ = some c := evalB_get hi hq hc

private theorem grun_assign {B : ℕ} {x : String} {e : Expr} {σ : Env} {c K : ℕ}
    (he : e.evalB B σ = some c) (hK : 1 + e.size ≤ K) :
    Run B (.assign x e) σ (σ.setVar x c) K := (Run.assign he).mono hK

private theorem grun_store {B : ℕ} {a : String} {i e : Expr} {σ : Env} {q c K : ℕ}
    (hi : i.evalB B σ = some q) (he : e.evalB B σ = some c)
    (hq : q < (σ.arrs a).length) (hK : 1 + i.size + e.size ≤ K) :
    Run B (.store a i e) σ (σ.setArr a q c) K := (Run.store hi he hq).mono hK

/-! ## §1 The two sorts, abstractly

Everything the six passes compute is a function of four data: the log's
offsets `offL`, its members `lmv`, the ordering `π` and the cluster
family `Xf`. This section names them, proves the log's rows are
duplicate-free, and builds the two addresses the scatters carry. -/

/-- **The log and the order region as the grouping reads them**:
`ClusterLog`'s existential unpacked (the offsets and the member
sequence as functions), together with `OrdArr`. Duplicate-freeness of a
row is *not* a field — it is derived (`GrpLog.row_injOn`). -/
structure GrpLog (lo lm od : String) {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ) (σ : Env) : Prop where
  /-- The offsets are anchored at zero. -/
  zero : offL 0 = 0
  /-- Row `i` is as long as the cluster of the rank-`i` vertex. -/
  step : ∀ i : Fin N, offL ((i : ℕ) + 1) = offL (i : ℕ) + (Xf (π.symm i)).ncard
  /-- The offset region is an allocation of at least `N + 1`. -/
  loLen : N + 1 ≤ (σ.arrs lo).length
  /-- And it holds the offsets. -/
  loGet : ∀ i, i ≤ N → (σ.arrs lo).getD i 0 = offL i
  /-- The member region is an allocation of at least the mass. -/
  lmLen : offL N ≤ (σ.arrs lm).length
  /-- And it holds the member sequence. -/
  lmGet : ∀ p, p < offL N → (σ.arrs lm).getD p 0 = lmv p
  /-- The order region is an allocation of at least the carrier. -/
  odLen : N ≤ (σ.arrs od).length
  /-- And entry `i` is the vertex of rank `i`. -/
  odGet : ∀ i : Fin N, (σ.arrs od).getD (i : ℕ) 0 = ((π.symm i : Fin N) : ℕ)
  /-- Every cell of row `i` is a member of the rank-`i` cluster. -/
  sound : ∀ i : Fin N, ∀ t : ℕ, t < (Xf (π.symm i)).ncard →
    ∃ z : Fin N, z ∈ Xf (π.symm i) ∧ lmv (offL (i : ℕ) + t) = (z : ℕ)
  /-- And every member is in a cell of its row. -/
  complete : ∀ i : Fin N, ∀ z : Fin N, z ∈ Xf (π.symm i) →
    ∃ t : ℕ, t < (Xf (π.symm i)).ncard ∧ lmv (offL (i : ℕ) + t) = (z : ℕ)

namespace GrpLog

variable {lo lm od : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
  {Xf : Fin N → Set (Fin N)} {offL lmv : ℕ → ℕ} {σ : Env}

/-- The region reads exactly three arrays: it transports along
agreement on them. -/
theorem of_eq (h : GrpLog lo lm od π Xf offL lmv σ) {σ' : Env}
    (hlo : σ'.arrs lo = σ.arrs lo) (hlm : σ'.arrs lm = σ.arrs lm)
    (hod : σ'.arrs od = σ.arrs od) : GrpLog lo lm od π Xf offL lmv σ' where
  zero := h.zero
  step := h.step
  loLen := by rw [hlo]; exact h.loLen
  loGet := by rw [hlo]; exact h.loGet
  lmLen := by rw [hlm]; exact h.lmLen
  lmGet := by rw [hlm]; exact h.lmGet
  odLen := by rw [hod]; exact h.odLen
  odGet := by rw [hod]; exact h.odGet
  sound := h.sound
  complete := h.complete

/-- The offsets do not decrease. -/
theorem mono (h : GrpLog lo lm od π Xf offL lmv σ) {i k : ℕ} (hik : i ≤ k)
    (hk : k ≤ N) : offL i ≤ offL k := by
  induction k with
  | zero => obtain rfl : i = 0 := by omega
            exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · have hs : offL (k + 1) = offL k + (Xf (π.symm ⟨k, by omega⟩)).ncard :=
          h.step ⟨k, by omega⟩
        have := ih (by omega) (by omega)
        omega
      · obtain rfl : i = k + 1 := by omega
        exact le_rfl

/-- Every row ends inside the mass. -/
theorem row_le (h : GrpLog lo lm od π Xf offL lmv σ) (i : Fin N) :
    offL ((i : ℕ) + 1) ≤ offL N := h.mono (by omega) le_rfl

/-- **A log row has no duplicates** (pigeonhole, the `slot_injOn`
idiom): completeness makes the cluster's values a subset of the row's
image and the count equates the cardinalities, so the row is an
*enumeration* of its cluster. This is what makes `logPos` a function. -/
theorem row_injOn (h : GrpLog lo lm od π Xf offL lmv σ) (i : Fin N) :
    Set.InjOn (fun t => lmv (offL (i : ℕ) + t))
      {t | t < (Xf (π.symm i)).ncard} := by
  classical
  have h1 : (Fin.val '' (Xf (π.symm i))) ⊆
      ↑((Finset.range ((Xf (π.symm i)).ncard)).image
        (fun t => lmv (offL (i : ℕ) + t))) := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨t, ht, hval⟩ := h.complete i z hz
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, hval⟩)
  have h2 : (Xf (π.symm i)).ncard ≤
      ((Finset.range ((Xf (π.symm i)).ncard)).image
        (fun t => lmv (offL (i : ℕ) + t))).card :=
    calc (Xf (π.symm i)).ncard
        = (Fin.val '' (Xf (π.symm i))).ncard :=
          (Set.ncard_image_of_injective _ Fin.val_injective).symm
      _ ≤ _ := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((Finset.range ((Xf (π.symm i)).ncard)).image
      (fun t => lmv (offL (i : ℕ) + t))).card
        = (Finset.range ((Xf (π.symm i)).ncard)).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_range]; exact h2)
  have hset : ({t | t < (Xf (π.symm i)).ncard} : Set ℕ)
      = ↑(Finset.range ((Xf (π.symm i)).ncard)) := by
    rw [Finset.coe_range]; rfl
  rw [hset]
  exact Finset.injOn_of_card_image_eq h3

/-- **Every cell of the log has an owner row** — the offsets tile
`[0, offL N)`, so a flat log pointer names a rank. -/
theorem owner (h : GrpLog lo lm od π Xf offL lmv σ) :
    ∀ m, m ≤ N → ∀ p, p < offL m →
      ∃ i : Fin N, offL (i : ℕ) ≤ p ∧ p < offL ((i : ℕ) + 1) := by
  intro m
  induction m with
  | zero => intro _ p hp; rw [h.zero] at hp; omega
  | succ m ih =>
      intro hm p hp
      rcases Nat.lt_or_ge p (offL m) with hlt | hge
      · exact ih (by omega) p hlt
      · exact ⟨⟨m, by omega⟩, hge, hp⟩

/-- **Every member of the log is a vertex** — soundness at the owner
row. -/
theorem lmv_lt (h : GrpLog lo lm od π Xf offL lmv σ) {p : ℕ} (hp : p < offL N) :
    lmv p < N := by
  obtain ⟨i, h1, h2⟩ := h.owner N le_rfl p hp
  have hs := h.step i
  obtain ⟨z, -, hz⟩ := h.sound i (p - offL (i : ℕ)) (by omega)
  rw [show offL (i : ℕ) + (p - offL (i : ℕ)) = p from by omega] at hz
  rw [hz]
  exact z.isLt

end GrpLog

/-! ### The log position of a member

The first sort reads the log flat and needs, at each cell, the centre
that owns it; the *proof* needs the reverse — the cell a given member
of a given centre sits in. Both are the same partial bijection; this
is its forward half, as a total function pinned on the pairs that
matter. -/

open Classical in
/-- **The log position of member `z` of centre `u`** — the cell of row
`π u` holding `z`, which `row_injOn` makes unique. -/
noncomputable def logPos {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ) (u z : Fin N) : ℕ :=
  offL ((π u : Fin N) : ℕ) +
    (if h : ∃ t : ℕ, t < (Xf u).ncard ∧
        lmv (offL ((π u : Fin N) : ℕ) + t) = (z : ℕ)
      then Classical.choose h else 0)

variable {lo lm od : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
  {Xf : Fin N → Set (Fin N)} {offL lmv : ℕ → ℕ} {σ : Env}

/-- What `logPos` is: a cell of `u`'s own row, holding `z`. -/
theorem logPos_spec (h : GrpLog lo lm od π Xf offL lmv σ) {u z : Fin N}
    (hz : z ∈ Xf u) :
    offL ((π u : Fin N) : ℕ) ≤ logPos π Xf offL lmv u z ∧
      logPos π Xf offL lmv u z < offL (((π u : Fin N) : ℕ) + 1) ∧
      lmv (logPos π Xf offL lmv u z) = (z : ℕ) := by
  have hsym : π.symm (π u) = u := Equiv.symm_apply_apply π u
  have hex : ∃ t : ℕ, t < (Xf u).ncard ∧
      lmv (offL ((π u : Fin N) : ℕ) + t) = (z : ℕ) := by
    obtain ⟨t, ht, hv⟩ := h.complete (π u) z (by rw [hsym]; exact hz)
    exact ⟨t, by rwa [hsym] at ht, hv⟩
  obtain ⟨ht, hv⟩ := Classical.choose_spec hex
  have hstep := h.step (π u)
  rw [hsym] at hstep
  rw [logPos, dif_pos hex]
  exact ⟨by omega, by omega, hv⟩

/-- `logPos` lands inside the log. -/
theorem logPos_lt (h : GrpLog lo lm od π Xf offL lmv σ) {u z : Fin N}
    (hz : z ∈ Xf u) : logPos π Xf offL lmv u z < offL N :=
  lt_of_lt_of_le (logPos_spec h hz).2.1 (h.row_le (π u))

/-- **`logPos` is injective**: rows are disjoint, and a row has no
duplicates. -/
theorem logPos_inj (h : GrpLog lo lm od π Xf offL lmv σ) {u u' z z' : Fin N}
    (hz : z ∈ Xf u) (hz' : z' ∈ Xf u')
    (he : logPos π Xf offL lmv u z = logPos π Xf offL lmv u' z') :
    u = u' ∧ z = z' := by
  obtain ⟨h1, h2, h3⟩ := logPos_spec h hz
  obtain ⟨h1', h2', h3'⟩ := logPos_spec h hz'
  have huu : (π u : Fin N) = (π u' : Fin N) := by
    by_contra hne
    rcases Nat.lt_or_ge ((π u : Fin N) : ℕ) ((π u' : Fin N) : ℕ) with hlt | hge
    · have := h.mono (i := ((π u : Fin N) : ℕ) + 1) (k := ((π u' : Fin N) : ℕ))
        (by omega) (by have := (π u' : Fin N).isLt; omega)
      omega
    · have hne' : ((π u' : Fin N) : ℕ) < ((π u : Fin N) : ℕ) := by
        rcases Nat.eq_or_lt_of_le hge with heq | hlt
        · exact absurd (Fin.ext heq.symm) hne
        · exact hlt
      have := h.mono (i := ((π u' : Fin N) : ℕ) + 1) (k := ((π u : Fin N) : ℕ))
        (by omega) (by have := (π u : Fin N).isLt; omega)
      omega
  have huu' : u = u' := by
    have := congrArg π.symm huu
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  exact ⟨huu', Fin.ext (by rw [← h3, ← h3', he])⟩

/-- **`logPos` is onto the log**: every cell of the log is the cell of
some member of some centre — soundness at the owner row, and
`row_injOn` to place it. -/
theorem logPos_surj (h : GrpLog lo lm od π Xf offL lmv σ) {p : ℕ}
    (hp : p < offL N) :
    ∃ u z : Fin N, z ∈ Xf u ∧ logPos π Xf offL lmv u z = p := by
  obtain ⟨i, h1, h2⟩ := h.owner N le_rfl p hp
  have hstep : offL ((i : ℕ) + 1) = offL (i : ℕ) + (Xf (π.symm i)).ncard := h.step i
  have ht : p - offL (i : ℕ) < (Xf (π.symm i)).ncard := by omega
  obtain ⟨z, hzmem, hzval⟩ := h.sound i (p - offL (i : ℕ)) ht
  refine ⟨π.symm i, z, hzmem, ?_⟩
  have hpi : (π (π.symm i) : Fin N) = i := Equiv.apply_symm_apply π i
  obtain ⟨g1, g2, g3⟩ := logPos_spec h hzmem
  rw [hpi] at g1 g2
  have hs : logPos π Xf offL lmv (π.symm i) z - offL (i : ℕ)
      < (Xf (π.symm i)).ncard := by omega
  have hval1 : lmv (offL (i : ℕ)
      + (logPos π Xf offL lmv (π.symm i) z - offL (i : ℕ))) = (z : ℕ) := by
    rw [show offL (i : ℕ) + (logPos π Xf offL lmv (π.symm i) z - offL (i : ℕ))
        = logPos π Xf offL lmv (π.symm i) z from by omega]
    exact g3
  have hinj : ∀ a b : ℕ, a < (Xf (π.symm i)).ncard → b < (Xf (π.symm i)).ncard →
      lmv (offL (i : ℕ) + a) = lmv (offL (i : ℕ) + b) → a = b :=
    fun a b ha hb hab => h.row_injOn i ha hb hab
  have heq := hinj _ _ hs ht (hval1.trans hzval.symm)
  omega

/-- **A log cell lies in one row only** — the offsets are monotone, so
two rows containing the same cell are the same row. -/
theorem row_unique (h : GrpLog lo lm od π Xf offL lmv σ) {a b p : ℕ}
    (ha : a < N) (hb : b < N) (h1 : offL a ≤ p) (h2 : p < offL (a + 1))
    (h3 : offL b ≤ p) (h4 : p < offL (b + 1)) : a = b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · have := h.mono (i := a + 1) (k := b) (by omega) (by omega)
    omega
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · omega
    · have := h.mono (i := b + 1) (k := a) (by omega) (by omega)
      omega

/-! ### The first sort: counting the log by member -/

/-- The cells below `k` whose member is `v` — what the first sort's
counting sweep has accumulated in `cnt[v]` after `k` turns. -/
def grCnt (lmv : ℕ → ℕ) (k v : ℕ) : ℕ :=
  ((Finset.range k).filter (fun p => lmv p = v)).card

theorem grCnt_zero (lmv : ℕ → ℕ) (v : ℕ) : grCnt lmv 0 v = 0 := by
  simp [grCnt]

theorem grCnt_succ (lmv : ℕ → ℕ) (k v : ℕ) :
    grCnt lmv (k + 1) v = grCnt lmv k v + (if lmv k = v then 1 else 0) := by
  classical
  rw [grCnt, grCnt, Finset.range_add_one, Finset.filter_insert]
  by_cases h : lmv k = v
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

theorem grCnt_mono (lmv : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) (v : ℕ) :
    grCnt lmv a v ≤ grCnt lmv b v := by
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

theorem grCnt_le (lmv : ℕ → ℕ) (k v : ℕ) : grCnt lmv k v ≤ k := by
  simpa [grCnt] using Finset.card_filter_le (Finset.range k) (fun p => lmv p = v)

/-- **The count strictly grows at a hit**: two cells holding the same
member have different counts below them, which is why the first sort's
cursor is an injective address. -/
theorem grCnt_lt_of_hit (lmv : ℕ → ℕ) {p p' v : ℕ} (hp : lmv p = v) (hlt : p < p') :
    grCnt lmv p v < grCnt lmv p' v := by
  have h1 : grCnt lmv (p + 1) v = grCnt lmv p v + 1 := by
    rw [grCnt_succ, if_pos hp]
  have h2 : grCnt lmv (p + 1) v ≤ grCnt lmv p' v := grCnt_mono lmv (by omega) v
  omega

/-- **A member is determined by its count**: on the fibre of `v`, the
running count is injective. -/
theorem grCnt_inj (lmv : ℕ → ℕ) {p p' v : ℕ} (hp : lmv p = v) (hp' : lmv p' = v)
    (he : grCnt lmv p v = grCnt lmv p' v) : p = p' := by
  rcases lt_trichotomy p p' with h | h | h
  · exact absurd he (Nat.ne_of_lt (grCnt_lt_of_hit lmv hp h))
  · exact h
  · exact absurd he.symm (Nat.ne_of_lt (grCnt_lt_of_hit lmv hp' h))

/-- The first sort's bucket offsets: the members below `k`. -/
def moff (lmv : ℕ → ℕ) (ms k : ℕ) : ℕ := ∑ v ∈ Finset.range k, grCnt lmv ms v

theorem moff_zero (lmv : ℕ → ℕ) (ms : ℕ) : moff lmv ms 0 = 0 := by simp [moff]

theorem moff_succ (lmv : ℕ → ℕ) (ms k : ℕ) :
    moff lmv ms (k + 1) = moff lmv ms k + grCnt lmv ms k := by
  rw [moff, moff, Finset.sum_range_succ]

theorem moff_mono (lmv : ℕ → ℕ) (ms : ℕ) {a b : ℕ} (hab : a ≤ b) :
    moff lmv ms a ≤ moff lmv ms b :=
  Finset.sum_le_sum_of_subset (fun x hx => by
    simp only [Finset.mem_range] at hx ⊢; omega)

/-- **The buckets tile the mass**: every member is a vertex, so the
fibres of `lmv` over `[0, N)` partition the log's cells. -/
theorem moff_last (h : GrpLog lo lm od π Xf offL lmv σ) :
    moff lmv (offL N) N = offL N := by
  classical
  have h0 : (Finset.range (offL N)).card
      = ∑ v ∈ Finset.range N,
          ((Finset.range (offL N)).filter (fun p => lmv p = v)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun p hp => Finset.mem_range.mpr (h.lmv_lt (Finset.mem_range.mp hp)))
  rw [Finset.card_range] at h0
  rw [moff]
  exact h0.symm

/-- **Every bucket cell has an owner member.** -/
theorem moff_owner (lmv : ℕ → ℕ) (ms : ℕ) :
    ∀ m : ℕ, ∀ q, q < moff lmv ms m →
      ∃ v : ℕ, v < m ∧ moff lmv ms v ≤ q ∧ q < moff lmv ms (v + 1) := by
  intro m
  induction m with
  | zero => intro q hq; rw [moff_zero] at hq; omega
  | succ m ih =>
      intro q hq
      rcases Nat.lt_or_ge q (moff lmv ms m) with hlt | hge
      · obtain ⟨v, h1, h2, h3⟩ := ih q hlt
        exact ⟨v, by omega, h2, h3⟩
      · exact ⟨m, by omega, hge, hq⟩

/-! ### The address the first sort writes at -/

/-- **The sorted position of member `z` of centre `u`**: its bucket,
plus the cells of that bucket that the log holds before it. This is
the address `grScatCom` writes the centre at, and — because the
buckets are the members in ascending order — the clock the second sort
runs on. -/
noncomputable def spos {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ) (ms : ℕ) (u z : Fin N) : ℕ :=
  moff lmv ms (z : ℕ) + grCnt lmv (logPos π Xf offL lmv u z) (z : ℕ)

/-- The address sits in its own bucket. -/
theorem spos_bucket (h : GrpLog lo lm od π Xf offL lmv σ) {u z : Fin N}
    (hz : z ∈ Xf u) :
    moff lmv (offL N) (z : ℕ) ≤ spos π Xf offL lmv (offL N) u z ∧
      spos π Xf offL lmv (offL N) u z < moff lmv (offL N) ((z : ℕ) + 1) := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [spos, moff_succ]
  have hlt : logPos π Xf offL lmv u z < offL N := logPos_lt h hz
  have := grCnt_lt_of_hit lmv (logPos_spec h hz).2.2 hlt
  omega

/-- The address is a cell of the sorted array. -/
theorem spos_lt (h : GrpLog lo lm od π Xf offL lmv σ) {u z : Fin N}
    (hz : z ∈ Xf u) : spos π Xf offL lmv (offL N) u z < offL N := by
  have h1 := (spos_bucket h hz).2
  have h2 : moff lmv (offL N) ((z : ℕ) + 1) ≤ moff lmv (offL N) N :=
    moff_mono lmv (offL N) z.isLt
  rw [moff_last h] at h2
  omega

/-- **The address is injective**: distinct buckets are disjoint, and
inside a bucket the count pins the log cell, which `logPos_inj` pins
the pair by. -/
theorem spos_inj (h : GrpLog lo lm od π Xf offL lmv σ) {u u' z z' : Fin N}
    (hz : z ∈ Xf u) (hz' : z' ∈ Xf u')
    (he : spos π Xf offL lmv (offL N) u z = spos π Xf offL lmv (offL N) u' z') :
    u = u' ∧ z = z' := by
  obtain ⟨b1, b2⟩ := spos_bucket h hz
  obtain ⟨b1', b2'⟩ := spos_bucket h hz'
  have hzz : (z : ℕ) = (z' : ℕ) := by
    by_contra hne
    rcases Nat.lt_or_ge (z : ℕ) (z' : ℕ) with hlt | hge
    · have := moff_mono lmv (offL N) (show (z : ℕ) + 1 ≤ (z' : ℕ) from hlt)
      omega
    · have hgt : (z' : ℕ) < (z : ℕ) := by omega
      have := moff_mono lmv (offL N) (show (z' : ℕ) + 1 ≤ (z : ℕ) from hgt)
      omega
  obtain rfl : z = z' := Fin.ext hzz
  have hcnt : grCnt lmv (logPos π Xf offL lmv u z) (z : ℕ)
      = grCnt lmv (logPos π Xf offL lmv u' z) (z : ℕ) := by
    rw [spos, spos] at he; omega
  have hpos := grCnt_inj lmv (logPos_spec h hz).2.2 (logPos_spec h hz').2.2 hcnt
  exact logPos_inj h hz hz' hpos

/-- **The address is onto the sorted array**: a cell names a bucket,
the bucket's own count names a log cell, and `logPos_surj` names the
pair. Nothing here is pigeonhole on the pairs — only on one fibre. -/
theorem spos_surj (h : GrpLog lo lm od π Xf offL lmv σ) {q : ℕ} (hq : q < offL N) :
    ∃ u z : Fin N, z ∈ Xf u ∧ spos π Xf offL lmv (offL N) u z = q := by
  classical
  set ms := offL N with hms
  obtain ⟨v, hvN, hv1, hv2⟩ :=
    moff_owner lmv ms N q (by rw [hms, moff_last h]; exact hq)
  rw [moff_succ] at hv2
  -- the fibre of `v`, and the count as a map out of it
  set F : Finset ℕ := (Finset.range ms).filter (fun p => lmv p = v) with hF
  have hFcard : F.card = grCnt lmv ms v := rfl
  have hmaps : ∀ p ∈ F, grCnt lmv p v ∈ Finset.range (grCnt lmv ms v) := by
    intro p hp
    rw [hF, Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_range.mpr (grCnt_lt_of_hit lmv hp.2 hp.1)
  have hinj : ∀ p ∈ F, ∀ p' ∈ F, grCnt lmv p v = grCnt lmv p' v → p = p' := by
    intro p hp p' hp' he
    rw [hF, Finset.mem_filter] at hp hp'
    exact grCnt_inj lmv hp.2 hp'.2 he
  have hcard : (Finset.range (grCnt lmv ms v)).card ≤ F.card := by
    rw [Finset.card_range, hFcard]
  obtain ⟨p, hpF, hpe⟩ :=
    Finset.surj_on_of_inj_on_of_card_le (s := F) (t := Finset.range (grCnt lmv ms v))
      (fun p _ => grCnt lmv p v) hmaps (fun a₁ a₂ h₁ h₂ he => hinj a₁ h₁ a₂ h₂ he)
      hcard (q - moff lmv ms v) (Finset.mem_range.mpr (by omega))
  rw [hF, Finset.mem_filter, Finset.mem_range] at hpF
  obtain ⟨u, z, hzmem, hzpos⟩ := logPos_surj h (by rw [← hms]; exact hpF.1)
  have hzv : (z : ℕ) = v := by rw [← (logPos_spec h hzmem).2.2, hzpos, hpF.2]
  refine ⟨u, z, hzmem, ?_⟩
  rw [spos, hzpos, hzv, ← hpe]
  omega

/-! ### The second sort: the carrier offsets -/

/-- The size of the cluster at carrier position `u`, as a total
function of a plain number. -/
noncomputable def csz {N : ℕ} (Xf : Fin N → Set (Fin N)) (u : ℕ) : ℕ :=
  if h : u < N then (Xf ⟨u, h⟩).ncard else 0

/-- **The carrier offsets** — `ClusterCsr`'s own anchored recursion,
as a function. Empty centres get their (empty) row: the sum runs over
every carrier position (Hazard 1). -/
noncomputable def offC {N : ℕ} (Xf : Fin N → Set (Fin N)) (k : ℕ) : ℕ :=
  ∑ u ∈ Finset.range k, csz Xf u

theorem offC_zero {N : ℕ} (Xf : Fin N → Set (Fin N)) : offC Xf 0 = 0 := by
  simp [offC]

theorem offC_succ {N : ℕ} (Xf : Fin N → Set (Fin N)) (k : ℕ) :
    offC Xf (k + 1) = offC Xf k + csz Xf k := by
  rw [offC, offC, Finset.sum_range_succ]

theorem offC_mono {N : ℕ} (Xf : Fin N → Set (Fin N)) {a b : ℕ} (hab : a ≤ b) :
    offC Xf a ≤ offC Xf b :=
  Finset.sum_le_sum_of_subset (fun x hx => by
    simp only [Finset.mem_range] at hx ⊢; omega)

theorem csz_coe {N : ℕ} (Xf : Fin N → Set (Fin N)) (u : Fin N) :
    csz Xf (u : ℕ) = (Xf u).ncard := by
  rw [csz, dif_pos u.isLt]

/-- **The carrier offsets close at the mass**: the peel order is a
permutation of the carrier, so the two orders sum to the same figure.
This is what lets the second sort's cursor start inside the output. -/
theorem offC_last (h : GrpLog lo lm od π Xf offL lmv σ) : offC Xf N = offL N := by
  have hpre : ∀ k, k ≤ N → offL k
      = ∑ i ∈ Finset.range k,
          if hi : i < N then (Xf (π.symm ⟨i, hi⟩)).ncard else 0 := by
    intro k
    induction k with
    | zero => intro _; simp [h.zero]
    | succ k ih =>
        intro hk
        have hkN : k < N := hk
        rw [Finset.sum_range_succ, ← ih (by omega), dif_pos hkN]
        exact h.step ⟨k, hkN⟩
  rw [hpre N le_rfl,
    Finset.sum_range fun i => if hi : i < N then (Xf (π.symm ⟨i, hi⟩)).ncard else 0]
  have hdif : ∑ i : Fin N,
      (if hi : (i : ℕ) < N then (Xf (π.symm ⟨(i : ℕ), hi⟩)).ncard else 0)
        = ∑ i : Fin N, (Xf (π.symm i)).ncard :=
    Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt, Fin.eta]
  rw [hdif]
  rw [offC, Finset.sum_range fun u => csz Xf u]
  have hc : ∑ u : Fin N, csz Xf (u : ℕ) = ∑ u : Fin N, (Xf u).ncard :=
    Finset.sum_congr rfl fun u _ => csz_coe Xf u
  rw [hc]
  exact (Fintype.sum_equiv π.symm (fun i => (Xf (π.symm i)).ncard)
    (fun u => (Xf u).ncard) (fun _ => rfl)).symm

/-! ### The order the second sort emits in

For a fixed centre, the sorted positions of its members are in the
same order as the members: bucket `z` sits entirely below bucket `z'`
when `z < z'`. That, and nothing else, is the stability the split's
Finding 1 asks for. -/

theorem spos_lt_iff (h : GrpLog lo lm od π Xf offL lmv σ) {u : Fin N} {z z' : Fin N}
    (hz : z ∈ Xf u) (hz' : z' ∈ Xf u) :
    spos π Xf offL lmv (offL N) u z < spos π Xf offL lmv (offL N) u z'
      ↔ (z : ℕ) < (z' : ℕ) := by
  obtain ⟨b1, b2⟩ := spos_bucket h hz
  obtain ⟨b1', b2'⟩ := spos_bucket h hz'
  constructor
  · intro hlt
    rcases Nat.lt_or_ge (z : ℕ) (z' : ℕ) with hc | hc
    · exact hc
    · rcases Nat.eq_or_lt_of_le hc with heq | hgt
      · obtain rfl : z = z' := Fin.ext heq.symm
        omega
      · have := moff_mono lmv (offL N) (show (z' : ℕ) + 1 ≤ (z : ℕ) from hgt)
        omega
  · intro hlt
    have := moff_mono lmv (offL N) (show (z : ℕ) + 1 ≤ (z' : ℕ) from hlt)
    omega


/-! ## §2 The grouping pass: the program

Six flat scans, two of them with an inner scan over a row.  Nothing
reads an array length: the carrier size is the arena's `nN` cell and
the mass is `lo[nN]`. -/

/-- The grouping pass's scratch scalars: the rank counter, the centre,
the running sum and the size it reads out before overwriting the cell,
the log pointer and the row end, the bucket end, the member, the
cursor, and the sorted pointer. -/
def grScalars : List String :=
  ["gp.i", "gp.u", "gp.a", "gp.d", "gp.j", "gp.f", "gp.e", "gp.v", "gp.c", "gp.q"]

/-- The names the grouping keeps apart: it writes `co`, `cm`, `cnt`,
`cur` and `sb`, reads `lo`, `lm` and `od`, and must not disturb the
assignment region `ca`. -/
structure GrpNames (lo lm od ca co cm cnt cur sb : String) : Prop where
  /-- No written region is a read one, or the assignment region. -/
  wr : ∀ b ∈ [co, cm, cnt, cur, sb], b ≠ lo ∧ b ≠ lm ∧ b ≠ od ∧ b ≠ ca
  /-- The membership region is not the offset region. -/
  cm_co : cm ≠ co
  /-- The first sort's counters are not the offsets. -/
  cnt_co : cnt ≠ co
  /-- The second sort's cursor is not the offsets. -/
  cur_co : cur ≠ co
  /-- The sorted centres are not the offsets. -/
  sb_co : sb ≠ co
  /-- The counters are not the memberships. -/
  cnt_cm : cnt ≠ cm
  /-- The cursor is not the memberships. -/
  cur_cm : cur ≠ cm
  /-- The sorted centres are not the memberships. -/
  sb_cm : sb ≠ cm
  /-- The cursor is not the counters. -/
  cur_cnt : cur ≠ cnt
  /-- The sorted centres are not the counters. -/
  sb_cnt : sb ≠ cnt
  /-- The sorted centres are not the cursor. -/
  sb_cur : sb ≠ cur

private theorem grScalars_ne {y : String} (h : y ∉ grScalars) :
    y ≠ "gp.i" ∧ y ≠ "gp.u" ∧ y ≠ "gp.a" ∧ y ≠ "gp.d" ∧ y ≠ "gp.j" ∧
      y ≠ "gp.f" ∧ y ≠ "gp.e" ∧ y ≠ "gp.v" ∧ y ≠ "gp.c" ∧ y ≠ "gp.q" := by
  simp only [grScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- **Pass 1 — the cluster sizes, by rank**: `cur[od[i]] := lo[i+1] −
lo[i]`.  The order region turns the rank-indexed log into a
carrier-indexed count, and because it is a bijection every cell of
`cur` is written — so no zeroing pass is owed. -/
def grLenCom (nN lo od cur : String) : Com :=
  .seq (.assign "gp.i" (.lit 0))
    (Csr.scan "gp.i" nN
      (.seq (.assign "gp.u" (.get od (.var "gp.i")))
        (.seq (.assign "gp.j" (.get lo (.var "gp.i")))
          (.seq (.assign "gp.f" (.get lo (.add (.var "gp.i") (.lit 1))))
            (.seq (.store cur (.var "gp.u") (.sub (.var "gp.f") (.var "gp.j")))
              (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))))

/-- **Pass 2 — the carrier prefix sum**: the offsets into `co` and into
`cur` (which becomes the second sort's cursor), the first sort's
counters zeroed on the way, and the last offset stored at `nN`.  Every
carrier position gets its offset, empty centres included. -/
def grOffCom (nN co cnt cur : String) : Com :=
  .seq (.assign "gp.a" (.lit 0))
    (.seq
      (.seq (.assign "gp.i" (.lit 0))
        (Csr.scan "gp.i" nN
          (.seq (.assign "gp.d" (.get cur (.var "gp.i")))
            (.seq (.store co (.var "gp.i") (.var "gp.a"))
              (.seq (.store cur (.var "gp.i") (.var "gp.a"))
                (.seq (.store cnt (.var "gp.i") (.lit 0))
                  (.seq (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d")))
                    (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))))))
      (.store co (.var nN) (.var "gp.a")))

/-- **Pass 3 — the first sort's count**, one turn a log cell:
`cnt[lm[p]] += 1`.  The extent is `lo[nN]`, the log's own last offset,
one array read. -/
def grCntCom (nN lo lm cnt : String) : Com :=
  .seq (.assign "gp.e" (.get lo (.var nN)))
    (.seq (.assign "gp.j" (.lit 0))
      (Csr.scan "gp.j" "gp.e"
        (.seq (.assign "gp.v" (.get lm (.var "gp.j")))
          (.seq (.store cnt (.var "gp.v") (.add (.get cnt (.var "gp.v")) (.lit 1)))
            (.assign "gp.j" (.add (.var "gp.j") (.lit 1)))))))

/-- **Pass 4 — the first sort's prefix sum**, in place: `cnt[v]` goes
from the bucket's size to the bucket's start. -/
def grMoffCom (nN cnt : String) : Com :=
  .seq (.assign "gp.a" (.lit 0))
    (.seq (.assign "gp.i" (.lit 0))
      (Csr.scan "gp.i" nN
        (.seq (.assign "gp.d" (.get cnt (.var "gp.i")))
          (.seq (.store cnt (.var "gp.i") (.var "gp.a"))
            (.seq (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d")))
              (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))))

/-- One inner turn of the first sort's scatter: read the member, take
its cursor, write the row's centre there and bump. -/
def grScatIn (lm cnt sb : String) : Com :=
  .seq (.assign "gp.v" (.get lm (.var "gp.j")))
    (.seq (.assign "gp.c" (.get cnt (.var "gp.v")))
      (.seq (.store sb (.var "gp.c") (.var "gp.u"))
        (.seq (.store cnt (.var "gp.v") (.add (.var "gp.c") (.lit 1)))
          (.assign "gp.j" (.add (.var "gp.j") (.lit 1))))))

/-- One outer turn: load the rank's centre and its row, and scan it. -/
def grScatOut (lo lm od cnt sb : String) : Com :=
  .seq (.assign "gp.u" (.get od (.var "gp.i")))
    (.seq (.assign "gp.j" (.get lo (.var "gp.i")))
      (.seq (.assign "gp.f" (.get lo (.add (.var "gp.i") (.lit 1))))
        (.seq (Csr.scan "gp.j" "gp.f" (grScatIn lm cnt sb))
          (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))

/-- **Pass 5 — the first sort's scatter**: ranks in increasing order,
each row's cells before the next.  `sb` ends holding the log's centres
grouped by member. -/
def grScatCom (nN lo lm od cnt sb : String) : Com :=
  .seq (.assign "gp.i" (.lit 0)) (Csr.scan "gp.i" nN (grScatOut lo lm od cnt sb))

/-- One inner turn of the second sort's scatter: read the centre, take
its cursor, write the member there and bump. -/
def grEmitIn (sb cur cm : String) : Com :=
  .seq (.assign "gp.u" (.get sb (.var "gp.q")))
    (.seq (.assign "gp.c" (.get cur (.var "gp.u")))
      (.seq (.store cm (.var "gp.c") (.var "gp.v"))
        (.seq (.store cur (.var "gp.u") (.add (.var "gp.c") (.lit 1)))
          (.assign "gp.q" (.add (.var "gp.q") (.lit 1))))))

/-- One outer turn: the bucket of the member ends where the first
sort's cursor stopped, and starts where the running pointer stands. -/
def grEmitOut (cnt sb cur cm : String) : Com :=
  .seq (.assign "gp.e" (.get cnt (.var "gp.v")))
    (.seq (Csr.scan "gp.q" "gp.e" (grEmitIn sb cur cm))
      (.assign "gp.v" (.add (.var "gp.v") (.lit 1))))

/-- **Pass 6 — the second sort's scatter**: members in increasing
order, each bucket before the next, so every row of `cm` is appended
to in ascending member order. -/
def grEmitCom (nN cnt sb cur cm : String) : Com :=
  .seq (.assign "gp.q" (.lit 0))
    (.seq (.assign "gp.v" (.lit 0)) (Csr.scan "gp.v" nN (grEmitOut cnt sb cur cm)))

/-- **The grouping pass**: sizes, carrier prefix sum, member count,
member prefix sum, member scatter, carrier scatter. -/
def grCom (nN lo lm od co cm cnt cur sb : String) : Com :=
  .seq (grLenCom nN lo od cur)
    (.seq (grOffCom nN co cnt cur)
      (.seq (grCntCom nN lo lm cnt)
        (.seq (grMoffCom nN cnt)
          (.seq (grScatCom nN lo lm od cnt sb)
            (grEmitCom nN cnt sb cur cm)))))

/-- **The grouping pass's budget** at `(N, ms)` with `ms` the cluster
mass: two carrier scans at `24` a vertex, a member prefix sum at `18`,
a log scan at `17` a cell, and the two scatters at `23`/`15` a vertex
and `22` a cell apiece. `O(N + ms)`, and no term is a carrier pass per
centre. -/
def grK (N ms : ℕ) : ℕ := 104 * N + 61 * ms + 49

/-- What every pass of the grouping keeps: the log and the order
region, the carrier cell, and the five allocations it writes into. -/
structure GrpFrame (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (σ : Env) : Prop where
  /-- The log and the order region, untouched. -/
  log : GrpLog lo lm od π Xf offL lmv σ
  /-- The carrier size, in its cell. -/
  carrier : σ.vars nN = N
  /-- The offsets fit. -/
  coLen : N + 1 ≤ (σ.arrs co).length
  /-- The memberships fit. -/
  cmLen : offL N ≤ (σ.arrs cm).length
  /-- The counters fit. -/
  cntLen : N ≤ (σ.arrs cnt).length
  /-- The cursor fits. -/
  curLen : N ≤ (σ.arrs cur).length
  /-- The sorted centres fit. -/
  sbLen : offL N ≤ (σ.arrs sb).length

theorem GrpFrame.of_eq {nN lo lm od co cm cnt cur sb : String} {N : ℕ}
    {π : Equiv.Perm (Fin N)} {Xf : Fin N → Set (Fin N)} {offL lmv : ℕ → ℕ}
    {σ : Env} (h : GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ)
    {σ' : Env} (hv : σ'.vars nN = σ.vars nN)
    (hlo : σ'.arrs lo = σ.arrs lo) (hlm : σ'.arrs lm = σ.arrs lm)
    (hod : σ'.arrs od = σ.arrs od)
    (hco : (σ'.arrs co).length = (σ.arrs co).length)
    (hcm : (σ'.arrs cm).length = (σ.arrs cm).length)
    (hcnt : (σ'.arrs cnt).length = (σ.arrs cnt).length)
    (hcur : (σ'.arrs cur).length = (σ.arrs cur).length)
    (hsb : (σ'.arrs sb).length = (σ.arrs sb).length) :
    GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' where
  log := h.log.of_eq hlo hlm hod
  carrier := by rw [hv]; exact h.carrier
  coLen := by rw [hco]; exact h.coLen
  cmLen := by rw [hcm]; exact h.cmLen
  cntLen := by rw [hcnt]; exact h.cntLen
  curLen := by rw [hcur]; exact h.curLen
  sbLen := by rw [hsb]; exact h.sbLen

section Passes

variable {B : ℕ} {nN lo lm od ca co cm cnt cur sb : String} {N : ℕ}
  {π : Equiv.Perm (Fin N)} {Xf : Fin N → Set (Fin N)} {offL lmv : ℕ → ℕ}

/-! ## §3 Pass 1: the cluster sizes, by rank

The one place the order region is read for its own sake.  Because `od`
is a bijection every carrier cell is written exactly once, which is why
the pass owes no zeroing scan and why the invariant is indexed by the
*rank* of a carrier position rather than by the position. -/

/-- The carried state: the frame, the counter inside the carrier, and
`cur` holding the cluster size at every centre whose rank is below the
counter. -/
private def GrpLenInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧ σ.vars "gp.i" ≤ N ∧
    ∀ u : Fin N, ((π u : Fin N) : ℕ) < σ.vars "gp.i" →
      (σ.arrs cur).getD (u : ℕ) 0 = (Xf u).ncard


/-- **Pass 1, discharged**: `cur[u]` ends at `|X_u|` for every carrier
position, at `24` a vertex. -/
theorem grLen_spec (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv)
      (grLenCom nN lo od cur)
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        ∀ u : Fin N, (σ'.arrs cur).getD (u : ℕ) 0 = csz Xf (u : ℕ))
      (24 * N + 6) := by
  obtain ⟨hni, hnu, -, -, hnj, hnf, -, -, -, -⟩ := grScalars_ne hnN
  obtain ⟨hcurlo, hcurlm, hcurod, -⟩ := hnm.wr cur (by simp)
  have hbody : Spec B
      (fun σ => GrpLenInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        σ.vars "gp.i" < N)
      (.seq (.assign "gp.u" (.get od (.var "gp.i")))
        (.seq (.assign "gp.j" (.get lo (.var "gp.i")))
          (.seq (.assign "gp.f" (.get lo (.add (.var "gp.i") (.lit 1))))
            (.seq (.store cur (.var "gp.u") (.sub (.var "gp.f") (.var "gp.j")))
              (.assign "gp.i" (.add (.var "gp.i") (.lit 1)))))))
      (fun σ σ' => GrpLenInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.i" = σ.vars "gp.i" + 1) 20 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hile, hcurv⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "gp.i" = i := ⟨_, rfl⟩
    rw [hi] at hile hlt hcurv
    have hlog := hfr.log
    obtain ⟨u0, hu0⟩ : ∃ u0 : Fin N, u0 = π.symm ⟨i, hlt⟩ := ⟨_, rfl⟩
    have hu0lt : (u0 : ℕ) < N := u0.isLt
    have hodget : (σ.arrs od)[i]? = some (u0 : ℕ) := by
      rw [gget? _ _ (by have := hlog.odLen; omega), hu0]
      exact congrArg some (hlog.odGet ⟨i, hlt⟩)
    have hloget : (σ.arrs lo)[i]? = some (offL i) := by
      rw [gget? _ _ (by have := hlog.loLen; omega), hlog.loGet i (by omega)]
    have hloget1 : (σ.arrs lo)[i + 1]? = some (offL (i + 1)) := by
      rw [gget? _ _ (by have := hlog.loLen; omega), hlog.loGet (i + 1) (by omega)]
    have hstep : offL (i + 1) = offL i + (Xf u0).ncard := by
      rw [hu0]; exact hlog.step ⟨i, hlt⟩
    have hoffi : offL i ≤ offL N := hlog.mono (by omega) le_rfl
    have hoffi1 : offL (i + 1) ≤ offL N := hlog.mono (by omega) le_rfl
    -- the five states of the turn
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.u" (u0 : ℕ) := ⟨_, rfl⟩
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setVar "gp.j" (offL i) := ⟨_, rfl⟩
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setVar "gp.f" (offL (i + 1)) := ⟨_, rfl⟩
    obtain ⟨σ4, e4⟩ : ∃ τ, τ = σ3.setArr cur (u0 : ℕ) (offL (i + 1) - offL i) :=
      ⟨_, rfl⟩
    obtain ⟨σ5, e5⟩ : ∃ τ, τ = σ4.setVar "gp.i" (i + 1) := ⟨_, rfl⟩
    have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
    have a2 : σ2.arrs = σ.arrs := by rw [e2, e1]; simp
    have a3 : σ3.arrs = σ.arrs := by rw [e3, e2, e1]; simp
    have v1i : σ1.vars "gp.i" = i := by rw [e1]; simp [hi]
    have v2i : σ2.vars "gp.i" = i := by rw [e2]; simp [v1i]
    have v3u : σ3.vars "gp.u" = (u0 : ℕ) := by rw [e3, e2, e1]; simp
    have v3j : σ3.vars "gp.j" = offL i := by rw [e3, e2]; simp
    have v3f : σ3.vars "gp.f" = offL (i + 1) := by rw [e3]; simp
    have v4i : σ4.vars "gp.i" = i := by rw [e4, e3, e2]; simp [v1i]
    have r1 : Run B (.assign "gp.u" (.get od (.var "gp.i"))) σ σ1 3 := by
      rw [e1]; exact grun_assign (gget (gvar hi (by omega)) hodget (by omega)) (by simp)
    have r2 : Run B (.assign "gp.j" (.get lo (.var "gp.i"))) σ1 σ2 3 := by
      rw [e2]
      exact grun_assign (gget (gvar v1i (by omega)) (by rw [a1]; exact hloget)
        (by omega)) (by simp)
    have r3 : Run B (.assign "gp.f" (.get lo (.add (.var "gp.i") (.lit 1)))) σ2 σ3 5 := by
      rw [e3]
      exact grun_assign (gget (gadd (gvar v2i (by omega)) (glit (by omega)) (by omega))
        (by rw [a2]; exact hloget1) (by omega)) (by simp)
    have r4 : Run B (.store cur (.var "gp.u") (.sub (.var "gp.f") (.var "gp.j")))
        σ3 σ4 5 := by
      rw [e4]
      exact grun_store (gvar v3u (by omega))
        (gsub (gvar v3f (by omega)) (gvar v3j (by omega)) (by omega))
        (by rw [a3]; have := hfr.curLen; omega) (by simp)
    have r5 : Run B (.assign "gp.i" (.add (.var "gp.i") (.lit 1))) σ4 σ5 4 := by
      rw [e5]
      exact grun_assign (gadd (gvar v4i (by omega)) (glit (by omega)) (by omega)) (by simp)
    -- the frame of the turn
    have a5 : ∀ b, b ≠ cur → σ5.arrs b = σ.arrs b := by
      intro b hb; rw [e5, e4, e3, e2, e1]; simp [hb]
    have len5 : ∀ b, (σ5.arrs b).length = (σ.arrs b).length := by
      intro b; rw [e5, e4, e3, e2, e1]
      simp only [arrs_setVar, length_arrs_setArr]
    have v5nN : σ5.vars nN = σ.vars nN := by
      rw [e5, e4, e3, e2, e1]; simp [hni, hnu, hnj, hnf]
    have v5i : σ5.vars "gp.i" = i + 1 := by rw [e5]; simp
    have a5cur : σ5.arrs cur = (σ.arrs cur).set (u0 : ℕ) (offL (i + 1) - offL i) := by
      rw [e5, e4, e3, e2, e1]; simp
    refine ⟨σ5, _, r1.seq (r2.seq (r3.seq (r4.seq r5))), by omega, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact hfr.of_eq v5nN (a5 lo (Ne.symm hcurlo)) (a5 lm (Ne.symm hcurlm))
        (a5 od (Ne.symm hcurod)) (len5 co) (len5 cm) (len5 cnt) (len5 cur) (len5 sb)
    · rw [v5i]; omega
    · intro u hu
      rw [v5i] at hu
      rw [a5cur]
      by_cases hcase : (u0 : ℕ) = (u : ℕ)
      · have huu : u = u0 := (Fin.ext hcase).symm
        rw [hcase, gsetD_self (by have := hfr.curLen; omega), huu]
        omega
      · rw [gsetD_ne hcase]
        refine hcurv u ?_
        have hne : ((π u : Fin N) : ℕ) ≠ i := by
          intro hc
          refine hcase ?_
          have : (π u : Fin N) = (⟨i, hlt⟩ : Fin N) := Fin.ext hc
          rw [hu0, ← this, Equiv.symm_apply_apply]
        omega
    · rw [v5i, hi]
  refine ((Spec.forRangeZero "gp.i" nN
    (GrpLenInv nN lo lm od co cm cnt cur sb π Xf offL lmv) N 20 (by omega)
    (fun σ hI => hI.2.1) (fun σ hI => hI.1.carrier) hbody).pre ?_).post ?_
  · intro σ hσ
    have hz : (σ.setVar "gp.i" 0).vars "gp.i" = 0 := by simp
    refine ⟨hσ.of_eq (by simp [hni]) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp), by rw [hz]; exact Nat.zero_le N, ?_⟩
    intro u hu
    rw [hz] at hu
    omega
  · rintro σ σ' - ⟨⟨hfr, -, hcurv⟩, hend⟩
    refine ⟨hfr, fun u => ?_⟩
    rw [csz_coe]
    exact hcurv u (by rw [hend]; exact (π u).isLt)

/-! ## §4 Pass 2: the carrier prefix sum

The transpose's in-place trick at the second sort's seam: the sizes in
`cur` become the offsets in `co` and the cursor in `cur` in one scan,
with the size read into a scalar before its cell is overwritten, and
the first sort's counters zeroed on the way — so the whole grouping
owns three scratch regions and not five. -/

/-- The carried state: below the counter the two regions hold the
offsets and `cnt` is zero, above it `cur` still holds the sizes, and
the running sum is the offset at the counter. -/
private def GrpOffInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧ σ.vars "gp.i" ≤ N ∧
    σ.vars "gp.a" = offC Xf (σ.vars "gp.i") ∧
    (∀ k, k < σ.vars "gp.i" → (σ.arrs co).getD k 0 = offC Xf k) ∧
    (∀ k, k < σ.vars "gp.i" → (σ.arrs cur).getD k 0 = offC Xf k) ∧
    (∀ k, k < σ.vars "gp.i" → (σ.arrs cnt).getD k 0 = 0) ∧
    (∀ k, σ.vars "gp.i" ≤ k → k < N → (σ.arrs cur).getD k 0 = csz Xf k)

/-- **Pass 2, discharged**: `co` holds `offC` on `[0, N]`, `cur` is
reset to the row starts and `cnt` to zero, at `24` a vertex. -/
theorem grOff_spec (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        ∀ u : Fin N, (σ.arrs cur).getD (u : ℕ) 0 = csz Xf (u : ℕ))
      (grOffCom nN co cnt cur)
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cnt).getD k 0 = 0))
      (24 * N + 11) := by
  obtain ⟨hni, -, hna, hnd, -, -, -, -, -, -⟩ := grScalars_ne hnN
  obtain ⟨hcolo, hcolm, hcood, -⟩ := hnm.wr co (by simp)
  obtain ⟨hcntlo, hcntlm, hcntod, -⟩ := hnm.wr cnt (by simp)
  obtain ⟨hcurlo, hcurlm, hcurod, -⟩ := hnm.wr cur (by simp)
  have hbody : Spec B
      (fun σ => GrpOffInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        σ.vars "gp.i" < N)
      (.seq (.assign "gp.d" (.get cur (.var "gp.i")))
        (.seq (.store co (.var "gp.i") (.var "gp.a"))
          (.seq (.store cur (.var "gp.i") (.var "gp.a"))
            (.seq (.store cnt (.var "gp.i") (.lit 0))
              (.seq (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d")))
                (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))))
      (fun σ σ' => GrpOffInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.i" = σ.vars "gp.i" + 1) 20 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hile, hav, hco, hcur, hcnt, hsz⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "gp.i" = i := ⟨_, rfl⟩
    rw [hi] at hile hlt hav hco hcur hcnt hsz
    have hlast : offC Xf N = offL N := offC_last hfr.log
    have hmono : ∀ k, k ≤ N → offC Xf k ≤ offL N := by
      intro k hk; rw [← hlast]; exact offC_mono Xf hk
    have hcsz : offC Xf (i + 1) = offC Xf i + csz Xf i := offC_succ Xf i
    have hoffi : offC Xf i ≤ offL N := hmono i (by omega)
    have hoffi1 : offC Xf (i + 1) ≤ offL N := hmono (i + 1) (by omega)
    have hdget : (σ.arrs cur)[i]? = some (csz Xf i) := by
      rw [gget? _ _ (by have := hfr.curLen; omega), hsz i le_rfl hlt]
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.d" (csz Xf i) := ⟨_, rfl⟩
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setArr co i (offC Xf i) := ⟨_, rfl⟩
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setArr cur i (offC Xf i) := ⟨_, rfl⟩
    obtain ⟨σ4, e4⟩ : ∃ τ, τ = σ3.setArr cnt i 0 := ⟨_, rfl⟩
    obtain ⟨σ5, e5⟩ : ∃ τ, τ = σ4.setVar "gp.a" (offC Xf i + csz Xf i) := ⟨_, rfl⟩
    obtain ⟨σ6, e6⟩ : ∃ τ, τ = σ5.setVar "gp.i" (i + 1) := ⟨_, rfl⟩
    have v1i : σ1.vars "gp.i" = i := by rw [e1]; simp [hi]
    have v1a : σ1.vars "gp.a" = offC Xf i := by rw [e1]; simp [hav]
    have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
    have v2i : σ2.vars "gp.i" = i := by rw [e2]; simp [v1i]
    have v2a : σ2.vars "gp.a" = offC Xf i := by rw [e2]; simp [v1a]
    have v3i : σ3.vars "gp.i" = i := by rw [e3]; simp [v2i]
    have v3a : σ3.vars "gp.a" = offC Xf i := by rw [e3]; simp [v2a]
    have v4a : σ4.vars "gp.a" = offC Xf i := by rw [e4]; simp [v3a]
    have v4d : σ4.vars "gp.d" = csz Xf i := by rw [e4, e3, e2, e1]; simp
    have v5i : σ5.vars "gp.i" = i := by rw [e5, e4, e3]; simp [v2i]
    have r1 : Run B (.assign "gp.d" (.get cur (.var "gp.i"))) σ σ1 3 := by
      rw [e1]
      exact grun_assign (gget (gvar hi (by omega)) hdget (by omega)) (by simp)
    have r2 : Run B (.store co (.var "gp.i") (.var "gp.a")) σ1 σ2 3 := by
      rw [e2]
      exact grun_store (gvar v1i (by omega)) (gvar v1a (by omega))
        (by rw [a1]; have := hfr.coLen; omega) (by simp)
    have r3 : Run B (.store cur (.var "gp.i") (.var "gp.a")) σ2 σ3 3 := by
      rw [e3]
      exact grun_store (gvar v2i (by omega)) (gvar v2a (by omega))
        (by rw [e2]; simp only [length_arrs_setArr]; rw [a1]
            have := hfr.curLen; omega)
        (by simp)
    have r4 : Run B (.store cnt (.var "gp.i") (.lit 0)) σ3 σ4 3 := by
      rw [e4]
      exact grun_store (gvar v3i (by omega)) (glit (by omega))
        (by rw [e3, e2]; simp only [length_arrs_setArr]; rw [a1]
            have := hfr.cntLen; omega)
        (by simp)
    have r5 : Run B (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d"))) σ4 σ5 4 := by
      rw [e5]
      exact grun_assign (gadd (gvar v4a (by omega)) (gvar v4d (by omega)) (by omega))
        (by simp)
    have r6 : Run B (.assign "gp.i" (.add (.var "gp.i") (.lit 1))) σ5 σ6 4 := by
      rw [e6]
      exact grun_assign (gadd (gvar v5i (by omega)) (glit (by omega)) (by omega))
        (by simp)
    have a6 : ∀ b, b ≠ co → b ≠ cur → b ≠ cnt → σ6.arrs b = σ.arrs b := by
      intro b h1 h2 h3; rw [e6, e5, e4, e3, e2, e1]; simp [h1, h2, h3]
    have len6 : ∀ b, (σ6.arrs b).length = (σ.arrs b).length := by
      intro b; rw [e6, e5, e4, e3, e2, e1]
      simp only [arrs_setVar, length_arrs_setArr]
    have v6nN : σ6.vars nN = σ.vars nN := by
      rw [e6, e5, e4, e3, e2, e1]; simp [hni, hna, hnd]
    have v6i : σ6.vars "gp.i" = i + 1 := by rw [e6]; simp
    have v6a : σ6.vars "gp.a" = offC Xf i + csz Xf i := by rw [e6, e5]; simp
    have a6co : σ6.arrs co = (σ.arrs co).set i (offC Xf i) := by
      rw [e6, e5, e4, e3, e2, e1]; simp [Ne.symm hnm.cnt_co, Ne.symm hnm.cur_co]
    have a6cur : σ6.arrs cur = (σ.arrs cur).set i (offC Xf i) := by
      rw [e6, e5, e4, e3, e2, e1]; simp [hnm.cur_cnt, hnm.cur_co]
    have a6cnt : σ6.arrs cnt = (σ.arrs cnt).set i 0 := by
      rw [e6, e5, e4, e3, e2, e1]; simp [hnm.cnt_co, Ne.symm hnm.cur_cnt]
    refine ⟨σ6, _, r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6)))), by omega,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hfr.of_eq v6nN (a6 lo (Ne.symm hcolo) (Ne.symm hcurlo) (Ne.symm hcntlo))
        (a6 lm (Ne.symm hcolm) (Ne.symm hcurlm) (Ne.symm hcntlm))
        (a6 od (Ne.symm hcood) (Ne.symm hcurod) (Ne.symm hcntod))
        (len6 co) (len6 cm) (len6 cnt) (len6 cur) (len6 sb)
    · rw [v6i]; omega
    · rw [v6i, v6a, hcsz]
    · intro k hk
      rw [v6i] at hk
      rw [a6co]
      by_cases hik : i = k
      · rw [← hik, gsetD_self (by have := hfr.coLen; omega)]
      · rw [gsetD_ne hik]; exact hco k (by omega)
    · intro k hk
      rw [v6i] at hk
      rw [a6cur]
      by_cases hik : i = k
      · rw [← hik, gsetD_self (by have := hfr.curLen; omega)]
      · rw [gsetD_ne hik]; exact hcur k (by omega)
    · intro k hk
      rw [v6i] at hk
      rw [a6cnt]
      by_cases hik : i = k
      · rw [← hik, gsetD_self (by have := hfr.cntLen; omega)]
      · rw [gsetD_ne hik]; exact hcnt k (by omega)
    · intro k hk1 hk2
      rw [v6i] at hk1
      rw [a6cur, gsetD_ne (by omega)]
      exact hsz k (by omega) hk2
    · rw [v6i, hi]
  have hloop : Spec B
      (fun σ => GrpOffInv nN lo lm od co cm cnt cur sb π Xf offL lmv
        (σ.setVar "gp.i" 0))
      (.seq (.assign "gp.i" (.lit 0)) (Csr.scan "gp.i" nN
        (.seq (.assign "gp.d" (.get cur (.var "gp.i")))
          (.seq (.store co (.var "gp.i") (.var "gp.a"))
            (.seq (.store cur (.var "gp.i") (.var "gp.a"))
              (.seq (.store cnt (.var "gp.i") (.lit 0))
                (.seq (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d")))
                  (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))))))
      (fun _ σ' => GrpOffInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.i" = N) (24 * N + 6) :=
    Spec.forRangeZero "gp.i" nN
      (GrpOffInv nN lo lm od co cm cnt cur sb π Xf offL lmv) N 20 (by omega)
      (fun σ hI => hI.2.1) (fun σ hI => hI.1.carrier) hbody
  have hinit : Spec B
      (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        ∀ u : Fin N, (σ.arrs cur).getD (u : ℕ) 0 = csz Xf (u : ℕ))
      (.assign "gp.a" (.lit 0))
      (fun _ σ' => GrpOffInv nN lo lm od co cm cnt cur sb π Xf offL lmv
        (σ'.setVar "gp.i" 0)) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hsz⟩ := hσ
    refine ⟨σ.setVar "gp.a" 0, 2, grun_assign (glit (by omega)) (by simp), le_rfl, ?_⟩
    have hz : ((σ.setVar "gp.a" 0).setVar "gp.i" 0).vars "gp.i" = 0 := by simp
    refine ⟨hfr.of_eq (by simp [hni, hna]) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp), by rw [hz]; exact Nat.zero_le N, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [hz, offC_zero]; simp
    · intro k hk; rw [hz] at hk; omega
    · intro k hk; rw [hz] at hk; omega
    · intro k hk; rw [hz] at hk; omega
    · intro k _ hk2
      rw [show ((σ.setVar "gp.a" 0).setVar "gp.i" 0).arrs cur = σ.arrs cur from by simp]
      exact hsz ⟨k, hk2⟩
  have hstore : Spec B
      (fun σ => GrpOffInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        σ.vars "gp.i" = N)
      (.store co (.var nN) (.var "gp.a"))
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cnt).getD k 0 = 0)) 3 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, -, hav, hco, hcur, hcnt, -⟩, hend⟩ := hσ
    rw [hend] at hav hco hcur hcnt
    have hlast : offC Xf N = offL N := offC_last hfr.log
    refine ⟨σ.setArr co N (offC Xf N), 3, grun_store (gvar hfr.carrier (by omega))
      (gvar hav (by omega)) (by have := hfr.coLen; omega) (by simp), le_rfl, ?_, ?_,
      ?_, ?_⟩
    · exact hfr.of_eq (by simp) (by simp [Ne.symm hcolo]) (by simp [Ne.symm hcolm])
        (by simp [Ne.symm hcood]) (by simp only [length_arrs_setArr])
        (by simp only [length_arrs_setArr]) (by simp only [length_arrs_setArr])
        (by simp only [length_arrs_setArr]) (by simp only [length_arrs_setArr])
    · intro k hk
      rw [show (σ.setArr co N (offC Xf N)).arrs co = (σ.arrs co).set N (offC Xf N)
        from by simp]
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · rw [gsetD_self (by have := hfr.coLen; omega)]
      · rw [gsetD_ne (by omega)]; exact hco k hlt
    · intro k hk
      rw [show (σ.setArr co N (offC Xf N)).arrs cur = σ.arrs cur
        from by simp [hnm.cur_co]]
      exact hcur k hk
    · intro k hk
      rw [show (σ.setArr co N (offC Xf N)).arrs cnt = σ.arrs cnt
        from by simp [hnm.cnt_co]]
      exact hcnt k hk
  exact (Spec.seq hinit (Spec.seq hloop hstore (fun _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq)) (fun _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq)).mono (by omega)

/-! ## §5 Pass 3: the first sort's count

One turn a log cell, and the extent is the log's own last offset —
`lo[nN]`, one array read.  The pass writes only `cnt`, so the carrier
offsets it inherits ride through untouched. -/

/-- The carried state: the frame, the extent in `gp.e`, the carrier
offsets, and `cnt` holding the member counts below the pointer. -/
private def GrpCntInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
    σ.vars "gp.e" = offL N ∧ σ.vars "gp.j" ≤ offL N ∧
    (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
    (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
    (∀ v, v < N → (σ.arrs cnt).getD v 0 = grCnt lmv (σ.vars "gp.j") v)

/-- **Pass 3, discharged**: `cnt[v]` ends at the number of log cells
holding `v`, at `17` a cell. -/
theorem grCnt_spec (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ.arrs cnt).getD v 0 = 0))
      (grCntCom nN lo lm cnt)
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ'.arrs cnt).getD v 0 = grCnt lmv (offL N) v))
      (17 * offL N + 9) := by
  obtain ⟨-, -, -, -, hnj, -, hne, hnv, -, -⟩ := grScalars_ne hnN
  obtain ⟨hcntlo, hcntlm, hcntod, -⟩ := hnm.wr cnt (by simp)
  have hbody : Spec B
      (fun σ => GrpCntInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        σ.vars "gp.j" < offL N)
      (.seq (.assign "gp.v" (.get lm (.var "gp.j")))
        (.seq (.store cnt (.var "gp.v") (.add (.get cnt (.var "gp.v")) (.lit 1)))
          (.assign "gp.j" (.add (.var "gp.j") (.lit 1)))))
      (fun σ σ' => GrpCntInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.j" = σ.vars "gp.j" + 1) 13 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hev, hjle, hco, hcur, hcntv⟩, hlt⟩ := hσ
    obtain ⟨j, hj⟩ : ∃ j, σ.vars "gp.j" = j := ⟨_, rfl⟩
    rw [hj] at hjle hlt hcntv
    have hlog := hfr.log
    have hvlt : lmv j < N := hlog.lmv_lt hlt
    have hlmget : (σ.arrs lm)[j]? = some (lmv j) := by
      rw [gget? _ _ (by have := hlog.lmLen; omega), hlog.lmGet j hlt]
    have hcv : (σ.arrs cnt).getD (lmv j) 0 = grCnt lmv j (lmv j) := hcntv _ hvlt
    have hcle : grCnt lmv j (lmv j) ≤ j := grCnt_le lmv j (lmv j)
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.v" (lmv j) := ⟨_, rfl⟩
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setArr cnt (lmv j) (grCnt lmv j (lmv j) + 1) :=
      ⟨_, rfl⟩
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setVar "gp.j" (j + 1) := ⟨_, rfl⟩
    have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
    have v1v : σ1.vars "gp.v" = lmv j := by rw [e1]; simp
    have v2j : σ2.vars "gp.j" = j := by rw [e2, e1]; simp [hj]
    have hcget : (σ1.arrs cnt)[lmv j]? = some (grCnt lmv j (lmv j)) := by
      rw [a1, gget? _ _ (by have := hfr.cntLen; omega), hcv]
    have r1 : Run B (.assign "gp.v" (.get lm (.var "gp.j"))) σ σ1 3 := by
      rw [e1]
      exact grun_assign (gget (gvar hj (by omega)) hlmget (by omega)) (by simp)
    have r2 : Run B (.store cnt (.var "gp.v") (.add (.get cnt (.var "gp.v")) (.lit 1)))
        σ1 σ2 6 := by
      rw [e2]
      exact grun_store (gvar v1v (by omega))
        (gadd (gget (gvar v1v (by omega)) hcget (by omega)) (glit (by omega))
          (by omega))
        (by rw [a1]; have := hfr.cntLen; omega) (by simp)
    have r3 : Run B (.assign "gp.j" (.add (.var "gp.j") (.lit 1))) σ2 σ3 4 := by
      rw [e3]
      exact grun_assign (gadd (gvar v2j (by omega)) (glit (by omega)) (by omega))
        (by simp)
    have a3 : ∀ b, b ≠ cnt → σ3.arrs b = σ.arrs b := by
      intro b hb; rw [e3, e2, e1]; simp [hb]
    have len3 : ∀ b, (σ3.arrs b).length = (σ.arrs b).length := by
      intro b; rw [e3, e2, e1]; simp only [arrs_setVar, length_arrs_setArr]
    have v3nN : σ3.vars nN = σ.vars nN := by rw [e3, e2, e1]; simp [hnj, hnv]
    have v3e : σ3.vars "gp.e" = σ.vars "gp.e" := by rw [e3, e2, e1]; simp
    have v3j : σ3.vars "gp.j" = j + 1 := by rw [e3]; simp
    have a3cnt : σ3.arrs cnt
        = (σ.arrs cnt).set (lmv j) (grCnt lmv j (lmv j) + 1) := by
      rw [e3, e2, e1]; simp
    refine ⟨σ3, _, r1.seq (r2.seq r3), by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hfr.of_eq v3nN (a3 lo (Ne.symm hcntlo)) (a3 lm (Ne.symm hcntlm))
        (a3 od (Ne.symm hcntod)) (len3 co) (len3 cm) (len3 cnt) (len3 cur) (len3 sb)
    · rw [v3e]; exact hev
    · rw [v3j]; omega
    · intro k hk; rw [a3 co (Ne.symm hnm.cnt_co)]; exact hco k hk
    · intro k hk; rw [a3 cur hnm.cur_cnt.symm.symm]; exact hcur k hk
    · intro v hv
      rw [v3j, a3cnt, grCnt_succ]
      by_cases hcase : lmv j = v
      · rw [hcase] at hcv ⊢
        rw [gsetD_self (by have := hfr.cntLen; omega), if_pos rfl, ← hcv, hcv]
      · rw [gsetD_ne hcase, if_neg hcase, Nat.add_zero]
        exact hcntv v hv
    · rw [v3j, hj]
  have hloop : Spec B
      (fun σ => GrpCntInv nN lo lm od co cm cnt cur sb π Xf offL lmv
        (σ.setVar "gp.j" 0))
      (.seq (.assign "gp.j" (.lit 0)) (Csr.scan "gp.j" "gp.e"
        (.seq (.assign "gp.v" (.get lm (.var "gp.j")))
          (.seq (.store cnt (.var "gp.v") (.add (.get cnt (.var "gp.v")) (.lit 1)))
            (.assign "gp.j" (.add (.var "gp.j") (.lit 1)))))))
      (fun _ σ' => GrpCntInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.j" = offL N) (17 * offL N + 6) :=
    Spec.forRangeZero "gp.j" "gp.e"
      (GrpCntInv nN lo lm od co cm cnt cur sb π Xf offL lmv) (offL N) 13 hmsB
      (fun σ hI => hI.2.2.1) (fun σ hI => hI.2.1) hbody
  have hinit : Spec B
      (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ.arrs cnt).getD v 0 = 0))
      (.assign "gp.e" (.get lo (.var nN)))
      (fun _ σ' => GrpCntInv nN lo lm od co cm cnt cur sb π Xf offL lmv
        (σ'.setVar "gp.j" 0)) 3 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hco, hcur, hcnt0⟩ := hσ
    have hlog := hfr.log
    have hloget : (σ.arrs lo)[N]? = some (offL N) := by
      rw [gget? _ _ (by have := hlog.loLen; omega), hlog.loGet N le_rfl]
    refine ⟨σ.setVar "gp.e" (offL N), 3,
      grun_assign (gget (gvar hfr.carrier (by omega)) hloget (by omega)) (by simp),
      le_rfl, ?_⟩
    have hz : ((σ.setVar "gp.e" (offL N)).setVar "gp.j" 0).vars "gp.j" = 0 := by simp
    have ha : ((σ.setVar "gp.e" (offL N)).setVar "gp.j" 0).arrs = σ.arrs := by simp
    refine ⟨hfr.of_eq (by simp [hne, hnj]) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp), by simp, by rw [hz]; omega, ?_, ?_, ?_⟩
    · intro k hk; rw [ha]; exact hco k hk
    · intro k hk; rw [ha]; exact hcur k hk
    · intro v hv; rw [ha, hz, grCnt_zero]; exact hcnt0 v hv
  exact (Spec.seq hinit hloop (fun _ _ _ hq => hq)
    (fun σ σ' σ'' _ _ hq => by
      obtain ⟨⟨hfr, -, -, hco, hcur, hcntv⟩, hend⟩ := hq
      exact ⟨hfr, hco, hcur, by rw [hend] at hcntv; exact hcntv⟩)).mono (by omega)

/-! ## §6 Pass 4: the first sort's prefix sum

In place, and with no second offset region: `cnt[v]` goes from the
bucket's size to the bucket's start, and the scatter of §7 will leave
it at the bucket's *end* — which is exactly the bound §8's outer scan
reads. -/

/-- The carried state: below the counter `cnt` holds the bucket starts,
above it the bucket sizes, and the running sum is the start at the
counter. -/
private def GrpMoffInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧ σ.vars "gp.i" ≤ N ∧
    σ.vars "gp.a" = moff lmv (offL N) (σ.vars "gp.i") ∧
    (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
    (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
    (∀ v, v < σ.vars "gp.i" → (σ.arrs cnt).getD v 0 = moff lmv (offL N) v) ∧
    (∀ v, σ.vars "gp.i" ≤ v → v < N →
      (σ.arrs cnt).getD v 0 = grCnt lmv (offL N) v)

/-- **Pass 4, discharged**: `cnt[v]` ends at the start of `v`'s bucket,
at `18` a vertex. -/
theorem grMoff_spec (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ.arrs cnt).getD v 0 = grCnt lmv (offL N) v))
      (grMoffCom nN cnt)
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ'.arrs cnt).getD v 0 = moff lmv (offL N) v))
      (18 * N + 8) := by
  obtain ⟨hni, -, hna, hnd, -, -, -, -, -, -⟩ := grScalars_ne hnN
  obtain ⟨hcntlo, hcntlm, hcntod, -⟩ := hnm.wr cnt (by simp)
  have hbody : Spec B
      (fun σ => GrpMoffInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        σ.vars "gp.i" < N)
      (.seq (.assign "gp.d" (.get cnt (.var "gp.i")))
        (.seq (.store cnt (.var "gp.i") (.var "gp.a"))
          (.seq (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d")))
            (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))
      (fun σ σ' => GrpMoffInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.i" = σ.vars "gp.i" + 1) 14 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hile, hav, hco, hcur, hstart, hsize⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "gp.i" = i := ⟨_, rfl⟩
    rw [hi] at hile hlt hav hstart hsize
    have hlog := hfr.log
    have hlast : moff lmv (offL N) N = offL N := moff_last hlog
    have hmono : ∀ k, k ≤ N → moff lmv (offL N) k ≤ offL N := by
      intro k hk; exact le_trans (moff_mono lmv (offL N) hk) (le_of_eq hlast)
    have hsucc : moff lmv (offL N) (i + 1)
        = moff lmv (offL N) i + grCnt lmv (offL N) i := moff_succ lmv (offL N) i
    have hoi : moff lmv (offL N) i ≤ offL N := hmono i (by omega)
    have hoi1 : moff lmv (offL N) (i + 1) ≤ offL N := hmono (i + 1) (by omega)
    have hdget : (σ.arrs cnt)[i]? = some (grCnt lmv (offL N) i) := by
      rw [gget? _ _ (by have := hfr.cntLen; omega), hsize i le_rfl hlt]
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.d" (grCnt lmv (offL N) i) := ⟨_, rfl⟩
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setArr cnt i (moff lmv (offL N) i) := ⟨_, rfl⟩
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setVar "gp.a"
      (moff lmv (offL N) i + grCnt lmv (offL N) i) := ⟨_, rfl⟩
    obtain ⟨σ4, e4⟩ : ∃ τ, τ = σ3.setVar "gp.i" (i + 1) := ⟨_, rfl⟩
    have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
    have v1i : σ1.vars "gp.i" = i := by rw [e1]; simp [hi]
    have v1a : σ1.vars "gp.a" = moff lmv (offL N) i := by rw [e1]; simp [hav]
    have v2a : σ2.vars "gp.a" = moff lmv (offL N) i := by rw [e2]; simp [v1a]
    have v2d : σ2.vars "gp.d" = grCnt lmv (offL N) i := by rw [e2, e1]; simp
    have v3i : σ3.vars "gp.i" = i := by rw [e3, e2]; simp [v1i]
    have r1 : Run B (.assign "gp.d" (.get cnt (.var "gp.i"))) σ σ1 3 := by
      rw [e1]
      exact grun_assign (gget (gvar hi (by omega)) hdget (by omega)) (by simp)
    have r2 : Run B (.store cnt (.var "gp.i") (.var "gp.a")) σ1 σ2 3 := by
      rw [e2]
      exact grun_store (gvar v1i (by omega)) (gvar v1a (by omega))
        (by rw [a1]; have := hfr.cntLen; omega) (by simp)
    have r3 : Run B (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d"))) σ2 σ3 4 := by
      rw [e3]
      exact grun_assign (gadd (gvar v2a (by omega)) (gvar v2d (by omega)) (by omega))
        (by simp)
    have r4 : Run B (.assign "gp.i" (.add (.var "gp.i") (.lit 1))) σ3 σ4 4 := by
      rw [e4]
      exact grun_assign (gadd (gvar v3i (by omega)) (glit (by omega)) (by omega))
        (by simp)
    have a4 : ∀ b, b ≠ cnt → σ4.arrs b = σ.arrs b := by
      intro b hb; rw [e4, e3, e2, e1]; simp [hb]
    have len4 : ∀ b, (σ4.arrs b).length = (σ.arrs b).length := by
      intro b; rw [e4, e3, e2, e1]; simp only [arrs_setVar, length_arrs_setArr]
    have v4nN : σ4.vars nN = σ.vars nN := by rw [e4, e3, e2, e1]; simp [hni, hna, hnd]
    have v4i : σ4.vars "gp.i" = i + 1 := by rw [e4]; simp
    have v4a : σ4.vars "gp.a" = moff lmv (offL N) i + grCnt lmv (offL N) i := by
      rw [e4, e3]; simp
    have a4cnt : σ4.arrs cnt = (σ.arrs cnt).set i (moff lmv (offL N) i) := by
      rw [e4, e3, e2, e1]; simp
    refine ⟨σ4, _, r1.seq (r2.seq (r3.seq r4)), by omega,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hfr.of_eq v4nN (a4 lo (Ne.symm hcntlo)) (a4 lm (Ne.symm hcntlm))
        (a4 od (Ne.symm hcntod)) (len4 co) (len4 cm) (len4 cnt) (len4 cur) (len4 sb)
    · rw [v4i]; omega
    · rw [v4i, v4a, hsucc]
    · intro k hk; rw [a4 co (Ne.symm hnm.cnt_co)]; exact hco k hk
    · intro k hk; rw [a4 cur hnm.cur_cnt.symm.symm]; exact hcur k hk
    · intro v hv
      rw [v4i] at hv
      rw [a4cnt]
      by_cases hiv : i = v
      · rw [← hiv, gsetD_self (by have := hfr.cntLen; omega)]
      · rw [gsetD_ne hiv]; exact hstart v (by omega)
    · intro v hv1 hv2
      rw [v4i] at hv1
      rw [a4cnt, gsetD_ne (by omega)]
      exact hsize v (by omega) hv2
    · rw [v4i, hi]
  have hloop : Spec B
      (fun σ => GrpMoffInv nN lo lm od co cm cnt cur sb π Xf offL lmv
        (σ.setVar "gp.i" 0))
      (.seq (.assign "gp.i" (.lit 0)) (Csr.scan "gp.i" nN
        (.seq (.assign "gp.d" (.get cnt (.var "gp.i")))
          (.seq (.store cnt (.var "gp.i") (.var "gp.a"))
            (.seq (.assign "gp.a" (.add (.var "gp.a") (.var "gp.d")))
              (.assign "gp.i" (.add (.var "gp.i") (.lit 1))))))))
      (fun _ σ' => GrpMoffInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.i" = N) (18 * N + 6) :=
    Spec.forRangeZero "gp.i" nN
      (GrpMoffInv nN lo lm od co cm cnt cur sb π Xf offL lmv) N 14 (by omega)
      (fun σ hI => hI.2.1) (fun σ hI => hI.1.carrier) hbody
  have hinit : Spec B
      (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ.arrs cnt).getD v 0 = grCnt lmv (offL N) v))
      (.assign "gp.a" (.lit 0))
      (fun _ σ' => GrpMoffInv nN lo lm od co cm cnt cur sb π Xf offL lmv
        (σ'.setVar "gp.i" 0)) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hco, hcur, hsize⟩ := hσ
    refine ⟨σ.setVar "gp.a" 0, 2, grun_assign (glit (by omega)) (by simp), le_rfl, ?_⟩
    have hz : ((σ.setVar "gp.a" 0).setVar "gp.i" 0).vars "gp.i" = 0 := by simp
    have ha : ((σ.setVar "gp.a" 0).setVar "gp.i" 0).arrs = σ.arrs := by simp
    refine ⟨hfr.of_eq (by simp [hni, hna]) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp), by rw [hz]; exact Nat.zero_le N, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [hz, moff_zero]; simp
    · intro k hk; rw [ha]; exact hco k hk
    · intro k hk; rw [ha]; exact hcur k hk
    · intro v hv; rw [hz] at hv; omega
    · intro v _ hv2; rw [ha]; exact hsize v hv2
  exact (Spec.seq hinit hloop (fun _ _ _ hq => hq)
    (fun σ σ' σ'' _ _ hq => by
      obtain ⟨⟨hfr, -, -, hco, hcur, hstart, -⟩, hend⟩ := hq
      exact ⟨hfr, hco, hcur, by rw [hend] at hstart; exact hstart⟩)).mono (by omega)

/-! ## §7 Pass 5: the first sort's scatter

The ranks run in increasing order, so the flat log pointer is also the
scatter's clock: after the cells below `P` have been placed, the cursor
of member `v` stands at `moff v + grCnt lmv P v`.  The carried
statement is therefore not "bucket `v` holds a set of centres" but the
exact address of each — `sb[spos u z] = u` — which pins injectivity
outright and leaves §8 nothing to derive. -/

/-- **What the first sort has built after the log cells below `P`**:
the cursor of each member, and each filled cell holding the centre that
put it there, at the address that centre's own clock determines. -/
structure GrpScatSt (cnt sb : String) {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ) (P : ℕ) (σ : Env) : Prop where
  /-- The cursor of a member. -/
  cursor : ∀ v : Fin N, (σ.arrs cnt).getD (v : ℕ) 0
    = moff lmv (offL N) (v : ℕ) + grCnt lmv P (v : ℕ)
  /-- Each member of each centre whose log cell is below `P` has been
  written at its sorted position. -/
  fill : ∀ u z : Fin N, z ∈ Xf u → logPos π Xf offL lmv u z < P →
    (σ.arrs sb).getD (spos π Xf offL lmv (offL N) u z) 0 = (u : ℕ)

theorem GrpScatSt.of_eq {cnt sb : String} {P : ℕ}
    (h : GrpScatSt cnt sb π Xf offL lmv P σ) {σ' : Env}
    (hcnt : σ'.arrs cnt = σ.arrs cnt) (hsb : σ'.arrs sb = σ.arrs sb) :
    GrpScatSt cnt sb π Xf offL lmv P σ' where
  cursor := by rw [hcnt]; exact h.cursor
  fill := by rw [hsb]; exact h.fill

/-- The carried state of one rank's inner scan. -/
private def GrpScInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (u0 : Fin N) (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
    (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
    (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
    σ.vars "gp.u" = (u0 : ℕ) ∧
    σ.vars "gp.f" = offL (((π u0 : Fin N) : ℕ) + 1) ∧
    offL ((π u0 : Fin N) : ℕ) ≤ σ.vars "gp.j" ∧
    σ.vars "gp.j" ≤ offL (((π u0 : Fin N) : ℕ) + 1) ∧
    GrpScatSt cnt sb π Xf offL lmv (σ.vars "gp.j") σ ∧
    σ.vars "gp.i" = ((π u0 : Fin N) : ℕ)

/-- The carried state of the scatter's outer scan. -/
private def GrpScOInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
    (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
    (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
    σ.vars "gp.i" ≤ N ∧
    GrpScatSt cnt sb π Xf offL lmv (offL (σ.vars "gp.i")) σ

/-- **One inner turn of the first sort's scatter**, at `18`: read the
member, take its cursor, write the row's centre there, bump. -/
private theorem grScatIn_step (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) {u0 : Fin N}
    {σ : Env} (hI : GrpScInv nN lo lm od co cm cnt cur sb π Xf offL lmv u0 σ)
    (hlt : σ.vars "gp.j" < offL (((π u0 : Fin N) : ℕ) + 1)) :
    ∃ σ' K', Run B (grScatIn lm cnt sb) σ σ' K' ∧
      GrpScInv nN lo lm od co cm cnt cur sb π Xf offL lmv u0 σ' ∧
      σ'.vars "gp.j" = σ.vars "gp.j" + 1 ∧ K' ≤ 18 := by
  obtain ⟨-, -, -, -, hnj, -, -, hnv, hnc, -⟩ := grScalars_ne hnN
  obtain ⟨hcntlo, hcntlm, hcntod, -⟩ := hnm.wr cnt (by simp)
  obtain ⟨hsblo, hsblm, hsbod, -⟩ := hnm.wr sb (by simp)
  obtain ⟨hfr, hco, hcur, hu, hf, hj1, hj2, hst, hiv⟩ := hI
  obtain ⟨j, hj⟩ : ∃ j, σ.vars "gp.j" = j := ⟨_, rfl⟩
  rw [hj] at hj1 hj2 hlt hst
  have hlog := hfr.log
  have hrow : ((π u0 : Fin N) : ℕ) < N := (π u0 : Fin N).isLt
  have hjms : j < offL N := lt_of_lt_of_le hlt (hlog.row_le (π u0))
  -- the pair whose cell this is
  obtain ⟨u', z, hzmem, hzpos⟩ := logPos_surj hlog hjms
  obtain ⟨g1, g2, g3⟩ := logPos_spec hlog hzmem
  rw [hzpos] at g1 g2 g3
  have hu' : u' = u0 := by
    have := row_unique hlog (π u' : Fin N).isLt hrow g1 g2 hj1 hlt
    have hpe : (π u' : Fin N) = (π u0 : Fin N) := Fin.ext this
    have := congrArg π.symm hpe
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  rw [hu'] at hzmem hzpos
  have hvlt : (z : ℕ) < N := z.isLt
  have hlmget : (σ.arrs lm)[j]? = some (z : ℕ) := by
    rw [gget? _ _ (by have := hlog.lmLen; omega), hlog.lmGet j hjms, g3]
  -- the address, and that it is the one the cursor holds
  have hspos : spos π Xf offL lmv (offL N) u0 z
      = moff lmv (offL N) (z : ℕ) + grCnt lmv j (z : ℕ) := by
    rw [spos, hzpos]
  have hcv : (σ.arrs cnt).getD (z : ℕ) 0 = spos π Xf offL lmv (offL N) u0 z := by
    rw [hst.cursor z, hspos]
  have hslt : spos π Xf offL lmv (offL N) u0 z < offL N := spos_lt hlog hzmem
  have hcget : (σ.arrs cnt)[(z : ℕ)]? = some (spos π Xf offL lmv (offL N) u0 z) := by
    rw [gget? _ _ (by have := hfr.cntLen; omega), hcv]
  obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.v" (z : ℕ) := ⟨_, rfl⟩
  obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setVar "gp.c" (spos π Xf offL lmv (offL N) u0 z) :=
    ⟨_, rfl⟩
  obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setArr sb (spos π Xf offL lmv (offL N) u0 z)
    (u0 : ℕ) := ⟨_, rfl⟩
  obtain ⟨σ4, e4⟩ : ∃ τ, τ = σ3.setArr cnt (z : ℕ)
    (spos π Xf offL lmv (offL N) u0 z + 1) := ⟨_, rfl⟩
  obtain ⟨σ5, e5⟩ : ∃ τ, τ = σ4.setVar "gp.j" (j + 1) := ⟨_, rfl⟩
  have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
  have a2 : σ2.arrs = σ.arrs := by rw [e2, e1]; simp
  have v1v : σ1.vars "gp.v" = (z : ℕ) := by rw [e1]; simp
  have v2v : σ2.vars "gp.v" = (z : ℕ) := by rw [e2]; simp [v1v]
  have v2c : σ2.vars "gp.c" = spos π Xf offL lmv (offL N) u0 z := by rw [e2]; simp
  have v2u : σ2.vars "gp.u" = (u0 : ℕ) := by rw [e2, e1]; simp [hu]
  have v3v : σ3.vars "gp.v" = (z : ℕ) := by rw [e3]; simp [v2v]
  have v3c : σ3.vars "gp.c" = spos π Xf offL lmv (offL N) u0 z := by rw [e3]; simp [v2c]
  have v4j : σ4.vars "gp.j" = j := by rw [e4, e3, e2, e1]; simp [hj]
  have r1 : Run B (.assign "gp.v" (.get lm (.var "gp.j"))) σ σ1 3 := by
    rw [e1]
    exact grun_assign (gget (gvar hj (by omega)) hlmget (by omega)) (by simp)
  have r2 : Run B (.assign "gp.c" (.get cnt (.var "gp.v"))) σ1 σ2 3 := by
    rw [e2]
    exact grun_assign (gget (gvar v1v (by omega)) (by rw [a1]; exact hcget)
      (by omega)) (by simp)
  have r3 : Run B (.store sb (.var "gp.c") (.var "gp.u")) σ2 σ3 3 := by
    rw [e3]
    exact grun_store (gvar v2c (by omega)) (gvar v2u (by omega))
      (by rw [a2]; have := hfr.sbLen; omega) (by simp)
  have r4 : Run B (.store cnt (.var "gp.v") (.add (.var "gp.c") (.lit 1))) σ3 σ4 5 := by
    rw [e4]
    exact grun_store (gvar v3v (by omega))
      (gadd (gvar v3c (by omega)) (glit (by omega)) (by omega))
      (by rw [e3]; simp only [length_arrs_setArr]; rw [a2]
          have := hfr.cntLen; omega)
      (by simp)
  have r5 : Run B (.assign "gp.j" (.add (.var "gp.j") (.lit 1))) σ4 σ5 4 := by
    rw [e5]
    exact grun_assign (gadd (gvar v4j (by omega)) (glit (by omega)) (by omega))
      (by simp)
  have a5 : ∀ b, b ≠ sb → b ≠ cnt → σ5.arrs b = σ.arrs b := by
    intro b h1 h2; rw [e5, e4, e3, e2, e1]; simp [h1, h2]
  have len5 : ∀ b, (σ5.arrs b).length = (σ.arrs b).length := by
    intro b; rw [e5, e4, e3, e2, e1]; simp only [arrs_setVar, length_arrs_setArr]
  have v5nN : σ5.vars nN = σ.vars nN := by
    rw [e5, e4, e3, e2, e1]; simp [hnj, hnv, hnc]
  have v5u : σ5.vars "gp.u" = (u0 : ℕ) := by rw [e5, e4, e3, e2, e1]; simp [hu]
  have v5f : σ5.vars "gp.f" = offL (((π u0 : Fin N) : ℕ) + 1) := by
    rw [e5, e4, e3, e2, e1]; simp [hf]
  have v5j : σ5.vars "gp.j" = j + 1 := by rw [e5]; simp
  have a5cnt : σ5.arrs cnt
      = (σ.arrs cnt).set (z : ℕ) (spos π Xf offL lmv (offL N) u0 z + 1) := by
    rw [e5, e4, e3, e2, e1]; simp [Ne.symm hnm.sb_cnt]
  have a5sb : σ5.arrs sb
      = (σ.arrs sb).set (spos π Xf offL lmv (offL N) u0 z) (u0 : ℕ) := by
    rw [e5, e4, e3, e2, e1]; simp [hnm.sb_cnt]
  refine ⟨σ5, _, r1.seq (r2.seq (r3.seq (r4.seq r5))), ⟨?_, ?_, ?_, v5u, v5f, ?_, ?_,
    ?_, by rw [e5, e4, e3, e2, e1]; simp [hiv]⟩, by rw [v5j, hj], by omega⟩
  · exact hfr.of_eq v5nN (a5 lo (Ne.symm hsblo) (Ne.symm hcntlo))
      (a5 lm (Ne.symm hsblm) (Ne.symm hcntlm))
      (a5 od (Ne.symm hsbod) (Ne.symm hcntod))
      (len5 co) (len5 cm) (len5 cnt) (len5 cur) (len5 sb)
  · intro k hk
    rw [a5 co (Ne.symm hnm.sb_co) (Ne.symm hnm.cnt_co)]; exact hco k hk
  · intro k hk
    rw [a5 cur (Ne.symm hnm.sb_cur) hnm.cur_cnt]; exact hcur k hk
  · rw [v5j]; omega
  · rw [v5j]; omega
  · refine ⟨fun v => ?_, fun u w hw hlt' => ?_⟩
    · rw [v5j, a5cnt, grCnt_succ]
      by_cases hcase : (z : ℕ) = (v : ℕ)
      · rw [hcase] at hspos ⊢
        rw [gsetD_self (by have := hfr.cntLen; have := v.isLt; omega),
          if_pos (by rw [g3]; exact hcase), hspos]
        omega
      · rw [gsetD_ne hcase, if_neg (by rw [g3]; exact hcase), Nat.add_zero]
        exact hst.cursor v
    · rw [v5j] at hlt'
      rw [a5sb]
      by_cases hcase : spos π Xf offL lmv (offL N) u0 z
          = spos π Xf offL lmv (offL N) u w
      · obtain ⟨rfl, rfl⟩ := spos_inj hlog hzmem hw hcase
        rw [gsetD_self (by have := hfr.sbLen; omega)]
      · rw [gsetD_ne hcase]
        refine hst.fill u w hw ?_
        rcases Nat.lt_or_ge (logPos π Xf offL lmv u w) j with hc | hc
        · exact hc
        · exfalso
          have hle : logPos π Xf offL lmv u w = j := by omega
          obtain ⟨rfl, rfl⟩ := logPos_inj hlog hw hzmem (by rw [hle, hzpos])
          exact hcase rfl

/-- **The first sort's inner scan**: one rank's whole row, at `22` a
cell. -/
private theorem grScatIn_scan (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) {u0 : Fin N}
    (hoff : offL (((π u0 : Fin N) : ℕ) + 1) ≤ offL N) :
    Spec B (fun σ => GrpScInv nN lo lm od co cm cnt cur sb π Xf offL lmv u0 σ ∧
        σ.vars "gp.j" = offL ((π u0 : Fin N) : ℕ))
      (Csr.scan "gp.j" "gp.f" (grScatIn lm cnt sb))
      (fun _ σ' => GrpScInv nN lo lm od co cm cnt cur sb π Xf offL lmv u0 σ' ∧
        σ'.vars "gp.j" = offL (((π u0 : Fin N) : ℕ) + 1))
      (22 * (offL (((π u0 : Fin N) : ℕ) + 1) - offL ((π u0 : Fin N) : ℕ)) + 4) :=
  Csr.rowScan_spec B _ (offL (((π u0 : Fin N) : ℕ) + 1)) 18 "gp.j" "gp.f"
    (grScatIn lm cnt sb)
    (fun σ => GrpScInv nN lo lm od co cm cnt cur sb π Xf offL lmv u0 σ)
    (by omega) (fun _ hI => ⟨hI.2.2.2.2.1, hI.2.2.2.2.2.2.1⟩)
    (fun _ hI hlt => grScatIn_step hnm hnN hNB hmsB hI hlt)
    (fun _ h => h.1) (fun _ h => by have := h.2; omega)


/-- **One outer turn of the first sort's scatter**: load the rank's
centre and its row, and scan it. -/
private theorem grScatOut_step (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) {σ : Env}
    (hO : GrpScOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ)
    (hlt : σ.vars "gp.i" < N) :
    ∃ σ' K', Run B (grScatOut lo lm od cnt sb) σ σ' K' ∧
      GrpScOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
      σ'.vars "gp.i" = σ.vars "gp.i" + 1 ∧
      K' ≤ 19 + 22 * (offL (σ.vars "gp.i" + 1) - offL (σ.vars "gp.i")) := by
  obtain ⟨hni, hnu, -, -, hnj, hnf, -, -, -, -⟩ := grScalars_ne hnN
  obtain ⟨hfr, hco, hcur, hile, hst⟩ := hO
  obtain ⟨i, hi⟩ : ∃ i, σ.vars "gp.i" = i := ⟨_, rfl⟩
  rw [hi] at hile hlt hst
  have hlog := hfr.log
  obtain ⟨u0, hu0⟩ : ∃ u0 : Fin N, u0 = π.symm ⟨i, hlt⟩ := ⟨_, rfl⟩
  have hpu : (π u0 : Fin N) = (⟨i, hlt⟩ : Fin N) := by
    rw [hu0, Equiv.apply_symm_apply]
  have hpuv : ((π u0 : Fin N) : ℕ) = i := by rw [hpu]
  have hodget : (σ.arrs od)[i]? = some (u0 : ℕ) := by
    rw [gget? _ _ (by have := hlog.odLen; omega), hu0]
    exact congrArg some (hlog.odGet ⟨i, hlt⟩)
  have hloget : (σ.arrs lo)[i]? = some (offL i) := by
    rw [gget? _ _ (by have := hlog.loLen; omega), hlog.loGet i (by omega)]
  have hloget1 : (σ.arrs lo)[i + 1]? = some (offL (i + 1)) := by
    rw [gget? _ _ (by have := hlog.loLen; omega), hlog.loGet (i + 1) (by omega)]
  have hmono1 : offL i ≤ offL (i + 1) := hlog.mono (by omega) (by omega)
  have hle1 : offL (i + 1) ≤ offL N := hlog.mono (by omega) le_rfl
  obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.u" (u0 : ℕ) := ⟨_, rfl⟩
  obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setVar "gp.j" (offL i) := ⟨_, rfl⟩
  obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setVar "gp.f" (offL (i + 1)) := ⟨_, rfl⟩
  have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
  have a2 : σ2.arrs = σ.arrs := by rw [e2, e1]; simp
  have a3 : σ3.arrs = σ.arrs := by rw [e3, e2, e1]; simp
  have v1i : σ1.vars "gp.i" = i := by rw [e1]; simp [hi]
  have v2i : σ2.vars "gp.i" = i := by rw [e2]; simp [v1i]
  have v3i : σ3.vars "gp.i" = i := by rw [e3]; simp [v2i]
  have v3j : σ3.vars "gp.j" = offL i := by rw [e3, e2]; simp
  have r1 : Run B (.assign "gp.u" (.get od (.var "gp.i"))) σ σ1 3 := by
    rw [e1]
    exact grun_assign (gget (gvar hi (by omega)) hodget (by have := u0.isLt; omega))
      (by simp)
  have r2 : Run B (.assign "gp.j" (.get lo (.var "gp.i"))) σ1 σ2 3 := by
    rw [e2]
    exact grun_assign (gget (gvar v1i (by omega)) (by rw [a1]; exact hloget)
      (by omega)) (by simp)
  have r3 : Run B (.assign "gp.f" (.get lo (.add (.var "gp.i") (.lit 1)))) σ2 σ3 5 := by
    rw [e3]
    exact grun_assign (gget (gadd (gvar v2i (by omega)) (glit (by omega)) (by omega))
      (by rw [a2]; exact hloget1) (by omega)) (by simp)
  have hI3 : GrpScInv nN lo lm od co cm cnt cur sb π Xf offL lmv u0 σ3 ∧
      σ3.vars "gp.j" = offL ((π u0 : Fin N) : ℕ) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [v3i, hpuv]⟩, by rw [v3j, hpuv]⟩
    · exact hfr.of_eq (by rw [e3, e2, e1]; simp [hnu, hnj, hnf])
        (by rw [a3]) (by rw [a3]) (by rw [a3]) (by rw [a3]) (by rw [a3]) (by rw [a3])
        (by rw [a3]) (by rw [a3])
    · intro k hk; rw [a3]; exact hco k hk
    · intro k hk; rw [a3]; exact hcur k hk
    · rw [e3, e2, e1]; simp
    · rw [e3]; simp [hpuv]
    · rw [v3j, hpuv]
    · rw [v3j, hpuv]; exact hmono1
    · rw [v3j]; exact hst.of_eq (by rw [a3]) (by rw [a3])
  obtain ⟨σ4, hr4, hI4, hj4⟩ :=
    (grScatIn_scan hnm hnN hNB hmsB (u0 := u0) (by rw [hpuv]; exact hle1)).run hI3
  obtain ⟨hfr4, hco4, hcur4, -, -, -, -, hst4, hiv4⟩ := hI4
  rw [hpuv] at hj4 hiv4
  obtain ⟨σ5, e5⟩ : ∃ τ, τ = σ4.setVar "gp.i" (i + 1) := ⟨_, rfl⟩
  have a5 : σ5.arrs = σ4.arrs := by rw [e5]; simp
  have v5i : σ5.vars "gp.i" = i + 1 := by rw [e5]; simp
  have r5 : Run B (.assign "gp.i" (.add (.var "gp.i") (.lit 1))) σ4 σ5 4 := by
    rw [e5]
    exact grun_assign (gadd (gvar hiv4 (by omega)) (glit (by omega)) (by omega))
      (by simp)
  refine ⟨σ5, _, r1.seq (r2.seq (r3.seq (hr4.seq r5))), ⟨?_, ?_, ?_, ?_, ?_⟩,
    by rw [v5i, hi], by rw [hi, hpuv]; omega⟩
  · exact hfr4.of_eq (by rw [e5]; simp [hni]) (by rw [a5]) (by rw [a5]) (by rw [a5])
      (by rw [a5]) (by rw [a5]) (by rw [a5]) (by rw [a5]) (by rw [a5])
  · intro k hk; rw [a5]; exact hco4 k hk
  · intro k hk; rw [a5]; exact hcur4 k hk
  · rw [v5i]; omega
  · rw [v5i]
    rw [hj4] at hst4
    exact hst4.of_eq (by rw [a5]) (by rw [a5])

/-- **The first sort's outer scan**: one turn a rank, `23` a rank and
`22` a log cell. -/
private theorem grScat_scan (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (fun σ => GrpScOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        σ.vars "gp.i" = 0)
      (Csr.scan "gp.i" nN (grScatOut lo lm od cnt sb))
      (fun _ σ' => GrpScOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.i" = N)
      (23 * N + 22 * offL N + 4) := by
  refine (Spec.while_potential (b := .lt (.var "gp.i") (.var nN))
    (fun σ => GrpScOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ)
    (fun σ => 23 * (N - σ.vars "gp.i") + 22 * (offL N - offL (σ.vars "gp.i")))
    (fun σ hO => evalB_condLt_vars (by have := hO.2.2.2.1; omega)
      (by have := hO.1.carrier; omega)) ?_ (fun σ h => h.1) ?_).post ?_
  · intro σ hO hc
    have hlt : σ.vars "gp.i" < N := by
      have h1 := lt_of_condLt_true hc
      have h2 := hO.1.carrier
      omega
    obtain ⟨σ', K', hrun, hO', hv', hK'⟩ := grScatOut_step hnm hnN hNB hmsB hO hlt
    refine ⟨σ', K', hrun, hO', ?_⟩
    have hlog := hO.1.log
    have hm1 : offL (σ.vars "gp.i") ≤ offL (σ.vars "gp.i" + 1) :=
      hlog.mono (by omega) (by omega)
    have hm2 : offL (σ.vars "gp.i" + 1) ≤ offL N := hlog.mono (by omega) le_rfl
    simp only [size_condLt, size_var]
    rw [hv']
    omega
  · intro σ h
    have hz := h.2
    have h0 : offL 0 = 0 := h.1.1.log.zero
    simp only [size_condLt, size_var]
    rw [hz, h0]
    omega
  · rintro σ σ' - ⟨hO', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hO'.1.carrier
    have h3 := hO'.2.2.2.1
    exact ⟨hO', by omega⟩

/-- **Pass 5, discharged**: `sb` holds every centre at the sorted
position of the member it was logged with. -/
theorem grScat_spec (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ.arrs cnt).getD v 0 = moff lmv (offL N) v))
      (grScatCom nN lo lm od cnt sb)
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cur).getD k 0 = offC Xf k) ∧
        GrpScatSt cnt sb π Xf offL lmv (offL N) σ')
      (23 * N + 22 * offL N + 7) := by
  obtain ⟨hni, -, -, -, -, -, -, -, -, -⟩ := grScalars_ne hnN
  have hstart : Spec B
      (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        (∀ v, v < N → (σ.arrs cnt).getD v 0 = moff lmv (offL N) v))
      (.assign "gp.i" (.lit 0))
      (fun _ σ' => GrpScOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.i" = 0) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hco, hcur, hcnt⟩ := hσ
    refine ⟨σ.setVar "gp.i" 0, 2, grun_assign (glit (by omega)) (by simp), le_rfl,
      ⟨?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · exact hfr.of_eq (by simp [hni]) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)
    · intro k hk; rw [show (σ.setVar "gp.i" 0).arrs co = σ.arrs co from by simp]
      exact hco k hk
    · intro k hk; rw [show (σ.setVar "gp.i" 0).arrs cur = σ.arrs cur from by simp]
      exact hcur k hk
    · simp
    · rw [show (σ.setVar "gp.i" 0).vars "gp.i" = 0 from by simp, hfr.log.zero]
      refine ⟨fun v => ?_, fun u z hz hlt => ?_⟩
      · rw [show (σ.setVar "gp.i" 0).arrs cnt = σ.arrs cnt from by simp,
          grCnt_zero, hcnt (v : ℕ) v.isLt]
        omega
      · omega
  refine ((Spec.seq hstart (grScat_scan hnm hnN hNB hmsB) (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => ?_)).mono (by omega))
  obtain ⟨⟨hfr, hco, hcur, -, hst⟩, hend⟩ := hq
  refine ⟨hfr, hco, hcur, ?_⟩
  rw [hend] at hst
  exact hst

/-! ## §8 Pass 6: the second sort's scatter

The members run in increasing order and each row is appended to, so
each row comes out ascending — and `ncard_lt_setEquiv` says the count
of members of `X_u` below `z` *is* `z`'s local name.  So the carried
address is `ClusterCsr`'s own clause, and the pass owes no sortedness
invariant and no pigeonhole at the end. -/

/-- **The local name of a member**, as a plain count: the members of
`X_u` strictly below `z`.  `ncard_lt_setEquiv` identifies it with the
index `Impl.restrictEmb` gives `z`. -/
noncomputable def crank {N : ℕ} (Xf : Fin N → Set (Fin N)) (u z : Fin N) : ℕ :=
  {y : Fin N | y ∈ Xf u ∧ y < z}.ncard

/-- The count *is* the local name — `setEquiv` is `orderIsoOfFin`. -/
theorem crank_setEquiv {N : ℕ} (Xf : Fin N → Set (Fin N)) (u : Fin N)
    (i : Fin (Xf u).ncard) :
    crank Xf u ((setEquiv (Xf u) i : Fin N)) = (i : ℕ) :=
  ncard_lt_setEquiv (Xf u) i

/-- Every member's local name is one of the row's slots. -/
theorem crank_lt {N : ℕ} {Xf : Fin N → Set (Fin N)} {u z : Fin N} (hz : z ∈ Xf u) :
    crank Xf u z < (Xf u).ncard := by
  obtain ⟨i, hi⟩ := exists_setEquiv hz
  rw [← hi, crank_setEquiv]
  exact i.isLt

/-- Distinct members get distinct local names. -/
theorem crank_inj {N : ℕ} {Xf : Fin N → Set (Fin N)} {u z z' : Fin N}
    (hz : z ∈ Xf u) (hz' : z' ∈ Xf u) (h : crank Xf u z = crank Xf u z') : z = z' := by
  obtain ⟨i, hi⟩ := exists_setEquiv hz
  obtain ⟨i', hi'⟩ := exists_setEquiv hz'
  rw [← hi, ← hi', crank_setEquiv, crank_setEquiv] at h
  rw [← hi, ← hi', Fin.ext h]

/-- **The output address determines the pair**: the rows tile the
membership region, and inside a row the local name is injective.  This
is what makes the second scatter's `fill` a statement no store can
disturb. -/
theorem addr_inj {N : ℕ} {Xf : Fin N → Set (Fin N)} {u u' z z' : Fin N}
    (hz : z ∈ Xf u) (hz' : z' ∈ Xf u')
    (h : offC Xf (u : ℕ) + crank Xf u z = offC Xf (u' : ℕ) + crank Xf u' z') :
    u = u' ∧ z = z' := by
  have h1 : offC Xf ((u : ℕ) + 1) = offC Xf (u : ℕ) + (Xf u).ncard := by
    rw [offC_succ, csz_coe]
  have h2 : offC Xf ((u' : ℕ) + 1) = offC Xf (u' : ℕ) + (Xf u').ncard := by
    rw [offC_succ, csz_coe]
  have k1 := crank_lt hz
  have k2 := crank_lt hz'
  have huu : (u : ℕ) = (u' : ℕ) := by
    rcases Nat.lt_trichotomy (u : ℕ) (u' : ℕ) with hc | hc | hc
    · have := offC_mono Xf (show (u : ℕ) + 1 ≤ (u' : ℕ) from hc)
      omega
    · exact hc
    · have := offC_mono Xf (show (u' : ℕ) + 1 ≤ (u : ℕ) from hc)
      omega
  obtain rfl : u = u' := Fin.ext huu
  exact ⟨rfl, crank_inj hz hz' (by omega)⟩

/-- **A cell of the sorted array lies in one bucket only.** -/
theorem bucket_unique (lmv : ℕ → ℕ) (ms : ℕ) {a b q : ℕ}
    (h1 : moff lmv ms a ≤ q) (h2 : q < moff lmv ms (a + 1))
    (h3 : moff lmv ms b ≤ q) (h4 : q < moff lmv ms (b + 1)) : a = b := by
  rcases Nat.lt_trichotomy a b with hc | hc | hc
  · have := moff_mono lmv ms (show a + 1 ≤ b from hc)
    omega
  · exact hc
  · have := moff_mono lmv ms (show b + 1 ≤ a from hc)
    omega

/-- **What the second sort has emitted after the sorted cells below
`Q`**: the count of a centre's members already placed, and each of them
at the address its own local name gives. -/
structure GrpEmitSt (cur cm : String) {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ) (Q : ℕ) (σ : Env) : Prop where
  /-- The cursor of a centre. -/
  cursor : ∀ u : Fin N, (σ.arrs cur).getD (u : ℕ) 0
    = offC Xf (u : ℕ)
      + {z : Fin N | z ∈ Xf u ∧ spos π Xf offL lmv (offL N) u z < Q}.ncard
  /-- Every member whose sorted cell is below `Q` sits at its local
  name inside its centre's row. -/
  fill : ∀ u z : Fin N, z ∈ Xf u → spos π Xf offL lmv (offL N) u z < Q →
    (σ.arrs cm).getD (offC Xf (u : ℕ) + crank Xf u z) 0 = (z : ℕ)

theorem GrpEmitSt.of_eq {cur cm : String} {Q : ℕ}
    (h : GrpEmitSt cur cm π Xf offL lmv Q σ) {σ' : Env}
    (hcur : σ'.arrs cur = σ.arrs cur) (hcm : σ'.arrs cm = σ.arrs cm) :
    GrpEmitSt cur cm π Xf offL lmv Q σ' where
  cursor := by rw [hcur]; exact h.cursor
  fill := by rw [hcm]; exact h.fill

/-- **The cursor of a centre at a member's own cell is its local
name**: the sorted cells of a centre's members are in the same order as
the members, so the members already placed are exactly those below the
one arriving. -/
theorem emitted_eq_crank (h : GrpLog lo lm od π Xf offL lmv σ) {u z : Fin N}
    (hz : z ∈ Xf u) :
    {y : Fin N | y ∈ Xf u ∧ spos π Xf offL lmv (offL N) u y
        < spos π Xf offL lmv (offL N) u z}.ncard = crank Xf u z := by
  rw [crank]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy, hlt⟩
    exact ⟨hy, (spos_lt_iff h hy hz).mp hlt⟩
  · rintro ⟨hy, hlt⟩
    exact ⟨hy, (spos_lt_iff h hy hz).mpr hlt⟩

/-- The carried state of one bucket's inner scan. -/
private def GrpEmInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (v : Fin N) (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
    (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
    GrpScatSt cnt sb π Xf offL lmv (offL N) σ ∧
    σ.vars "gp.v" = (v : ℕ) ∧
    σ.vars "gp.e" = moff lmv (offL N) ((v : ℕ) + 1) ∧
    moff lmv (offL N) (v : ℕ) ≤ σ.vars "gp.q" ∧
    σ.vars "gp.q" ≤ moff lmv (offL N) ((v : ℕ) + 1) ∧
    GrpEmitSt cur cm π Xf offL lmv (σ.vars "gp.q") σ

/-- The carried state of the second sort's outer scan. -/
private def GrpEmOInv (nN lo lm od co cm cnt cur sb : String) {N : ℕ}
    (π : Equiv.Perm (Fin N)) (Xf : Fin N → Set (Fin N)) (offL lmv : ℕ → ℕ)
    (σ : Env) : Prop :=
  GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
    (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
    GrpScatSt cnt sb π Xf offL lmv (offL N) σ ∧
    σ.vars "gp.v" ≤ N ∧
    σ.vars "gp.q" = moff lmv (offL N) (σ.vars "gp.v") ∧
    GrpEmitSt cur cm π Xf offL lmv (σ.vars "gp.q") σ

/-- **One inner turn of the second sort's scatter**, at `18`: read the
centre, take its cursor, write the member there, bump. -/
private theorem grEmitIn_step (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) {v : Fin N}
    {σ : Env} (hI : GrpEmInv nN lo lm od co cm cnt cur sb π Xf offL lmv v σ)
    (hlt : σ.vars "gp.q" < moff lmv (offL N) ((v : ℕ) + 1)) :
    ∃ σ' K', Run B (grEmitIn sb cur cm) σ σ' K' ∧
      GrpEmInv nN lo lm od co cm cnt cur sb π Xf offL lmv v σ' ∧
      σ'.vars "gp.q" = σ.vars "gp.q" + 1 ∧ K' ≤ 18 := by
  obtain ⟨-, hnu, -, -, -, -, hne, hnv, hnc, hnq⟩ := grScalars_ne hnN
  obtain ⟨hcurlo, hcurlm, hcurod, -⟩ := hnm.wr cur (by simp)
  obtain ⟨hcmlo, hcmlm, hcmod, -⟩ := hnm.wr cm (by simp)
  obtain ⟨hfr, hco, hsc, hvv, hev, hq1, hq2, hem⟩ := hI
  obtain ⟨q, hq⟩ : ∃ q, σ.vars "gp.q" = q := ⟨_, rfl⟩
  rw [hq] at hq1 hq2 hlt hem
  have hlog := hfr.log
  have hmlast : moff lmv (offL N) N = offL N := moff_last hlog
  have hqms : q < offL N := by
    have := moff_mono lmv (offL N) (show (v : ℕ) + 1 ≤ N from v.isLt)
    omega
  -- the pair whose sorted cell this is
  obtain ⟨u0, z0, hz0, hs0⟩ := spos_surj hlog hqms
  obtain ⟨hb1, hb2⟩ := spos_bucket hlog hz0
  rw [hs0] at hb1 hb2
  have hzv : (z0 : ℕ) = (v : ℕ) := bucket_unique lmv (offL N) hb1 hb2 hq1 hlt
  have hveq : z0 = v := Fin.ext hzv
  rw [hveq] at hz0 hs0
  have hu0lt : (u0 : ℕ) < N := u0.isLt
  have hsbv : (σ.arrs sb).getD q 0 = (u0 : ℕ) := by
    rw [← hs0]
    exact hsc.fill u0 v hz0 (logPos_lt hlog hz0)
  have hsbget : (σ.arrs sb)[q]? = some (u0 : ℕ) := by
    rw [gget? _ _ (by have := hfr.sbLen; omega), hsbv]
  -- the address it goes to
  have hcrk : {z : Fin N | z ∈ Xf u0 ∧ spos π Xf offL lmv (offL N) u0 z < q}.ncard
      = crank Xf u0 v := by rw [← hs0]; exact emitted_eq_crank hlog hz0
  have hcurv : (σ.arrs cur).getD (u0 : ℕ) 0 = offC Xf (u0 : ℕ) + crank Xf u0 v := by
    rw [hem.cursor u0, hcrk]
  have hklt : crank Xf u0 v < (Xf u0).ncard := crank_lt hz0
  have hsucc : offC Xf ((u0 : ℕ) + 1) = offC Xf (u0 : ℕ) + (Xf u0).ncard := by
    rw [offC_succ, csz_coe]
  have hlast : offC Xf N = offL N := offC_last hlog
  have haddr : offC Xf (u0 : ℕ) + crank Xf u0 v < offL N := by
    have := offC_mono Xf (show (u0 : ℕ) + 1 ≤ N from hu0lt)
    omega
  have hcurget : (σ.arrs cur)[(u0 : ℕ)]?
      = some (offC Xf (u0 : ℕ) + crank Xf u0 v) := by
    rw [gget? _ _ (by have := hfr.curLen; omega), hcurv]
  obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.u" (u0 : ℕ) := ⟨_, rfl⟩
  obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setVar "gp.c"
    (offC Xf (u0 : ℕ) + crank Xf u0 v) := ⟨_, rfl⟩
  obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setArr cm (offC Xf (u0 : ℕ) + crank Xf u0 v)
    (v : ℕ) := ⟨_, rfl⟩
  obtain ⟨σ4, e4⟩ : ∃ τ, τ = σ3.setArr cur (u0 : ℕ)
    (offC Xf (u0 : ℕ) + crank Xf u0 v + 1) := ⟨_, rfl⟩
  obtain ⟨σ5, e5⟩ : ∃ τ, τ = σ4.setVar "gp.q" (q + 1) := ⟨_, rfl⟩
  have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
  have a2 : σ2.arrs = σ.arrs := by rw [e2, e1]; simp
  have v1u : σ1.vars "gp.u" = (u0 : ℕ) := by rw [e1]; simp
  have v2u : σ2.vars "gp.u" = (u0 : ℕ) := by rw [e2]; simp [v1u]
  have v2c : σ2.vars "gp.c" = offC Xf (u0 : ℕ) + crank Xf u0 v := by rw [e2]; simp
  have v2v : σ2.vars "gp.v" = (v : ℕ) := by rw [e2, e1]; simp [hvv]
  have v3u : σ3.vars "gp.u" = (u0 : ℕ) := by rw [e3]; simp [v2u]
  have v3c : σ3.vars "gp.c" = offC Xf (u0 : ℕ) + crank Xf u0 v := by rw [e3]; simp [v2c]
  have v4q : σ4.vars "gp.q" = q := by rw [e4, e3, e2, e1]; simp [hq]
  have r1 : Run B (.assign "gp.u" (.get sb (.var "gp.q"))) σ σ1 3 := by
    rw [e1]
    exact grun_assign (gget (gvar hq (by omega)) hsbget (by omega)) (by simp)
  have r2 : Run B (.assign "gp.c" (.get cur (.var "gp.u"))) σ1 σ2 3 := by
    rw [e2]
    exact grun_assign (gget (gvar v1u (by omega)) (by rw [a1]; exact hcurget)
      (by omega)) (by simp)
  have r3 : Run B (.store cm (.var "gp.c") (.var "gp.v")) σ2 σ3 3 := by
    rw [e3]
    exact grun_store (gvar v2c (by omega)) (gvar v2v (by have := v.isLt; omega))
      (by rw [a2]; have := hfr.cmLen; omega) (by simp)
  have r4 : Run B (.store cur (.var "gp.u") (.add (.var "gp.c") (.lit 1)))
      σ3 σ4 5 := by
    rw [e4]
    exact grun_store (gvar v3u (by omega))
      (gadd (gvar v3c (by omega)) (glit (by omega)) (by omega))
      (by rw [e3]; simp only [length_arrs_setArr]; rw [a2]
          have := hfr.curLen; omega)
      (by simp)
  have r5 : Run B (.assign "gp.q" (.add (.var "gp.q") (.lit 1))) σ4 σ5 4 := by
    rw [e5]
    exact grun_assign (gadd (gvar v4q (by omega)) (glit (by omega)) (by omega))
      (by simp)
  have a5 : ∀ b, b ≠ cm → b ≠ cur → σ5.arrs b = σ.arrs b := by
    intro b h1 h2; rw [e5, e4, e3, e2, e1]; simp [h1, h2]
  have len5 : ∀ b, (σ5.arrs b).length = (σ.arrs b).length := by
    intro b; rw [e5, e4, e3, e2, e1]; simp only [arrs_setVar, length_arrs_setArr]
  have v5nN : σ5.vars nN = σ.vars nN := by
    rw [e5, e4, e3, e2, e1]; simp [hnu, hnc, hnq]
  have v5v : σ5.vars "gp.v" = (v : ℕ) := by rw [e5, e4, e3, e2, e1]; simp [hvv]
  have v5e : σ5.vars "gp.e" = moff lmv (offL N) ((v : ℕ) + 1) := by
    rw [e5, e4, e3, e2, e1]; simp [hev]
  have v5q : σ5.vars "gp.q" = q + 1 := by rw [e5]; simp
  have a5cm : σ5.arrs cm
      = (σ.arrs cm).set (offC Xf (u0 : ℕ) + crank Xf u0 v) (v : ℕ) := by
    rw [e5, e4, e3, e2, e1]; simp [Ne.symm hnm.cur_cm]
  have a5cur : σ5.arrs cur
      = (σ.arrs cur).set (u0 : ℕ) (offC Xf (u0 : ℕ) + crank Xf u0 v + 1) := by
    rw [e5, e4, e3, e2, e1]; simp [hnm.cur_cm]
  refine ⟨σ5, _, r1.seq (r2.seq (r3.seq (r4.seq r5))),
    ⟨?_, ?_, ?_, v5v, v5e, ?_, ?_, ?_⟩, by rw [v5q, hq], by omega⟩
  · exact hfr.of_eq v5nN (a5 lo (Ne.symm hcmlo) (Ne.symm hcurlo))
      (a5 lm (Ne.symm hcmlm) (Ne.symm hcurlm))
      (a5 od (Ne.symm hcmod) (Ne.symm hcurod))
      (len5 co) (len5 cm) (len5 cnt) (len5 cur) (len5 sb)
  · intro k hk; rw [a5 co (Ne.symm hnm.cm_co) (Ne.symm hnm.cur_co)]; exact hco k hk
  · exact hsc.of_eq (a5 cnt hnm.cnt_cm (Ne.symm hnm.cur_cnt))
      (a5 sb hnm.sb_cm hnm.sb_cur)
  · rw [v5q]; omega
  · rw [v5q]; omega
  · refine ⟨fun u => ?_, fun u w hw hlt' => ?_⟩
    · rw [v5q, a5cur]
      by_cases hcase : (u0 : ℕ) = (u : ℕ)
      · have hu0u : u = u0 := (Fin.ext hcase).symm
        rw [hu0u, gsetD_self (by have := hfr.curLen; omega)]
        have hins : {z : Fin N | z ∈ Xf u0 ∧
            spos π Xf offL lmv (offL N) u0 z < q + 1}
            = insert v {z : Fin N | z ∈ Xf u0 ∧
              spos π Xf offL lmv (offL N) u0 z < q} := by
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
          constructor
          · rintro ⟨hy, hlty⟩
            rcases Nat.lt_or_ge (spos π Xf offL lmv (offL N) u0 y) q with hc | hc
            · exact Or.inr ⟨hy, hc⟩
            · have hEq : spos π Xf offL lmv (offL N) u0 y
                  = spos π Xf offL lmv (offL N) u0 v := by omega
              exact Or.inl (spos_inj hlog hy hz0 hEq).2
          · rintro (rfl | ⟨hy, hlty⟩)
            · exact ⟨hz0, by omega⟩
            · exact ⟨hy, by omega⟩
        have hnotmem : v ∉ {z : Fin N | z ∈ Xf u0 ∧
            spos π Xf offL lmv (offL N) u0 z < q} := by
          simp only [Set.mem_setOf_eq]
          rintro ⟨-, hc⟩
          omega
        rw [hins, Set.ncard_insert_of_notMem hnotmem (Set.toFinite _), hcrk]
        omega
      · rw [gsetD_ne hcase]
        have heq : {z : Fin N | z ∈ Xf u ∧
            spos π Xf offL lmv (offL N) u z < q + 1}
            = {z : Fin N | z ∈ Xf u ∧ spos π Xf offL lmv (offL N) u z < q} := by
          ext y
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨hy, hlty⟩
            refine ⟨hy, ?_⟩
            rcases Nat.lt_or_ge (spos π Xf offL lmv (offL N) u y) q with hc | hc
            · exact hc
            · exfalso
              have hEq : spos π Xf offL lmv (offL N) u y
                  = spos π Xf offL lmv (offL N) u0 v := by omega
              exact hcase (congrArg (fun w : Fin N => (w : ℕ))
                (spos_inj hlog hy hz0 hEq).1).symm
          · rintro ⟨hy, hlty⟩
            exact ⟨hy, by omega⟩
        rw [heq]
        exact hem.cursor u
    · rw [v5q] at hlt'
      rw [a5cm]
      by_cases hcase : offC Xf (u0 : ℕ) + crank Xf u0 v
          = offC Xf (u : ℕ) + crank Xf u w
      · obtain ⟨-, hvw⟩ := addr_inj hz0 hw hcase
        rw [hcase, gsetD_self (by have := hfr.cmLen; omega), hvw]
      · rw [gsetD_ne hcase]
        refine hem.fill u w hw ?_
        rcases Nat.lt_or_ge (spos π Xf offL lmv (offL N) u w) q with hc | hc
        · exact hc
        · exfalso
          have hEq : spos π Xf offL lmv (offL N) u w
              = spos π Xf offL lmv (offL N) u0 v := by omega
          obtain ⟨hu1, hw1⟩ := spos_inj hlog hw hz0 hEq
          exact hcase (by rw [hu1, hw1])

/-- **The second sort's inner scan**: one member's whole bucket, at
`22` a cell. -/
private theorem grEmitIn_scan (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) {v : Fin N}
    (hoff : moff lmv (offL N) ((v : ℕ) + 1) ≤ offL N) :
    Spec B (fun σ => GrpEmInv nN lo lm od co cm cnt cur sb π Xf offL lmv v σ ∧
        σ.vars "gp.q" = moff lmv (offL N) (v : ℕ))
      (Csr.scan "gp.q" "gp.e" (grEmitIn sb cur cm))
      (fun _ σ' => GrpEmInv nN lo lm od co cm cnt cur sb π Xf offL lmv v σ' ∧
        σ'.vars "gp.q" = moff lmv (offL N) ((v : ℕ) + 1))
      (22 * (moff lmv (offL N) ((v : ℕ) + 1) - moff lmv (offL N) (v : ℕ)) + 4) :=
  Csr.rowScan_spec B _ (moff lmv (offL N) ((v : ℕ) + 1)) 18 "gp.q" "gp.e"
    (grEmitIn sb cur cm)
    (fun σ => GrpEmInv nN lo lm od co cm cnt cur sb π Xf offL lmv v σ)
    (by omega) (fun _ hI => ⟨hI.2.2.2.2.1, hI.2.2.2.2.2.2.1⟩)
    (fun _ hI hlt => grEmitIn_step hnm hnN hNB hmsB hI hlt)
    (fun _ h => h.1) (fun _ h => by have := h.2; omega)

/-- **One outer turn of the second sort's scatter**: the bucket ends
where the first sort's cursor stopped, and begins where the running
pointer stands. -/
private theorem grEmitOut_step (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) {σ : Env}
    (hO : GrpEmOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ)
    (hlt : σ.vars "gp.v" < N) :
    ∃ σ' K', Run B (grEmitOut cnt sb cur cm) σ σ' K' ∧
      GrpEmOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
      σ'.vars "gp.v" = σ.vars "gp.v" + 1 ∧
      K' ≤ 11 + 22 * (moff lmv (offL N) (σ.vars "gp.v" + 1)
        - moff lmv (offL N) (σ.vars "gp.v")) := by
  obtain ⟨hni, -, -, -, -, -, hne, hnv, -, hnq⟩ := grScalars_ne hnN
  obtain ⟨hfr, hco, hsc, hile, hqv, hem⟩ := hO
  obtain ⟨i, hi⟩ : ∃ i, σ.vars "gp.v" = i := ⟨_, rfl⟩
  rw [hi] at hile hlt hqv
  have hlog := hfr.log
  have hmlast : moff lmv (offL N) N = offL N := moff_last hlog
  have hmono1 : moff lmv (offL N) i ≤ moff lmv (offL N) (i + 1) :=
    moff_mono lmv (offL N) (by omega)
  have hle1 : moff lmv (offL N) (i + 1) ≤ offL N := by
    have := moff_mono lmv (offL N) (show i + 1 ≤ N from hlt)
    omega
  have hcntv : (σ.arrs cnt).getD i 0 = moff lmv (offL N) (i + 1) := by
    have := hsc.cursor ⟨i, hlt⟩
    rw [moff_succ]
    exact this
  have hcntget : (σ.arrs cnt)[i]? = some (moff lmv (offL N) (i + 1)) := by
    rw [gget? _ _ (by have := hfr.cntLen; omega), hcntv]
  obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setVar "gp.e" (moff lmv (offL N) (i + 1)) := ⟨_, rfl⟩
  have a1 : σ1.arrs = σ.arrs := by rw [e1]; simp
  have r1 : Run B (.assign "gp.e" (.get cnt (.var "gp.v"))) σ σ1 3 := by
    rw [e1]
    exact grun_assign (gget (gvar hi (by omega)) hcntget (by omega)) (by simp)
  have hI1 : GrpEmInv nN lo lm od co cm cnt cur sb π Xf offL lmv ⟨i, hlt⟩ σ1 ∧
      σ1.vars "gp.q" = moff lmv (offL N) ((⟨i, hlt⟩ : Fin N) : ℕ) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [e1]; simp [hqv]⟩
    · exact hfr.of_eq (by rw [e1]; simp [hne]) (by rw [a1]) (by rw [a1]) (by rw [a1])
        (by rw [a1]) (by rw [a1]) (by rw [a1]) (by rw [a1]) (by rw [a1])
    · intro k hk; rw [a1]; exact hco k hk
    · exact hsc.of_eq (by rw [a1]) (by rw [a1])
    · rw [e1]; simp [hi]
    · rw [e1]; simp
    · rw [e1]; simp [hqv]
    · rw [e1]; simp [hqv]; exact hmono1
    · rw [e1]
      simp only [vars_setVar]
      rw [show (if "gp.q" = "gp.e" then moff lmv (offL N) (i + 1) else σ.vars "gp.q")
        = σ.vars "gp.q" from by simp]
      exact hem.of_eq (by rw [← e1, a1]) (by rw [← e1, a1])
  obtain ⟨σ2, hr2, hI2, hq2⟩ :=
    (grEmitIn_scan hnm hnN hNB hmsB (v := ⟨i, hlt⟩) (by simpa using hle1)).run hI1
  obtain ⟨hfr2, hco2, hsc2, hvv2, -, -, -, hem2⟩ := hI2
  simp only at hq2 hvv2
  obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setVar "gp.v" (i + 1) := ⟨_, rfl⟩
  have a3 : σ3.arrs = σ2.arrs := by rw [e3]; simp
  have v3v : σ3.vars "gp.v" = i + 1 := by rw [e3]; simp
  have v3q : σ3.vars "gp.q" = σ2.vars "gp.q" := by rw [e3]; simp
  have r3 : Run B (.assign "gp.v" (.add (.var "gp.v") (.lit 1))) σ2 σ3 4 := by
    rw [e3]
    exact grun_assign (gadd (gvar hvv2 (by omega)) (glit (by omega)) (by omega))
      (by simp)
  have hfv : ((⟨i, hlt⟩ : Fin N) : ℕ) = i := rfl
  refine ⟨σ3, _, r1.seq (hr2.seq r3), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [v3v, hi], by rw [hi, hfv]; omega⟩
  · exact hfr2.of_eq (by rw [e3]; simp [hnv]) (by rw [a3]) (by rw [a3]) (by rw [a3])
      (by rw [a3]) (by rw [a3]) (by rw [a3]) (by rw [a3]) (by rw [a3])
  · intro k hk; rw [a3]; exact hco2 k hk
  · exact hsc2.of_eq (by rw [a3]) (by rw [a3])
  · rw [v3v]; omega
  · rw [v3v, v3q, hq2]
  · rw [v3q]; exact hem2.of_eq (by rw [a3]) (by rw [a3])

/-- **The second sort's outer scan**: one turn a member, `15` a member
and `22` a sorted cell. -/
private theorem grEmit_scan (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (fun σ => GrpEmOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        σ.vars "gp.v" = 0)
      (Csr.scan "gp.v" nN (grEmitOut cnt sb cur cm))
      (fun _ σ' => GrpEmOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.v" = N)
      (15 * N + 22 * offL N + 4) := by
  refine (Spec.while_potential (b := .lt (.var "gp.v") (.var nN))
    (fun σ => GrpEmOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ)
    (fun σ => 15 * (N - σ.vars "gp.v")
      + 22 * (offL N - moff lmv (offL N) (σ.vars "gp.v")))
    (fun σ hO => evalB_condLt_vars (by have := hO.2.2.2.1; omega)
      (by have := hO.1.carrier; omega)) ?_ (fun σ h => h.1) ?_).post ?_
  · intro σ hO hc
    have hlt : σ.vars "gp.v" < N := by
      have h1 := lt_of_condLt_true hc
      have h2 := hO.1.carrier
      omega
    obtain ⟨σ', K', hrun, hO', hv', hK'⟩ := grEmitOut_step hnm hnN hNB hmsB hO hlt
    refine ⟨σ', K', hrun, hO', ?_⟩
    have hlog := hO.1.log
    have hmlast : moff lmv (offL N) N = offL N := moff_last hlog
    have hm1 : moff lmv (offL N) (σ.vars "gp.v") ≤ moff lmv (offL N) (σ.vars "gp.v" + 1) :=
      moff_mono lmv (offL N) (by omega)
    have hm2 : moff lmv (offL N) (σ.vars "gp.v" + 1) ≤ offL N := by
      have := moff_mono lmv (offL N) (show σ.vars "gp.v" + 1 ≤ N from hlt)
      omega
    simp only [size_condLt, size_var]
    rw [hv']
    omega
  · intro σ h
    have hz := h.2
    have h0 : moff lmv (offL N) 0 = 0 := moff_zero lmv (offL N)
    simp only [size_condLt, size_var]
    rw [hz, h0]
    omega
  · rintro σ σ' - ⟨hO', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hO'.1.carrier
    have h3 := hO'.2.2.2.1
    exact ⟨hO', by omega⟩

/-- **Pass 6, discharged**: every row of `cm` holds its cluster in
ascending vertex order — `Impl.restrictEmb`'s enumeration, entry for
entry. -/
theorem grEmit_spec (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        GrpScatSt cnt sb π Xf offL lmv (offL N) σ)
      (grEmitCom nN cnt sb cur cm)
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ (u : Fin N) (t : ℕ), ∀ ht : t < (Xf u).ncard,
          (σ'.arrs cm).getD (offC Xf (u : ℕ) + t) 0
            = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ)))
      (15 * N + 22 * offL N + 8) := by
  obtain ⟨-, -, -, -, -, -, -, hnv, -, hnq⟩ := grScalars_ne hnN
  have hq0 : Spec B
      (fun σ => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        GrpScatSt cnt sb π Xf offL lmv (offL N) σ)
      (.assign "gp.q" (.lit 0))
      (fun _ σ' => (GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ'.arrs cur).getD k 0 = offC Xf k) ∧
        GrpScatSt cnt sb π Xf offL lmv (offL N) σ') ∧ σ'.vars "gp.q" = 0) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hco, hcur, hsc⟩ := hσ
    refine ⟨σ.setVar "gp.q" 0, 2, grun_assign (glit (by omega)) (by simp), le_rfl,
      ⟨?_, ?_, ?_, ?_⟩, by simp⟩
    · exact hfr.of_eq (by simp [hnq]) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)
    · intro k hk
      rw [show (σ.setVar "gp.q" 0).arrs co = σ.arrs co from by simp]
      exact hco k hk
    · intro k hk
      rw [show (σ.setVar "gp.q" 0).arrs cur = σ.arrs cur from by simp]
      exact hcur k hk
    · exact hsc.of_eq (by simp) (by simp)
  have hv0 : Spec B
      (fun σ => (GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ ∧
        (∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k) ∧
        (∀ k, k < N → (σ.arrs cur).getD k 0 = offC Xf k) ∧
        GrpScatSt cnt sb π Xf offL lmv (offL N) σ) ∧ σ.vars "gp.q" = 0)
      (.assign "gp.v" (.lit 0))
      (fun _ σ' => GrpEmOInv nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        σ'.vars "gp.v" = 0) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hco, hcur, hsc⟩, hq⟩ := hσ
    have hqv : (σ.setVar "gp.v" 0).vars "gp.q" = 0 := by simp [hq]
    refine ⟨σ.setVar "gp.v" 0, 2, grun_assign (glit (by omega)) (by simp), le_rfl,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · exact hfr.of_eq (by simp [hnv]) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)
    · intro k hk
      rw [show (σ.setVar "gp.v" 0).arrs co = σ.arrs co from by simp]
      exact hco k hk
    · exact hsc.of_eq (by simp) (by simp)
    · simp
    · rw [show (σ.setVar "gp.v" 0).vars "gp.v" = 0 from by simp, hqv, moff_zero]
    · rw [hqv]
      refine ⟨fun u => ?_, fun u z hz hlt => ?_⟩
      · rw [show (σ.setVar "gp.v" 0).arrs cur = σ.arrs cur from by simp,
          hcur (u : ℕ) u.isLt,
          show {z : Fin N | z ∈ Xf u ∧ spos π Xf offL lmv (offL N) u z < 0}
            = (∅ : Set (Fin N)) from by ext y; simp]
        simp
      · omega
  refine ((Spec.seq hq0 (Spec.seq hv0 (grEmit_scan hnm hnN hNB hmsB)
    (fun σ σ' _ hq => hq) (fun σ σ' σ'' _ _ hq => hq)) (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' hpre _ hq => ?_)).mono (by omega))
  obtain ⟨⟨hfr, hco, -, -, hqv, hem⟩, hend⟩ := hq
  rw [show σ''.vars "gp.q" = offL N from by
    rw [hqv, hend, moff_last hfr.log]] at hem
  refine ⟨hfr, hco, fun u t ht => ?_⟩
  have hz : ((setEquiv (Xf u) ⟨t, ht⟩ : Fin N)) ∈ Xf u := (setEquiv (Xf u) ⟨t, ht⟩).2
  have hcrk : crank Xf u ((setEquiv (Xf u) ⟨t, ht⟩ : Fin N)) = t :=
    crank_setEquiv Xf u ⟨t, ht⟩
  have := hem.fill u ((setEquiv (Xf u) ⟨t, ht⟩ : Fin N)) hz (spos_lt hfr.log hz)
  rw [hcrk] at this
  rw [this, Impl.restrictEmb_apply]

/-! ## §9 The six passes, composed -/

/-- Every cluster fits the carrier, so the mass is at most `N²` — the
figure `sq_lt_mcB` makes a word. -/
theorem offC_le_sq {N : ℕ} (Xf : Fin N → Set (Fin N)) {k : ℕ} (hk : k ≤ N) :
    offC Xf k ≤ N * N := by
  have hcsz : ∀ u, csz Xf u ≤ N := by
    intro u
    rw [csz]
    split
    · rename_i h
      have h1 := Set.ncard_le_ncard (Set.subset_univ (Xf ⟨u, h⟩)) Set.finite_univ
      simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h1
    · exact Nat.zero_le _
  calc offC Xf k ≤ ∑ _u ∈ Finset.range k, N :=
        Finset.sum_le_sum (fun u _ => hcsz u)
    _ = k * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ N * N := Nat.mul_le_mul_right N hk

/-- **The grouping pass, discharged**: from the log, the order region
and the four allocations, `co` and `cm` are `ClusterCsr`'s two regions
— offsets in carrier order, rows in ascending vertex order. -/
theorem grAll_spec (hnm : GrpNames lo lm od ca co cm cnt cur sb)
    (hnN : nN ∉ grScalars) (hNB : N + 1 < B) (hmsB : offL N < B) :
    Spec B (GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv)
      (grCom nN lo lm od co cm cnt cur sb)
      (fun _ σ' => GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ' ∧
        (∀ k, k ≤ N → (σ'.arrs co).getD k 0 = offC Xf k) ∧
        (∀ (u : Fin N) (t : ℕ), ∀ ht : t < (Xf u).ncard,
          (σ'.arrs cm).getD (offC Xf (u : ℕ) + t) 0
            = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ)))
      (grK N (offL N)) :=
  (Spec.seq (grLen_spec hnm hnN hNB hmsB)
    (Spec.seq (grOff_spec hnm hnN hNB hmsB)
      (Spec.seq (grCnt_spec hnm hnN hNB hmsB)
        (Spec.seq (grMoff_spec hnm hnN hNB hmsB)
          (Spec.seq (grScat_spec hnm hnN hNB hmsB)
            (grEmit_spec hnm hnN hNB hmsB)
            (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
          (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
        (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
      (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
    (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq)).mono (by simp [grK]; omega)

/-- **The output of the six passes is `ClusterCsr`** — the offsets are
`offC`, anchored per centre (empty centres included), and the rows are
`Impl.restrictEmb`'s enumeration. -/
theorem clusterCsr_of_grAll {σ : Env}
    (hfr : GrpFrame nN lo lm od co cm cnt cur sb π Xf offL lmv σ)
    (hco : ∀ k, k ≤ N → (σ.arrs co).getD k 0 = offC Xf k)
    (hcm : ∀ (u : Fin N) (t : ℕ), ∀ ht : t < (Xf u).ncard,
      (σ.arrs cm).getD (offC Xf (u : ℕ) + t) 0
        = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ)) :
    ClusterCsr co cm Xf σ := by
  refine ⟨offC Xf, offC_zero Xf, hfr.coLen, hco, fun u => ?_, ?_, hcm⟩
  · rw [offC_succ, csz_coe]
  · rw [offC_last hfr.log]; exact hfr.cmLen

/-- The arrays the grouping stores into are its five. -/
theorem not_mem_warrs_grCom {b : String} (h1 : b ≠ co) (h2 : b ≠ cm)
    (h3 : b ≠ cnt) (h4 : b ≠ cur) (h5 : b ≠ sb) :
    b ∉ (grCom nN lo lm od co cm cnt cur sb).warrs := by
  simp [grCom, grLenCom, grOffCom, grCntCom, grMoffCom, grScatCom, grScatOut,
    grScatIn, grEmitCom, grEmitOut, grEmitIn, Com.warrs, Csr.scan, h1, h2, h3, h4, h5]

/-- The scalars the grouping assigns to are its ten. -/
theorem not_mem_wvars_grCom {y : String} (h : y ∉ grScalars) :
    y ∉ (grCom nN lo lm od co cm cnt cur sb).wvars := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := grScalars_ne h
  simp [grCom, grLenCom, grOffCom, grCntCom, grMoffCom, grScatCom, grScatOut,
    grScatIn, grEmitCom, grEmitOut, grEmitIn, Com.wvars, Csr.scan, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10]

end Passes

/-! ## §10 `PeelGroupIn`, discharged

The residual, verbatim, from hypotheses only of the F7-suppliable
kinds: `1 ≤ q` (the schedule constant is positive), the region names'
distinctness, and the four allocation lengths — which the scratch
descriptor `Sgr` states **against the log's own arrays**, since a level
predicate cannot mention the arena (Finding 1). -/

/-- The mass in carrier order. -/
theorem offC_eq_sum {N : ℕ} (Xf : Fin N → Set (Fin N)) :
    offC Xf N = ∑ u : Fin N, (Xf u).ncard := by
  rw [offC, Finset.sum_range fun u => csz Xf u]
  exact Finset.sum_congr rfl fun u _ => csz_coe Xf u

/-- The arena's own figure is a word (`SolveSweepBuild`'s `sq_lt_mcB`,
restated here rather than importing the build pass — the same
duplication `SolveAugFrameProg` makes). -/
private theorem gsq_lt_mcB {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {q : ℕ}
    (henc : EncodesGraph x n G) (hq : 1 ≤ q) : n * n < mcB q x := by
  have hlen := henc.length_eq
  have h2 : (x.length + 1) ^ 2 ≤ mcB q x := by
    rw [mcB]
    exact Nat.le_mul_of_pos_left _ hq
  rw [pow_two] at h2
  have h4 : (n + 1) * (n + 1) ≤ (x.length + 1) * (x.length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
  omega

open Classical in
/-- **F6c12 residual 4-ii, discharged verbatim**: the grouping pass —
the concrete program `grCom` at `peelK 153 61 0` — turns the peel-order
log into `ClusterCsr` with the arena and the assignment region
untouched. The budget is `104` a vertex, `61` a cluster cell and `49`
of fixed blocks, folded into `153·N + 61·mass` by `1 ≤ N` (which
`¬ A.G = ⊥` supplies) and `N ≤ mass` — **no edge term**, because the
grouping never reads the graph. -/
theorem peelGroupIn_grCom (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm cnt cur sb : ℕ → String) (od lo lm : ℕ → String)
    (hq : 1 ≤ q)
    (hnm : ∀ j, GrpNames (lo j) (lm j) (od j) (ca j) (co j) (cm j) (cnt j)
      (cur j) (sb j))
    (hnN : ∀ j, (arenaNames j).nN ∉ grScalars)
    (hnS : ∀ j, (arenaNames j).nS ∉ grScalars)
    (harena : ∀ j, ∀ b ∈ [co j, cm j, cnt j, cur j, sb j],
      b ≠ (arenaNames j).off ∧ b ≠ (arenaNames j).tgt ∧ b ≠ (arenaNames j).col ∧
      b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist) :
    PeelGroupIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm od lo lm
      (fun j σ => (σ.arrs (lm j)).length ≤ (σ.arrs (cm j)).length ∧
        (σ.arrs (lm j)).length ≤ (σ.arrs (sb j)).length ∧
        (σ.arrs (co j)).length ≤ (σ.arrs (cnt j)).length ∧
        (σ.arrs (co j)).length ≤ (σ.arrs (cur j)).length)
      (fun j => grCom (arenaNames j).nN (lo j) (lm j) (od j) (co j) (cm j)
        (cnt j) (cur j) (sb j))
      153 61 := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hArena, hctr, hod, hlogC, hcoL, hcmL, hsbL, hcntL, hcurL⟩ := hσ
  obtain ⟨offL, hz0, hloL, hloG, hstepL, hlmL, hsound, hcomp⟩ := hlogC
  -- the log and the order region, in the shape the six passes read
  have hlog : GrpLog (lo j) (lm j) (od j) ((ord A.N A.G).order)
      (cluster (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) offL
      (fun p => (σ.arrs (lm j)).getD p 0) σ :=
    { zero := hz0, step := hstepL, loLen := hloL, loGet := hloG, lmLen := hlmL,
      lmGet := fun _ _ => rfl, odLen := hod.1, odGet := hod.2,
      sound := hsound, complete := hcomp }
  -- the two figures, and that they are words
  have hcarrier : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  have hNn : A.N ≤ n := hArena.st.N_le_root
  have henc : EncodesGraph x n G := hx.1
  have hxB : x.length + 1 < mcB q x := length_add_one_lt_mcB (three_le_length henc) hq
  have hlenx := henc.length_eq
  have hNB : A.N + 1 < mcB q x := by omega
  have hsq : n * n < mcB q x := gsq_lt_mcB henc hq
  have hmass : offL A.N
      = clusterMass (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order) := by
    rw [← offC_last hlog, offC_eq_sum]
    rfl
  have hmsle : offL A.N ≤ A.N * A.N := by
    rw [← offC_last hlog]; exact offC_le_sq _ le_rfl
  have hmsB : offL A.N < mcB q x := by
    have : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
    omega
  have hNpos : 0 < A.N := by
    by_contra hcon
    exact hbot (by ext a b; exact absurd a.isLt (by omega))
  -- the frame the six passes keep
  have hGF : GrpFrame (arenaNames j).nN (lo j) (lm j) (od j) (co j) (cm j)
      (cnt j) (cur j) (sb j) ((ord A.N A.G).order)
      (cluster (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) offL
      (fun p => (σ.arrs (lm j)).getD p 0) σ :=
    { log := hlog, carrier := hcarrier, coLen := hcoL, cmLen := by omega,
      cntLen := by omega, curLen := by omega, sbLen := by omega }
  obtain ⟨σ', hrun, ⟨hfr', hco', hcm'⟩, hfv, hfa, -, -⟩ :=
    (grAll_spec (hnm j) (hnN j) hNB hmsB).frame.run hGF
  -- the names the pass never touches
  obtain ⟨o1, t1, c1, u1, h1⟩ := harena j (co j) (by simp)
  obtain ⟨o2, t2, c2, u2, h2⟩ := harena j (cm j) (by simp)
  obtain ⟨o3, t3, c3, u3, h3⟩ := harena j (cnt j) (by simp)
  obtain ⟨o4, t4, c4, u4, h4⟩ := harena j (cur j) (by simp)
  obtain ⟨o5, t5, c5, u5, h5⟩ := harena j (sb j) (by simp)
  have hcaeq : σ'.arrs (ca j) = σ.arrs (ca j) :=
    hfa _ (not_mem_warrs_grCom (Ne.symm ((hnm j).wr (co j) (by simp)).2.2.2)
      (Ne.symm ((hnm j).wr (cm j) (by simp)).2.2.2)
      (Ne.symm ((hnm j).wr (cnt j) (by simp)).2.2.2)
      (Ne.symm ((hnm j).wr (cur j) (by simp)).2.2.2)
      (Ne.symm ((hnm j).wr (sb j) (by simp)).2.2.2))
  refine ⟨σ', hrun.mono ?_, ?_, ?_, clusterCsr_of_grAll hfr' hco' hcm'⟩
  · show grK A.N (offL A.N) ≤ _
    rw [peelK, ← hmass]
    simp only [grK, Nat.zero_mul, Nat.add_zero]
    have : A.N ≤ offL A.N := by rw [hmass]; exact card_le_clusterMass _ _ _
    omega
  · exact arenaStW_of_eq hArena (hfv _ (not_mem_wvars_grCom (hnN j)))
      (hfv _ (not_mem_wvars_grCom (hnS j)))
      (hfa _ (not_mem_warrs_grCom (Ne.symm o1) (Ne.symm o2) (Ne.symm o3)
        (Ne.symm o4) (Ne.symm o5)))
      (hfa _ (not_mem_warrs_grCom (Ne.symm t1) (Ne.symm t2) (Ne.symm t3)
        (Ne.symm t4) (Ne.symm t5)))
      (hfa _ (not_mem_warrs_grCom (Ne.symm c1) (Ne.symm c2) (Ne.symm c3)
        (Ne.symm c4) (Ne.symm c5)))
      (hfa _ (not_mem_warrs_grCom (Ne.symm u1) (Ne.symm u2) (Ne.symm u3)
        (Ne.symm u4) (Ne.symm u5)))
      (hfa _ (not_mem_warrs_grCom (Ne.symm h1) (Ne.symm h2) (Ne.symm h3)
        (Ne.symm h4) (Ne.symm h5)))
  · exact ⟨by rw [hcaeq]; exact hctr.1, fun v => by rw [hcaeq]; exact hctr.2 v⟩

/-! The leaf's axiom profile: the six passes and their assembly use
nothing but the three of the ambient logic; the residual's statement
quotes `Headline.headlineSetup`, so — exactly like the landed
`covPeelIn_of_sweep_group` it feeds — it additionally carries Lax12's
endorsed `uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms grAll_spec

#print axioms clusterCsr_of_grAll

#print axioms peelGroupIn_grCom

end Lax3Proofs.Prog
