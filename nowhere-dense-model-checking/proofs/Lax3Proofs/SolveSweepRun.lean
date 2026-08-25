import Lax3Proofs.SolveSweepPeel

/-!
# F6c12 (residual 4-i) — the peel sweep's own loop, and its budget

`SolveSweepPeel` splits `CovPeelIn` at the seam its output shape forces
and names **`PeelSweepIn`** (`SolveSweepPeel.lean:328`) — GKS's
ascending peel — leaving it undischarged. This file owns that residual's
*outer* structure: the sentinel pass the contract silently owes, the
peel loop with its invariant, the landed delete inside the loop body,
and the budget summation that turns a per-centre cost into
`peelK asw bsw csw`. What it leaves named is one centre's frontier BFS.

## What is proved here

`peelSweepIn_of_bfs` (§7) discharges

    PeelSweepIn … (fun j => sweepCom (bfC j) …) (abf + 42) (bbf + 54) cbf

from a single named residual `PeelBfsIn` (§4) at
`abf + bbf·|X_u| + cbf·Σ_{w ∈ X_u} d_<(w)`. The program is real
everywhere except at `bfC j`:

    sweepCom bfC ca lo ao aj dg mt od nn
      = sweepInitCom ca lo nn ;
        "sw.i" := 0 ;
        while "sw.i" < nn do
          "sw.v" := od["sw.i"] ;
          bfC ;                                   -- the named residual
          delAdjCom ao aj dg mt "sw.v" ;          -- landed (§5 MdPeel)
          "sw.i" := "sw.i" + 1

The deletion half of every turn is therefore *not* a residual: it is the
landed `delAdjCom` at `AdjDeleteInW` (`SolveSweepMdPeel.lean:944`), and
the loop's region invariant walks `DelAdjSt … (peelSet π i)` up one rank
per turn through `peelSet_succ`. `AdjDeleteIn` as landed is false
(`not_adjDeleteIn`), so the `W` form is used and its word bound
`A.N + A.N² < mcB q x` is discharged here from `1 ≤ q` and `A.N ≤ n`.

## The three constants, and which terms are tight

* `asw = abf + 42 = (abf + 16) + 11 + 15`. The `abf + 16` is one
  turn: the residual's own `abf`, the loop test (`4`), the order read
  (`3`), the counter bump (`4`) and the delete's own `5`. The `11` is
  the sentinel pass's per-cell cost (a store at `3`, a bump at `4`,
  the scan's own `4`). The `15` is the three whole-program constants —
  the sentinel pass's `9`, the counter's `2`, the loop's last test
  `4` — folded into the linear term against `1 ≤ A.N`, which
  `¬ A.G = ⊥` gives (a graph on an empty carrier is `⊥`). Nothing here
  is tight: every figure is a literal `Com` size, not a fitted
  constant.
* `bsw = bbf + 54` **is tight against the landed delete**: `54` is
  exactly `AdjDeleteInW`'s per-edge-copy charge, and it enters the mass
  term only because `curDeg_at_deletion_le_cluster` prices `u`'s current
  degree at its deletion by `|X_u|`. That step needs `1 ≤ S.R`
  (Hazard 3) and is where this file spends it.
* `csw = cbf` — the edge term is the BFS's alone; nothing outside
  `bfC` reads an adjacency cell.

`peelBudget_le` then closes the whole sweep at `O(N·D²)` with no
further work, since the shape is `peelK` verbatim.

## The two BFS constraints, restated as they now bind

Both of `SolveSweepPeel`'s Finding 2 survive into `PeelBfsIn` and are
recorded there rather than here, because both are properties of the
program `bfC` and neither is visible in a `Spec`:

1. **The BFS must not expand its final level.** `PeelBfsIn`'s budget
   summand is `cbf·Σ_{w ∈ X_u} d_<(w)`; by `sum_induced_deg_le_two_sum_dlt`
   that pays for the cells of the edges *inside* `X_u` and for no
   others. Expanding the vertices at distance exactly `2R` reads rows
   whose far endpoint is outside `X_u`, and no `cbf` covers them.
2. **Visited marks are cleared by re-walking the reached list.** A
   per-centre pass over the carrier is `Θ(N²)`; the budget has no such
   term. The one carrier pass the sweep is allowed is the sentinel pass
   of §2, which happens **once**, before the loop, and rides inside
   `asw·N`.

A third of `SolveSweepPeel`'s findings is discharged here rather than
passed on: `ca` arrives as a bare allocation, so *something* owes an
`O(N)` initialisation before "not yet assigned" can be tested.
`sweepInitCom` is that pass, and `CtrPart` (§1) is the sharpened
invariant it establishes — every cell `≤ A.N`, with `< A.N` *iff* the
vertex has already been claimed. That is Hazard 5 in its concrete form:
IMP+ has no disequality, so the body's "already assigned?" test is
`ca[v] < nn`, and it is sound only against this sharpening.

## What remains, and what §8 hands it

`PeelBfsIn` — one centre's work: the frontier-queue BFS at radius `2R`
in the current structure, the `R`-level first-hit marks, the `2R`-ball
row appended to the log at `lo["sw.i"]`, and the mark clean-up. Its pre-
and postcondition are the *same* `SweepSt` at consecutive mark indices,
so a discharger sees exactly one obligation per clause and the loop is
already paid for. Nothing else of the sweep is left.

§8 discharges, at the state level, the three facts that pass would
otherwise have to find for itself:

* `centre_eq_iff_first_hit` — the first-hit set **is** the centre's
  fibre, in both directions. `centre_eq_of_hit_first` gives only
  sufficiency; a marking pass also needs that it marks nothing it
  should not, and that is the converse (`ctr`'s minimality).
* `ctrPart_succ` — writing the centre into its fibre and nothing else
  advances the assignment region one rank. The "leave the cell alone"
  branch is where first-assignment-wins is spent.
* `logPart_succ` — appending row `i` at `lo[i]` and writing `lo[i+1]`
  advances the log one rank; earlier rows sit strictly below the new
  anchor, so they are untouched by construction. No duplicate-freeness
  clause is asked: `ClusterLog.row_injOn` derives it downstream.

`arena_sq_lt_mcB` (§7) is the word bound `AdjDeleteInW` asks for, at
`1 ≤ q` — the BFS pass owes the same bound for its own slot
arithmetic, and this is where it comes from.

Everything stays parametric in `ord`: no clause mentions how the
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

/-! ## §1 The two partial regions the loop walks

The sweep's two outputs are written incrementally: the assignment
region gains the marks of one centre a turn, the log gains one row a
turn. Neither landed contract (`CtrArr`, `ClusterLog`) has a partial
form, so the loop needs one, indexed by the rank already processed.
Both collapse to the landed contract at `i = A.N`. -/

/-- **The assignment region, part-filled**: cell `v` holds `ctrF v`
once the rank of that centre has been passed, and the sentinel `N`
otherwise.

The sentinel is `N` itself, not a fresh symbol: it is a word (`A.N` is
below every bound in play) and it is *outside* the carrier, so the
stamp test "`ca[v] < nn`" separates the two cases exactly
(`CtrPart.lt_iff`). This is what Hazard 5 forces — IMP+ has no
disequality, so the invariant has to be sharpened to "every cell `≤ N`"
before an order test can stand in for one. -/
def CtrPart (ca : String) {N : ℕ} (ctrF : Fin N → Fin N)
    (π : Equiv.Perm (Fin N)) (i : ℕ) (σ : Env) : Prop :=
  N ≤ (σ.arrs ca).length ∧
    ∀ v : Fin N, (σ.arrs ca).getD (v : ℕ) 0 =
      if ((π (ctrF v) : Fin N) : ℕ) < i then ((ctrF v : Fin N) : ℕ) else N

/-- The region reads one array: it transports along agreement on it. -/
theorem CtrPart.of_eq {ca : String} {N : ℕ} {ctrF : Fin N → Fin N}
    {π : Equiv.Perm (Fin N)} {i : ℕ} {σ σ' : Env} (h : CtrPart ca ctrF π i σ)
    (hca : σ'.arrs ca = σ.arrs ca) : CtrPart ca ctrF π i σ' := by
  rw [CtrPart, hca]; exact h

/-- **Every cell is at most `N`** — the sharpening the stamp test needs
(Hazard 5). -/
theorem CtrPart.le {ca : String} {N : ℕ} {ctrF : Fin N → Fin N}
    {π : Equiv.Perm (Fin N)} {i : ℕ} {σ : Env} (h : CtrPart ca ctrF π i σ)
    (v : Fin N) : (σ.arrs ca).getD (v : ℕ) 0 ≤ N := by
  rw [h.2 v]
  split
  · exact le_of_lt (Fin.isLt _)
  · exact le_rfl

/-- **The stamp test is exact**: a cell is below `N` exactly when its
vertex has already been claimed by a processed centre. The body's
"already assigned?" branch is this `<`. -/
theorem CtrPart.lt_iff {ca : String} {N : ℕ} {ctrF : Fin N → Fin N}
    {π : Equiv.Perm (Fin N)} {i : ℕ} {σ : Env} (h : CtrPart ca ctrF π i σ)
    (v : Fin N) :
    (σ.arrs ca).getD (v : ℕ) 0 < N ↔ ((π (ctrF v) : Fin N) : ℕ) < i := by
  rw [h.2 v]
  constructor
  · intro hlt
    by_contra hc
    rw [if_neg hc] at hlt
    exact absurd hlt (lt_irrefl N)
  · intro hc
    rw [if_pos hc]
    exact Fin.isLt _

/-- **At the end of the sweep the part-filled region is the landed
one**: every centre's rank is below `N`, so no cell still holds the
sentinel. -/
theorem CtrPart.full {ca : String} {N : ℕ} {ctrF : Fin N → Fin N}
    {π : Equiv.Perm (Fin N)} {σ : Env} (h : CtrPart ca ctrF π N σ) :
    CtrArr ca ctrF σ :=
  ⟨h.1, fun v => by rw [h.2 v, if_pos (Fin.isLt _)]⟩

/-- **The log's offsets, as a function**: the running mass in peel
order. `ClusterLog` leaves its offset function existential; the loop
needs a *fixed* one, since the row written at turn `i` must land where
turn `i-1` stopped. The anchor and the step determine it, so naming it
loses nothing. -/
noncomputable def peelOff {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) : ℕ → ℕ
  | 0 => 0
  | (k + 1) => peelOff π Xf k + (if h : k < N then (Xf (π.symm ⟨k, h⟩)).ncard else 0)

@[simp] theorem peelOff_zero {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) : peelOff π Xf 0 = 0 := rfl

/-- One row's worth of offset: `ClusterLog`'s step clause, at the named
function. -/
theorem peelOff_step {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (k : Fin N) :
    peelOff π Xf ((k : ℕ) + 1) = peelOff π Xf (k : ℕ) + (Xf (π.symm k)).ncard := by
  rw [peelOff, dif_pos k.isLt, Fin.eta]

theorem peelOff_mono {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) {i k : ℕ} (h : i ≤ k) :
    peelOff π Xf i ≤ peelOff π Xf k := by
  induction k with
  | zero =>
      obtain rfl : i = 0 := Nat.le_zero.mp h
      exact le_rfl
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · refine le_trans (ih (by omega)) ?_
        rw [peelOff]
        omega

/-- **The log never overruns an `N²` allocation**: each row is at most
the carrier wide, and there are at most `N` of them. This is the
headroom clause `Spl` owes (Hazard 6: `ClusterLog`'s `offL N ≤ length`
is a binding requirement on whoever establishes the precondition, and
it is invisible in the contract text). -/
theorem peelOff_le_sq {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) {i : ℕ} (hi : i ≤ N) :
    peelOff π Xf i ≤ N * N := by
  have key : ∀ k, k ≤ N → peelOff π Xf k ≤ k * N := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ m ih =>
        intro hm
        have hmN : m < N := hm
        have hcard : (Xf (π.symm ⟨m, hmN⟩)).ncard ≤ N := by
          have := Set.ncard_le_ncard (Set.subset_univ (Xf (π.symm ⟨m, hmN⟩)))
            (Set.toFinite _)
          simpa using this
        have h1 := ih (by omega)
        rw [peelOff, dif_pos hmN]
        calc peelOff π Xf m + (Xf (π.symm ⟨m, hmN⟩)).ncard
            ≤ m * N + N := Nat.add_le_add h1 hcard
          _ = (m + 1) * N := by ring
  exact le_trans (key i hi) (Nat.mul_le_mul_right N hi)

/-- **The log, part-filled**: the offsets are written up to `i`, the
rows below `i` are complete, and the cells beyond `offL i` are still
free. At `i = N` this is `ClusterLog` verbatim (`LogPart.full`). -/
def LogPart (lo lm : String) {N : ℕ} (π : Equiv.Perm (Fin N))
    (Xf : Fin N → Set (Fin N)) (i : ℕ) (σ : Env) : Prop :=
  N + 1 ≤ (σ.arrs lo).length ∧
  (∀ k, k ≤ i → (σ.arrs lo).getD k 0 = peelOff π Xf k) ∧
  peelOff π Xf i ≤ (σ.arrs lm).length ∧
  (∀ k : Fin N, (k : ℕ) < i → ∀ t : ℕ, t < (Xf (π.symm k)).ncard →
    ∃ z : Fin N, z ∈ Xf (π.symm k) ∧
      (σ.arrs lm).getD (peelOff π Xf (k : ℕ) + t) 0 = (z : ℕ)) ∧
  (∀ k : Fin N, (k : ℕ) < i → ∀ z : Fin N, z ∈ Xf (π.symm k) →
    ∃ t : ℕ, t < (Xf (π.symm k)).ncard ∧
      (σ.arrs lm).getD (peelOff π Xf (k : ℕ) + t) 0 = (z : ℕ))

/-- The log reads exactly two arrays: it transports along agreement on
them. -/
theorem LogPart.of_eq {lo lm : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {Xf : Fin N → Set (Fin N)} {i : ℕ} {σ σ' : Env} (h : LogPart lo lm π Xf i σ)
    (hlo : σ'.arrs lo = σ.arrs lo) (hlm : σ'.arrs lm = σ.arrs lm) :
    LogPart lo lm π Xf i σ' := by
  rw [LogPart, hlo, hlm]; exact h

/-- **At the end of the sweep the part-filled log is the landed one.**
The offset function `ClusterLog` leaves existential is `peelOff`. -/
theorem LogPart.full {lo lm : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {Xf : Fin N → Set (Fin N)} {σ : Env} (h : LogPart lo lm π Xf N σ) :
    ClusterLog lo lm π Xf σ := by
  obtain ⟨hlo, hread, hlen, hsnd, hcmp⟩ := h
  exact ⟨peelOff π Xf, rfl, hlo, hread, peelOff_step π Xf, hlen,
    fun i => hsnd i i.isLt, fun i => hcmp i i.isLt⟩

/-! ## §2 The sentinel pass

`CovPeelIn` offers `ca` as a bare allocation with no initial contents
(`SolveSweepPeel`'s third finding). Before any "already assigned?" test
can be made the whole prefix must hold the sentinel, and — since the
grouping half never touches `ca` and the loop must not run a carrier
pass per centre — this is the sweep's *only* carrier pass. It also
anchors the log at `lo[0] = 0`.

`11·N + 9`: `3` a store, `4` a counter bump, `4` the loop's own turn,
`6` the counter's initialisation and the loop's last test, `3` for
`lo[0] := 0`. -/

/-- Reading back the array just stored into. -/
theorem arrs_setArr_self (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).arrs a = (σ.arrs a).set i v := by
  simp [Env.setArr]

/-- Reading back a different array. -/
theorem arrs_setArr_ne (σ : Env) {a b : String} (i v : ℕ) (h : b ≠ a) :
    (σ.setArr a i v).arrs b = σ.arrs b := by
  simp [Env.setArr, h]

/-- The sentinel scan's invariant: the counter has filled its own
prefix with the sentinel, and the log's anchor already stands. -/
def SweepInitInv (ca lo nn : String) (N : ℕ) (σ : Env) : Prop :=
  σ.vars nn = N ∧ σ.vars "sw.i" ≤ N ∧ N ≤ (σ.arrs ca).length ∧
    (σ.arrs lo).getD 0 0 = 0 ∧
    ∀ v, v < σ.vars "sw.i" → (σ.arrs ca).getD v 0 = N

/-- The sentinel pass: `lo[0] := 0`, then `ca[v] := nn` for every
carrier cell. `nn` is the arena's own carrier cell, so the sentinel is
`A.N` — a word, and outside the carrier. -/
def sweepInitCom (ca lo nn : String) : Com :=
  .seq (.store lo (.lit 0) (.lit 0))
    (.seq (.assign "sw.i" (.lit 0))
      (.while (.lt (.var "sw.i") (.var nn))
        (.seq (.store ca (.var "sw.i") (.var nn))
          (.assign "sw.i" (.add (.var "sw.i") (.lit 1))))))

/-- **The sentinel pass does what the marking test needs**, and touches
only `ca`, `lo` and its own counter. -/
theorem sweepInit_spec {ca lo nn : String} (hcl : ca ≠ lo) (hni : nn ≠ "sw.i")
    {B N : ℕ} (hNB : N < B) :
    Spec B
      (fun σ => σ.vars nn = N ∧ N ≤ (σ.arrs ca).length ∧ 0 < (σ.arrs lo).length)
      (sweepInitCom ca lo nn)
      (fun σ σ' => (∀ v, v < N → (σ'.arrs ca).getD v 0 = N) ∧
        (σ'.arrs lo).getD 0 0 = 0 ∧
        (∀ b : String, b ≠ ca → b ≠ lo → σ'.arrs b = σ.arrs b) ∧
        (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y : String, y ≠ "sw.i" → σ'.vars y = σ.vars y))
      (11 * N + 9) := by
  have hbody : Spec B
      (fun σ => SweepInitInv ca lo nn N σ ∧ σ.vars "sw.i" < N)
      (.seq (.store ca (.var "sw.i") (.var nn))
        (.assign "sw.i" (.add (.var "sw.i") (.lit 1))))
      (fun σ σ' => SweepInitInv ca lo nn N σ' ∧
        σ'.vars "sw.i" = σ.vars "sw.i" + 1) 7 := by
    have hst : Spec B (fun σ => SweepInitInv ca lo nn N σ ∧ σ.vars "sw.i" < N)
        (.store ca (.var "sw.i") (.var nn))
        (fun σ σ' => σ' = σ.setArr ca (σ.vars "sw.i") (σ.vars nn)) (1 + 1 + 1) :=
      Spec.store
        (fun _ hσ => evalB_var (by omega))
        (fun _ hσ => evalB_var (by rw [hσ.1.1]; omega))
        (fun _ hσ => lt_of_lt_of_le hσ.2 hσ.1.2.2.1)
    have has : Spec B (fun τ => τ.vars "sw.i" + 1 < B)
        (.assign "sw.i" (.add (.var "sw.i") (.lit 1)))
        (fun τ τ' => τ' = τ.setVar "sw.i" (τ.vars "sw.i" + 1)) (1 + 3) :=
      Spec.assign (fun _ hτ =>
        evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hτ))
    refine (Spec.seq hst has ?_ ?_).mono (by omega)
    · rintro σ σ' ⟨hI, hlt⟩ rfl
      show (σ.setArr ca (σ.vars "sw.i") (σ.vars nn)).vars "sw.i" + 1 < B
      rw [vars_setArr]
      omega
    · rintro σ σ' σ'' ⟨hI, hlt⟩ rfl rfl
      obtain ⟨hnn, hle, hlen, hlo0, hfill⟩ := hI
      rw [vars_setArr]
      have hac : ((σ.setArr ca (σ.vars "sw.i") (σ.vars nn)).setVar "sw.i"
          (σ.vars "sw.i" + 1)).arrs ca
            = (σ.arrs ca).set (σ.vars "sw.i") (σ.vars nn) := by
        rw [arrs_setVar, arrs_setArr_self]
      have halo : ((σ.setArr ca (σ.vars "sw.i") (σ.vars nn)).setVar "sw.i"
          (σ.vars "sw.i" + 1)).arrs lo = σ.arrs lo := by
        rw [arrs_setVar, arrs_setArr_ne _ _ _ (Ne.symm hcl)]
      have hxi : ((σ.setArr ca (σ.vars "sw.i") (σ.vars nn)).setVar "sw.i"
          (σ.vars "sw.i" + 1)).vars "sw.i" = σ.vars "sw.i" + 1 := by
        rw [vars_setVar, if_pos rfl]
      have hxn : ((σ.setArr ca (σ.vars "sw.i") (σ.vars nn)).setVar "sw.i"
          (σ.vars "sw.i" + 1)).vars nn = N := by
        rw [vars_setVar, if_neg hni, vars_setArr, hnn]
      refine ⟨⟨hxn, ?_, ?_, ?_, ?_⟩, hxi⟩
      · rw [hxi]; omega
      · rw [hac, List.length_set]; exact hlen
      · rw [halo]; exact hlo0
      · intro v hv
        rw [hxi] at hv
        rw [hac]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv' | rfl
        · rw [getD_set_of_ne (by omega)]
          exact hfill v hv'
        · rw [getD_set_self (by omega), hnn]
  have hscan := Spec.forRangeZero (B := B) "sw.i" nn (SweepInitInv ca lo nn N) N 7
    hNB (fun _ hσ => hσ.2.1) (fun _ hσ => hσ.1) hbody
  have hanchor : Spec B
      (fun σ => σ.vars nn = N ∧ N ≤ (σ.arrs ca).length ∧ 0 < (σ.arrs lo).length)
      (.store lo (.lit 0) (.lit 0))
      (fun σ σ' => σ' = σ.setArr lo 0 0) (1 + 1 + 1) :=
    Spec.store (idx := fun _ => 0) (f := fun _ => 0)
      (fun _ _ => evalB_lit (by omega)) (fun _ _ => evalB_lit (by omega))
      (fun _ hσ => hσ.2.2)
  intro σ hσ
  obtain ⟨hnn, hca, hlo⟩ := hσ
  obtain ⟨σ₁, hr1, rfl⟩ := hanchor.run ⟨hnn, hca, hlo⟩
  have hac0 : ((σ.setArr lo 0 0).setVar "sw.i" 0).arrs ca = σ.arrs ca := by
    rw [arrs_setVar, arrs_setArr_ne _ _ _ hcl]
  have halo0 : ((σ.setArr lo 0 0).setVar "sw.i" 0).arrs lo = (σ.arrs lo).set 0 0 := by
    rw [arrs_setVar, arrs_setArr_self]
  have hI0 : SweepInitInv ca lo nn N ((σ.setArr lo 0 0).setVar "sw.i" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg hni, vars_setArr, hnn]
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [hac0]; exact hca
    · rw [halo0]; exact getD_set_self hlo
    · intro v hv
      rw [vars_setVar, if_pos rfl] at hv
      omega
  obtain ⟨σ', hr2, hI', hxN⟩ := hscan.run hI0
  have hrun : Run B (sweepInitCom ca lo nn) σ σ' (11 * N + 9) :=
    (hr1.seq hr2).mono (by omega)
  refine ⟨σ', hrun, fun v hv => hI'.2.2.2.2 v (by omega), hI'.2.2.2.1, ?_, ?_, ?_⟩
  · intro b h1 h2
    exact hrun.frame_arr b (by simp [sweepInitCom, Com.warrs, h1, h2])
  · exact run_arrs_length_eq hrun
  · intro y h1
    exact hrun.frame_var y (by simp [sweepInitCom, Com.wvars, h1])

/-! ## §3 One turn's budget, and the sum over the sweep

`peelK` is affine in three *aggregate* figures; a loop pays a
*per-centre* price. `sum_peelTurn` is the identity between them, and it
is the whole reason the sweep's cost has `peelK`'s shape rather than
some fitted expression: the sweep visits every rank exactly once, so
summing the per-centre price in peel order is summing the aggregate in
carrier order. -/

variable {L n₀ Λ : ℕ}

open Classical in
/-- **The price of the turn at rank `k`**: the per-centre overhead, the
mass of that centre's cluster, and the `d_<` sum over it — the three
figures of `peelK`, localized. Off the carrier it is `0`, so the turn
function is total. -/
noncomputable def peelTurn (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (a b c : ℕ) (k : ℕ) : ℕ :=
  if h : k < A.N then
    a + b * (cluster S A π (π.symm ⟨k, h⟩)).ncard
      + c * ∑ z ∈ Finset.univ.filter (fun z => z ∈ cluster S A π (π.symm ⟨k, h⟩)),
          Impl.dlt A.G π z
  else 0

open Classical in
/-- **Summing the turns is `peelK`.** The peel order is a permutation
of the carrier, so the two per-centre figures reindex; the overhead is
paid once a rank. This is the identity the loop's potential is built
on. -/
theorem sum_peelTurn (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (a b c : ℕ) :
    ∑ k ∈ Finset.range A.N, peelTurn S A π a b c k = peelK a b c S A π := by
  classical
  rw [Finset.sum_range fun k => peelTurn S A π a b c k]
  have hpt : ∀ k : Fin A.N, peelTurn S A π a b c (k : ℕ)
      = a + b * (cluster S A π (π.symm k)).ncard
        + c * ∑ z ∈ Finset.univ.filter (fun z => z ∈ cluster S A π (π.symm k)),
            Impl.dlt A.G π z := by
    intro k
    rw [peelTurn, dif_pos k.isLt, Fin.eta]
  rw [Finset.sum_congr rfl fun k _ => hpt k]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ _k : Fin A.N, a = a * A.N := by simp [mul_comm]
  have h2 : ∑ k : Fin A.N, (cluster S A π (π.symm k)).ncard = clusterMass S A π :=
    Fintype.sum_equiv π.symm _ _ (fun _ => rfl)
  have h3 : ∑ k : Fin A.N,
      ∑ z ∈ Finset.univ.filter (fun z => z ∈ cluster S A π (π.symm k)),
        Impl.dlt A.G π z = peelEdgeWork S A π :=
    Fintype.sum_equiv π.symm _ _ (fun _ => rfl)
  rw [h1, h2, h3, peelK]

/-- One turn's own price, split off the tail of the potential. -/
theorem sum_Ico_peelTurn_succ (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (a b c : ℕ) {i : ℕ} (hi : i < A.N) :
    ∑ k ∈ Finset.Ico i A.N, peelTurn S A π a b c k
      = peelTurn S A π a b c i
        + ∑ k ∈ Finset.Ico (i + 1) A.N, peelTurn S A π a b c k :=
  Finset.sum_eq_sum_Ico_succ_bot hi _

/-- The loop's own per-turn overhead folds into the turn's constant
term: `+4` a turn is `+4` in `a`. -/
theorem peelTurn_add_const (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (a b c e : ℕ) {k : ℕ} (hk : k < A.N) :
    peelTurn S A π a b c k + e = peelTurn S A π (a + e) b c k := by
  rw [peelTurn, peelTurn, dif_pos hk, dif_pos hk]
  ring

/-! ## §4 The loop's state, and the one named residual

`SweepSt` is the conjunction the sweep's loop carries. Two indices, not
one: `d` counts the ranks already *deleted* from the adjacency region
and `i` the ranks already *written* into the marks and the log. A turn
moves `i` first (the BFS reads the structure it must not yet have
changed) and `d` second (the delete), so the two are apart for exactly
the length of the body's middle. -/

/-- **The peel loop's state.** Everything but the last three conjuncts
is carried unchanged through a turn; `DelAdjSt` advances at the delete,
`CtrPart` and `LogPart` at the BFS. -/
def SweepSt (S : Setup L) (j : ℕ) {ℓp : ℕ} (hb : ℕ) (A : Arena Λ n₀)
    (htab : Fin A.N → Fin ℓp → List (Fin A.N)) (π : Equiv.Perm (Fin A.N))
    (ca co ao aj dg mt od lo lm : String) (Ssc : Env → Prop)
    (d i : ℕ) (σ : Env) : Prop :=
  ArenaStW (arenaNames j) hb (Impl.ofArena A htab) σ ∧
  OrdArr od π σ ∧
  A.N + 1 ≤ (σ.arrs co).length ∧
  n₀ * n₀ ≤ (σ.arrs lm).length ∧
  Ssc σ ∧
  DelAdjSt ao aj dg mt A.G (peelSet π d) σ ∧
  CtrPart ca (centre S A π) π i σ ∧
  LogPart lo lm π (cluster S A π) i σ

/-- The arena's carrier cell, read out of the loop state. -/
theorem SweepSt.n_eq {S : Setup L} {j : ℕ} {ℓp : ℕ} {hb : ℕ} {A : Arena Λ n₀}
    {htab : Fin A.N → Fin ℓp → List (Fin A.N)} {π : Equiv.Perm (Fin A.N)}
    {ca co ao aj dg mt od lo lm : String} {Ssc : Env → Prop} {d i : ℕ} {σ : Env}
    (h : SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc d i σ) :
    σ.vars (arenaNames j).nN = A.N := h.1.n_eq

/-- **Named residual (4-i-a): one centre's BFS.** From the loop state
at rank `i`, with `"sw.i"` naming the rank and `"sw.v"` the centre of
that rank, run the frontier-queue BFS at radius `2R` **in the current
(peeled) structure** and leave the loop state at mark index `i + 1`:
the `R`-level first-hit marks written into `ca`
(`centre_eq_of_hit_first` is what makes them `Driver.centre`), the
`2R`-ball appended to the log as row `i` at offset `lo[i]`
(`cluster_eq_ball_peelSet` is what makes that ball the cluster), and
`lo[i+1]` written. The adjacency region is left exactly as found — the
delete that follows in the same turn is not this pass's business.

Budget `peelTurn S A π abf bbf cbf i`, i.e.
`abf + bbf·|X_u| + cbf·Σ_{w ∈ X_u} d_<(w)`. **Two constraints on the
program are invisible in this statement and are binding**
(`SolveSweepPeel`'s Finding 2):

* the BFS must **not expand its final level** — only the vertices at
  distance `< 2R` may have their live rows read, or the cells of edges
  leaving `X_u` are read and `cbf` does not pay for them
  (`sum_induced_deg_le_two_sum_dlt` bounds only the edges *inside*
  `X_u`);
* the visited marks must be cleared by **re-walking the pass's own
  reached list**; a carrier pass per centre is `Θ(N²)` and there is no
  `N²` term in `peelK`.

An empty current ball is *not* a special case: row `i` is still emitted
(as the empty row) and `lo[i+1] := lo[i]` still written, because
`LogPart`'s offsets are anchored per rank, not per nonempty rank. -/
def PeelBfsIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ao aj dg mt od lo lm : ℕ → String)
    (Ssc : ℕ → Env → Prop) (bfC : ℕ → Com) (abf bbf cbf : ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      ∀ (i : ℕ) (hi : i < A.N),
      Spec (mcB q x)
        (fun σ => SweepSt (Headline.headlineSetup C hC φ) j (hbf j) A (htabF j A)
            ((ord A.N A.G).order) (ca j) (co j) (ao j) (aj j) (dg j) (mt j)
            (od j) (lo j) (lm j) (Ssc j) i i σ ∧
          σ.vars "sw.i" = i ∧
          σ.vars "sw.v" = ((((ord A.N A.G).order).symm ⟨i, hi⟩ : Fin A.N) : ℕ))
        (bfC j)
        (fun _ σ' => SweepSt (Headline.headlineSetup C hC φ) j (hbf j) A
            (htabF j A) ((ord A.N A.G).order) (ca j) (co j) (ao j) (aj j)
            (dg j) (mt j) (od j) (lo j) (lm j) (Ssc j) i (i + 1) σ' ∧
          σ'.vars "sw.i" = i ∧
          σ'.vars "sw.v" = ((((ord A.N A.G).order).symm ⟨i, hi⟩ : Fin A.N) : ℕ))
        (peelTurn (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)
          abf bbf cbf i)

/-! ## §5 The sweep's program -/

/-- One turn: name the centre of the current rank, run the BFS, delete
the centre with the landed swap-delete, advance the rank. -/
def sweepBodyCom (bfC : Com) (ao aj dg mt od : String) : Com :=
  .seq (.assign "sw.v" (.get od (.var "sw.i")))
    (.seq bfC
      (.seq (delAdjCom ao aj dg mt "sw.v")
        (.assign "sw.i" (.add (.var "sw.i") (.lit 1)))))

/-- **The sweep**: the sentinel pass, then the ascending peel. -/
def sweepCom (bfC : Com) (ca lo ao aj dg mt od nn : String) : Com :=
  .seq (sweepInitCom ca lo nn)
    (.seq (.assign "sw.i" (.lit 0))
      (.while (.lt (.var "sw.i") (.var nn)) (sweepBodyCom bfC ao aj dg mt od)))

/-! ## §6 The loop

The transport lemmas first: everything in `SweepSt` but the adjacency
region rides on array agreement, and the region is replaced outright at
the delete. -/

/-- The order region reads one array. -/
theorem OrdArr.of_eq {od : String} {N : ℕ} {π : Equiv.Perm (Fin N)} {σ σ' : Env}
    (h : OrdArr od π σ) (hod : σ'.arrs od = σ.arrs od) : OrdArr od π σ' := by
  rw [OrdArr, hod]; exact h

/-- **One step of the loop state**: everything but the adjacency region
transports along agreement on the seven arrays and two cells it reads;
the region itself is supplied afresh, at whatever rank prefix the step
left it. -/
theorem SweepSt.step {S : Setup L} {j : ℕ} {ℓp hb : ℕ} {A : Arena Λ n₀}
    {htab : Fin A.N → Fin ℓp → List (Fin A.N)} {π : Equiv.Perm (Fin A.N)}
    {ca co ao aj dg mt od lo lm : String} {Ssc : Env → Prop} {d d' i : ℕ}
    {σ σ' : Env}
    (h : SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc d i σ)
    (hoff : σ'.arrs (arenaNames j).off = σ.arrs (arenaNames j).off)
    (htgt : σ'.arrs (arenaNames j).tgt = σ.arrs (arenaNames j).tgt)
    (hcol : σ'.arrs (arenaNames j).col = σ.arrs (arenaNames j).col)
    (hup : σ'.arrs (arenaNames j).up = σ.arrs (arenaNames j).up)
    (hhis : σ'.arrs (arenaNames j).hist = σ.arrs (arenaNames j).hist)
    (hnN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN)
    (hnS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS)
    (hodA : σ'.arrs od = σ.arrs od) (hcoA : σ'.arrs co = σ.arrs co)
    (hlmA : σ'.arrs lm = σ.arrs lm) (hcaA : σ'.arrs ca = σ.arrs ca)
    (hloA : σ'.arrs lo = σ.arrs lo) (hS : Ssc σ')
    (hdel : DelAdjSt ao aj dg mt A.G (peelSet π d') σ') :
    SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc d' i σ' := by
  obtain ⟨hA, hordr, hco, hlm, -, -, hctr, hlog⟩ := h
  exact ⟨arenaStW_of_eq hA hnN hnS hoff htgt hcol hup hhis,
    hordr.of_eq hodA, by rw [hcoA]; exact hco, by rw [hlmA]; exact hlm,
    hS, hdel, hctr.of_eq hcaA, hlog.of_eq hloA hlmA⟩

/-- A level-tagged arena scalar is never one of the sweep's or the
delete's four-character scratch names. -/
theorem arenaScalars_ne (j : ℕ) {t : String} (ht : t.length = 4)
    (h1 : "sv.n" ≠ t) (h2 : "sv.m" ≠ t) :
    (arenaNames j).nN ≠ t ∧ (arenaNames j).nS ≠ t :=
  ⟨lv_ne_len4 (by decide) ht h1 j, lv_ne_len4 (by decide) ht h2 j⟩

/-- The delete writes three arrays. -/
theorem delAdj_arrs_eq {ao aj dg mt vx : String} {B K : ℕ} {σ σ' : Env}
    (h : Run B (delAdjCom ao aj dg mt vx) σ σ' K) (b : String)
    (h1 : b ≠ aj) (h2 : b ≠ dg) (h3 : b ≠ mt) : σ'.arrs b = σ.arrs b :=
  h.frame_arr b (by simp [delAdjCom, delAdjBody, Com.warrs, h1, h2, h3])

/-- The delete writes six scratch scalars. -/
theorem delAdj_vars_eq {ao aj dg mt vx : String} {B K : ℕ} {σ σ' : Env}
    (h : Run B (delAdjCom ao aj dg mt vx) σ σ' K) (y : String)
    (h1 : y ≠ "dl.i") (h2 : y ≠ "dl.w") (h3 : y ≠ "dl.p") (h4 : y ≠ "dl.l")
    (h5 : y ≠ "dl.u") (h6 : y ≠ "dl.q") : σ'.vars y = σ.vars y :=
  h.frame_var y (by
    simp [delAdjCom, delAdjBody, Com.wvars, h1, h2, h3, h4, h5, h6])

set_option maxHeartbeats 1000000 in
/-- **The peel loop.** From the loop state at rank `0` it reaches the
loop state at rank `A.N`, at the budget `peelK (abf+16) (bbf+54) cbf`
plus the loop's last test.

The proof is `Spec.while_potential` at the potential
`Σ_{k ≥ "sw.i"} peelTurn (abf+16) (bbf+54) cbf k`: one turn's price
splits off the front (`sum_Ico_peelTurn_succ`), the loop's own `4`
folds into the turn's constant (`peelTurn_add_const`), and the entry
value is `peelK` by `sum_peelTurn`. The `54` of the delete lands in the
mass term through `curDeg_at_deletion_le_cluster`, which is where
`1 ≤ S.R` is spent. -/
theorem sweepLoop_spec {S : Setup L} {j : ℕ} {ℓp hb : ℕ} {A : Arena Λ n₀}
    {htab : Fin A.N → Fin ℓp → List (Fin A.N)} {π : Equiv.Perm (Fin A.N)}
    {ca co ao aj dg mt od lo lm : String} {Ssc : Env → Prop}
    {bfC : Com} {abf bbf cbf B : ℕ}
    (hoa : ao ≠ aj) (hom : ao ≠ mt) (hod : ao ≠ dg)
    (ham : aj ≠ mt) (had : aj ≠ dg) (hmd : mt ≠ dg)
    (hkeep : ∀ b : String, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
      b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od ∨ b = co ∨ b = lm ∨ b = ca ∨ b = lo →
      b ≠ aj ∧ b ≠ dg ∧ b ≠ mt)
    (hSsc : ∀ σ σ' : Env,
      (∀ b : String, b ≠ ca → b ≠ lo → b ≠ lm → b ≠ aj → b ≠ dg → b ≠ mt →
        σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ≠ "sw.i" → y ≠ "sw.v" → y ≠ "dl.i" → y ≠ "dl.w" →
        y ≠ "dl.p" → y ≠ "dl.l" → y ≠ "dl.u" → y ≠ "dl.q" →
        σ'.vars y = σ.vars y) → Ssc σ → Ssc σ')
    (hR : 1 ≤ S.R) (hB : A.N + A.N * A.N < B)
    (hbfs : ∀ (i : ℕ) (hi : i < A.N),
      Spec B
        (fun σ => SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc i i σ ∧
          σ.vars "sw.i" = i ∧ σ.vars "sw.v" = ((π.symm ⟨i, hi⟩ : Fin A.N) : ℕ))
        bfC
        (fun _ σ' => SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc
            i (i + 1) σ' ∧
          σ'.vars "sw.i" = i ∧
          σ'.vars "sw.v" = ((π.symm ⟨i, hi⟩ : Fin A.N) : ℕ))
        (peelTurn S A π abf bbf cbf i)) :
    Spec B
      (fun σ => SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc 0 0 σ ∧
        σ.vars "sw.i" = 0)
      (.while (.lt (.var "sw.i") (.var (arenaNames j).nN))
        (sweepBodyCom bfC ao aj dg mt od))
      (fun _ σ' =>
        SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc A.N A.N σ')
      (peelK (abf + 16) (bbf + 54) cbf S A π + 4) := by
  classical
  -- the arena's two cells are not scratch names
  obtain ⟨hnNi, hnSi⟩ := arenaScalars_ne j (t := "sw.i") (by decide)
    (by decide) (by decide)
  obtain ⟨hnNv, hnSv⟩ := arenaScalars_ne j (t := "sw.v") (by decide)
    (by decide) (by decide)
  have hANB : A.N < B := lt_of_le_of_lt (Nat.le_add_right _ _) hB
  obtain ⟨hnNa, hnSa⟩ := arenaScalars_ne j (t := "dl.i") (by decide)
    (by decide) (by decide)
  obtain ⟨hnNb, hnSb⟩ := arenaScalars_ne j (t := "dl.w") (by decide)
    (by decide) (by decide)
  obtain ⟨hnNc, hnSc⟩ := arenaScalars_ne j (t := "dl.p") (by decide)
    (by decide) (by decide)
  obtain ⟨hnNd, hnSd⟩ := arenaScalars_ne j (t := "dl.l") (by decide)
    (by decide) (by decide)
  obtain ⟨hnNe, hnSe⟩ := arenaScalars_ne j (t := "dl.u") (by decide)
    (by decide) (by decide)
  obtain ⟨hnNf, hnSf⟩ := arenaScalars_ne j (t := "dl.q") (by decide)
    (by decide) (by decide)
  set I : Env → Prop := fun σ =>
    SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc
      (σ.vars "sw.i") (σ.vars "sw.i") σ ∧ σ.vars "sw.i" ≤ A.N with hIdef
  set Φ : Env → ℕ := fun σ =>
    ∑ k ∈ Finset.Ico (σ.vars "sw.i") A.N, peelTurn S A π (abf + 16) (bbf + 54) cbf k
    with hΦdef
  refine (Spec.while_potential I Φ ?_ ?_ ?_ ?_).post ?_
  · -- the test evaluates
    rintro σ ⟨hst, hle⟩
    exact evalB_condLt_vars (by omega) (by rw [hst.n_eq]; omega)
  · -- one turn
    rintro σ ⟨hst, hle⟩ htrue
    have hlt : σ.vars "sw.i" < σ.vars (arenaNames j).nN := lt_of_condLt_true htrue
    rw [hst.n_eq] at hlt
    set i := σ.vars "sw.i" with hidef
    have hi : i < A.N := hlt
    set u : Fin A.N := π.symm ⟨i, hi⟩ with hudef
    have hpu : ((π u : Fin A.N) : ℕ) = i := by rw [hudef, Equiv.apply_symm_apply]
    have hunot : u ∉ peelSet π i := by
      simp only [peelSet, Set.mem_setOf_eq, hpu]
      omega
    -- step 1: name the centre of this rank
    have hstep1 : Spec B (fun τ => τ.vars "sw.i" = i ∧ OrdArr od π τ)
        (.assign "sw.v" (.get od (.var "sw.i")))
        (fun τ τ' => τ' = τ.setVar "sw.v" ((u : Fin A.N) : ℕ)) 3 := by
      refine (Spec.assign (f := fun _ => ((u : Fin A.N) : ℕ)) ?_).mono
        (by simp [Expr.size])
      rintro τ ⟨hxi, hordr⟩
      have hlen : τ.vars "sw.i" < (τ.arrs od).length := by
        rw [hxi]; exact lt_of_lt_of_le hi hordr.1
      refine evalB_get (evalB_var (by omega)) ?_ (lt_trans u.isLt hANB)
      rw [List.getElem?_eq_getElem hlen]
      congr 1
      rw [← List.getD_eq_getElem (τ.arrs od) 0 hlen, hxi]
      exact hordr.2 ⟨i, hi⟩
    obtain ⟨σ1, hr1, rfl⟩ := hstep1.run ⟨hidef.symm, hst.2.1⟩
    -- the loop state survives naming a scalar
    have hst1 : SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc i i
        (σ.setVar "sw.v" ((u : Fin A.N) : ℕ)) := by
      refine hst.step rfl rfl rfl rfl rfl (by rw [vars_setVar, if_neg hnNv])
        (by rw [vars_setVar, if_neg hnSv]) rfl rfl rfl rfl rfl ?_ hst.2.2.2.2.2.1
      exact hSsc σ _ (fun _ _ _ _ _ _ _ => rfl) (fun _ => rfl)
        (fun y _ h2 _ _ _ _ _ _ => by rw [vars_setVar, if_neg h2]) hst.2.2.2.2.1
    have hxi1 : (σ.setVar "sw.v" ((u : Fin A.N) : ℕ)).vars "sw.i" = i := by
      rw [vars_setVar, if_neg (by decide : ("sw.i" : String) ≠ "sw.v")]
    have hxv1 : (σ.setVar "sw.v" ((u : Fin A.N) : ℕ)).vars "sw.v"
        = ((π.symm ⟨i, hi⟩ : Fin A.N) : ℕ) := by
      rw [vars_setVar, if_pos rfl, hudef]
    -- step 2: the BFS
    obtain ⟨σ2, hr2, hst2, hxi2, hxv2⟩ :=
      (hbfs i hi).run ⟨hst1, hxi1, hxv1⟩
    -- step 3: the landed delete
    obtain ⟨σ3, hr3, hdel3⟩ :=
      ((adjDeleteInW_delAdjCom (vx := "sw.v") hoa hom hod ham had hmd
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) B)
        A.G (peelSet π i) u hunot hB).run
        ⟨hst2.2.2.2.2.2.1, by rw [hxv2, hudef]⟩
    have harr3 : ∀ b : String, b ≠ aj → b ≠ dg → b ≠ mt → σ3.arrs b = σ2.arrs b :=
      fun b h1 h2 h3 => delAdj_arrs_eq hr3 b h1 h2 h3
    have hkarr : ∀ b : String, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
        b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
        b = (arenaNames j).hist ∨ b = od ∨ b = co ∨ b = lm ∨ b = ca ∨ b = lo →
        σ3.arrs b = σ2.arrs b := by
      intro b hb
      obtain ⟨k1, k2, k3⟩ := hkeep b hb
      exact harr3 b k1 k2 k3
    have hvar3 : ∀ y : String, y ≠ "dl.i" → y ≠ "dl.w" → y ≠ "dl.p" →
        y ≠ "dl.l" → y ≠ "dl.u" → y ≠ "dl.q" → σ3.vars y = σ2.vars y :=
      fun y h1 h2 h3 h4 h5 h6 => delAdj_vars_eq hr3 y h1 h2 h3 h4 h5 h6
    have hst3 : SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc
        (i + 1) (i + 1) σ3 := by
      refine hst2.step (hkarr _ (Or.inl rfl)) (hkarr _ (Or.inr (Or.inl rfl)))
        (hkarr _ (Or.inr (Or.inr (Or.inl rfl))))
        (hkarr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        (hkarr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        (hvar3 _ hnNa hnNb hnNc hnNd hnNe hnNf)
        (hvar3 _ hnSa hnSb hnSc hnSd hnSe hnSf)
        (hkarr _ (by tauto)) (hkarr _ (by tauto)) (hkarr _ (by tauto))
        (hkarr _ (by tauto)) (hkarr _ (by tauto)) ?_ ?_
      · exact hSsc σ2 σ3 (fun b _ _ _ k1 k2 k3 => harr3 b k1 k2 k3)
          (run_arrs_length_eq hr3)
          (fun y _ _ h3 h4 h5 h6 h7 h8 => hvar3 y h3 h4 h5 h6 h7 h8)
          hst2.2.2.2.2.1
      · rw [peelSet_succ π hi, ← hudef]
        exact hdel3
    -- step 4: advance the rank
    have hxi3 : σ3.vars "sw.i" = i := by
      rw [hvar3 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hxi2]
    have hstep4 : Spec B (fun τ => τ.vars "sw.i" = i)
        (.assign "sw.i" (.add (.var "sw.i") (.lit 1)))
        (fun τ τ' => τ' = τ.setVar "sw.i" (i + 1)) 4 := by
      refine (Spec.assign (f := fun _ => i + 1) ?_).mono (by simp [Expr.size])
      intro τ hτ
      have hval : (i : ℕ) + 1 = Bop.add.apply (τ.vars "sw.i") 1 := by
        rw [hτ]; rfl
      rw [hval]
      exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega))
        (by rw [Bop.apply_add, hτ]; omega)
    obtain ⟨σ4, hr4, rfl⟩ := hstep4.run hxi3
    have hxi4 : (σ3.setVar "sw.i" (i + 1)).vars "sw.i" = i + 1 := by
      rw [vars_setVar, if_pos rfl]
    have hst4 : SweepSt S j hb A htab π ca co ao aj dg mt od lo lm Ssc
        (i + 1) (i + 1) (σ3.setVar "sw.i" (i + 1)) := by
      refine hst3.step rfl rfl rfl rfl rfl (by rw [vars_setVar, if_neg hnNi])
        (by rw [vars_setVar, if_neg hnSi]) rfl rfl rfl rfl rfl ?_
        hst3.2.2.2.2.2.1
      exact hSsc σ3 _ (fun _ _ _ _ _ _ _ => rfl) (fun _ => rfl)
        (fun y h1 _ _ _ _ _ _ _ => by rw [vars_setVar, if_neg h1])
        hst3.2.2.2.2.1
    -- the turn's price, and the deletion inside the mass term
    have hd : ((deleteVerts A.G (peelSet π i)).neighborSet u).ncard
        ≤ (cluster S A π (π.symm ⟨i, hi⟩)).ncard := by
      have h := curDeg_at_deletion_le_cluster S A π hR u
      rw [hpu] at h
      rw [← hudef]
      exact h
    have hcost : 3 + (peelTurn S A π abf bbf cbf i +
          ((54 * ((deleteVerts A.G (peelSet π i)).neighborSet u).ncard + 5) + 4))
        ≤ peelTurn S A π (abf + 12) (bbf + 54) cbf i := by
      rw [peelTurn, peelTurn, dif_pos hi, dif_pos hi]
      have h54 : 54 * ((deleteVerts A.G (peelSet π i)).neighborSet u).ncard
          ≤ 54 * (cluster S A π (π.symm ⟨i, hi⟩)).ncard :=
        Nat.mul_le_mul_left 54 hd
      have hexp : (bbf + 54) * (cluster S A π (π.symm ⟨i, hi⟩)).ncard
          = bbf * (cluster S A π (π.symm ⟨i, hi⟩)).ncard
            + 54 * (cluster S A π (π.symm ⟨i, hi⟩)).ncard := by ring
      omega
    refine ⟨σ3.setVar "sw.i" (i + 1), peelTurn S A π (abf + 12) (bbf + 54) cbf i,
      (hr1.seq (hr2.seq (hr3.seq hr4))).mono hcost,
      ⟨by rw [hxi4]; exact hst4, by rw [hxi4]; omega⟩, ?_⟩
    -- the potential pays for the turn and the loop's own test
    simp only [hΦdef, hxi4, hidef.symm]
    rw [sum_Ico_peelTurn_succ S A π (abf + 16) (bbf + 54) cbf hi]
    have hfold : peelTurn S A π (abf + 12) (bbf + 54) cbf i + 4
        = peelTurn S A π (abf + 16) (bbf + 54) cbf i := by
      rw [peelTurn_add_const S A π (abf + 12) (bbf + 54) cbf 4 hi]
    simp only [Cond.size, Expr.size]
    omega
  · rintro σ ⟨hst, hxi⟩
    exact ⟨by rw [hxi]; exact hst, by rw [hxi]; omega⟩
  · rintro σ ⟨hst, hxi⟩
    have : Φ σ = peelK (abf + 16) (bbf + 54) cbf S A π := by
      rw [hΦdef]
      simp only [hxi]
      rw [← Finset.range_eq_Ico, sum_peelTurn]
    simp only [Cond.size, Expr.size]
    omega
  · rintro σ σ' - ⟨hI, hfalse⟩
    obtain ⟨hst, hle⟩ := hI
    have hge : σ'.vars (arenaNames j).nN ≤ σ'.vars "sw.i" := le_of_condLt_false hfalse
    rw [hst.n_eq] at hge
    have : σ'.vars "sw.i" = A.N := by omega
    rw [this] at hst
    exact hst

/-! ## §7 The residual, discharged from its BFS

The word bound first — `AdjDeleteInW` asks for `N + N² < B`, and it is
free at the peel's own bound. Unlike the landed `AdjDeleteIn`, whose
carrier size is quantified with no tie to `B` at all
(`not_adjDeleteIn`), a level arena's carrier is bounded by the input
graph's, and that by the input's own length. Exported because the
discharger of `PeelBfsIn` owes exactly the same bound for its own slot
arithmetic. -/

/-- **Every slot index of a level arena fits in a word**, at the peel's
own bound and `1 ≤ q`: the slot space is at most `A.N²` wide, and
`A.N ≤ n < |x|`. -/
theorem arena_sq_lt_mcB {n : ℕ} {G : SimpleGraph (Fin n)} {c w q : ℕ}
    (hq : 1 ≤ q) {x : List ℕ} (hx : x ∈ mcD n G c w) {Λ : ℕ} (A : Arena Λ n) :
    A.N + A.N * A.N < mcB q x := by
  have henc : EncodesGraph x n G := hx.1
  have hlen := henc.length_eq
  have hAN : A.N ≤ n := by
    have h := Fintype.card_le_of_embedding A.up
    simpa using h
  have h1 : A.N * A.N ≤ n * n := Nat.mul_le_mul hAN hAN
  have h2 : (x.length + 1) * (x.length + 1) ≤ mcB q x := by
    rw [mcB, pow_two]
    exact Nat.le_mul_of_pos_left _ hq
  have h3 : n * n + n + 1 < (x.length + 1) * (x.length + 1) := by nlinarith
  omega

/-! ### The discharge

`PeelSweepIn` at the concrete program of §5, from `PeelBfsIn` and
nothing else. The three constants are `abf + 42`, `bbf + 54`, `cbf`;
the docstring accounts for each. -/

set_option maxHeartbeats 1000000 in
/-- **F6c12 residual (4-i), reduced to one centre's BFS.**
`PeelSweepIn` holds — every clause verbatim — of

    sweepInitCom ca lo nn ; "sw.i" := 0 ; while "sw.i" < nn do <turn>

at `peelK (abf + 42) (bbf + 54) cbf`, given `PeelBfsIn` at
`peelTurn abf bbf cbf`. The sentinel pass and the peel loop are real
programs; the delete inside each turn is the landed `delAdjCom` at
`AdjDeleteInW`, and its `54·d + 5` rides into the mass term through
`curDeg_at_deletion_le_cluster` — which is why `1 ≤ S.R` (Hazard 3) is
a hypothesis here and is stated rather than hidden.

The scratch descriptor asked of the caller is
`n + 1 ≤ |lo| ∧ n·n ≤ |lm| ∧ Ssc`: the log's offset row and its cell
space. The `n·n` is Hazard 6 made explicit — `ClusterLog` demands
`offL N ≤ |lm|` and nothing in `CovPeelIn`'s text says who owes the
allocation; `peelOff_le_sq` is why `n·n` is enough. The same descriptor
comes back out, so the grouping pass inherits it.

`1 ≤ A.N` is not assumed: it follows from `¬ A.G = ⊥`, since a graph on
an empty carrier is `⊥`. It is what lets the program's three
whole-run constants be folded into `asw·A.N`. -/
theorem peelSweepIn_of_bfs (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od lo lm : ℕ → String) (Ssc : ℕ → Env → Prop)
    (bfC : ℕ → Com) (abf bbf cbf : ℕ) (hq : 1 ≤ q)
    (hR : 1 ≤ (Headline.headlineSetup C hC φ).R)
    (hnd : ∀ j, ao j ≠ aj j ∧ ao j ≠ mt j ∧ ao j ≠ dg j ∧
      aj j ≠ mt j ∧ aj j ≠ dg j ∧ mt j ≠ dg j ∧ ca j ≠ lo j)
    (hkeep : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ca j ∨
      b = lo j → b ≠ aj j ∧ b ≠ dg j ∧ b ≠ mt j)
    (hfresh : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ao j ∨
      b = aj j ∨ b = dg j ∨ b = mt j → b ≠ ca j ∧ b ≠ lo j)
    (hSsc : ∀ (j : ℕ) (σ σ' : Env),
      (∀ b : String, b ≠ ca j → b ≠ lo j → b ≠ lm j → b ≠ aj j → b ≠ dg j →
        b ≠ mt j → σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ≠ "sw.i" → y ≠ "sw.v" → y ≠ "dl.i" → y ≠ "dl.w" →
        y ≠ "dl.p" → y ≠ "dl.l" → y ≠ "dl.u" → y ≠ "dl.q" →
        σ'.vars y = σ.vars y) → Ssc j σ → Ssc j σ')
    (hbfs : PeelBfsIn C hC φ ord G c w q ℓp htabF hbf Adm ca co
      ao aj dg mt od lo lm Ssc bfC abf bbf cbf) :
    PeelSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
      ao aj dg mt od lo lm
      (fun j σ => n + 1 ≤ (σ.arrs (lo j)).length ∧
        n * n ≤ (σ.arrs (lm j)).length ∧ Ssc j σ)
      (fun j σ => n + 1 ≤ (σ.arrs (lo j)).length ∧
        n * n ≤ (σ.arrs (lm j)).length ∧ Ssc j σ)
      (fun j => sweepCom (bfC j) (ca j) (lo j) (ao j) (aj j) (dg j) (mt j)
        (od j) (arenaNames j).nN)
      (abf + 42) (bbf + 54) cbf := by
  classical
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hAW, -, hordr, hdel0, hca, hco, hloLen, hlmLen, hSscσ⟩ := hσ
  obtain ⟨ho1, ho2, ho3, ha1, ha2, hm1, hcl⟩ := hnd j
  obtain ⟨hnNi, hnSi⟩ := arenaScalars_ne j (t := "sw.i") (by decide)
    (by decide) (by decide)
  -- the word bound, and the carrier's fit inside the input
  have hAN : A.N ≤ n := by
    have h := Fintype.card_le_of_embedding A.up
    simpa using h
  have hBnd : A.N + A.N * A.N < mcB q x := arena_sq_lt_mcB hq hx A
  have hANB : A.N < mcB q x := lt_of_le_of_lt (Nat.le_add_right _ _) hBnd
  -- an arena with no edges is `⊥`, so the carrier is nonempty
  have hN1 : 1 ≤ A.N := by
    by_contra hcc
    have h0 : A.N = 0 := by omega
    exact hbot (by ext a b; exact absurd a.isLt (by omega))
  have hnN : σ.vars (arenaNames j).nN = A.N := hAW.n_eq
  -- the sentinel pass
  obtain ⟨σ1, hr1, hfill, hlo0, harr1, hlen1, hvar1⟩ :=
    (sweepInit_spec (ca := ca j) (lo := lo j) (nn := (arenaNames j).nN)
      hcl hnNi hANB).run ⟨hnN, hca, by omega⟩
  have hfr1 : ∀ b : String, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
      b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ao j ∨
      b = aj j ∨ b = dg j ∨ b = mt j → σ1.arrs b = σ.arrs b := by
    intro b hb
    obtain ⟨k1, k2⟩ := hfresh j b hb
    exact harr1 b k1 k2
  have hst0 : SweepSt (Headline.headlineSetup C hC φ) j (hbf j) A (htabF j A)
      ((ord A.N A.G).order) (ca j) (co j) (ao j) (aj j) (dg j) (mt j) (od j)
      (lo j) (lm j) (Ssc j) 0 0 σ1 := by
    refine ⟨arenaStW_of_eq hAW (hvar1 _ hnNi) (hvar1 _ hnSi)
        (hfr1 _ (Or.inl rfl)) (hfr1 _ (Or.inr (Or.inl rfl)))
        (hfr1 _ (Or.inr (Or.inr (Or.inl rfl))))
        (hfr1 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        (hfr1 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
      hordr.of_eq (hfr1 _ (by tauto)), by rw [hlen1 (co j)]; exact hco,
      by rw [hlen1 (lm j)]; exact hlmLen,
      hSsc j σ σ1 (fun b h1 h2 _ _ _ _ => harr1 b h1 h2) hlen1
        (fun y h1 _ _ _ _ _ _ _ => hvar1 y h1) hSscσ, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [peelSet_zero]
      exact hdel0.of_eq (hfr1 _ (by tauto)) (hfr1 _ (by tauto))
        (hfr1 _ (by tauto)) (hfr1 _ (by tauto))
    · rw [hlen1 (ca j)]; exact hca
    · intro v
      rw [if_neg (by omega)]
      exact hfill (v : ℕ) v.isLt
    · rw [hlen1 (lo j)]; omega
    · intro k hk
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact hlo0
    · simp
    · intro k hk; omega
    · intro k hk; omega
  -- the counter, then the loop
  have hzero : Spec (mcB q x) (fun _ : Env => True) (.assign "sw.i" (.lit 0))
      (fun τ τ' => τ' = τ.setVar "sw.i" 0) 2 :=
    (Spec.assign (f := fun _ => 0) (fun _ _ => evalB_lit (by omega))).mono
      (by simp [Expr.size])
  obtain ⟨σ2, hr2, rfl⟩ := hzero.run trivial
  have hst2 : SweepSt (Headline.headlineSetup C hC φ) j (hbf j) A (htabF j A)
      ((ord A.N A.G).order) (ca j) (co j) (ao j) (aj j) (dg j) (mt j) (od j)
      (lo j) (lm j) (Ssc j) 0 0 (σ1.setVar "sw.i" 0) := by
    refine hst0.step rfl rfl rfl rfl rfl (by rw [vars_setVar, if_neg hnNi])
      (by rw [vars_setVar, if_neg hnSi]) rfl rfl rfl rfl rfl ?_ hst0.2.2.2.2.2.1
    exact hSsc j σ1 _ (fun _ _ _ _ _ _ _ => rfl) (fun _ => rfl)
      (fun y h1 _ _ _ _ _ _ _ => by rw [vars_setVar, if_neg h1]) hst0.2.2.2.2.1
  obtain ⟨σ3, hr3, hst3⟩ :=
    (sweepLoop_spec (S := Headline.headlineSetup C hC φ) (j := j) (hb := hbf j)
      (htab := htabF j A) (π := (ord A.N A.G).order) (bfC := bfC j)
      ho1 ho2 ho3 ha1 ha2 hm1 (hkeep j)
      (fun τ τ' k1 k2 k3 k4 => hSsc j τ τ' k1 k2 k3 k4) hR hBnd
      (fun i hi => hbfs x hx j hj A hAdm hbot i hi)).run
      ⟨hst2, by rw [vars_setVar, if_pos rfl]⟩
  -- the whole run, at the summed budget
  have hcost : 11 * A.N + 9 + (2 + (peelK (abf + 16) (bbf + 54) cbf
        (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order) + 4))
      ≤ peelK (abf + 42) (bbf + 54) cbf (Headline.headlineSetup C hC φ) A
          ((ord A.N A.G).order) := by
    rw [peelK, peelK]
    have hexp : (abf + 42) * A.N = (abf + 16) * A.N + 26 * A.N := by ring
    omega
  refine ⟨σ3, (hr1.seq (hr2.seq hr3)).mono hcost, hst3.1, ?_, hst3.2.1, ?_,
    hst3.2.2.1, ?_, ?_, hst3.2.2.2.2.1⟩
  · exact hst3.2.2.2.2.2.2.1.full
  · exact hst3.2.2.2.2.2.2.2.full
  · have h1 := run_arrs_length_eq hr1 (lo j)
    have h2 := run_arrs_length_eq hr2 (lo j)
    have h3 := run_arrs_length_eq hr3 (lo j)
    omega
  · have h1 := run_arrs_length_eq hr1 (lm j)
    have h2 := run_arrs_length_eq hr2 (lm j)
    have h3 := run_arrs_length_eq hr3 (lm j)
    omega

/-! ## §8 What the BFS half must establish, at the state level

Three lemmas the discharger of `PeelBfsIn` consumes. They are here
rather than there because each is about the *loop's* invariant, not
about a program, and getting either step wrong is the way a BFS that
looks right emits the wrong region.

`centre_eq_iff_first_hit` is `centre_eq_of_hit_first` **and its
converse**: the marking condition is not merely sufficient, it is
exactly `Driver.centre`, so a pass that marks the first-hit set marks
neither too few nor too many. -/

/-- **The first-hit set is exactly the centre's fibre.** `v` is claimed
by `u` precisely when `u`'s `R`-ball at `u`'s own peel state reaches
`v` and no `π`-earlier centre's did — the "first assignment wins"
discipline, in both directions. The forward direction is
`centre_eq_of_hit_first`; the converse is the minimality of `ctr`. -/
theorem centre_eq_iff_first_hit (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u v : Fin A.N) :
    centre S A π v = u ↔
      (v ∈ ball (deleteVerts A.G (peelSet π ((π u : Fin A.N) : ℕ))) S.R u ∧
        ∀ u' : Fin A.N, π u' < π u →
          v ∉ ball (deleteVerts A.G (peelSet π ((π u' : Fin A.N) : ℕ))) S.R u') := by
  constructor
  · rintro rfl
    refine ⟨?_, fun u' hlt hmem => ?_⟩
    · rw [peelSet_rank]
      exact Impl.mem_wreach_iff_mem_peeledBall.mp
        (Lax3Proofs.CoverCentres.ctr_mem_wreach A.G π S.R v)
    · rw [peelSet_rank] at hmem
      exact absurd hlt (not_lt.mpr (Lax3Proofs.CoverCentres.ctr_le_of_mem_wreach
        (Impl.mem_wreach_iff_mem_peeledBall.mpr hmem)))
  · rintro ⟨h1, h2⟩
    exact centre_eq_of_hit_first S A π h1 h2

/-- **The marking step.** A pass that writes its own centre into the
cells of that centre's fibre and leaves every other cell alone moves
the part-filled assignment region up one rank. Nothing else is asked —
in particular no clause about the order the cells are visited in, and
none about cells outside the fibre beyond their being untouched.

The `ctrF v ≠ u` branch is where "first assignment wins" is spent: a
cell already holding an earlier centre is *not* rewritten, and the
invariant records that as "its centre's rank has already passed". -/
theorem ctrPart_succ {ca : String} {N : ℕ} {ctrF : Fin N → Fin N}
    {π : Equiv.Perm (Fin N)} {i : ℕ} (hi : i < N) {σ σ' : Env}
    (h : CtrPart ca ctrF π i σ)
    (hlen : N ≤ (σ'.arrs ca).length)
    (hhit : ∀ v : Fin N, ctrF v = π.symm ⟨i, hi⟩ →
      (σ'.arrs ca).getD (v : ℕ) 0 = ((π.symm ⟨i, hi⟩ : Fin N) : ℕ))
    (hmiss : ∀ v : Fin N, ctrF v ≠ π.symm ⟨i, hi⟩ →
      (σ'.arrs ca).getD (v : ℕ) 0 = (σ.arrs ca).getD (v : ℕ) 0) :
    CtrPart ca ctrF π (i + 1) σ' := by
  refine ⟨hlen, fun v => ?_⟩
  by_cases hv : ctrF v = π.symm ⟨i, hi⟩
  · have hrank : ((π (ctrF v) : Fin N) : ℕ) = i := by
      rw [hv, Equiv.apply_symm_apply]
    rw [hhit v hv, if_pos (by omega), hv]
  · have hrank : ((π (ctrF v) : Fin N) : ℕ) ≠ i := by
      intro hc
      exact hv (by
        rw [← Equiv.symm_apply_apply π (ctrF v)]
        congr 1
        exact Fin.ext hc)
    rw [hmiss v hv, h.2 v]
    by_cases hlt : ((π (ctrF v) : Fin N) : ℕ) < i
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- **The log step.** A pass that appends row `i` at `lo[i]`, writes
`lo[i+1]`, and disturbs neither the earlier offsets nor the earlier
rows moves the part-filled log up one rank.

The row's own clauses are `ClusterLog`'s two, at this row only:
soundness (every written cell is a member) and completeness (every
member is written). Duplicate-freeness is *not* asked — it is derived
downstream by `ClusterLog.row_injOn`, and asking for it here would put
a clause into the invariant that the pass would have to maintain for
no consumer. -/
theorem logPart_succ {lo lm : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {Xf : Fin N → Set (Fin N)} {i : ℕ} (hi : i < N) {σ σ' : Env}
    (h : LogPart lo lm π Xf i σ)
    (hlolen : N + 1 ≤ (σ'.arrs lo).length)
    (holdoff : ∀ k, k ≤ i → (σ'.arrs lo).getD k 0 = (σ.arrs lo).getD k 0)
    (hnewoff : (σ'.arrs lo).getD (i + 1) 0 = peelOff π Xf (i + 1))
    (hlmlen : peelOff π Xf (i + 1) ≤ (σ'.arrs lm).length)
    (holdrow : ∀ m, m < peelOff π Xf i →
      (σ'.arrs lm).getD m 0 = (σ.arrs lm).getD m 0)
    (hsnd : ∀ t : ℕ, t < (Xf (π.symm ⟨i, hi⟩)).ncard →
      ∃ z : Fin N, z ∈ Xf (π.symm ⟨i, hi⟩) ∧
        (σ'.arrs lm).getD (peelOff π Xf i + t) 0 = (z : ℕ))
    (hcmp : ∀ z : Fin N, z ∈ Xf (π.symm ⟨i, hi⟩) →
      ∃ t : ℕ, t < (Xf (π.symm ⟨i, hi⟩)).ncard ∧
        (σ'.arrs lm).getD (peelOff π Xf i + t) 0 = (z : ℕ)) :
    LogPart lo lm π Xf (i + 1) σ' := by
  obtain ⟨-, hread, -, hs, hc⟩ := h
  -- an earlier row sits strictly below the new row's anchor
  have hbelow : ∀ k : Fin N, (k : ℕ) < i → ∀ t : ℕ, t < (Xf (π.symm k)).ncard →
      peelOff π Xf (k : ℕ) + t < peelOff π Xf i := by
    intro k hk t ht
    have h1 : peelOff π Xf ((k : ℕ) + 1) = peelOff π Xf (k : ℕ)
        + (Xf (π.symm k)).ncard := peelOff_step π Xf k
    have h2 : peelOff π Xf ((k : ℕ) + 1) ≤ peelOff π Xf i :=
      peelOff_mono π Xf (by omega)
    omega
  refine ⟨hlolen, ?_, hlmlen, ?_, ?_⟩
  · intro k hk
    rcases Nat.eq_or_lt_of_le hk with rfl | hk'
    · exact hnewoff
    · rw [holdoff k (by omega)]
      exact hread k (by omega)
  · intro k hk t ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
    · obtain ⟨z, hz, hval⟩ := hs k hk' t ht
      exact ⟨z, hz, by rw [holdrow _ (hbelow k hk' t ht)]; exact hval⟩
    · obtain rfl : k = (⟨i, hi⟩ : Fin N) := Fin.ext hk'
      exact hsnd t ht
  · intro k hk z hz
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
    · obtain ⟨t, ht, hval⟩ := hc k hk' z hz
      exact ⟨t, ht, by rw [holdrow _ (hbelow k hk' t ht)]; exact hval⟩
    · obtain rfl : k = (⟨i, hi⟩ : Fin N) := Fin.ext hk'
      exact hcmp z hz

/-! The leaf's axiom profile. The loop, its budget and the sentinel
pass use nothing but the three of the ambient logic; the discharge
quotes `Headline.headlineSetup`, so — exactly like the
`covPeelIn_of_sweep_group` it feeds — it additionally carries Lax12's
endorsed `uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms sweepInit_spec

#print axioms sum_peelTurn

#print axioms sweepLoop_spec

#print axioms centre_eq_iff_first_hit

#print axioms peelSweepIn_of_bfs

end Lax3Proofs.Prog
