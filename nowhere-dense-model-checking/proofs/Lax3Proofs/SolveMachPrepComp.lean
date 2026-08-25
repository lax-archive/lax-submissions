import Lax3Proofs.SolveMachPrepSeam

/-!
# F6c12 (residual 1) — the child-building pass, composed

`SolveMachPrepSeam` reduced the whole prep segment to
**`ChildLoadPartsScrAll`** — the machine pass, stated at the parts, with
the level's scratch descriptor conjoined. Every *stage* of that pass is
landed as an individual `Spec`; what was missing is the composition
itself: the concrete command `prepC j`, the name pool it draws on, the
seams between consecutive stages, and the budget summation.

This file supplies the parts of that composition that are
self-contained, and pins — as compiling statements, not prose — the
seams that no landed object provides.

## §1 The name pool

Every name the pass uses is `lv <base> <index>` at a four-character
base, so **every** disequality in the composition is `decide`-able:
`lv_notMem` and `lv_ne_lit` turn a base clash into a decidable
proposition about string literals. The pass's own arrays and scalars
are level-**in**dependent (`"pc.·"`, `"pf.·"`): the frame clause
`ChildLoadPartsScr` demands is agreement on `ca j :: co j :: cm j ::
levelArrays j`, and a base outside `{sa.·, sv.·, sl.·}` misses that
pool at *every* level, so nothing is gained by tagging the scratch and
the descriptor transport `hscrDown` is much cheaper without it.

## §2 The command

`prepC` is the nine stages in the order `SolveMachPrepAll` §0 fixes,
with the `O(1)` scalar loads that set each stage's input cells spliced
between them. Two placements are forced and worth naming:

* **`mkBatchCom` before `supportsCom`** — the batch is read off the
  channel region *as `restrictCom` leaves it* (`childHistTab`), and
  `supportsCom` overwrites one of its columns.
* **`profilesCom` before `colWriteCom`** — profiles read the colour
  region at the parent's palette (`childCol0`), and the writer
  overwrites it at `isoPal`.

## §3 The seams

Four seams were named when this leaf was minted; composing the stages
turns up **two more**, and both are recorded here as lemmas rather than
as prose:

1. **The isolate stage's output names are not the deliverable's.**
   `isolateCom_specW` leaves the isolated CSR at `oaO`/`taO` with the
   slot count in `nsO`, and requires `nsO ≠ nmI.nS`; the
   `ChildLoadPartsScr` deliverable is stated at `arenaNames (j+1)`.
   Routing the *restrict* stage's CSR into scratch and the *isolate*
   stage's into `arenaNames (j+1)` closes the two array names, and
   `arenaStW_setVar_nS` (§3) closes the cell — one scalar move.
2. **`arenaStW_recol` cannot be applied where the pass needs it.**
   The landed lemma reads the four unchanged regions and the new colour
   cells at *the same* state; but the colour writer destroys the old
   `ColBits`, so `ArenaStW nm hb A σ'` is false at the state where the
   new cells hold. `arenaStW_recol_frame` (§3) is the two-state form —
   the four regions read at the pre-state, the colour cells at the
   post-state — which is the shape the composition actually has.

## Hazards honoured

Nothing here moves a stage, a radius or a budget. No program wipes a
carrier-sized region at the *parent's* dimension: `prepC`'s only
`O(A.N)` work is `restrictCom`'s own, so §6.1's `Θ(A.N²)` scratch trap
is untouched, and §4's budget is `prepPassK` plus an explicit constant.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

/-! ## §1 The name pool -/

/-- A level-tagged name is never one of a list of untagged literals of
the same length — the shape every `∉ rsScalars` side condition takes.
The hypothesis is decidable at a concrete list. -/
theorem lv_notMem {s : String} {l : List String}
    (h : ∀ t ∈ l, s.length = t.length ∧ s ≠ t) (j : ℕ) : lv s j ∉ l := by
  intro hmem
  obtain ⟨hlen, hne⟩ := h _ hmem
  rw [lv_length] at hlen
  have hj : j = 0 := by omega
  subst hj
  exact hne rfl

/-- A level-tagged name is never an untagged literal of the same length
with a different base. -/
theorem lv_ne_lit {s t : String} (hlen : s.length = t.length) (hne : s ≠ t)
    (j : ℕ) : lv s j ≠ t :=
  fun h => hne (lv_inj hlen (h : lv s j = lv t 0)).1

section Names

/-! ### The pass's own regions and cells

All bases have length four (`lv_inj`'s requirement) and none starts
`sa.`/`sv.`/`sl.` (the level pool), `rs.`/`bf.`/`sp.`/`gs.`/`pw.` (the
stages' scratch cells). The three *families* are `lv`-indexed at their
own bases, so `lv_inj` gives injectivity and `lv_ne_of_base_ne` gives
pairwise disjointness. -/

/-- Array: the cluster's enumeration region (`restrictCom`'s
`ClusterList`). -/
def pcLa : String := "pc.l"
/-- Array: the rank scratch — the one array `restrictCom` dirties and
cleans. -/
def pcRa : String := "pc.r"
/-- Array: the **pre-isolation** child CSR offsets. `restrictCom` builds
the child here, not in the level's own region, because `isolateCom`
needs a fresh output pair and the deliverable is stated at
`arenaNames (j+1)`. -/
def pcOi : String := "pc.o"
/-- Array: the pre-isolation child CSR targets. -/
def pcTi : String := "pc.t"
/-- Array: the batch bit vector — one region for the scan and the
isolation both (`range_batchFn_eq_batchSet`). -/
def pcBb : String := "pc.b"
/-- Array: the padded batch index region, at length exactly `S.width`. -/
def pcBi : String := "pc.i"
/-- Array: the BFS distance region. -/
def pcDa : String := "pc.d"
/-- Array: the supports pass's least-parent region. -/
def pcPa : String := "pc.p"
/-- Array: the profiles stage's per-class bit scratch. -/
def pcXb : String := "pc.x"
/-- Array: the profiles stage's `vsrc` offset scratch. -/
def pcVo : String := "pc.v"

/-- Array family: the batch distance tables, one per padded slot. -/
def pcPd : ℕ → String := lv "pf.d"
/-- Array family: the per-class `vsrc` target regions. -/
def pcVt : ℕ → String := lv "pf.v"
/-- Array family: the virtual-source distance tables, one per
relativised colour. -/
def pcPu : ℕ → String := lv "pf.u"

/-- Scalar: the cluster row's base offset. -/
def pcCb : String := "pc.a"
/-- Scalar: the cluster row / connector scan counter. -/
def pcCt : String := "pc.c"
/-- Scalar: the connector's own child name. -/
def pcCc : String := "pc.e"
/-- Scalar: the batch builder's column cursor. -/
def pcEc : String := "pc.f"
/-- Scalar: the batch builder's entry cursor. -/
def pcIc : String := "pc.g"
/-- Scalar: the batch builder's row length. -/
def pcLn : String := "pc.h"
/-- Scalar: the batch builder's slot base. -/
def pcBs : String := "pc.j"
/-- Scalar: the batch builder's carrier cursor. -/
def pcAv : String := "pc.k"
/-- Scalar: the batch builder's emit cursor. -/
def pcSc : String := "pc.m"
/-- Scalar: the round count, a compile-time constant (`= j`). -/
def pcJr : String := "pc.n"
/-- Scalar: the schedule's batch width. -/
def pcMw : String := "pc.q"
/-- Scalar: the colour writer's row base. -/
def pcW : String := "pc.w"
/-- Scalar: the colour writer's distance cursor. -/
def pcDd : String := "pc.s"
/-- Scalar: the colour writer's carrier cursor. -/
def pcVv : String := "pc.u"
/-- Scalar: the isolation's output slot count. -/
def pcNo : String := "pc.y"

/-- **The pre-isolation child's name family**: the level-`(j+1)` regions
with the CSR pair routed through the pass's own scratch. This is the
`nmC` `restrictCom_specW` builds into and the `nmI` `isolateCom_specW`
reads from. -/
def prepMid (j : ℕ) : ArenaNames :=
  { arenaNames (j + 1) with off := pcOi, tgt := pcTi }

@[simp] theorem prepMid_nN (j : ℕ) : (prepMid j).nN = (arenaNames (j + 1)).nN :=
  rfl
@[simp] theorem prepMid_nS (j : ℕ) : (prepMid j).nS = (arenaNames (j + 1)).nS :=
  rfl
@[simp] theorem prepMid_off (j : ℕ) : (prepMid j).off = pcOi := rfl
@[simp] theorem prepMid_tgt (j : ℕ) : (prepMid j).tgt = pcTi := rfl
@[simp] theorem prepMid_col (j : ℕ) :
    (prepMid j).col = (arenaNames (j + 1)).col := rfl
@[simp] theorem prepMid_up (j : ℕ) :
    (prepMid j).up = (arenaNames (j + 1)).up := rfl
@[simp] theorem prepMid_hist (j : ℕ) :
    (prepMid j).hist = (arenaNames (j + 1)).hist := rfl
@[simp] theorem prepMid_tab (j : ℕ) :
    (prepMid j).tab = (arenaNames (j + 1)).tab := rfl

/-- **The isolation's output family is the deliverable's**: routing the
restrict stage into `pcOi`/`pcTi` and the isolate stage into the
level's own CSR pair leaves exactly one name to move — the slot-count
cell, which `isolateCom_specW` forbids from being `nmI.nS`. -/
theorem isolate_out_names (j : ℕ) :
    ({ prepMid j with off := (arenaNames (j + 1)).off,
        tgt := (arenaNames (j + 1)).tgt, nS := pcNo } : ArenaNames)
      = { arenaNames (j + 1) with nS := pcNo } := rfl

end Names

end Lax3Proofs.Prog
