import Lax3Proofs.RamDriverCluster
import Lax3Proofs.RamDriverFrames
import Lax3Proofs.Refine.DriverCache
import Lax3Proofs.Refine.MassWeight
import Lax3Proofs.Refine.ScatterDeadPass

/-!
The passes of one cluster of `Lax3Proofs.RamDriver`, walked: the
padding, the retained descent, and the expansion chains used by the
colouring.

This file is stage three of the driver. It carries the walks of
`RamDriver.enumBatch` and of `RamDriver.expandCom`/`chainCom` — the
first is a whole obligation of `Lax3Proofs.RamDriverCluster`, the second
supplies the colouring's three slot families (and the standalone legacy
ball specification) — together with the three transport lemmas a pass
needs to hand a depth's state on.

# What is proved

* `enumBatch_spec`, the padding pass: the buffer ends holding exactly
  `mb` entries, every one a vertex BOTH the batch and the cluster mark,
  and every such vertex among them (wave R1.8-T3-flip (c2a) — the
  cluster guard; the verdict that put it there is
  `Refine.ScatterDeadPass` §0b). Its content is a counting argument —
  `markedBelow` and `count_lt_of_mark` at the product cell — that the
  collecting loop never overruns the buffer, and `PadInv` for the
  repetition that follows.
* `enumStepW`, that pass at the surface `RamDriverCluster.EnumStep`
  states it at, and `enumStep_of_maskWords`, which turns it into the
  obligation itself from one clause about the batch indicator.
* `expandSlot_step`, `expandStep_spec`, `expandCom_spec`: one step of
  neighbourhood expansion, the inner block scan against
  `Csr.rowScan_spec` with `RamDriverCluster.ScanHit`, the outer pass
  against `Refine.SigmaLoop.forRangeZeroSum` with
  `RamDriverCluster.ExpandInv`, and
  `RamDriverCluster.hit_eq_expandVal` at the join.  The live scan
  invariant retains the row's lower endpoint, so the per-row charges
  telescope to the CSR target length instead of multiplying that length
  by the carrier size.
* `chainCom_spec`, the chain of `r` of them: the last name of the
  family marks the `r`-neighbourhood of what the first one marked. The
  induction peels the chain from the *front*, which is what the syntax
  of `RamDriver.foldRange` gives (`chainCom_succ`), so the radius
  arithmetic it needs is `ballOf_nbhd` and not
  `RamDriverCluster.nbhd_ballOf`. The family of names is a parameter:
  the standalone ball chain alternates between two names
  (`RamDriver.ballStage`) and the colour chains run through distinct
  ones, and both are instances.
* `levelPre_congr`, `coverHeld_congr`, `batchData_congr`: the clauses of
  `RamDriverCluster.TurnPre` and the descent's data, carried across a
  pass off the frame rule's equations.

# The surface repairs, and what is left

`RamDriverCluster.EnumStep`, `RamDriverCluster.ColourStep`, and
`RamDriverCluster.DescendStep` are proved (`enumStep`, `colourStep`, and
`descendStep`). The batch contract below records the semantic repair
that made the descent executable.

The clauses the two obligations used to be short of, and where each
went:

1. **Indicator cells are bits.** `BatchData` carries
   `∀ k < n, Xa k ≤ 1` at `cluName j` — which is what
   `clusterLoad_spec` proves and what `oldCom`'s product needs, since
   the obligation's own postcondition says the product is a bit — and
   `∀ k < n, Wa k < B` at `batName j`, beside the ones `resName j`
   already had. `RamDriver.LevelPre` carries
   `∀ c < sigL cap mb j, ∀ z < n, C c z ≤ 1` for the colour arrays
   `oldCom` multiplies, which is `ColourStep`'s own postcondition one
   depth down and the empty palette at the root. And
   `RamDriverCluster.CoverHeld` carries `∀ z < n, ord z < n`, which with
   `n < B` is what `descendCom`'s first read of the ordering needs.
2. **The per-cluster arrays exist.** `RamDriver.DepthMem`, a conjunct of
   `LevelPre`, sizes every per-depth array of *every* depth — the
   cluster indicator, the restricted mask, the ball's two halves, the
   batch, the ordering, the cover's three copies, and the colour family
   `colName j c` for `c < sigL cap mb j`. It is depth-independent for
   the reason `RamDriver.TablesSized` is: a level runs the level below
   it, which stores into the arrays of *its* depth.
3. **The recorded play is in the state.** `RamDriver.PlayRec` is the
   invariant: the connectors `ctrName a` and the game masks `gamName a`
   of every `a < j` are there, hold vertices and words, and — off the
   dead branch — are the rounds of a monotone `ReachedSubR` play whose
   retained position is the depth's own game arena. `RamDriver.playRec_succ` is the descent
   step and `RamDriver.playOk_of_playRec` the bridge to the old
   invariant. `DescendStep`'s last clause is now `PlayRec` one depth
   down, and `EnumStep`/`ColourStep` carry it across.
4. **The unreachable ancestor is guarded.** `RamDriver.ancestorStep`
   runs the search and the walk back separately, the second only under
   `dist[tv] < 2·cap + 1`. The recorded game's walk clause is guarded by
   the same condition — a round owes a walk to an earlier connector only
   where its own arena puts the two within `2·cap` — so the skip branch
   owes nothing at all, and what discharges it is
   `RamBfs.BfsTree.reach` read backwards: a sentinel distance is a proof
   of `¬ WithinDist`.
5. **`mb < B`** is the second conjunct of `RamDriver.WordBoundK`, and
   `enumStepW` reads it off `WordBoundK.mb_lt`.
6. **The graph is a hypothesis of `ColourStep`.** The three slot
   families are expansion chains and read the block structure, so the
   obligation is prefixed by `CsrGraph G ns O T` and `WordBoundK`,
   exactly as `DescendStep` is.

# The executable batch contract

The obstruction this file used to record was at the *surface*. The game
`RamDriver.playRec_succ` descended in was parameterized by an oracle: a
round isolated the oracle's batch, a **function** of the arena and the
two vertices, and the game's step rule extended a play to that function's
value and to no subgraph of it. The machine cannot produce
it. `RamBfsPaths.bfsPath_spec` pins the extraction buffer only as

    ∃ p, p.length ≤ d ∧ bufSet n L Buf = {z | z ∈ p.support}

— *some* walk of length at most the cap — and no function of `(A, u, v)`
is extractable from that. The sharp instance is `C₄` at `cap ≥ 1`: the
two antipodal vertices are joined by two walks of length two, the
machine picks by the order of the block structure's rows and
`SplitterWin.pathSet` picks by `Classical.choice`, and the two choices
are independent. Weakening the game to a containment did not help
either, since the program's buffer contains the oracle's chosen walk no
more than it equals it.

`Lax3Proofs.SplitterWinRec` is the repair, and it is on the game side:
the round **records** the set it isolated, and is asked only for what
the win argument consumes and what `bfsPath_spec` certifies. So the
batch phase owes, of the set `W` the batch indicator marks:

* `W ⊆ X ⊆ ball (masked G Gm) (2·cap) v` — `batchCom` cuts directly to
  the retained cover cluster `X`, whose inclusion in the ball is a cover
  theorem rather than an executable expansion;
* `v ∈ W` — the store of `1` at `ctrName j` at its start;
* for every round the state records, `RamDriver.RecordedRound`, whose
  arena puts its connector within `2·cap` of `v`: the support of *some*
  walk of length at most `2·cap` between them in that arena, intersected
  with `X`, lies in `W` — one turn of the fold, in the branch the
  guard takes;
* `W.Nonempty` and `W.ncard ≤ mb` — the connector, which is the
  centre `clusterLoad` materialized the cluster of and so lies in it
  (`RamCover.self_mem_wreach`, wave R1.8-T3-flip (c2a)), and one buffer
  of at most `2·cap + 1` vertices per earlier round;
* and the mask equations, which are `RamDriver.masked_step` and
  `masked_mul` as before, with `RamDriver.stepArena_le_nextArena` showing
  the retained game position is below the exact splitter successor.

The size bound is the one clause that needs something from outside the
turn: `1 + j · (2·cap + 1) ≤ mb` holds because `mb = ℓ · (2·cap + 1)` and
`j < ℓ`, and neither is a clause of `RamDriverCluster.DescendStep`.
Neither has to be: they are hypotheses of the *theorem* discharging it,
in the manner of `RamDriverCluster.clusterStepImplements`'s `hcap`, and
the assembly wave has both where it applies that theorem —
`RamDriverCluster.levelImplements` quantifies its cluster-step hypothesis
over `j < ℓ`, and `mb`'s value is the driver's standing choice.

None of the rest is an equation with a set the program did not compute,
so all of it is symbolic execution over `RamBfsPaths.bfsPar_spec`,
`extractPath_spec` and the flat passes around them. `andSelfCom_spec`
below discharges the final cut to the cluster.

# One more gap, in the kit — closed

`descendCom`'s last pass is
`subCom (gamName (j + 1)) (batName j) (gamName (j + 1))` — the source
and the destination are the **same array**. The pass is correct (a flat
pass writes cell `i` from cell `i` of everything it reads, so no cell is
read after it is written), but `RamDriverCluster.subCom_spec` asks
`a ≠ dst`, because `RamDriverCluster.fill_spec` carries its readers as a
`Frozen` family — an equation about the *whole* array, false of the
destination halfway through the loop — that the pass may not write. So
the obligation had no proof at the kit it was stated over, and it is not
the batch phase's gap: it survives every repair of that one.

`selfFill_spec` and `subSelfCom_spec` are the kit's in-place flat pass
and the mask operation the last line needs, with the destination's
*entering* cell function carried by the invariant (`SelfBelow`) instead
of frozen. No program change is needed.
-/

namespace Lax3Proofs.RamDriverDescend

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax3Proofs.Horizon Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance
open Lax3Proofs.FormulaTables Lax3Proofs.SplitterWin Lax3Proofs.SplitterWinRec
open Lax3Proofs.RamBfs (masked masked_adj CsrGraph MAdj WD)
open Lax3Proofs.RamDriver Lax3Proofs.RamDriverCluster
open Lax3Proofs.Refine.DriverCache
open Lax3Proofs.Refine.MassMath (blockSize)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ### Reading a mask cell

A pass that reads a mask reads a *cell of a list*, and the bounded
semantics asks two things of such a read: that the index is inside the
list, and that the value it finds is a word. The first is the array's
length and the second is a clause about its contents — `MaskWords`
below — which no equation of the form `σ.arrs a = arrOf n Wa` implies
and which every pass that reads an indicator therefore has to be
handed. -/

/-- Every cell of the array named `a` is a word. Stated on the list, so
that `RamDriver.run_mem_arrs_lt` carries it across any run. -/
def MaskWords (B : ℕ) (a : String) (σ : Env) : Prop := ∀ v ∈ σ.arrs a, v < B

/-- A cell of an `arrOf` array is one of its members. -/
theorem mem_arrOf {N : ℕ} (f : ℕ → ℕ) {k : ℕ} (hk : k < N) : f k ∈ arrOf N f :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

/-- The word clause, read at a cell. -/
theorem MaskWords.get {B N : ℕ} {a : String} {σ : Env} {f : ℕ → ℕ} (h : MaskWords B a σ)
    (harr : σ.arrs a = arrOf N f) {k : ℕ} (hk : k < N) : f k < B :=
  h _ (by rw [harr]; exact mem_arrOf f hk)

/-- The clause survives any run. -/
theorem MaskWords.run {B : ℕ} {a : String} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : MaskWords B a σ) (hr : Run B c σ σ' K) : MaskWords B a σ' :=
  run_mem_arrs_lt hr a h

/-! ### Carrying a depth's state across a pass

A pass of the driver writes a handful of arrays and a handful of
scalars, and everything else a depth is holding has to come back. The
frame rule reads off the syntax *which* names are safe; what it does
not do is put the depth's clauses back together out of them, and these
three lemmas are that — one per clause of `RamDriverCluster.TurnPre`
and one for the descent's own data. Each asks exactly for the names its
clause mentions, so a pass discharges it with one frame equation per
line and nothing is decided twice.

The memory clauses (`RamDriver.LevelMem`, the `Sized` list of
`RamDriver.OrderMem`) are not framed at all: a run cannot change the
length of an array, so they cross any pass by `RamDriver.Sized.run`. -/

section Frames

variable {B n cap mb ns Ws j K : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
  {σ σ' : Env} {c : Com}

/-- **The engines' scratch, across a pass.** Only the eight zeroed
accumulators have to be named: the lengths cross by themselves, and so
do the two word clauses, since a bounded run stores only words. -/
theorem orderMem_congr (h : OrderMem B n ns Ws σ) (hr : Run B c σ σ' K)
    (hlw : σ'.vars "lw" = σ.vars "lw")
    (hz : ∀ a ∈ (["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"] : List String),
      σ'.arrs a = σ.arrs a) : OrderMem B n ns Ws σ' :=
  ⟨h.1, by rw [hlw]; exact h.2.1, h.2.2.1.run hr, by rw [hz "elm" (by simp)]; exact h.2.2.2.1,
    by rw [hz "bh" (by simp)]; exact h.2.2.2.2.1,
    by rw [hz "ooff" (by simp)]; exact h.2.2.2.2.2.1,
    by rw [hz "noff" (by simp)]; exact h.2.2.2.2.2.2.1,
    by rw [hz "stf" (by simp)]; exact h.2.2.2.2.2.2.2.1,
    by rw [hz "sta" (by simp)]; exact h.2.2.2.2.2.2.2.2.1,
    by rw [hz "std" (by simp)]; exact h.2.2.2.2.2.2.2.2.2.1,
    by rw [hz "ste" (by simp)]; exact h.2.2.2.2.2.2.2.2.2.2.1,
    run_mem_arrs_lt hr "itg" h.2.2.2.2.2.2.2.2.2.2.2.1,
    run_mem_arrs_lt hr "ntg" h.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- **The depth's state, across a pass.** -/
theorem levelPre_congr (h : LevelPre B n cap mb ns Ws O T j M Gm C σ) (hr : Run B c σ σ' K)
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m")
    (hlw : σ'.vars "lw" = σ.vars "lw")
    (hoff : σ'.arrs "off" = σ.arrs "off") (htgt : σ'.arrs "tgt" = σ.arrs "tgt")
    (halv : σ'.arrs (alvName j) = σ.arrs (alvName j))
    (hgam : σ'.arrs (gamName j) = σ.arrs (gamName j))
    (hcol : ∀ c' < sigL cap mb j, σ'.arrs (colName j c') = σ.arrs (colName j c'))
    (hz : ∀ a ∈ (["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"] : List String),
      σ'.arrs a = σ.arrs a)
    (hmemA : σ'.arrs (memName j) = σ.arrs (memName j))
    (hmm : σ'.vars (mnumName j) = σ.vars (mnumName j)) :
    LevelPre B n cap mb ns Ws O T j M Gm C σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    Mem, mmj, hma, hmv, hme, hmB⟩ := h
  exact ⟨by rw [hn]; exact h1, by rw [hoff]; exact h2, by rw [htgt]; exact h3,
    by rw [halv]; exact h4, by rw [hgam]; exact h5,
    fun c' hc' => by rw [hcol c' hc']; exact h6 c' hc',
    h7, h8, h9, levelMem_run hr h10, h11.run hr,
    by rw [hm]; exact h12, orderMem_congr h13 hr hlw hz, h14, h15,
    Mem, mmj, by rw [hmemA]; exact hma, by rw [hmm]; exact hmv, hme, hmB⟩

variable {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}

/-- **The cover's three answers, across a pass.** -/
theorem coverHeld_congr (h : CoverHeld B n j G M π ord cap Xoff Xmem asg m σ)
    (hord : σ'.arrs (ordName j) = σ.arrs (ordName j))
    (hxoff : σ'.arrs (xofName j) = σ.arrs (xofName j))
    (hxmem : σ'.arrs (xmmName j) = σ.arrs (xmmName j))
    (hasg : σ'.arrs (asgName j) = σ.arrs (asgName j))
    (hxp : σ'.vars (xpName j) = σ.vars (xpName j)) :
    CoverHeld B n j G M π ord cap Xoff Xmem asg m σ' :=
  ⟨by rw [hord]; exact h.1, by rw [hxoff]; exact h.2.1, by rw [hxmem]; exact h.2.2.1,
    by rw [hasg]; exact h.2.2.2.1, by rw [hxp]; exact h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

variable {X W : Set (Fin n)} {Alv' Gam' : ℕ → ℕ}

/-- **The cell arithmetic of the child mask, pointwise** (wave R1.8-T1,
design §2.4). The `hcell` step inside `RamDriver.masked_step`, named: the
product the descent stores at `alvName (j + 1)` is nonzero exactly at the
alive vertices of the cluster that the batch does not delete.
`masked_step` turns this equivalence into the graph equation; the
pointwise clause of `RamDriverCluster.BatchData` is the equivalence
itself, which is why one walk of the descent exports both. -/
theorem mask_cell_ne_zero (M Xa Wa : ℕ → ℕ) (a : ℕ) :
    M a * Xa a * (1 - Wa a) ≠ 0 ↔ (M a ≠ 0 ∧ Xa a ≠ 0 ∧ Wa a = 0) := by
  constructor
  · intro h
    refine ⟨fun hc => h (by rw [hc]; ring), fun hc => h (by rw [hc]; ring), ?_⟩
    by_contra hc
    obtain ⟨t, ht⟩ : ∃ t, Wa a = t + 1 := ⟨Wa a - 1, by omega⟩
    exact h (by rw [ht, show 1 - (t + 1) = 0 by omega, Nat.mul_zero])
  · rintro ⟨h1, h2, h3⟩
    rw [h3]
    simpa using Nat.mul_ne_zero h1 h2

/-- **The descent's data, across a pass.** The pointwise mask clause
crosses every pass for free: it speaks about `Alv'`, `M`, `X` and `W`
alone and about no array of the state. -/
theorem batchData_congr (h : BatchData n j B G M X W Alv' Gam' σ)
    (hclu : σ'.arrs (cluName j) = σ.arrs (cluName j))
    (hbat : σ'.arrs (batName j) = σ.arrs (batName j))
    (hres : σ'.arrs (resName j) = σ.arrs (resName j))
    (halv : σ'.arrs (alvName (j + 1)) = σ.arrs (alvName (j + 1)))
    (hgam : σ'.arrs (gamName (j + 1)) = σ.arrs (gamName (j + 1)))
    (hmemA : σ'.arrs (memName (j + 1)) = σ.arrs (memName (j + 1)))
    (hmm : σ'.vars (mnumName (j + 1)) = σ.vars (mnumName (j + 1))) :
    BatchData n j B G M X W Alv' Gam' σ' := by
  obtain ⟨⟨Xa, hXa, hXs⟩, ⟨Wa, hWa, hWs⟩, ⟨Ra, hRa, hRm, hRB⟩, hA, hAB, hAm, hApt, hGa, hGB,
    Mem', mm', hma, hmv, hme, hmB⟩ := h
  exact ⟨⟨Xa, by rw [hclu]; exact hXa, hXs⟩, ⟨Wa, by rw [hbat]; exact hWa, hWs⟩,
    ⟨Ra, by rw [hres]; exact hRa, hRm, hRB⟩, by rw [halv]; exact hA, hAB, hAm, hApt,
    by rw [hgam]; exact hGa, hGB,
    Mem', mm', by rw [hmemA]; exact hma, by rw [hmm]; exact hmv, hme, hmB⟩

end Frames

/-! ### The batch, enumerated

`RamDriver.enumBatch` is two loops over one buffer: the first collects
the marked vertices in vertex order, the second repeats the first entry
to the fixed width `mb`. What the first loop owes is that its counter
never leaves the buffer, and that is a *counting* statement — the
entries written so far are distinct marked vertices, so there are at
most `mb` of them. `markedBelow` is the set they are, and the three
lemmas below are its arithmetic. -/

section Enum

/-- The marked vertices below a position. -/
def markedBelow (n : ℕ) (Wa : ℕ → ℕ) (z : ℕ) : Set (Fin n) :=
  {v : Fin n | (v : ℕ) < z ∧ Wa (v : ℕ) ≠ 0}

/-- What is marked below a position is marked. -/
theorem markedBelow_subset (n : ℕ) (Wa : ℕ → ℕ) (z : ℕ) :
    markedBelow n Wa z ⊆ markSet n Wa := fun _ hv => hv.2

/-- Nothing is below zero. -/
theorem ncard_markedBelow_zero (n : ℕ) (Wa : ℕ → ℕ) : (markedBelow n Wa 0).ncard = 0 := by
  have h : markedBelow n Wa 0 = ∅ := by
    ext v
    simp only [markedBelow, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    omega
  rw [h, Set.ncard_empty]

/-- Passing a marked vertex adds one. -/
theorem ncard_markedBelow_succ_of_mark {n : ℕ} {Wa : ℕ → ℕ} {z : ℕ} (hz : z < n)
    (h : Wa z ≠ 0) :
    (markedBelow n Wa (z + 1)).ncard = (markedBelow n Wa z).ncard + 1 := by
  have hins : markedBelow n Wa (z + 1) = insert (⟨z, hz⟩ : Fin n) (markedBelow n Wa z) := by
    ext v
    simp only [markedBelow, Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hv, hw⟩
      rcases Nat.lt_or_ge (v : ℕ) z with h' | h'
      · exact Or.inr ⟨h', hw⟩
      · exact Or.inl (Fin.ext (show (v : ℕ) = z by omega))
    · rintro (rfl | ⟨hv, hw⟩)
      · exact ⟨Nat.lt_succ_self z, h⟩
      · exact ⟨by omega, hw⟩
  rw [hins, Set.ncard_insert_of_notMem (by simp [markedBelow])]

/-- Passing an unmarked vertex adds nothing. -/
theorem markedBelow_succ_of_unmarked {n : ℕ} {Wa : ℕ → ℕ} {z : ℕ} (h : Wa z = 0) :
    markedBelow n Wa (z + 1) = markedBelow n Wa z := by
  ext v
  simp only [markedBelow, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hv, hw⟩
    have hne : (v : ℕ) ≠ z := fun hc => hw (by rw [hc, h])
    exact ⟨by omega, hw⟩
  · rintro ⟨hv, hw⟩
    exact ⟨by omega, hw⟩

/-- **The buffer is never overrun.** At a marked vertex the entries
written so far, together with the vertex itself, are distinct marked
vertices, so there are at most `mb` of them and the counter is inside
the buffer. -/
theorem count_lt_of_mark {n mb : ℕ} {Wa : ℕ → ℕ} {z b : ℕ} (hz : z < n) (h : Wa z ≠ 0)
    (hb : b ≤ (markedBelow n Wa z).ncard) (hcard : (markSet n Wa).ncard ≤ mb) : b < mb := by
  have hsub : insert (⟨z, hz⟩ : Fin n) (markedBelow n Wa z) ⊆ markSet n Wa := by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv'
    · exact h
    · exact hv'.2
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by simp [markedBelow])] at hle
  omega

/-- What the collecting loop has done by the position `z`: the buffer's
first `bc` cells are distinct vertices below `z` that BOTH masks mark,
and every such vertex below `z` is one of them.

**Two masks, not one** (wave R1.8-T3-flip (c2a)): the pass enumerates
the batch cut down to the cluster, so the marker is the product cell
`Wa v * Xa v` and the counting arithmetic above is read at it. -/
def CollectAt (n mb : ℕ) (Wa Xa : ℕ → ℕ) (bat clu : String) (z : ℕ) (σ : Env) : Prop :=
  σ.arrs bat = arrOf n Wa ∧ σ.arrs clu = arrOf n Xa ∧
    σ.vars "bc" ≤ (markedBelow n (fun k => Wa k * Xa k) z).ncard ∧
    ∃ E : ℕ → ℕ, σ.arrs "wa" = arrOf mb E ∧
      (∀ i, i < σ.vars "bc" → E i < z ∧ Wa (E i) * Xa (E i) ≠ 0) ∧
      (∀ v, v < z → Wa v * Xa v ≠ 0 → ∃ i, i < σ.vars "bc" ∧ E i = v)

/-- The invariant of the collecting loop: its own counter, and what it
has done by where the counter stands. -/
def CollectInv (n mb : ℕ) (Wa Xa : ℕ → ℕ) (bat clu : String) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "z" ≤ n ∧ CollectAt n mb Wa Xa bat clu (σ.vars "z") σ

/-- **One turn of the collecting loop.** A vertex both masks mark is
appended to the buffer and the counter moves on; any other is passed
over. -/
theorem collectBody_spec (B n mb : ℕ) (Wa Xa : ℕ → ℕ) (bat clu : String) (hbat : bat ≠ "wa")
    (hclu : clu ≠ "wa")
    (hB : 1 < B) (hnB : n < B) (hmbB : mb < B)
    (hcard : (markSet n (fun k => Wa k * Xa k)).ncard ≤ mb)
    (hWB : ∀ k, k < n → Wa k < B) (hX1 : ∀ k, k < n → Xa k ≤ 1) :
    Spec B (fun σ => CollectInv n mb Wa Xa bat clu σ ∧ σ.vars "z" < n)
      (.seq (.ite (.lt (.lit 0) (.mul (.get bat (.var "z")) (.get clu (.var "z"))))
              (.seq (.store "wa" (.var "bc") (.var "z"))
                (.assign "bc" (.add (.var "bc") (.lit 1))))
              .skip)
        (.assign "z" (.add (.var "z") (.lit 1))))
      (fun σ σ' => CollectInv n mb Wa Xa bat clu σ' ∧ σ'.vars "z" = σ.vars "z" + 1) 19 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hn, hzn, hbatσ, hcluσ, hbc, E, hwa, hlt, hcov⟩, hz⟩ := hσ
  have hzB : σ.vars "z" < B := by omega
  have hbcmb : σ.vars "bc" ≤ mb :=
    le_trans hbc (le_trans (Set.ncard_le_ncard (markedBelow_subset n _ _) (Set.toFinite _)) hcard)
  have hWaB : Wa (σ.vars "z") < B := hWB _ hz
  have hXa1 : Xa (σ.vars "z") ≤ 1 := hX1 _ hz
  have hprodB : Wa (σ.vars "z") * Xa (σ.vars "z") < B :=
    lt_of_le_of_lt (le_trans (Nat.mul_le_mul_left _ hXa1) (by omega)) hWaB
  have hcond : (Cond.lt (.lit 0)
      (.mul (.get bat (.var "z")) (.get clu (.var "z")))).evalB B σ =
      some (decide (0 < Wa (σ.vars "z") * Xa (σ.vars "z"))) := by
    refine evalB_condLt (evalB_lit (by omega)) (evalB_bin ?_ ?_ ?_)
    · exact evalB_get (evalB_var hzB) (by rw [hbatσ, getElem?_arrOf Wa hz]) hWaB
    · exact evalB_get (evalB_var hzB) (by rw [hcluσ, getElem?_arrOf Xa hz]) (by omega)
    · simpa only [Bop.apply_mul] using hprodB
  by_cases hm : Wa (σ.vars "z") * Xa (σ.vars "z") = 0
  · -- an unmarked vertex: the buffer is untouched
    have hz' : (σ.setVar "z" (σ.vars "z" + 1)).vars "z" = σ.vars "z" + 1 := by simp
    have hbc' : (σ.setVar "z" (σ.vars "z" + 1)).vars "bc" = σ.vars "bc" := by simp
    refine ⟨σ.setVar "z" (σ.vars "z" + 1), 13, ?_, by omega,
      ⟨by simpa using hn, by rw [hz']; omega, by simpa using hbatσ, by simpa using hcluσ, ?_, E,
        by simpa using hwa, ?_, ?_⟩, hz'⟩
    · exact (Run.ite_false (by rw [hcond, hm]; simp) Run.skip).seq
        (Run.assign (evalB_bin (evalB_var hzB) (evalB_lit (by omega)) (by simp; omega)))
    · rw [hbc', hz', markedBelow_succ_of_unmarked (Wa := fun k => Wa k * Xa k) hm]
      exact hbc
    · intro i hi
      rw [hbc'] at hi
      rw [hz']
      exact ⟨by have := (hlt i hi).1; omega, (hlt i hi).2⟩
    · intro v hv hwv
      rw [hz'] at hv
      rw [hbc']
      have hvz : v < σ.vars "z" := by
        rcases Nat.lt_or_ge v (σ.vars "z") with h' | h'
        · exact h'
        · exact absurd hwv (by rw [show v = σ.vars "z" by omega, hm]; simp)
      exact hcov v hvz hwv
  · -- a marked vertex: it is appended
    have hbclt : σ.vars "bc" < mb :=
      count_lt_of_mark (Wa := fun k => Wa k * Xa k) hz hm hbc hcard
    have hwalen : σ.vars "bc" < (σ.arrs "wa").length := by rw [hwa, length_arrOf]; exact hbclt
    set τ := ((σ.setArr "wa" (σ.vars "bc") (σ.vars "z")).setVar "bc"
      (σ.vars "bc" + 1)).setVar "z" (σ.vars "z" + 1) with hτ
    have hz' : τ.vars "z" = σ.vars "z" + 1 := by rw [hτ]; simp
    have hbc' : τ.vars "bc" = σ.vars "bc" + 1 := by rw [hτ]; simp
    have hn' : τ.vars "n" = σ.vars "n" := by rw [hτ]; simp
    have hwa' : τ.arrs "wa" = arrOf mb (upd E (σ.vars "bc") (σ.vars "z")) := by
      rw [hτ]
      simp [hwa, set_arrOf_eq_upd]
    have hbat' : τ.arrs bat = arrOf n Wa := by
      rw [hτ]
      simp only [arrs_setVar, arrs_setArr, if_neg hbat]
      exact hbatσ
    have hclu' : τ.arrs clu = arrOf n Xa := by
      rw [hτ]
      simp only [arrs_setVar, arrs_setArr, if_neg hclu]
      exact hcluσ
    refine ⟨τ, 19, ?_, le_rfl,
      ⟨by rw [hn']; exact hn, by rw [hz']; omega, hbat', hclu', ?_,
        upd E (σ.vars "bc") (σ.vars "z"), hwa', ?_, ?_⟩, hz'⟩
    · refine (Run.ite_true (by
        rw [hcond]
        simp only [Option.some.injEq, decide_eq_true_eq]
        exact Nat.pos_of_ne_zero hm)
        ((Run.store (evalB_var (by omega)) (evalB_var hzB) hwalen).seq
          (Run.assign (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
            (by simp; omega))))).seq
        (Run.assign (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
          (by simp; omega))) |>.mono (by simp)
    · rw [hbc', hz', ncard_markedBelow_succ_of_mark (Wa := fun k => Wa k * Xa k) hz hm]
      omega
    · intro i hi
      rw [hbc'] at hi
      rw [hz']
      by_cases hie : i = σ.vars "bc"
      · subst hie
        exact ⟨by rw [upd_self]; omega, by rw [upd_self]; exact hm⟩
      · rw [upd_of_ne _ hie]
        exact ⟨by have := (hlt i (by omega)).1; omega, (hlt i (by omega)).2⟩
    · intro v hv hwv
      rw [hz'] at hv
      rw [hbc']
      by_cases hve : v = σ.vars "z"
      · exact ⟨σ.vars "bc", by omega, by rw [upd_self, hve]⟩
      · obtain ⟨i, hi, hEi⟩ := hcov v (by omega) hwv
        exact ⟨i, by omega, by rw [upd_of_ne _ (by omega), hEi]⟩

/-- What the padding loop carries: every cell below the counter is a
marked vertex, the collected enumeration is still in the first `bc`
cells, and the first cell — the one being repeated — is unchanged. -/
def PadInv (n mb : ℕ) (Wa : ℕ → ℕ) (bc v0 : ℕ) (σ : Env) : Prop :=
  bc ≤ σ.vars "k" ∧ σ.vars "k" ≤ mb ∧
    ∃ E : ℕ → ℕ, σ.arrs "wa" = arrOf mb E ∧ E 0 = v0 ∧
      (∀ i, i < σ.vars "k" → E i < n ∧ Wa (E i) ≠ 0) ∧
      (∀ v, v < n → Wa v ≠ 0 → ∃ i, i < bc ∧ E i = v)

/-- **One turn of the padding loop**: the first entry is copied into the
cell the counter names. -/
theorem padBody_spec (B n mb : ℕ) (Wa : ℕ → ℕ) (bc v0 : ℕ) (hB : 1 < B) (hnB : n < B)
    (hmbB : mb < B) (hbcpos : 1 ≤ bc) :
    Spec B (fun σ => PadInv n mb Wa bc v0 σ ∧
        (Cond.lt (.var "k") (.lit mb)).evalB B σ = some true)
      (.seq (.store "wa" (.var "k") (.get "wa" (.lit 0)))
        (.assign "k" (.add (.var "k") (.lit 1))))
      (fun σ σ' => PadInv n mb Wa bc v0 σ' ∧ mb - σ'.vars "k" < mb - σ.vars "k") 8 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hkbc, hkmb, E, hwa, hE0, hlt, hcov⟩, hcond⟩ := hσ
  have hkB : σ.vars "k" < B := by omega
  have hk : σ.vars "k" < mb := by
    rw [evalB_condLt (evalB_var hkB) (evalB_lit hmbB)] at hcond
    simpa using hcond
  have hE0n : E 0 < n := (hlt 0 (by omega)).1
  have hE0B : E 0 < B := by omega
  have hget : (Expr.get "wa" (.lit 0)).evalB B σ = some (E 0) :=
    evalB_get (evalB_lit (by omega)) (by rw [hwa, getElem?_arrOf E (by omega)]) hE0B
  have hwalen : σ.vars "k" < (σ.arrs "wa").length := by rw [hwa, length_arrOf]; exact hk
  set τ := (σ.setArr "wa" (σ.vars "k") (E 0)).setVar "k" (σ.vars "k" + 1) with hτ
  have hk' : τ.vars "k" = σ.vars "k" + 1 := by rw [hτ]; simp
  have hwa' : τ.arrs "wa" = arrOf mb (upd E (σ.vars "k") (E 0)) := by
    rw [hτ]; simp [hwa, set_arrOf_eq_upd]
  refine ⟨τ, 8, ((Run.store (evalB_var hkB) hget hwalen).seq
      (Run.assign (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
        (by simp; omega)))).mono (by simp), le_rfl,
    ⟨by rw [hk']; omega, by rw [hk']; omega, upd E (σ.vars "k") (E 0), hwa', ?_, ?_, ?_⟩,
    by rw [hk']; omega⟩
  · rw [upd_of_ne _ (by omega), hE0]
  · intro i hi
    rw [hk'] at hi
    by_cases hie : i = σ.vars "k"
    · subst hie
      rw [upd_self]
      exact ⟨hE0n, (hlt 0 (by omega)).2⟩
    · rw [upd_of_ne _ hie]
      exact hlt i (by omega)
  · intro v hv hwv
    obtain ⟨i, hi, hEi⟩ := hcov v hv hwv
    exact ⟨i, hi, by rw [upd_of_ne _ (by omega), hEi]⟩

/-- **The padding pass.** `RamDriver.enumBatch` leaves in `wa` exactly
`mb` entries, every one of them a vertex both masks mark, and every such
vertex among them. -/
theorem enumBatch_spec (B n mb : ℕ) (Wa Xa : ℕ → ℕ) (bat clu : String) (hbat : bat ≠ "wa")
    (hclu : clu ≠ "wa")
    (hB : 1 < B) (hnB : n < B) (hmbB : mb < B)
    (hcard : (markSet n (fun k => Wa k * Xa k)).ncard ≤ mb)
    (hne : (markSet n (fun k => Wa k * Xa k)).Nonempty)
    (hWB : ∀ k, k < n → Wa k < B) (hX1 : ∀ k, k < n → Xa k ≤ 1) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs bat = arrOf n Wa ∧ σ.arrs clu = arrOf n Xa ∧
        (∃ g, σ.arrs "wa" = arrOf mb g))
      (enumBatch bat clu mb)
      (fun _ σ' => ∃ E : ℕ → ℕ, σ'.arrs "wa" = arrOf mb E ∧
        (∀ i, i < mb → E i < n ∧ Wa (E i) * Xa (E i) ≠ 0) ∧
        (∀ v, v < n → Wa v * Xa v ≠ 0 → ∃ i, i < mb ∧ E i = v))
      (23 * n + 12 * mb + 30) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hbatσ, hcluσ, gwa, hwa⟩ := hσ
  -- the two counters, zeroed
  have hr₁ : Run B (.assign "bc" (.lit 0)) σ (σ.setVar "bc" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hr₂ : Run B (.assign "z" (.lit 0)) (σ.setVar "bc" 0)
      ((σ.setVar "bc" 0).setVar "z" 0) 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₂ := (σ.setVar "bc" 0).setVar "z" 0 with hσ₂
  have hz₂ : σ₂.vars "z" = 0 := by rw [hσ₂]; simp
  have hbc₂ : σ₂.vars "bc" = 0 := by rw [hσ₂]; simp
  have hI₂ : CollectInv n mb Wa Xa bat clu σ₂ := by
    refine ⟨by rw [hσ₂]; simpa using hn, by rw [hz₂]; omega,
      by rw [hσ₂]; simpa using hbatσ, by rw [hσ₂]; simpa using hcluσ, ?_, gwa,
      by rw [hσ₂]; simpa using hwa, ?_, ?_⟩
    · rw [hbc₂, hz₂, ncard_markedBelow_zero]
    · intro i hi; rw [hbc₂] at hi; omega
    · intro v hv hwv; rw [hz₂] at hv; omega
  -- the collecting loop
  obtain ⟨σ₃, hr₃, hI₃, hz₃⟩ :=
    (Spec.forRange (B := B) (P := CollectInv n mb Wa Xa bat clu) "z" "n"
      (CollectInv n mb Wa Xa bat clu) n 19 (23 * n + 4)
      (fun τ hτ => by have := hτ.2.1; omega) (fun τ hτ => by rw [hτ.1]; exact hnB)
      (fun τ hτ => hτ.1) (fun τ hτ => hτ.2.1)
      (collectBody_spec B n mb Wa Xa bat clu hbat hclu hB hnB hmbB hcard hWB hX1)
      (fun _ hτ => hτ)
      (fun τ _ => by
        have : (19 + 4) * (n - τ.vars "z") ≤ 23 * n := by
          have := Nat.mul_le_mul_left 23 (Nat.sub_le n (τ.vars "z"))
          omega
        omega)).run hI₂
  obtain ⟨hn₃, -, hbat₃, hclu₃, hbc₃, E₃, hwa₃, hlt₃, hcov₃⟩ := hI₃
  rw [hz₃] at hbc₃ hlt₃ hcov₃
  -- the batch's cluster half is not empty, so the buffer's first cell is one of it
  obtain ⟨v, hv⟩ := hne
  obtain ⟨i₀, hi₀, -⟩ := hcov₃ (v : ℕ) v.isLt hv
  have hbcpos : 1 ≤ σ₃.vars "bc" := by omega
  have hbcmb : σ₃.vars "bc" ≤ mb :=
    le_trans hbc₃ (le_trans (Set.ncard_le_ncard (markedBelow_subset n _ n) (Set.toFinite _)) hcard)
  -- k := bc
  have hr₄ : Run B (.assign "k" (.var "bc")) σ₃ (σ₃.setVar "k" (σ₃.vars "bc")) 2 :=
    (Run.assign (evalB_var (by omega))).mono (by simp)
  set σ₄ := σ₃.setVar "k" (σ₃.vars "bc") with hσ₄
  have hk₄ : σ₄.vars "k" = σ₃.vars "bc" := by rw [hσ₄]; simp
  have hI₄ : PadInv n mb (fun k => Wa k * Xa k) (σ₃.vars "bc") (E₃ 0) σ₄ := by
    refine ⟨by rw [hk₄], by rw [hk₄]; exact hbcmb, E₃, by rw [hσ₄]; simpa using hwa₃, rfl, ?_, ?_⟩
    · intro i hi
      rw [hk₄] at hi
      exact hlt₃ i hi
    · exact hcov₃
  -- the padding loop
  obtain ⟨σ₅, hr₅, hI₅, hfalse⟩ :=
    (Spec.while_count (B := B)
      (P := PadInv n mb (fun k => Wa k * Xa k) (σ₃.vars "bc") (E₃ 0)) (K := 12 * mb + 4)
      (PadInv n mb (fun k => Wa k * Xa k) (σ₃.vars "bc") (E₃ 0)) (fun τ => mb - τ.vars "k") 8
      (fun τ hτ => evalB_condLt_var_lit (by have := hτ.2.1; omega) hmbB)
      (padBody_spec B n mb (fun k => Wa k * Xa k) (σ₃.vars "bc") (E₃ 0) hB hnB hmbB hbcpos)
      (fun _ hτ => hτ)
      (fun τ _ => by
        have : (1 + 3 + 8) * (mb - τ.vars "k") ≤ 12 * mb := by
          have := Nat.mul_le_mul_left 12 (Nat.sub_le mb (τ.vars "k"))
          omega
        simp only [size_condLt, size_var, size_lit]
        omega)).run hI₄
  obtain ⟨-, hkmb₅, E₅, hwa₅, -, hlt₅, hcov₅⟩ := hI₅
  have hk₅ : σ₅.vars "k" = mb := by
    have hkB : σ₅.vars "k" < B := by omega
    rw [evalB_condLt (evalB_var hkB) (evalB_lit hmbB)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hk₅] at hlt₅
  exact ⟨σ₅, _, hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅))), by omega,
    E₅, hwa₅, hlt₅, fun v hv hwv => by
      obtain ⟨i, hi, hEi⟩ := hcov₅ v hv hwv
      exact ⟨i, by omega, hEi⟩⟩

/-! ### The obligation

`RamDriverCluster.EnumStep` is the padding pass at the surface the
cluster step consumes it at. Its precondition is missing one clause —
that the batch indicator holds *words* — without which the pass's very
first read, `bat[z]`, has no value in the bounded semantics and the
`Spec` is not provable at all: `RamDriverCluster.BatchData` pins what
the array marks (`markSet n Wa = W`) and never what its cells are. The
clause is `MaskWords B (batName j)`, it is what the descent that writes
the array leaves behind, and it survives every pass by
`MaskWords.run`; `EnumStepW` is the obligation with it, and
`enumStep_of_maskWords` turns the one into the other. -/

/-- `RamDriverCluster.EnumStep`, with the word clause its precondition
owes. -/
def EnumStepW (B cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      BatchData n j B G M X W Alv' Gam' σ ∧ PlayRec B cap G (j + 1) Alv' Gam' σ ∧
      (W ∩ X).Nonempty ∧ W.ncard ≤ mb ∧ (∃ g, σ.arrs "wa" = arrOf mb g) ∧
      MaskWords B (batName j) σ)
    (enumBatch (batName j) (cluName j) mb)
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∃ w : Fin mb → Fin n, ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
        ClusterWa mb w σ') K

/-! The three frame readings of the pass, on its syntax. -/

theorem not_mem_wvars_enumBatch {bat clu y : String} {mb : ℕ} (h1 : y ≠ "bc") (h2 : y ≠ "z")
    (h3 : y ≠ "k") : y ∉ (enumBatch bat clu mb).wvars := by
  simp [enumBatch, Com.wvars, h1, h2, h3]

theorem not_mem_warrs_enumBatch {bat clu a : String} {mb : ℕ} (h : a ≠ "wa") :
    a ∉ (enumBatch bat clu mb).warrs := by simp [enumBatch, Com.warrs, h]

theorem noWrite_enumBatch (bat clu : String) (mb : ℕ) : (enumBatch bat clu mb).NoWrite := by
  simp [enumBatch, Com.NoWrite]

/-- **The padding, discharged.** -/
theorem enumStepW {B cap mb ns Ws j K : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)} {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    {X W : Set (Fin n)} {Alv' Gam' : ℕ → ℕ}
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hK : 23 * n + 12 * mb + 30 ≤ K) :
    EnumStepW B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m X W Alv' Gam' K := by
  have hmbB : mb < B := hB.mb_lt
  intro σ hσ
  obtain ⟨⟨hlev, hplayrec, hheld⟩, hbat, hplay', hne, hcard, ⟨gwa, hwa⟩, hmw⟩ := hσ
  obtain ⟨Xa, hXaarr, hXs, hXa1⟩ := hbat.1
  obtain ⟨Wa, hWaarr, hWs, -⟩ := hbat.2.1
  have hbatwa : batName j ≠ "wa" := by simp [batName, String.ext_iff]
  have hcluwa : cluName j ≠ "wa" := by simp [cluName, String.ext_iff]
  -- the product cell marks exactly the batch's cluster half
  have hprod : markSet n (fun k => Wa k * Xa k) = W ∩ X := by
    ext v
    show Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 ↔ _
    rw [← hWs, ← hXs]
    exact ⟨fun h => ⟨fun hc => h (by rw [hc]; ring), fun hc => h (by rw [hc]; ring)⟩,
      fun h => Nat.mul_ne_zero h.1 h.2⟩
  obtain ⟨σ', hr, ⟨E, hwa', hltE, hcovE⟩, hfv, hfa, -, hout⟩ :=
    ((enumBatch_spec B n mb Wa Xa (batName j) (cluName j) hbatwa hcluwa hB.one_lt hB.n_lt hmbB
      (by rw [hprod]; exact le_trans (Set.ncard_le_ncard Set.inter_subset_left
        (Set.toFinite _)) hcard)
      (by rw [hprod]; exact hne)
      (fun k hk => hmw.get hWaarr hk) hXa1).frame).run ⟨hlev.1, hWaarr, hXaarr, gwa, hwa⟩
  have hav : ∀ a : String, a ≠ "wa" → σ'.arrs a = σ.arrs a :=
    fun a ha => hfa a (not_mem_warrs_enumBatch ha)
  have hvv : ∀ y : String, y ≠ "bc" → y ≠ "z" → y ≠ "k" → σ'.vars y = σ.vars y :=
    fun y h1 h2 h3 => hfv y (not_mem_wvars_enumBatch h1 h2 h3)
  -- the enumeration the buffer holds
  refine ⟨σ', hr.mono (by omega), ⟨levelPre_congr hlev hr (hvv "n" (by decide) (by decide)
      (by decide)) (hvv "m" (by decide) (by decide) (by decide))
      (hvv "lw" (by decide) (by decide) (by decide)) (hav "off" (by decide))
      (hav "tgt" (by decide)) (hav _ (by simp [alvName, String.ext_iff]))
      (hav _ (by simp [gamName, String.ext_iff]))
      (fun c' _ => hav _ (by simp [colName, String.ext_iff]))
      (fun a ha => hav a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      (hav _ (by simp [memName, String.ext_iff]))
      (hvv _ (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff])),
    hplayrec.congr
      (fun a _ => hvv (ctrName a) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => hav (resName a) (by simp [resName, String.ext_iff]))
      (fun a _ => hav (gamName a) (by simp [gamName, String.ext_iff]))
      (fun a _ => hav (parName a) (by simp [parName, balName, String.ext_iff])),
    coverHeld_congr hheld (hav _ (by simp [ordName, String.ext_iff]))
      (hav _ (by simp [xofName, String.ext_iff]))
      (hav _ (by simp [xmmName, String.ext_iff]))
      (hav _ (by simp [asgName, String.ext_iff]))
      (hvv _ (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff])
        (by simp [xpName, String.ext_iff]))⟩,
    hplay'.congr
      (fun a _ => hvv (ctrName a) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => hav (resName a) (by simp [resName, String.ext_iff]))
      (fun a _ => hav (gamName a) (by simp [gamName, String.ext_iff]))
      (fun a _ => hav (parName a) (by simp [parName, balName, String.ext_iff])),
    hout (noWrite_enumBatch _ _ _),
    hvv _ (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
      (by simp [curName, String.ext_iff]),
    fun i => ⟨E (i : ℕ), (hltE (i : ℕ) i.isLt).1⟩, ⟨?_, ?_⟩, ?_⟩
  · exact batchData_congr hbat (hav _ (by simp [cluName, String.ext_iff])) (hav _ hbatwa)
      (hav _ (by simp [resName, String.ext_iff])) (hav _ (by simp [alvName, String.ext_iff]))
      (hav _ (by simp [gamName, String.ext_iff]))
      (hav _ (by simp [memName, String.ext_iff]))
      (hvv _ (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]))
  · -- the range of the padded enumeration is the batch's cluster half
    apply Set.eq_of_subset_of_subset
    · rintro v ⟨i, rfl⟩
      rw [← hprod]
      exact (hltE (i : ℕ) i.isLt).2
    · intro v hv
      rw [← hprod] at hv
      obtain ⟨i, hi, hEi⟩ := hcovE (v : ℕ) v.isLt hv
      exact ⟨⟨i, hi⟩, Fin.ext hEi⟩
  · rw [ClusterWa, hwa']
    exact arrOf_congr (fun i hi => by rw [dif_pos hi])

/-- **The obligation itself, discharged.** The clause the surface used
to owe is now a conjunct of `RamDriverCluster.BatchData` — `∀ k < n,
Wa k < B` at the batch indicator — and `MaskWords` reads it off the
array `BatchData` names, so nothing is left over. -/
theorem enumStep {B cap mb ns Ws j K : ℕ} {G : SimpleGraph (Fin n)}
        {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)} {Alv' Gam' : ℕ → ℕ}
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hK : 23 * n + 12 * mb + 30 ≤ K) :
    EnumStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m X W Alv' Gam' K :=
  (enumStepW hB hK).pre (fun _ hσ => by
    obtain ⟨hturn, hbat, hplay, hne, hcard, hwa⟩ := hσ
    obtain ⟨Wa, hWaarr, -, hWaB⟩ := hbat.2.1
    refine ⟨hturn, hbat, hplay, hne, hcard, hwa, fun v hv => ?_⟩
    rw [hWaarr] at hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
    exact hWaB k (List.mem_range.1 hk))

end Enum

/-! ### One step of neighbourhood expansion, walked

`RamDriver.expandCom` is the pass the three slot families in the
colouring are built from, and it is the one pass of the driver with a loop inside
a loop. `RamDriverCluster` carries its mathematics and both of its
invariants; what is walked here is the symbolic execution between them:
the inner scan against `Csr.rowScan_spec` with `ScanHit`, the outer pass
against `Refine.SigmaLoop.forRangeZeroSum` with `ExpandInv`, and
`hit_eq_expandVal` at
the join. -/

section Expand

variable {ns nt w p₀ e z c : ℕ} {G : SimpleGraph (Fin n)}
  {O T Msk Src A₀ Idx Xoff Xmem : ℕ → ℕ} {msk src dst idx : String} {σ : Env}

/-! The carrier pass below packages its destination as `Fill.Below`,
which deliberately ties the next row to the carrier counter.  A block
walk visits arbitrary vertices, so its one-row engine needs the same
read-only context with the destination frozen at an arbitrary entry
function instead.  `ExpandAt` and `ScanHitAt` are that separation; no
program text changes at the row boundary. -/

/-- The read-only expansion context at one arbitrary row, together
with the destination before that row is written. -/
def ExpandAt (n ns nt : ℕ) (O T Msk Src A₀ : ℕ → ℕ)
    (msk src dst : String) (z : ℕ) (σ : Env) : Prop :=
  σ.vars "z" = z ∧ σ.vars "n" = n ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
    σ.arrs msk = arrOf n Msk ∧ σ.arrs src = arrOf n Src ∧ σ.arrs dst = arrOf n A₀

open Classical in
/-- The inner CSR scan at an arbitrary outer row. -/
def ScanHitAt (n ns nt : ℕ)
    (O T Msk Src A₀ : ℕ → ℕ) (msk src dst : String) (z : ℕ) (σ : Env) : Prop :=
  ExpandAt n ns nt O T Msk Src A₀ msk src dst z σ ∧
    σ.vars "jend" = O (z + 1) ∧ O z ≤ σ.vars "j" ∧ σ.vars "j" ≤ O (z + 1) ∧
    σ.vars "hit" =
      (if ∃ p, O z ≤ p ∧ p < σ.vars "j" ∧ Msk (T p) ≠ 0 ∧ Src (T p) ≠ 0 then 1 else Src z)

/-- The graph CSR relation read out of an arbitrary-row state. -/
theorem csr_of_expandAt {σ : Env} (hcsr : CsrGraph G ns O T)
    (h : ExpandAt n ns nt O T Msk Src A₀ msk src dst z σ) :
    CsrWide.CsrW "off" "tgt" n ns nt n O T σ :=
  ⟨h.2.2.1, h.2.2.2.1, fun i hi => hcsr.mono i hi, hcsr.last, h.2.2.2.2.1,
    fun p hp => hcsr.target_lt p hp⟩

/-- Scalar-only scan work leaves an arbitrary-row state intact. -/
theorem expandAt_congr {σ σ' : Env}
    (h : ExpandAt n ns nt O T Msk Src A₀ msk src dst z σ)
    (hz : σ'.vars "z" = σ.vars "z") (hn : σ'.vars "n" = σ.vars "n")
    (ha : ∀ a : String, σ'.arrs a = σ.arrs a) :
    ExpandAt n ns nt O T Msk Src A₀ msk src dst z σ' :=
  ⟨by rw [hz]; exact h.1, by rw [hn]; exact h.2.1,
    by rw [ha]; exact h.2.2.1, by rw [ha]; exact h.2.2.2.1, h.2.2.2.2.1,
    by rw [ha]; exact h.2.2.2.2.2.1, by rw [ha]; exact h.2.2.2.2.2.2.1,
    by rw [ha]; exact h.2.2.2.2.2.2.2⟩

/-- **One slot of an arbitrary row.**  This is `expandSlot_step` with
the carrier-prefix component removed; the program and the cost are
identical. -/
theorem expandSlotAt_step {B z : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B)
    (hnB : n < B) (hnsB : ns < B) (hMB : ∀ k, k < n → Msk k < B)
    (hSB : ∀ k, k < n → Src k < B) (hzn : z < n) (σ : Env)
    (hI : ScanHitAt n ns nt O T Msk Src A₀ msk src dst z σ)
    (hj : σ.vars "j" < O (z + 1)) :
    ∃ σ' K', Run B (expandSlot msk src) σ σ' K' ∧
      ScanHitAt n ns nt O T Msk Src A₀ msk src dst z σ' ∧
      σ'.vars "j" = σ.vars "j" + 1 ∧ K' ≤ 20 := by
  classical
  obtain ⟨hinv, hjend, hjlo, -, hhit⟩ := hI
  have hcsrRel := csr_of_expandAt hcsr hinv
  have hjns : σ.vars "j" < ns := lt_of_lt_of_le hj (hcsrRel.row_le hzn)
  have hjB : σ.vars "j" < B := by omega
  have hTn : T (σ.vars "j") < n := hcsr.target_lt _ hjns
  have hslot : (Expr.get "tgt" (.var "j")).evalB B σ = some (T (σ.vars "j")) :=
    evalB_get (evalB_var hjB)
      (by rw [hinv.2.2.2.1, getElem?_arrOf T (lt_of_lt_of_le hjns hinv.2.2.2.2.1)])
      (by omega)
  set τ := σ.setVar "w" (T (σ.vars "j")) with hτ
  have hrw : Run B (.assign "w" (.get "tgt" (.var "j"))) σ τ 3 :=
    (Run.assign hslot).mono (by simp)
  have hwv : τ.vars "w" = T (σ.vars "j") := by rw [hτ]; simp
  have hcmsk : (Cond.lt (.lit 0) (.get msk (.var "w"))).evalB B τ =
      some (decide (0 < Msk (T (σ.vars "j")))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hwv]; omega))
        (by rw [hτ, arrs_setVar, hinv.2.2.2.2.2.1, hwv,
          getElem?_arrOf Msk hTn]) (hMB _ hTn))
  have hcsrc : (Cond.lt (.lit 0) (.get src (.var "w"))).evalB B τ =
      some (decide (0 < Src (T (σ.vars "j")))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hwv]; omega))
        (by rw [hτ, arrs_setVar, hinv.2.2.2.2.2.2.1, hwv,
          getElem?_arrOf Src hTn]) (hSB _ hTn))
  by_cases hm : Msk (T (σ.vars "j")) = 0
  · refine ⟨τ.setVar "j" (σ.vars "j" + 1), 20,
      (hrw.seq ((Run.ite_false (by rw [hcmsk, hm]; simp) Run.skip).seq
        (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
          (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
    refine ⟨expandAt_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp)
        (fun a => by rw [hτ]; simp),
      by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega, by rw [hτ]; simp; omega, ?_⟩
    rw [show (τ.setVar "j" (σ.vars "j" + 1)).vars "hit" = σ.vars "hit" by rw [hτ]; simp,
      show (τ.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by rw [hτ]; simp,
      hhit]
    congr 1
    refine propext ⟨fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, by omega, h₃, h₄⟩,
      fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, ?_, h₃, h₄⟩⟩
    rcases Nat.lt_or_ge p (σ.vars "j") with h' | h'
    · exact h'
    · exact absurd h₃ (by rw [show p = σ.vars "j" by omega, hm]; simp)
  · by_cases hs : Src (T (σ.vars "j")) = 0
    · refine ⟨τ.setVar "j" (σ.vars "j" + 1), 20,
        (hrw.seq ((Run.ite_true (by rw [hcmsk]; simp; omega)
          (Run.ite_false (by rw [hcsrc, hs]; simp) Run.skip)).seq
          (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
            (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
      refine ⟨expandAt_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp)
          (fun a => by rw [hτ]; simp),
        by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega, by rw [hτ]; simp; omega, ?_⟩
      rw [show (τ.setVar "j" (σ.vars "j" + 1)).vars "hit" = σ.vars "hit" by rw [hτ]; simp,
        show (τ.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by rw [hτ]; simp,
        hhit]
      congr 1
      refine propext ⟨fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, by omega, h₃, h₄⟩,
        fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, ?_, h₃, h₄⟩⟩
      rcases Nat.lt_or_ge p (σ.vars "j") with h' | h'
      · exact h'
      · exact absurd h₄ (by rw [show p = σ.vars "j" by omega, hs]; simp)
    · refine ⟨(τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1), 20,
        (hrw.seq ((Run.ite_true (by rw [hcmsk]; simp; omega)
          (Run.ite_true (by rw [hcsrc]; simp; omega)
            (Run.assign (evalB_lit (by omega))))).seq
          (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
            (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
      refine ⟨expandAt_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp)
          (fun a => by rw [hτ]; simp),
        by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega, by rw [hτ]; simp; omega, ?_⟩
      rw [show ((τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1)).vars "hit" = 1 by
          rw [hτ]; simp,
        show ((τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1)).vars "j" =
            σ.vars "j" + 1 by rw [hτ]; simp]
      rw [if_pos ⟨σ.vars "j", hjlo, by omega, hm, hs⟩]

/-- **One arbitrary vertex of an expansion.**  Unlike
`expandStep_spec`, this statement does not require the destination to
be a carrier prefix.  It exposes the single store as an `upd`, which is
the form a block walk can accumulate in an arbitrary visitation order. -/
theorem expandStepAt_spec {B z : ℕ} (hcsr : CsrGraph G ns O T) (hz : z < n)
    (hB : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdm : dst ≠ msk) (hds : dst ≠ src) (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B (ExpandAt n ns nt O T Msk Src A₀ msk src dst z)
      (expandStep msk src dst)
      (fun _ σ' => ExpandAt n ns nt O T Msk Src
        (upd A₀ z (expandVal G Msk Src z)) msk src dst (z + 1) σ')
      (24 * Csr.rowLen O z + 40) := by
  classical
  refine Spec.of_exists (fun σ hinv => ?_)
  have hzσ : σ.vars "z" = z := hinv.1
  have hzB : σ.vars "z" < B := by omega
  have hSz : Src (σ.vars "z") < B := hSB _ (by omega)
  have hr₁ : Run B (.assign "hit" (.get src (.var "z"))) σ
      (σ.setVar "hit" (Src (σ.vars "z"))) 3 :=
    (Run.assign (evalB_get (evalB_var hzB)
      (by rw [hinv.2.2.2.2.2.2.1, getElem?_arrOf Src (by omega)]) hSz)).mono (by simp)
  set σ₁ := σ.setVar "hit" (Src (σ.vars "z")) with hσ₁
  have hz₁ : σ₁.vars "z" = σ.vars "z" := by rw [hσ₁]; simp
  have hhit₁ : σ₁.vars "hit" = Src (σ.vars "z") := by rw [hσ₁]; simp
  have hinv₁ : ExpandAt n ns nt O T Msk Src A₀ msk src dst z σ₁ :=
    expandAt_congr hinv hz₁ (by rw [hσ₁]; simp) (fun a => by rw [hσ₁]; simp)
  have hcond : (Cond.lt (.lit 0) (.get msk (.var "z"))).evalB B σ₁ =
      some (decide (0 < Msk (σ.vars "z"))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hz₁]; omega))
        (by rw [hinv₁.2.2.2.2.2.1, hz₁, getElem?_arrOf Msk (by omega)])
        (hMB _ (by omega)))
  have key : ∃ σ₂ K₂, Run B (.ite (.lt (.lit 0) (.get msk (.var "z")))
        (.seq (Csr.loadRow "off" "z" "j" "jend") (Csr.scan "j" "jend" (expandSlot msk src)))
        .skip) σ₁ σ₂ K₂ ∧ K₂ ≤ 24 * Csr.rowLen O z + 17 ∧
      ExpandAt n ns nt O T Msk Src A₀ msk src dst z σ₂ ∧
      σ₂.vars "z" = σ.vars "z" ∧ σ₂.vars "hit" = expandVal G Msk Src (σ.vars "z") := by
    by_cases hm : Msk (σ.vars "z") = 0
    · exact ⟨σ₁, 6, Run.ite_false (by rw [hcond, hm]; simp) Run.skip, by omega, hinv₁, hz₁,
        by rw [hhit₁, expandVal_of_dead hm]⟩
    · obtain ⟨σ₂, hr₂, hcsr₂, hj₂, hjend₂, hst₂⟩ :=
        (CsrWide.loadRow_spec B n ns nt n "off" "tgt" "z" "j" "jend" O T
            (by decide) (by decide)).run
          (σ := σ₁) ⟨⟨csr_of_expandAt hcsr hinv₁, by omega, hnsB⟩,
            by rw [hz₁, hzσ]; exact hz, by rw [hz₁, hzσ]; omega⟩
      rw [hz₁] at hj₂ hjend₂
      have hzz : σ₂.vars "z" = σ.vars "z" := by rw [hst₂]; simp [hz₁]
      have hhit₂ : σ₂.vars "hit" = Src (σ.vars "z") := by rw [hst₂]; simp [hhit₁]
      have hinv₂ : ExpandAt n ns nt O T Msk Src A₀ msk src dst z σ₂ :=
        expandAt_congr hinv₁ (by rw [hst₂]; simp) (by rw [hst₂]; simp)
          (fun a => by rw [hst₂]; simp)
      have hrow : O (σ.vars "z" + 1) ≤ ns :=
        (csr_of_expandAt hcsr hinv).row_le (by omega)
      have hlo : O (σ.vars "z") ≤ O (σ.vars "z" + 1) := hcsr.mono _ (by omega)
      have hclause : σ₂.vars "hit" =
          (if ∃ p, O (σ.vars "z") ≤ p ∧ p < σ₂.vars "j" ∧ Msk (T p) ≠ 0 ∧ Src (T p) ≠ 0
            then 1 else Src (σ.vars "z")) := by
        rw [hhit₂, if_neg]
        rintro ⟨p, h₁, h₂, -⟩
        rw [hj₂] at h₂
        omega
      have hI₂ : ScanHitAt n ns nt O T Msk Src A₀ msk src dst (σ.vars "z") σ₂ :=
        ⟨by simpa [hzσ] using hinv₂, hjend₂, by omega, by omega, hclause⟩
      obtain ⟨σ₃, hr₃, hI₃, hj₃⟩ :=
        (Csr.rowScan_spec B (24 * Csr.rowLen O z + 4) (O (σ.vars "z" + 1)) 20 "j" "jend"
          (expandSlot msk src)
          (P := ScanHitAt n ns nt O T Msk Src A₀ msk src dst (σ.vars "z"))
          (ScanHitAt n ns nt O T Msk Src A₀ msk src dst (σ.vars "z")) (by omega)
          (fun ρ hρ => ⟨hρ.2.1, hρ.2.2.2.1⟩)
          (fun ρ hρ hjlt => expandSlotAt_step hcsr hB hnB hnsB hMB hSB
            (by omega) ρ hρ hjlt)
          (fun _ hρ => hρ)
          (fun ρ hρ => by
            have hloρ : O z ≤ ρ.vars "j" := by
              simpa [hzσ] using hρ.2.2.1
            have hrem : O (σ.vars "z" + 1) - ρ.vars "j" ≤ Csr.rowLen O z := by
              change O (σ.vars "z" + 1) - ρ.vars "j" ≤ O (z + 1) - O z
              rw [hzσ]
              exact Nat.sub_le_sub_left hloρ _
            have h1 : (20 + 4) * (O (σ.vars "z" + 1) - ρ.vars "j") ≤
                24 * Csr.rowLen O z := Nat.mul_le_mul_left 24 hrem
            omega)).run hI₂
      refine ⟨σ₃, 1 + 4 + (8 + (24 * Csr.rowLen O z + 4)),
        Run.ite_true (by rw [hcond]; simp; omega) (hr₂.seq hr₃), by omega,
        by simpa [hzσ] using hI₃.1, hI₃.1.1, ?_⟩
      rw [hI₃.2.2.2.2, hj₃, hit_eq_expandVal hcsr (by omega) hm]
  obtain ⟨σ₂, K₂, hr₂, hK₂, hinv₂, hzz, hhit₂⟩ := key
  obtain ⟨hz₂, hn₂, hoff₂, htgt₂, hnt₂, hmsk₂, hsrc₂, hdst₂⟩ := hinv₂
  have hval : expandVal G Msk Src (σ.vars "z") < B := by
    rcases expandVal_eq_or G Msk Src (σ.vars "z") with h | h
    · rw [h]; omega
    · rw [h]; exact hSz
  have hdlen : σ₂.vars "z" < (σ₂.arrs dst).length := by
    rw [hdst₂, length_arrOf, hzz, hzσ]
    exact hz
  refine ⟨(σ₂.setArr dst (σ₂.vars "z") (σ₂.vars "hit")).setVar "z" (σ₂.vars "z" + 1),
    3 + (K₂ + (3 + 4)), (hr₁.seq (hr₂.seq
      ((Run.store (evalB_var (by rw [hzz, hzσ]; omega))
        (evalB_var (by rw [hhit₂]; exact hval)) hdlen).seq
        (Run.assign (evalB_bin (evalB_var (by simp [hzz, hzσ]; omega))
          (evalB_lit (by omega)) (by simp [hzz, hzσ]; omega)))))), by omega, ?_⟩
  refine ⟨by simp [hzz, hzσ], ?_, ?_, ?_, hnt₂, ?_, ?_, ?_⟩
  · simp only [vars_setVar, if_neg (by decide : ¬ ("n" = "z")), vars_setArr]
    exact hn₂
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdo)]; exact hoff₂
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdt)]; exact htgt₂
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdm)]; exact hmsk₂
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hds)]; exact hsrc₂
  · rw [arrs_setVar, arrs_setArr, if_pos rfl, hdst₂, set_arrOf_eq_upd,
      hzz, hhit₂, hzσ]

/-! #### The block outer loop -/

/-- The row mass of the members in slots `[a,b)`.  At the cover arrays
and a block's two offsets this is definitionally
`MassWeight.blockRowSum`. -/
def expandRowSum (O Idx : ℕ → ℕ) (a b : ℕ) : ℕ :=
  ∑ q ∈ Finset.Ico a b, Csr.rowLen O (Idx q)

@[simp] theorem expandRowSum_self (O Idx : ℕ → ℕ) (a : ℕ) :
    expandRowSum O Idx a a = 0 := by simp [expandRowSum]

theorem expandRowSum_succ_bot (O Idx : ℕ → ℕ) {a b : ℕ} (h : a < b) :
    expandRowSum O Idx a b = Csr.rowLen O (Idx a) + expandRowSum O Idx (a + 1) b := by
  rw [expandRowSum, expandRowSum, Finset.sum_eq_sum_Ico_succ_bot h]

theorem expandRowSum_mono_left (O Idx : ℕ → ℕ) {a a' b : ℕ} (h : a ≤ a') :
    expandRowSum O Idx a' b ≤ expandRowSum O Idx a b := by
  simp only [expandRowSum]
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico h le_rfl)

/-- The invariant of the executable block expansion.  It records both
halves of the sparse-write contract: every member already visited has
the expansion value, and every cell not visited still has its entry
value.  Repeated members are harmless because every visit writes the
same pointwise value. -/
def ExpandBlockInv (n ns nt w p₀ e : ℕ) (G : SimpleGraph (Fin n))
    (O T Idx Msk Src A₀ : ℕ → ℕ) (idx msk src dst : String) (σ : Env) : Prop :=
  σ.vars "pend" = e ∧ p₀ ≤ σ.vars "p" ∧ σ.vars "p" ≤ e ∧ σ.vars "n" = n ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
    σ.arrs msk = arrOf n Msk ∧ σ.arrs src = arrOf n Src ∧
    σ.arrs idx = arrOf w Idx ∧
    ∃ A, σ.arrs dst = arrOf n A ∧
      (∀ q, p₀ ≤ q → q < σ.vars "p" → A (Idx q) = expandVal G Msk Src (Idx q)) ∧
      (∀ v, v < n → (∀ q, p₀ ≤ q → q < σ.vars "p" → Idx q ≠ v) → A v = A₀ v)

/-- Read the sparse-write contract at loop exit. -/
theorem ExpandBlockInv.done
    (h : ExpandBlockInv n ns nt w p₀ e G O T Idx Msk Src A₀ idx msk src dst σ)
    (hp : σ.vars "p" = e) :
    ∃ A, σ.arrs dst = arrOf n A ∧
      (∀ q, p₀ ≤ q → q < e → A (Idx q) = expandVal G Msk Src (Idx q)) ∧
      (∀ v, v < n → (∀ q, p₀ ≤ q → q < e → Idx q ≠ v) → A v = A₀ v) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, A, hA, hset, hkeep⟩ := h
  exact ⟨A, hA, fun q hq hq' => hset q hq (by rw [hp]; exact hq'),
    fun v hv hn => hkeep v hv (fun q hq hq' => hn q hq (by rw [← hp]; exact hq'))⟩

/-- A cell function is supported by the slots of one block when every
carrier cell not named by the block is zero.  This is the sparse analogue
of the carrier-wide zero fill used by `expandCom`: a block expansion may
leave unvisited cells alone precisely because those cells already contain
zero. -/
def BlockSupported (n p₀ e : ℕ) (Idx F : ℕ → ℕ) : Prop :=
  ∀ v, v < n → (∀ q, p₀ ≤ q → q < e → Idx q ≠ v) → F v = 0

@[simp] theorem blockSupported_zero (n p₀ e : ℕ) (Idx : ℕ → ℕ) :
    BlockSupported n p₀ e Idx (fun _ => 0) := by
  intro _ _ _
  rfl

/-- A sparse block write agrees with its intended whole-carrier value
whenever both the entry array and that intended value vanish off the
block.  This is the common join used by the flat cover maps and by the
expansion engine below. -/
theorem sparseBlock_eq_of_supported
    {n p₀ e : ℕ} {Idx A A₀ F : ℕ → ℕ}
    (hset : ∀ q, p₀ ≤ q → q < e → A (Idx q) = F (Idx q))
    (hkeep : ∀ v, v < n → (∀ q, p₀ ≤ q → q < e → Idx q ≠ v) → A v = A₀ v)
    (hA₀ : BlockSupported n p₀ e Idx A₀)
    (hF : BlockSupported n p₀ e Idx F) :
    (∀ v, v < n → A v = F v) ∧ BlockSupported n p₀ e Idx A := by
  have hval : ∀ v, v < n → A v = F v := by
    intro v hv
    by_cases hin : ∃ q, p₀ ≤ q ∧ q < e ∧ Idx q = v
    · obtain ⟨q, hq₀, hqe, hqv⟩ := hin
      rw [← hqv]
      exact hset q hq₀ hqe
    · have hout : ∀ q, p₀ ≤ q → q < e → Idx q ≠ v := by
        intro q hq₀ hqe hqv
        exact hin ⟨q, hq₀, hqe, hqv⟩
      rw [hkeep v hv hout, hA₀ v hv hout, hF v hv hout]
  exact ⟨hval, fun v hv hout => by rw [hval v hv]; exact hF v hv hout⟩

/-- A product is supported as soon as its left factor is. -/
theorem blockSupported_mul_left
    {n p₀ e : ℕ} {Idx A C : ℕ → ℕ}
    (hA : BlockSupported n p₀ e Idx A) :
    BlockSupported n p₀ e Idx (fun v => A v * C v) := by
  intro v hv hout
  change A v * C v = 0
  rw [hA v hv hout, Nat.zero_mul]

/-- Killing cells of a supported mask preserves its support. -/
theorem blockSupported_sub_left
    {n p₀ e : ℕ} {Idx A C : ℕ → ℕ}
    (hA : BlockSupported n p₀ e Idx A) :
    BlockSupported n p₀ e Idx (fun v => A v * (1 - C v)) := by
  intro v hv hout
  change A v * (1 - C v) = 0
  rw [hA v hv hout, Nat.zero_mul]

/-- Expansion preserves block support.  Off the block both the arena mask
and the source are zero; the dead-vertex equation therefore leaves zero. -/
theorem blockSupported_expandVal
    (hM : BlockSupported n p₀ e Idx Msk)
    (hS : BlockSupported n p₀ e Idx Src) :
    BlockSupported n p₀ e Idx (expandVal G Msk Src) := by
  intro v hv hout
  rw [expandVal_of_dead (hM v hv hout), hS v hv hout]

/-- At loop exit, supported entry storage upgrades the sparse-write
contract to the same carrier-wide pointwise equation exported by
`expandCom_spec`. -/
theorem ExpandBlockInv.done_eq
    (h : ExpandBlockInv n ns nt w p₀ e G O T Idx Msk Src A₀ idx msk src dst σ)
    (hp : σ.vars "p" = e)
    (hA₀ : BlockSupported n p₀ e Idx A₀)
    (hM : BlockSupported n p₀ e Idx Msk)
    (hS : BlockSupported n p₀ e Idx Src) :
    ∃ A, σ.arrs dst = arrOf n A ∧
      (∀ v, v < n → A v = expandVal G Msk Src v) ∧
      BlockSupported n p₀ e Idx A := by
  obtain ⟨A, hA, hset, hkeep⟩ := h.done hp
  have hExp := blockSupported_expandVal (G := G) hM hS
  have hval : ∀ v, v < n → A v = expandVal G Msk Src v := by
    intro v hv
    by_cases hin : ∃ q, p₀ ≤ q ∧ q < e ∧ Idx q = v
    · obtain ⟨q, hq₀, hqe, hqv⟩ := hin
      rw [← hqv]
      exact hset q hq₀ hqe
    · have hout : ∀ q, p₀ ≤ q → q < e → Idx q ≠ v := by
        intro q hq₀ hqe hqv
        exact hin ⟨q, hq₀, hqe, hqv⟩
      rw [hkeep v hv hout, hA₀ v hv hout, hExp v hv hout]
  refine ⟨A, hA, hval, ?_⟩
  intro v hv hout
  rw [hval v hv]
  exact hExp v hv hout

/-- One turn of the block outer loop: read its arbitrary member, run
the already-walked row engine there, then advance the slot pointer. -/
theorem expandBlockBody_spec {B w p₀ e q : ℕ} (hcsr : CsrGraph G ns O T)
    (hpq₀ : p₀ ≤ q) (hqe : q < e) (heB : e < B) (hew : e ≤ w)
    (hB : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (hIdx : ∀ r, p₀ ≤ r → r < e → Idx r < n)
    (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdi : dst ≠ idx) (hdm : dst ≠ msk) (hds : dst ≠ src)
    (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B
      (fun σ => ExpandBlockInv n ns nt w p₀ e G O T Idx Msk Src A₀ idx msk src dst σ ∧
        σ.vars "p" = q)
      (.seq (.assign "z" (.get idx (.var "p")))
        (.seq (expandStep msk src dst) (.assign "p" (.add (.var "p") (.lit 1)))))
      (fun _ σ' => ExpandBlockInv n ns nt w p₀ e G O T Idx Msk Src A₀
          idx msk src dst σ' ∧ σ'.vars "p" = q + 1)
      (24 * Csr.rowLen O (Idx q) + 47) := by
  classical
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hI, hpq⟩ := hσ
  obtain ⟨hpend, hp₀, hpe, hn, hoff, htgt, hnt, hmsk, hsrc, hidx,
    A, hdst, hdone, hkeep⟩ := hI
  have hqw : q < w := lt_of_lt_of_le hqe hew
  have hqn : Idx q < n := hIdx q hpq₀ hqe
  have hqB : q < B := lt_trans hqe heB
  have hIdxB : Idx q < B := lt_trans hqn hnB
  have hread : (Expr.get idx (.var "p")).evalB B σ = some (Idx q) :=
    evalB_get (evalB_var (B := B) (x := "p") (σ := σ) (by rw [hpq]; exact hqB))
      (by rw [hidx, hpq, getElem?_arrOf Idx hqw]) hIdxB
  set σ₁ := σ.setVar "z" (Idx q) with hσ₁
  have hr₁ : Run B (.assign "z" (.get idx (.var "p"))) σ σ₁ 3 :=
    (Run.assign hread).mono (by simp [Expr.size])
  have hAt₁ : ExpandAt n ns nt O T Msk Src A msk src dst (Idx q) σ₁ := by
    refine ⟨by rw [hσ₁, vars_setVar, if_pos rfl], ?_, ?_, ?_, hnt, ?_, ?_, ?_⟩
    · rw [hσ₁, vars_setVar, if_neg (by decide)]; exact hn
    · rw [hσ₁, arrs_setVar]; exact hoff
    · rw [hσ₁, arrs_setVar]; exact htgt
    · rw [hσ₁, arrs_setVar]; exact hmsk
    · rw [hσ₁, arrs_setVar]; exact hsrc
    · rw [hσ₁, arrs_setVar]; exact hdst
  obtain ⟨σ₂, hr₂, hAt₂⟩ :=
    (expandStepAt_spec (G := G) (A₀ := A) hcsr hqn hB hnB hnsB hMB hSB
      hdm hds hdo hdt).run hAt₁
  obtain ⟨hz₂, hn₂, hoff₂, htgt₂, hnt₂, hmsk₂, hsrc₂, hdst₂⟩ := hAt₂
  have hp₂ : σ₂.vars "p" = q := by
    rw [hr₂.frame_var "p" (by simp [expandStep, expandSlot, Csr.loadRow, Csr.scan,
      Com.wvars]), hσ₁, vars_setVar, if_neg (by decide), hpq]
  have hpend₂ : σ₂.vars "pend" = e := by
    rw [hr₂.frame_var "pend" (by simp [expandStep, expandSlot, Csr.loadRow, Csr.scan,
      Com.wvars]), hσ₁, vars_setVar, if_neg (by decide)]
    exact hpend
  have hidx₂ : σ₂.arrs idx = arrOf w Idx := by
    rw [hr₂.frame_arr idx (by simpa [expandStep, expandSlot, Csr.loadRow, Csr.scan,
      Com.warrs] using (Ne.symm hdi)), hσ₁, arrs_setVar]
    exact hidx
  have hpEval : (Expr.var "p").evalB B σ₂ = some q := by
    have h := evalB_var (B := B) (x := "p") (σ := σ₂) (by rw [hp₂]; exact hqB)
    rwa [hp₂] at h
  have hinc : (Expr.add (.var "p") (.lit 1)).evalB B σ₂ = some (q + 1) :=
    evalB_bin hpEval (evalB_lit hB) (by change q + 1 < B; omega)
  set σ₃ := σ₂.setVar "p" (q + 1) with hσ₃
  have hr₃ : Run B (.assign "p" (.add (.var "p") (.lit 1))) σ₂ σ₃ 4 :=
    (Run.assign hinc).mono (by simp [Expr.size])
  have hp₃ : σ₃.vars "p" = q + 1 := by rw [hσ₃, vars_setVar, if_pos rfl]
  refine ⟨σ₃, 3 + ((24 * Csr.rowLen O (Idx q) + 40) + 4),
    hr₁.seq (hr₂.seq hr₃), by omega, ?_, hp₃⟩
  refine ⟨by rw [hσ₃, vars_setVar, if_neg (by decide)]; exact hpend₂,
    by rw [hp₃]; omega, by rw [hp₃]; omega,
    by rw [hσ₃, vars_setVar, if_neg (by decide)]; exact hn₂,
    by rw [hσ₃, arrs_setVar]; exact hoff₂,
    by rw [hσ₃, arrs_setVar]; exact htgt₂, hnt₂,
    by rw [hσ₃, arrs_setVar]; exact hmsk₂,
    by rw [hσ₃, arrs_setVar]; exact hsrc₂,
    by rw [hσ₃, arrs_setVar]; exact hidx₂,
    upd A (Idx q) (expandVal G Msk Src (Idx q)),
    by rw [hσ₃, arrs_setVar]; exact hdst₂, ?_, ?_⟩
  · intro r hr₀ hr
    rw [hp₃] at hr
    by_cases hsame : Idx r = Idx q
    · rw [hsame, upd_self]
    · rw [upd_of_ne _ hsame]
      apply hdone r hr₀
      rw [hpq]
      by_contra hnot
      have hrq : r = q := by omega
      exact hsame (by rw [hrq])
  · intro v hv hnot
    have hcur : Idx q ≠ v := hnot q hpq₀ (by rw [hp₃]; omega)
    rw [upd_of_ne _ (Ne.symm hcur)]
    exact hkeep v hv (fun r hr₀ hr => hnot r hr₀ (by rw [hp₃, hpq] at *; omega))

/-- The block loop itself.  Its potential has one currency for members
and one for their row slots, so the cost is a sum over precisely the
visited block. -/
theorem expandBlockLoop_spec {B w p₀ e : ℕ} (hcsr : CsrGraph G ns O T)
    (heB : e < B) (hew : e ≤ w)
    (hB : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (hIdx : ∀ q, p₀ ≤ q → q < e → Idx q < n)
    (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdi : dst ≠ idx) (hdm : dst ≠ msk) (hds : dst ≠ src)
    (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B
      (fun σ => ExpandBlockInv n ns nt w p₀ e G O T Idx Msk Src A₀
          idx msk src dst σ ∧ σ.vars "p" = p₀)
      (expandBlockLoop idx msk src dst)
      (fun _ σ' => ExpandBlockInv n ns nt w p₀ e G O T Idx Msk Src A₀
          idx msk src dst σ' ∧ σ'.vars "p" = e)
      (51 * (e - p₀) + 24 * expandRowSum O Idx p₀ e + 4) := by
  let I := ExpandBlockInv n ns nt w p₀ e G O T Idx Msk Src A₀ idx msk src dst
  let Φ : Env → ℕ := fun σ =>
    51 * (e - σ.vars "p") + 24 * expandRowSum O Idx (σ.vars "p") e
  refine ((Spec.while_potential (b := .lt (.var "p") (.var "pend"))
    (c := .seq (.assign "z" (.get idx (.var "p")))
      (.seq (expandStep msk src dst) (.assign "p" (.add (.var "p") (.lit 1)))))
    I Φ (fun σ hσ => evalB_condLt_vars (lt_of_le_of_lt hσ.2.2.1 heB)
      (by rw [hσ.1]; exact heB)) ?_ (fun _ h => h) ?_).pre (fun _ h => h.1)).post ?_
  · intro σ hI hb
    have hp₀ : p₀ ≤ σ.vars "p" := hI.2.1
    have hpe : σ.vars "p" < e := by
      have hlt := lt_of_condLt_true hb
      rw [hI.1] at hlt
      exact hlt
    obtain ⟨σ', hr, hI', hp'⟩ :=
      (expandBlockBody_spec (A₀ := A₀) hcsr hp₀ hpe heB hew hB hnB hnsB hIdx
        hMB hSB hdi hdm hds hdo hdt).run ⟨hI, rfl⟩
    refine ⟨σ', 24 * Csr.rowLen O (Idx (σ.vars "p")) + 47, hr, hI', ?_⟩
    change 1 + (Cond.lt (Expr.var "p") (Expr.var "pend")).size +
        (24 * Csr.rowLen O (Idx (σ.vars "p")) + 47) + Φ σ' ≤ Φ σ
    simp only [Cond.size, Expr.size, Φ]
    rw [hp', show e - σ.vars "p" = (e - (σ.vars "p" + 1)) + 1 by omega,
      expandRowSum_succ_bot O Idx hpe]
    omega
  · intro σ hI
    have hsum : expandRowSum O Idx (σ.vars "p") e ≤ expandRowSum O Idx p₀ e :=
      expandRowSum_mono_left O Idx (b := e) hI.2.1
    have hsub : e - σ.vars "p" ≤ e - p₀ := Nat.sub_le_sub_left hI.2.1 e
    have hmemCost := Nat.mul_le_mul_left 51 hsub
    have hrowCost := Nat.mul_le_mul_left 24 hsum
    change Φ σ + 1 + (Cond.lt (Expr.var "p") (Expr.var "pend")).size ≤
      51 * (e - p₀) + 24 * expandRowSum O Idx p₀ e + 4
    simp only [Cond.size, Expr.size, Φ]
    omega
  · intro σ σ' hpre hpost
    refine ⟨hpost.1, ?_⟩
    have hge := le_of_condLt_false hpost.2
    have hle := hpost.1.2.2.1
    have heq := hpost.1.1
    omega

/-- **One cover block, executable.**  `expandBlockCom` first reads the
two block offsets, then runs `expandBlockLoop`.  The exported charge is
the block's member count and its own CSR row mass; neither carrier-wide
quantity occurs. -/
theorem expandBlockCom_spec {B w m c j : ℕ} (hcsr : CsrGraph G ns O T)
    (hc : c < n) (hmB : m < B)
    (hB : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdi : dst ≠ xmmName j) (hdm : dst ≠ msk) (hds : dst ≠ src)
    (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.vars "n" = n ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
        σ.arrs msk = arrOf n Msk ∧ σ.arrs src = arrOf n Src ∧
        σ.arrs dst = arrOf n A₀)
      (expandBlockCom j msk src dst)
      (fun _ σ' =>
        ExpandBlockInv n ns nt w (Xoff c) (Xoff (c + 1)) G O T Xmem Msk Src A₀
          (xmmName j) msk src dst σ' ∧ σ'.vars "p" = Xoff (c + 1))
      (51 * blockSize Xoff c +
        24 * Refine.MassWeight.blockRowSum O Xoff Xmem c + 12) := by
  classical
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcov, hcur, hn, hoff, htgt, hnt, hmsk, hsrc, hdst⟩ := hσ
  have heM : Xoff (c + 1) ≤ m := hcov.row_le hc
  have hpE : Xoff c ≤ Xoff (c + 1) := hcov.off_le_succ hc
  have heB : Xoff (c + 1) < B := lt_of_le_of_lt heM hmB
  have hew : Xoff (c + 1) ≤ w := le_trans heM hcov.ns_le
  have hmem : ∀ q, Xoff c ≤ q → q < Xoff (c + 1) → Xmem q < n := by
    intro q _ hq
    exact hcov.target (lt_of_lt_of_le hq heM)
  obtain ⟨σ₁, hr₁, hcov₁, hp₁, he₁, hst₁⟩ :=
    (CsrWide.loadRow_spec B n m w n (xofName j) (xmmName j) (curName j) "p" "pend"
      Xoff Xmem (by simp [curName, String.ext_iff]) (by decide)).run
      ⟨⟨hcov, by omega, hmB⟩, by rw [hcur]; exact hc, by rw [hcur]; omega⟩
  rw [hcur] at hp₁ he₁
  have hI₁ : ExpandBlockInv n ns nt w (Xoff c) (Xoff (c + 1))
      G O T Xmem Msk Src A₀ (xmmName j) msk src dst σ₁ := by
    refine ⟨he₁, by rw [hp₁], by rw [hp₁]; exact hpE, ?_, ?_, ?_, hnt, ?_, ?_,
      hcov₁.tgtArr, A₀, ?_, ?_, ?_⟩
    · rw [hst₁]
      simp only [vars_setVar, if_neg (by decide : ¬ ("n" = "pend")),
        if_neg (by decide : ¬ ("n" = "p"))]
      exact hn
    · rw [hst₁]; simp only [arrs_setVar]; exact hoff
    · rw [hst₁]; simp only [arrs_setVar]; exact htgt
    · rw [hst₁]; simp only [arrs_setVar]; exact hmsk
    · rw [hst₁]; simp only [arrs_setVar]; exact hsrc
    · rw [hst₁]; simp only [arrs_setVar]; exact hdst
    · intro q _ hq
      rw [hp₁] at hq
      omega
    · intro _ _ _
      rfl
  obtain ⟨σ₂, hr₂, hI₂, hp₂⟩ :=
    (expandBlockLoop_spec (A₀ := A₀) hcsr heB hew hB hnB hnsB hmem hMB hSB
      hdi hdm hds hdo hdt).run ⟨hI₁, hp₁⟩
  refine ⟨σ₂, 8 +
      (51 * (Xoff (c + 1) - Xoff c) + 24 * expandRowSum O Xmem (Xoff c) (Xoff (c + 1)) + 4),
    hr₁.seq hr₂, ?_, hI₂, hp₂⟩
  simp only [blockSize, Refine.MassWeight.blockRowSum, expandRowSum]
  omega

/-- The compositional form of `expandBlockCom_spec`.  If the mask, source,
and entry destination are supported by the current cover block, the sparse
pass agrees with `expandVal` on the whole carrier.  The cover row and its
current centre are framed explicitly so another block pass can follow. -/
theorem expandBlockCom_supported_spec {B w m c j : ℕ} (hcsr : CsrGraph G ns O T)
    (hc : c < n) (hmB : m < B)
    (hB : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdx : dst ≠ xofName j) (hdi : dst ≠ xmmName j)
    (hdm : dst ≠ msk) (hds : dst ≠ src)
    (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.vars "n" = n ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
        σ.arrs msk = arrOf n Msk ∧ σ.arrs src = arrOf n Src ∧
        σ.arrs dst = arrOf n A₀ ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem Msk ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem Src ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A₀)
      (expandBlockCom j msk src dst)
      (fun _ σ' => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
        σ'.vars (curName j) = c ∧ σ'.vars "n" = n ∧
        σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
        σ'.arrs msk = arrOf n Msk ∧ σ'.arrs src = arrOf n Src ∧
        ∃ A, σ'.arrs dst = arrOf n A ∧
          (∀ v, v < n → A v = expandVal G Msk Src v) ∧
          BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A)
      (51 * blockSize Xoff c +
        24 * Refine.MassWeight.blockRowSum O Xoff Xmem c + 12) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcov, hcur, hn, hoff, htgt, hnt, hmsk, hsrc, hdst,
    hM, hS, hA₀⟩ := hσ
  obtain ⟨σ', hr, hI, hp⟩ :=
    (expandBlockCom_spec (A₀ := A₀) hcsr hc hmB hB hnB hnsB hMB hSB
      hdi hdm hds hdo hdt).run
      ⟨hcov, hcur, hn, hoff, htgt, hnt, hmsk, hsrc, hdst⟩
  obtain ⟨A, hA, hval, hsup⟩ := ExpandBlockInv.done_eq hI hp hA₀ hM hS
  obtain ⟨hpend, hp₀, hpe, hn', hoff', htgt', hnt', hmsk', hsrc', hidx', -⟩ := hI
  have hxof : σ'.arrs (xofName j) = σ.arrs (xofName j) :=
    hr.frame_arr (xofName j) (by
      simpa [expandBlockCom, expandBlockLoop, expandStep, expandSlot, Csr.loadRow,
        Csr.scan, Com.warrs] using (Ne.symm hdx))
  have hcov' : CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' :=
    hcov.of_eq hxof (by rw [hidx', hcov.tgtArr])
  have hcur' : σ'.vars (curName j) = c := by
    rw [hr.frame_var (curName j) (by
      simp [expandBlockCom, expandBlockLoop, expandStep, expandSlot, Csr.loadRow,
        Csr.scan, Com.wvars, curName, String.ext_iff]), hcur]
  exact ⟨σ', _, hr, le_rfl, hcov', hcur', hn', hoff', htgt', hnt', hmsk', hsrc',
    A, hA, hval, hsup⟩

/-! #### Loaded cover maps at the driver boundary -/

/-- Compose the cover row load with the generic executable interval map.
The result frames the cover itself and exposes the same sparse-write
contract as the driver-independent loop. -/
theorem coverMapCom_spec {B w m c j : ℕ} {x : Expr} {F g₀ : ℕ → ℕ}
    {l : List (String × ℕ × (ℕ → ℕ))} (hc : c < n) (hmB : m < B)
    (hB : 1 < B) (hnB : n < B) (hdx : dst ≠ xofName j)
    (hdi : dst ≠ xmmName j) (hdf : ∀ a ∈ l, a.1 ≠ dst)
    (hx : ∀ (σ : Env) q, Xoff c ≤ q → q < Xoff (c + 1) → σ.vars "p" = q →
      σ.vars "cw" = Xmem q →
      Refine.BlockLeaves.BlockMapRangeInv n w (Xoff c) (Xoff (c + 1))
        (xmmName j) dst Xmem F g₀ l σ → x.evalB B σ = some (F (Xmem q))) :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        Refine.BlockLeaves.BlockFrozen l σ)
      (.seq (Csr.loadRow (xofName j) (curName j) "p" "pend")
        (Refine.BlockLeaves.blockMapRangeCom (xmmName j) dst x))
      (fun _ σ' =>
        CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
        σ'.vars (curName j) = c ∧
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ q, Xoff c ≤ q → q < Xoff (c + 1) → g (Xmem q) = F (Xmem q)) ∧
          (∀ v, v < n →
            (∀ q, Xoff c ≤ q → q < Xoff (c + 1) → Xmem q ≠ v) → g v = g₀ v)) ∧
        Refine.BlockLeaves.BlockFrozen l σ')
      ((13 + x.size) * blockSize Xoff c + 12) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcov, hcur, hdst, hfr⟩ := hσ
  have heM : Xoff (c + 1) ≤ m := hcov.row_le hc
  have hpE : Xoff c ≤ Xoff (c + 1) := hcov.off_le_succ hc
  have heB : Xoff (c + 1) < B := lt_of_le_of_lt heM hmB
  have hew : Xoff (c + 1) ≤ w := le_trans heM hcov.ns_le
  have hmem : ∀ q, Xoff c ≤ q → q < Xoff (c + 1) → Xmem q < n := by
    intro q _ hq
    exact hcov.target (lt_of_lt_of_le hq heM)
  obtain ⟨σ₁, hr₁, hcov₁, hp₁, he₁, hst₁⟩ :=
    (CsrWide.loadRow_spec B n m w n (xofName j) (xmmName j) (curName j) "p" "pend"
      Xoff Xmem (by simp [curName, String.ext_iff]) (by decide)).run
      ⟨⟨hcov, by omega, hmB⟩, by rw [hcur]; exact hc, by rw [hcur]; omega⟩
  rw [hcur] at hp₁ he₁
  have hdst₁ : σ₁.arrs dst = arrOf n g₀ := by rw [hst₁]; simp only [arrs_setVar]; exact hdst
  have hfr₁ : Refine.BlockLeaves.BlockFrozen l σ₁ := by
    intro a ha
    rw [hst₁]
    simp only [arrs_setVar]
    exact hfr a ha
  obtain ⟨σ₂, hr₂, hout₂, hp₂, hpend₂, hidx₂, hfr₂⟩ :=
    (Refine.BlockLeaves.blockMapRangeCom_spec (B := B) (n := n) (w := w)
      (p₀ := Xoff c) (e := Xoff (c + 1)) (idx := xmmName j) (dst := dst)
      (x := x) (Idx := Xmem) (F := F) (g₀ := g₀) (l := l)
      hB hnB heB hew hpE hmem hdi hdf hx).run
      ⟨hp₁, he₁, hcov₁.tgtArr, hdst₁, hfr₁⟩
  have hxof₂ : σ₂.arrs (xofName j) = σ₁.arrs (xofName j) :=
    hr₂.frame_arr (xofName j) (by
      simpa [Refine.BlockLeaves.blockMapRangeCom, Com.warrs] using (Ne.symm hdx))
  have hcov₂ : CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ₂ :=
    hcov₁.of_eq hxof₂ (by rw [hidx₂, hcov₁.tgtArr])
  have hcur₂ : σ₂.vars (curName j) = c := by
    rw [hr₂.frame_var (curName j) (by
      simp [Refine.BlockLeaves.blockMapRangeCom, Com.wvars, curName, String.ext_iff]),
      hst₁]
    exact hcur
  refine ⟨σ₂, 8 + ((13 + x.size) * (Xoff (c + 1) - Xoff c) + 4),
    hr₁.seq hr₂, ?_, hcov₂, hcur₂, hout₂, hfr₂⟩
  simp only [blockSize]
  omega

/-- The compositional form of `coverMapCom_spec`.  If both the entry
destination and the value being written are supported by the loaded
cover block, the sparse contract upgrades to a whole-carrier equation
and the resulting destination remains supported. -/
theorem coverMapCom_supported_spec {B w m c j : ℕ} {x : Expr} {F g₀ : ℕ → ℕ}
    {l : List (String × ℕ × (ℕ → ℕ))} (hc : c < n) (hmB : m < B)
    (hB : 1 < B) (hnB : n < B) (hdx : dst ≠ xofName j)
    (hdi : dst ≠ xmmName j) (hdf : ∀ a ∈ l, a.1 ≠ dst)
    (hx : ∀ (σ : Env) q, Xoff c ≤ q → q < Xoff (c + 1) → σ.vars "p" = q →
      σ.vars "cw" = Xmem q →
      Refine.BlockLeaves.BlockMapRangeInv n w (Xoff c) (Xoff (c + 1))
        (xmmName j) dst Xmem F g₀ l σ → x.evalB B σ = some (F (Xmem q))) :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        Refine.BlockLeaves.BlockFrozen l σ ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem F ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀)
      (.seq (Csr.loadRow (xofName j) (curName j) "p" "pend")
        (Refine.BlockLeaves.blockMapRangeCom (xmmName j) dst x))
      (fun _ σ' =>
        CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
        σ'.vars (curName j) = c ∧
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = F v) ∧
          BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g) ∧
        Refine.BlockLeaves.BlockFrozen l σ')
      ((13 + x.size) * blockSize Xoff c + 12) := by
  refine (coverMapCom_spec hc hmB hB hnB hdx hdi hdf hx).pre ?_ |>.post ?_
  · rintro σ ⟨hcov, hcur, hdst, hfr, -, -⟩
    exact ⟨hcov, hcur, hdst, hfr⟩
  · rintro σ σ' ⟨-, -, -, -, hF, hg₀⟩ ⟨hcov, hcur, ⟨g, hg, hset, hkeep⟩, hfr⟩
    obtain ⟨hval, hsup⟩ := sparseBlock_eq_of_supported hset hkeep hg₀ hF
    exact ⟨hcov, hcur, ⟨g, hg, hval, hsup⟩, hfr⟩

/-- Clear the current cover block from supported storage.  The result is
the zero function on the whole carrier, so this is the cleanup operation
that closes a block-local scratch array's lifecycle. -/
theorem coverClearCom_supported_spec {B w m c j : ℕ} {g₀ : ℕ → ℕ}
    (hc : c < n) (hmB : m < B) (hB : 1 < B) (hnB : n < B)
    (hdx : dst ≠ xofName j) (hdi : dst ≠ xmmName j) :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀)
      (coverClearCom j dst)
      (fun _ σ' =>
        CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
        σ'.vars (curName j) = c ∧
        ∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = 0) ∧
          BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g)
      (14 * blockSize Xoff c + 12) := by
  have h := coverMapCom_supported_spec (n := n) (Xoff := Xoff) (Xmem := Xmem)
    (dst := dst) (B := B) (w := w) (m := m) (c := c) (j := j)
    (x := .lit 0) (F := fun _ => 0) (g₀ := g₀) (l := [])
    hc hmB hB hnB hdx hdi
    (by simp)
    (by
      intro σ q _ _ _ _ _
      exact evalB_lit (by omega))
  simpa [coverClearCom, Refine.BlockLeaves.blockClearRangeCom,
    Refine.BlockLeaves.BlockFrozen, Expr.size] using h

/-- Copy a supported source over the current cover block.  Supported
entry storage turns the sparse write into the same whole-carrier copy
equation as `copyCom`, while retaining support for the next block pass. -/
theorem coverCopyCom_supported_spec {B w m c j : ℕ} {A g₀ : ℕ → ℕ}
    {src : String} (hc : c < n) (hmB : m < B) (hB : 1 < B) (hnB : n < B)
    (hmem : ∀ q, Xoff c ≤ q → q < Xoff (c + 1) → Xmem q < n)
    (hAB : ∀ v, v < n → A v < B)
    (hdx : dst ≠ xofName j) (hdi : dst ≠ xmmName j) (hds : dst ≠ src) :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        σ.arrs src = arrOf n A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀)
      (coverCopyCom j src dst)
      (fun _ σ' =>
        CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
        σ'.vars (curName j) = c ∧
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = A v) ∧
          BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g) ∧
        σ'.arrs src = arrOf n A)
      (15 * blockSize Xoff c + 12) := by
  have hbase := coverMapCom_supported_spec (n := n) (Xoff := Xoff) (Xmem := Xmem)
    (dst := dst) (B := B) (w := w) (m := m) (c := c) (j := j)
    (x := .get src (.var "cw")) (F := A) (g₀ := g₀) (l := [(src, n, A)])
    hc hmB hB hnB hdx hdi
    (by rintro a ha; rcases List.mem_singleton.mp ha with rfl; exact Ne.symm hds)
    (by
      intro σ q hq₀ hqe _ hcw hI
      obtain ⟨-, -, -, -, hfr, -⟩ := hI
      have hsrc := hfr (src, n, A) (by simp)
      have hecw : (Expr.var "cw").evalB B σ = some (Xmem q) := by
        have he := evalB_var (B := B) (x := "cw") (σ := σ) (by
          rw [hcw]
          exact lt_trans (hmem q hq₀ hqe) hnB)
        rwa [hcw] at he
      exact evalB_get hecw
        (by rw [hsrc, getElem?_arrOf A (hmem q hq₀ hqe)])
        (hAB _ (hmem q hq₀ hqe)))
  have h := hbase.pre (P' := fun σ =>
      CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        σ.arrs src = arrOf n A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀) (by
    rintro σ ⟨hcov, hcur, hdst, hsrc, hAsup, hg₀sup⟩
    exact ⟨hcov, hcur, hdst, (by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact hsrc), hAsup, hg₀sup⟩)
  simpa [coverCopyCom, Refine.BlockLeaves.blockCopyRangeCom,
    Refine.BlockLeaves.BlockFrozen, Expr.size] using h

/-- Conjoin two frozen arrays over the current cover block.  Support of
the left factor is enough to support the product. -/
theorem coverAndCom_supported_spec {B w m c j : ℕ} {A C g₀ : ℕ → ℕ}
    {a b : String} (hc : c < n) (hmB : m < B) (hB : 1 < B) (hnB : n < B)
    (hmem : ∀ q, Xoff c ≤ q → q < Xoff (c + 1) → Xmem q < n)
    (hAB : ∀ v, v < n → A v < B) (hCB : ∀ v, v < n → C v < B)
    (hACB : ∀ q, Xoff c ≤ q → q < Xoff (c + 1) → A (Xmem q) * C (Xmem q) < B)
    (hdx : dst ≠ xofName j) (hdi : dst ≠ xmmName j)
    (hda : dst ≠ a) (hdb : dst ≠ b) :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        σ.arrs a = arrOf n A ∧ σ.arrs b = arrOf n C ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀)
      (coverAndCom j a b dst)
      (fun _ σ' =>
        CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
        σ'.vars (curName j) = c ∧
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = A v * C v) ∧
          BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g) ∧
        σ'.arrs a = arrOf n A ∧ σ'.arrs b = arrOf n C)
      (18 * blockSize Xoff c + 12) := by
  have hbase := coverMapCom_supported_spec (n := n) (Xoff := Xoff) (Xmem := Xmem)
    (dst := dst) (B := B) (w := w) (m := m) (c := c) (j := j)
    (x := .mul (.get a (.var "cw")) (.get b (.var "cw")))
    (F := fun v => A v * C v) (g₀ := g₀) (l := [(a, n, A), (b, n, C)])
    hc hmB hB hnB hdx hdi
    (by
      rintro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Ne.symm hda
      · exact Ne.symm hdb)
    (by
      intro σ q hq₀ hqe _ hcw hI
      obtain ⟨-, -, -, -, hfr, -⟩ := hI
      have ha := hfr (a, n, A) (by simp)
      have hb := hfr (b, n, C) (by simp)
      have hq : Xmem q < n := hmem q hq₀ hqe
      have hecw : (Expr.var "cw").evalB B σ = some (Xmem q) := by
        have he := evalB_var (B := B) (x := "cw") (σ := σ) (by
          rw [hcw]; exact lt_trans hq hnB)
        rwa [hcw] at he
      exact evalB_bin
        (evalB_get hecw (by rw [ha, getElem?_arrOf A hq]) (hAB _ hq))
        (evalB_get hecw (by rw [hb, getElem?_arrOf C hq]) (hCB _ hq))
        (hACB q hq₀ hqe))
  have h := hbase.pre (P' := fun σ =>
      CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        σ.arrs a = arrOf n A ∧ σ.arrs b = arrOf n C ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀) (by
    rintro σ ⟨hcov, hcur, hdst, ha, hb, hAsup, hg₀sup⟩
    exact ⟨hcov, hcur, hdst, (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb), blockSupported_mul_left (C := C) hAsup, hg₀sup⟩)
  simpa [coverAndCom, Refine.BlockLeaves.blockAndRangeCom,
    Refine.BlockLeaves.BlockFrozen, Expr.size] using h

/-- Subtract a frozen mask over the current cover block.  Support of the
left factor survives the pointwise subtraction. -/
theorem coverSubCom_supported_spec {B w m c j : ℕ} {A C g₀ : ℕ → ℕ}
    {a b : String} (hc : c < n) (hmB : m < B) (hB : 1 < B) (hnB : n < B)
    (hmem : ∀ q, Xoff c ≤ q → q < Xoff (c + 1) → Xmem q < n)
    (hAB : ∀ v, v < n → A v < B) (hCB : ∀ v, v < n → C v < B)
    (hACB : ∀ q, Xoff c ≤ q → q < Xoff (c + 1) →
      A (Xmem q) * (1 - C (Xmem q)) < B)
    (hdx : dst ≠ xofName j) (hdi : dst ≠ xmmName j)
    (hda : dst ≠ a) (hdb : dst ≠ b) :
    Spec B
      (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        σ.arrs a = arrOf n A ∧ σ.arrs b = arrOf n C ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀)
      (coverSubCom j a b dst)
      (fun _ σ' =>
        CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
        σ'.vars (curName j) = c ∧
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = A v * (1 - C v)) ∧
          BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g) ∧
        σ'.arrs a = arrOf n A ∧ σ'.arrs b = arrOf n C)
      (20 * blockSize Xoff c + 12) := by
  have hbase := coverMapCom_supported_spec (n := n) (Xoff := Xoff) (Xmem := Xmem)
    (dst := dst) (B := B) (w := w) (m := m) (c := c) (j := j)
    (x := .mul (.get a (.var "cw")) (.sub (.lit 1) (.get b (.var "cw"))))
    (F := fun v => A v * (1 - C v)) (g₀ := g₀)
    (l := [(a, n, A), (b, n, C)]) hc hmB hB hnB hdx hdi
    (by
      rintro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Ne.symm hda
      · exact Ne.symm hdb)
    (by
      intro σ q hq₀ hqe _ hcw hI
      obtain ⟨-, -, -, -, hfr, -⟩ := hI
      have ha := hfr (a, n, A) (by simp)
      have hb := hfr (b, n, C) (by simp)
      have hq : Xmem q < n := hmem q hq₀ hqe
      have hecw : (Expr.var "cw").evalB B σ = some (Xmem q) := by
        have he := evalB_var (B := B) (x := "cw") (σ := σ) (by
          rw [hcw]; exact lt_trans hq hnB)
        rwa [hcw] at he
      exact evalB_bin
        (evalB_get hecw (by rw [ha, getElem?_arrOf A hq]) (hAB _ hq))
        (evalB_bin (evalB_lit hB)
          (evalB_get hecw (by rw [hb, getElem?_arrOf C hq]) (hCB _ hq))
          (by change 1 - C (Xmem q) < B; omega))
        (hACB q hq₀ hqe))
  have h := hbase.pre (P' := fun σ =>
      CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
        σ.vars (curName j) = c ∧ σ.arrs dst = arrOf n g₀ ∧
        σ.arrs a = arrOf n A ∧ σ.arrs b = arrOf n C ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A ∧
        BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem g₀) (by
    rintro σ ⟨hcov, hcur, hdst, ha, hb, hAsup, hg₀sup⟩
    exact ⟨hcov, hcur, hdst, (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb), blockSupported_sub_left (C := C) hAsup, hg₀sup⟩)
  simpa [coverSubCom, Refine.BlockLeaves.blockSubRangeCom,
    Refine.BlockLeaves.BlockFrozen, Expr.size] using h

/-- The executable expansion's two-currency charge fits the one
block-weight slot used by the almost-linear recurrence. -/
theorem expandBlockCost_le_weight (hcsr : RamElim.CsrSimple G ns O T)
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    51 * blockSize Xoff c + 24 * Refine.MassWeight.blockRowSum O Xoff Xmem c + 12 ≤
      200 * (Refine.MassWeight.blockWeight n G Xoff Xmem c + 1) := by
  rw [Refine.MassWeight.blockRowSum_eq_blockDegSum hcsr hmem,
    Refine.MassWeight.blockWeight_eq_add_degSum G Xoff Xmem hmem]
  omega

/-- The block structure of a depth, as the reasoning kit's relation. -/
theorem csr_of_expandInv {σ : Env} (hcsr : CsrGraph G ns O T)
    (h : ExpandInv n ns nt G O T Msk Src msk src dst σ) :
    CsrWide.CsrW "off" "tgt" n ns nt n O T σ :=
  ⟨h.2.2.1, h.2.2.2.1, fun i hi => hcsr.mono i hi, hcsr.last, h.2.2.2.2.1,
    fun p hp => hcsr.target_lt p hp⟩

/-- The pass's state does not see the three scalars the scan moves. -/
theorem expandInv_congr {σ σ' : Env} (h : ExpandInv n ns nt G O T Msk Src msk src dst σ)
    (hz : σ'.vars "z" = σ.vars "z") (hn : σ'.vars "n" = σ.vars "n")
    (ha : ∀ a : String, σ'.arrs a = σ.arrs a) :
    ExpandInv n ns nt G O T Msk Src msk src dst σ' :=
  ⟨h.1.of_eq (ha dst) hz, by rw [hn]; exact h.2.1, by rw [ha]; exact h.2.2.1,
    by rw [ha]; exact h.2.2.2.1, h.2.2.2.2.1, by rw [ha]; exact h.2.2.2.2.2.1,
    by rw [ha]; exact h.2.2.2.2.2.2⟩

/-- **One slot of the block.** The hit flag rises exactly when the slot
names a live marked vertex, which is the one turn `Csr.rowScan_spec`
asks for. -/
theorem expandSlot_step {B z : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hzn : z < n) (σ : Env) (hI : ScanHit n ns nt G O T Msk Src msk src dst z σ)
    (hj : σ.vars "j" < O (z + 1)) :
    ∃ σ' K', Run B (expandSlot msk src) σ σ' K' ∧
      ScanHit n ns nt G O T Msk Src msk src dst z σ' ∧ σ'.vars "j" = σ.vars "j" + 1 ∧ K' ≤ 20 := by
  classical
  obtain ⟨hinv, hzv, hjend, hjlo, -, hhit⟩ := hI
  have hcsrRel := csr_of_expandInv hcsr hinv
  have hjns : σ.vars "j" < ns := lt_of_lt_of_le hj (hcsrRel.row_le hzn)
  have hjB : σ.vars "j" < B := by omega
  have hTn : T (σ.vars "j") < n := hcsr.target_lt _ hjns
  have hslot : (Expr.get "tgt" (.var "j")).evalB B σ = some (T (σ.vars "j")) :=
    evalB_get (evalB_var hjB)
      (by rw [hinv.2.2.2.1, getElem?_arrOf T (lt_of_lt_of_le hjns hinv.2.2.2.2.1)]) (by omega)
  set τ := σ.setVar "w" (T (σ.vars "j")) with hτ
  have hrw : Run B (.assign "w" (.get "tgt" (.var "j"))) σ τ 3 :=
    (Run.assign hslot).mono (by simp)
  have hwv : τ.vars "w" = T (σ.vars "j") := by rw [hτ]; simp
  have hcmsk : (Cond.lt (.lit 0) (.get msk (.var "w"))).evalB B τ =
      some (decide (0 < Msk (T (σ.vars "j")))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hwv]; omega))
        (by rw [hτ, arrs_setVar, hinv.2.2.2.2.2.1, hwv, getElem?_arrOf Msk hTn]) (hMB _ hTn))
  have hcsrc : (Cond.lt (.lit 0) (.get src (.var "w"))).evalB B τ =
      some (decide (0 < Src (T (σ.vars "j")))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hwv]; omega))
        (by rw [hτ, arrs_setVar, hinv.2.2.2.2.2.2, hwv, getElem?_arrOf Src hTn]) (hSB _ hTn))
  -- the hit flag after the two tests, in either shape
  have hstepGen : ∀ (ρ : Env) (Kb : ℕ), Run B
        (.ite (.lt (.lit 0) (.get msk (.var "w")))
          (.ite (.lt (.lit 0) (.get src (.var "w"))) (.assign "hit" (.lit 1)) .skip) .skip) τ ρ Kb →
      ρ.vars "j" = σ.vars "j" → True := fun _ _ _ _ => trivial
  clear hstepGen
  by_cases hm : Msk (T (σ.vars "j")) = 0
  · -- a dead neighbour: nothing happens
    refine ⟨τ.setVar "j" (σ.vars "j" + 1), 20,
      (hrw.seq ((Run.ite_false (by rw [hcmsk, hm]; simp) Run.skip).seq
        (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
          (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
    refine ⟨expandInv_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp) (fun a => by rw [hτ]; simp),
      by rw [hτ]; simp [hzv], by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega,
      by rw [hτ]; simp; omega, ?_⟩
    rw [show (τ.setVar "j" (σ.vars "j" + 1)).vars "hit" = σ.vars "hit" by rw [hτ]; simp,
      show (τ.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by rw [hτ]; simp, hhit]
    congr 1
    refine propext ⟨fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, by omega, h₃, h₄⟩,
      fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, ?_, h₃, h₄⟩⟩
    rcases Nat.lt_or_ge p (σ.vars "j") with h' | h'
    · exact h'
    · exact absurd h₃ (by rw [show p = σ.vars "j" by omega, hm]; simp)
  · by_cases hs : Src (T (σ.vars "j")) = 0
    · -- alive but unmarked: nothing happens either
      refine ⟨τ.setVar "j" (σ.vars "j" + 1), 20,
        (hrw.seq ((Run.ite_true (by rw [hcmsk]; simp; omega)
          (Run.ite_false (by rw [hcsrc, hs]; simp) Run.skip)).seq
          (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
            (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
      refine ⟨expandInv_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp)
          (fun a => by rw [hτ]; simp),
        by rw [hτ]; simp [hzv], by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega,
        by rw [hτ]; simp; omega, ?_⟩
      rw [show (τ.setVar "j" (σ.vars "j" + 1)).vars "hit" = σ.vars "hit" by rw [hτ]; simp,
        show (τ.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by rw [hτ]; simp, hhit]
      congr 1
      refine propext ⟨fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, by omega, h₃, h₄⟩,
        fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, ?_, h₃, h₄⟩⟩
      rcases Nat.lt_or_ge p (σ.vars "j") with h' | h'
      · exact h'
      · exact absurd h₄ (by rw [show p = σ.vars "j" by omega, hs]; simp)
    · -- a live marked neighbour: the flag rises
      refine ⟨(τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1), 20,
        (hrw.seq ((Run.ite_true (by rw [hcmsk]; simp; omega)
          (Run.ite_true (by rw [hcsrc]; simp; omega)
            (Run.assign (evalB_lit (by omega))))).seq
          (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
            (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
      refine ⟨expandInv_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp)
          (fun a => by rw [hτ]; simp),
        by rw [hτ]; simp [hzv], by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega,
        by rw [hτ]; simp; omega, ?_⟩
      rw [show ((τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1)).vars "hit" = 1 by rw [hτ]; simp,
        show ((τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by
          rw [hτ]; simp]
      rw [if_pos ⟨σ.vars "j", hjlo, by omega, hm, hs⟩]

/-- **One vertex of the expansion.** The source's own cell, raised to
one when a live neighbour is marked: the block scan decides which, and
`hit_eq_expandVal` is what a full scan is worth. -/
theorem expandStep_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (z : ℕ) (hz : z < n)
    (hB : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdm : dst ≠ msk) (hds : dst ≠ src) (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B (fun σ => ExpandInv n ns nt G O T Msk Src msk src dst σ ∧ σ.vars "z" = z)
      (expandStep msk src dst)
      (fun _ σ' => ExpandInv n ns nt G O T Msk Src msk src dst σ' ∧ σ'.vars "z" = z + 1)
      (24 * Csr.rowLen O z + 40) := by
  classical
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hinv, hzσ⟩ := hσ
  have hzlt : σ.vars "z" < n := by rw [hzσ]; exact hz
  have hzB : σ.vars "z" < B := by omega
  have hSz : Src (σ.vars "z") < B := hSB _ hzlt
  -- hit := src[z]
  have hr₁ : Run B (.assign "hit" (.get src (.var "z"))) σ
      (σ.setVar "hit" (Src (σ.vars "z"))) 3 :=
    (Run.assign (evalB_get (evalB_var hzB)
      (by rw [hinv.2.2.2.2.2.2, getElem?_arrOf Src hzlt]) hSz)).mono (by simp)
  set σ₁ := σ.setVar "hit" (Src (σ.vars "z")) with hσ₁
  have hz₁ : σ₁.vars "z" = σ.vars "z" := by rw [hσ₁]; simp
  have hhit₁ : σ₁.vars "hit" = Src (σ.vars "z") := by rw [hσ₁]; simp
  have hinv₁ : ExpandInv n ns nt G O T Msk Src msk src dst σ₁ :=
    expandInv_congr hinv hz₁ (by rw [hσ₁]; simp) (fun a => by rw [hσ₁]; simp)
  have hcond : (Cond.lt (.lit 0) (.get msk (.var "z"))).evalB B σ₁ =
      some (decide (0 < Msk (σ.vars "z"))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hz₁]; omega))
        (by rw [hinv₁.2.2.2.2.2.1, hz₁, getElem?_arrOf Msk hzlt]) (hMB _ hzlt))
  -- the conditional: a live vertex scans its block, a dead one does not
  have key : ∃ σ₂ K₂, Run B (.ite (.lt (.lit 0) (.get msk (.var "z")))
        (.seq (Csr.loadRow "off" "z" "j" "jend") (Csr.scan "j" "jend" (expandSlot msk src)))
        .skip) σ₁ σ₂ K₂ ∧ K₂ ≤ 24 * Csr.rowLen O z + 17 ∧
      ExpandInv n ns nt G O T Msk Src msk src dst σ₂ ∧ σ₂.vars "z" = σ.vars "z" ∧
      σ₂.vars "hit" = expandVal G Msk Src (σ.vars "z") := by
    by_cases hm : Msk (σ.vars "z") = 0
    · exact ⟨σ₁, 6, Run.ite_false (by rw [hcond, hm]; simp) Run.skip, by omega, hinv₁, hz₁,
        by rw [hhit₁, expandVal_of_dead hm]⟩
    · obtain ⟨σ₂, hr₂, hcsr₂, hj₂, hjend₂, hst₂⟩ :=
        (CsrWide.loadRow_spec B n ns nt n "off" "tgt" "z" "j" "jend" O T
            (by decide) (by decide)).run
          (σ := σ₁) ⟨⟨csr_of_expandInv hcsr hinv₁, by omega, hnsB⟩,
            by rw [hz₁]; exact hzlt, by rw [hz₁]; omega⟩
      rw [hz₁] at hj₂ hjend₂
      have hzz : σ₂.vars "z" = σ.vars "z" := by rw [hst₂]; simp [hz₁]
      have hhit₂ : σ₂.vars "hit" = Src (σ.vars "z") := by rw [hst₂]; simp [hhit₁]
      have hinv₂ : ExpandInv n ns nt G O T Msk Src msk src dst σ₂ :=
        expandInv_congr hinv₁ (by rw [hst₂]; simp) (by rw [hst₂]; simp)
          (fun a => by rw [hst₂]; simp)
      have hrow : O (σ.vars "z" + 1) ≤ ns := (csr_of_expandInv hcsr hinv).row_le hzlt
      have hlo : O (σ.vars "z") ≤ O (σ.vars "z" + 1) := hcsr.mono _ hzlt
      have hclause : σ₂.vars "hit" =
          (if ∃ p, O (σ.vars "z") ≤ p ∧ p < σ₂.vars "j" ∧ Msk (T p) ≠ 0 ∧ Src (T p) ≠ 0
            then 1 else Src (σ.vars "z")) := by
        rw [hhit₂, if_neg]
        rintro ⟨p, h₁, h₂, -⟩
        rw [hj₂] at h₂
        omega
      have hI₂ : ScanHit n ns nt G O T Msk Src msk src dst (σ.vars "z") σ₂ :=
        ⟨hinv₂, hzz, hjend₂, by omega, by omega, hclause⟩
      obtain ⟨σ₃, hr₃, hI₃, hj₃⟩ :=
        (Csr.rowScan_spec B (24 * Csr.rowLen O z + 4) (O (σ.vars "z" + 1)) 20 "j" "jend"
          (expandSlot msk src) (P := ScanHit n ns nt G O T Msk Src msk src dst (σ.vars "z"))
          (ScanHit n ns nt G O T Msk Src msk src dst (σ.vars "z")) (by omega)
          (fun ρ hρ => ⟨hρ.2.2.1, hρ.2.2.2.2.1⟩)
          (fun ρ hρ hjlt => expandSlot_step hcsr hB hnB hnsB hMB hSB hzlt ρ hρ hjlt)
          (fun _ hρ => hρ)
          (fun ρ hρ => by
            have hloρ : O z ≤ ρ.vars "j" := by
              simpa [hzσ] using hρ.2.2.2.1
            have hrem : O (σ.vars "z" + 1) - ρ.vars "j" ≤ Csr.rowLen O z := by
              change O (σ.vars "z" + 1) - ρ.vars "j" ≤ O (z + 1) - O z
              rw [hzσ]
              exact Nat.sub_le_sub_left hloρ _
            have h1 : (20 + 4) * (O (σ.vars "z" + 1) - ρ.vars "j") ≤
                24 * Csr.rowLen O z := Nat.mul_le_mul_left 24 hrem
            omega)).run hI₂
      refine ⟨σ₃, 1 + 4 + (8 + (24 * Csr.rowLen O z + 4)),
        Run.ite_true (by rw [hcond]; simp; omega)
        (hr₂.seq hr₃), by omega, hI₃.1, hI₃.2.1, ?_⟩
      rw [hI₃.2.2.2.2.2, hj₃, hit_eq_expandVal hcsr hzlt hm]
  obtain ⟨σ₂, K₂, hr₂, hK₂, hinv₂, hzz, hhit₂⟩ := key
  -- the store, and the counter
  have hval : expandVal G Msk Src (σ.vars "z") < B := by
    rcases expandVal_eq_or G Msk Src (σ.vars "z") with h | h
    · rw [h]; omega
    · rw [h]; exact hSz
  have hdlen : σ₂.vars "z" < (σ₂.arrs dst).length := by rw [hinv₂.1.length, hzz]; exact hzlt
  refine ⟨(σ₂.setArr dst (σ₂.vars "z") (σ₂.vars "hit")).setVar "z" (σ₂.vars "z" + 1),
    3 + (K₂ + (3 + 4)), (hr₁.seq (hr₂.seq
      ((Run.store (evalB_var (by rw [hzz]; omega)) (evalB_var (by rw [hhit₂]; exact hval)) hdlen).seq
        (Run.assign (evalB_bin (evalB_var (by simp [hzz]; omega)) (evalB_lit (by omega))
          (by simp [hzz]; omega)))))), by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [hzz, hzσ]⟩
  · exact hinv₂.1.step (by rw [hzz]; exact hzlt) (by rw [hhit₂, hzz])
  · simp only [vars_setVar, if_neg (by decide : ¬ ("n" = "z")), vars_setArr]
    exact hinv₂.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdo)]; exact hinv₂.2.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdt)]; exact hinv₂.2.2.2.1
  · exact hinv₂.2.2.2.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdm)]; exact hinv₂.2.2.2.2.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hds)]; exact hinv₂.2.2.2.2.2.2

/-- **One expansion pass, discharged.** The destination holds
`RamDriverCluster.expandVal` at every vertex of the carrier — so, by
`markSet_expandVal`, it marks one neighbourhood step of what the source
marks — and everything the pass reads comes back. -/
theorem expandCom_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hMB : ∀ k, k < n → Msk k < B)
    (hSB : ∀ k, k < n → Src k < B)
    (hdm : dst ≠ msk) (hds : dst ≠ src) (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf nt T ∧ σ.arrs msk = arrOf n Msk ∧ σ.arrs src = arrOf n Src ∧
        (∃ g, σ.arrs dst = arrOf n g))
      (expandCom msk src dst)
      (fun _ σ' => (∃ g, σ'.arrs dst = arrOf n g ∧
          ∀ k, k < n → g k = expandVal G Msk Src k) ∧
        σ'.vars "z" = n ∧ σ'.vars "n" = n ∧ σ'.arrs "off" = arrOf (n + 1) O ∧
        σ'.arrs "tgt" = arrOf nt T ∧ σ'.arrs msk = arrOf n Msk ∧ σ'.arrs src = arrOf n Src)
      (24 * ns + 44 * n + 6) := by
  refine ((Refine.SigmaLoop.forRangeZeroSum (B := B) "z" "n"
    (ExpandInv n ns nt G O T Msk Src msk src dst) n
    (fun z => 24 * Csr.rowLen O z + 40) hnB (fun τ hτ => hτ.1.le)
    (fun τ hτ => hτ.2.1)
    (fun z hz => expandStep_spec hcsr z hz hB hnB hnsB hMB hSB hdm hds hdo hdt)).pre ?_).post
      ?_ |>.mono ?_
  · rintro σ ⟨hn, hoff, htgt, hmsk, hsrc, g, hdst⟩
    exact ⟨Fill.below_zero (by rw [arrs_setVar]; exact hdst) (by simp),
      by simpa using hn, by simpa using hoff, by simpa using htgt, hnt, by simpa using hmsk,
      by simpa using hsrc⟩
  · rintro σ σ' - ⟨hinv, hz⟩
    exact ⟨hinv.1.done hz, hz, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.2.1,
      hinv.2.2.2.2.2.2⟩
  · have hpt : ∀ z ∈ Finset.range n,
        (24 * Csr.rowLen O z + 40 + 4) = 24 * Csr.rowLen O z + 44 :=
      fun _ _ => by omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum,
      hcsr.sum_rowLen le_rfl, hcsr.zero, hcsr.last, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
    omega

/-! ### The chain

`RamDriver.chainCom` is `expandCom` iterated, and its walk is an
induction whose step is the equation below: the chain of `r + 1`
expansions is one pass into the first scratch name followed by the
chain of `r` at the shifted family. The ball's chain alternates between
two names (`RamDriver.ballStage`) and the colour chains run through
distinct ones; both are instances of the same recursion, which is why
the family is a parameter. -/

theorem foldRange_succ (f : ℕ → Com) (r : ℕ) :
    foldRange f (r + 1) = .seq (f 0) (foldRange (fun a => f (a + 1)) r) := by
  simp [foldRange, List.range_succ_eq_map, List.foldr_map]

theorem chainCom_zero (msk : String) (nm : ℕ → String) : chainCom msk nm 0 = .skip := rfl

theorem chainCom_succ (msk : String) (nm : ℕ → String) (r : ℕ) :
    chainCom msk nm (r + 1) =
      .seq (expandCom msk (nm 0) (nm 1)) (chainCom msk (fun a => nm (a + 1)) r) := by
  simp [chainCom, foldRange_succ]

theorem chainBlockCom_zero (j : ℕ) (msk : String) (nm : ℕ → String) :
    chainBlockCom j msk nm 0 = .skip := rfl

theorem chainBlockCom_succ (j : ℕ) (msk : String) (nm : ℕ → String) (r : ℕ) :
    chainBlockCom j msk nm (r + 1) =
      .seq (expandBlockCom j msk (nm 0) (nm 1))
        (chainBlockCom j msk (fun a => nm (a + 1)) r) := by
  simp [chainBlockCom, foldRange_succ]

/-- **The radius of a chain that expands first.** The walk peels the
chain from the *front*, so what its induction produces is `r` units of
radius around one neighbourhood step; `nbhd_ballOf` is the same
statement with the step taken last. -/
theorem ballOf_nbhd (A : SimpleGraph (Fin n)) (r : ℕ) (S : Set (Fin n)) :
    ballOf A r (nbhd A S) = ballOf A (r + 1) S := by
  induction r with
  | zero => rw [ballOf_zero, ← nbhd_ballOf, ballOf_zero]
  | succ r ih => rw [← nbhd_ballOf A r, ih, nbhd_ballOf]

/-- A mask is what it marks below the carrier. -/
theorem markSet_congr {f g : ℕ → ℕ} (h : ∀ k, k < n → f k = g k) :
    markSet n f = markSet n g := by
  ext v
  rw [mem_markSet, mem_markSet, h (v : ℕ) v.isLt]

/-- An array that was there is still there: a run cannot change a
length. -/
theorem exists_arrOf_run {B K N : ℕ} {c : Com} {σ σ' : Env} {a : String}
    (hr : Run B c σ σ' K) (h : ∃ g, σ.arrs a = arrOf N g) : ∃ g, σ'.arrs a = arrOf N g :=
  exists_arrOf ((run_length_arrs hr a).trans (by obtain ⟨g, hg⟩ := h; rw [hg, length_arrOf]))

/-- **The chain of expansions, discharged.** After `r` passes the last
name of the family marks the `r`-neighbourhood of what the first one
marked, in the arena the mask cuts out.

A chain that starts at a **bit** array ends at one — one expansion writes
either `1` or the source's own cell.  The driver's batch truncation
multiplies its accumulating indicator by the ball, so this bit bound keeps
that in-place product below the word bound. -/
theorem chainCom_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hMB : ∀ k, k < n → Msk k < B) :
    ∀ (r : ℕ) (nm : ℕ → String) (Sr : ℕ → ℕ), (∀ a, nm a ≠ nm (a + 1)) → (∀ a, nm a ≠ msk) →
      (∀ a, nm a ≠ "off") → (∀ a, nm a ≠ "tgt") → (∀ k, k < n → Sr k ≤ 1) →
      Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
          σ.arrs "tgt" = arrOf nt T ∧ σ.arrs msk = arrOf n Msk ∧
          σ.arrs (nm 0) = arrOf n Sr ∧ (∀ a, 0 < a → a ≤ r → ∃ g, σ.arrs (nm a) = arrOf n g))
        (chainCom msk nm r)
        (fun _ σ' => (∃ g, σ'.arrs (nm r) = arrOf n g ∧ (∀ k, k < n → g k ≤ 1) ∧
            markSet n g = ballOf (masked G Msk) r (markSet n Sr)) ∧
          σ'.vars "n" = n ∧ σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧
          σ'.arrs msk = arrOf n Msk)
        ((24 * ns + 44 * n + 6) * r + 1) := by
  intro r
  induction r with
  | zero =>
    intro nm Sr _ _ _ _ hSB
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hn, hoff, htgt, hmskA, hsrc, -⟩ := hσ
    exact ⟨σ, 1, by rw [chainCom_zero]; exact Run.skip, by omega,
      ⟨Sr, hsrc, hSB, by rw [ballOf_zero]⟩, hn, hoff, htgt, hmskA⟩
  | succ r ih =>
    intro nm Sr hne hmk hof htg hSB
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hn, hoff, htgt, hmskA, hsrc, hmem⟩ := hσ
    obtain ⟨g₁, hg₁⟩ := hmem 1 (by omega) (by omega)
    have hSB' : ∀ k, k < n → Sr k < B := fun k hk => lt_of_le_of_lt (hSB k hk) hB
    obtain ⟨σ₁, hr₁, ⟨g, hgarr, hgval⟩, -, hn₁, hoff₁, htgt₁, hmsk₁, hsrc₁⟩ :=
      (expandCom_spec (dst := nm 1) (src := nm 0) hcsr hB hnB hnsB hnt hMB hSB' (hmk 1)
        (Ne.symm (hne 0)) (hof 1) (htg 1)).run ⟨hn, hoff, htgt, hmskA, hsrc, g₁, hg₁⟩
    have hgB : ∀ k, k < n → g k ≤ 1 := by
      intro k hk
      rw [hgval k hk]
      rcases expandVal_eq_or G Msk Sr k with h | h
      · rw [h]
      · rw [h]; exact hSB k hk
    obtain ⟨σ₂, hr₂, ⟨g', hg'arr, hg'B, hg'mark⟩, hn₂, hoff₂, htgt₂, hmsk₂⟩ :=
      (ih (fun a => nm (a + 1)) g (fun a => hne (a + 1)) (fun a => hmk (a + 1))
        (fun a => hof (a + 1)) (fun a => htg (a + 1)) hgB).run
        ⟨hn₁, hoff₁, htgt₁, hmsk₁, hgarr,
          fun a _ ha => exists_arrOf_run hr₁ (hmem (a + 1) (by omega) (by omega))⟩
    refine ⟨σ₂, _, by rw [chainCom_succ]; exact hr₁.seq hr₂, by ring_nf; omega,
      ⟨g', hg'arr, hg'B, ?_⟩, hn₂, hoff₂, htgt₂, hmsk₂⟩
    rw [hg'mark, markSet_congr hgval, markSet_expandVal, ballOf_nbhd]

/-- A supported array crosses a command that does not write its name. -/
theorem exists_blockSupported_run {B K : ℕ} {cmd : Com} {σ σ' : Env} {a : String}
    (hr : Run B cmd σ σ' K) (ha : a ∉ cmd.warrs)
    (h : ∃ F, σ.arrs a = arrOf n F ∧ BlockSupported n p₀ e Idx F) :
    ∃ F, σ'.arrs a = arrOf n F ∧ BlockSupported n p₀ e Idx F := by
  obtain ⟨F, hF, hsup⟩ := h
  exact ⟨F, by rw [hr.frame_arr a ha, hF], hsup⟩

/-- **A radius chain over one cover block.**  This is the compositional
counterpart of `chainCom_spec`: every destination is supported on entry,
and `expandBlockCom_supported_spec` proves that the stage both computes the
same neighbourhood and preserves that support for later stages (including
the alternating two-array ball chain). -/
theorem chainBlockCom_spec {B w m c j : ℕ} (hcsr : CsrGraph G ns O T)
    (hc : c < n) (hmB : m < B) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hMB : ∀ k, k < n → Msk k < B) :
    ∀ (r : ℕ) (nm : ℕ → String) (Sr : ℕ → ℕ),
      (∀ a, nm a ≠ nm (a + 1)) →
      (∀ a, nm a ≠ msk) → (∀ a, nm a ≠ xofName j) →
      (∀ a, nm a ≠ xmmName j) →
      (∀ a, nm a ≠ "off") → (∀ a, nm a ≠ "tgt") →
      (∀ k, k < n → Sr k ≤ 1) →
      BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem Msk →
      BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem Sr →
      Spec B
        (fun σ => CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ ∧
          σ.vars (curName j) = c ∧ σ.vars "n" = n ∧
          σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
          σ.arrs msk = arrOf n Msk ∧ σ.arrs (nm 0) = arrOf n Sr ∧
          (∀ a, 0 < a → a ≤ r → ∃ F, σ.arrs (nm a) = arrOf n F ∧
            BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem F))
        (chainBlockCom j msk nm r)
        (fun _ σ' =>
          (∃ F, σ'.arrs (nm r) = arrOf n F ∧
            (∀ k, k < n → F k ≤ 1) ∧
            markSet n F = ballOf (masked G Msk) r (markSet n Sr) ∧
            BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem F) ∧
          CsrWide.CsrW (xofName j) (xmmName j) n m w n Xoff Xmem σ' ∧
          σ'.vars (curName j) = c ∧ σ'.vars "n" = n ∧
          σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧
          σ'.arrs msk = arrOf n Msk)
        ((51 * blockSize Xoff c +
          24 * Refine.MassWeight.blockRowSum O Xoff Xmem c + 12) * r + 1) := by
  intro r
  induction r with
  | zero =>
    intro nm Sr _ _ _ _ _ _ hSB hM hS
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hcov, hcur, hn, hoff, htgt, hmskA, hsrc, -⟩ := hσ
    exact ⟨σ, 1, by rw [chainBlockCom_zero]; exact Run.skip, by omega,
      ⟨Sr, hsrc, hSB, by rw [ballOf_zero], hS⟩, hcov, hcur, hn, hoff, htgt, hmskA⟩
  | succ r ih =>
    intro nm Sr hne hmk hxo hxm hof htg hSB hM hS
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hcov, hcur, hn, hoff, htgt, hmskA, hsrc, hmem⟩ := hσ
    obtain ⟨A₁, hA₁, hA₁sup⟩ := hmem 1 (by omega) (by omega)
    have hSrB : ∀ k, k < n → Sr k < B :=
      fun k hk => lt_of_le_of_lt (hSB k hk) hB
    obtain ⟨σ₁, hr₁, hcov₁, hcur₁, hn₁, hoff₁, htgt₁, hnt₁,
      hmsk₁, hsrc₁, F, hF, hFval, hFsup⟩ :=
      (expandBlockCom_supported_spec (A₀ := A₁) (dst := nm 1) (src := nm 0)
        hcsr hc hmB hB hnB hnsB hMB hSrB (hxo 1) (hxm 1) (hmk 1)
        (Ne.symm (hne 0)) (hof 1) (htg 1)).run
        ⟨hcov, hcur, hn, hoff, htgt, hnt, hmskA, hsrc, hA₁, hM, hS, hA₁sup⟩
    have hFB : ∀ k, k < n → F k ≤ 1 := by
      intro k hk
      rw [hFval k hk]
      rcases expandVal_eq_or G Msk Sr k with h | h
      · rw [h]
      · rw [h]
        exact hSB k hk
    have hfuture : ∀ a, 0 < a → a ≤ r →
        ∃ A, σ₁.arrs (nm (a + 1)) = arrOf n A ∧
          BlockSupported n (Xoff c) (Xoff (c + 1)) Xmem A := by
      intro a ha har
      by_cases heq : nm (a + 1) = nm 1
      · exact ⟨F, by rw [heq]; exact hF, hFsup⟩
      · apply exists_blockSupported_run hr₁
        · simpa [expandBlockCom, expandBlockLoop, expandStep, expandSlot, Csr.loadRow,
            Csr.scan, Com.warrs] using heq
        · exact hmem (a + 1) (by omega) (by omega)
    obtain ⟨σ₂, hr₂, ⟨F', hF', hF'B, hF'mark, hF'sup⟩,
      hcov₂, hcur₂, hn₂, hoff₂, htgt₂, hmsk₂⟩ :=
      (ih (fun a => nm (a + 1)) F (fun a => hne (a + 1))
        (fun a => hmk (a + 1)) (fun a => hxo (a + 1)) (fun a => hxm (a + 1))
        (fun a => hof (a + 1)) (fun a => htg (a + 1)) hFB hM hFsup).run
        ⟨hcov₁, hcur₁, hn₁, hoff₁, htgt₁, hmsk₁, hF, hfuture⟩
    refine ⟨σ₂, _, by rw [chainBlockCom_succ]; exact hr₁.seq hr₂, ?_,
      ⟨F', hF', hF'B, ?_, hF'sup⟩, hcov₂, hcur₂, hn₂, hoff₂, htgt₂,
      hmsk₂⟩
    · ring_nf
      omega
    · rw [hF'mark, markSet_congr hFval, markSet_expandVal, ballOf_nbhd]

/-- A chain of `r` block expansions spends `r` copies of the block-weight
slot, plus the fold's terminal skip. -/
theorem chainBlockCost_le_weight (r : ℕ) (hcsr : RamElim.CsrSimple G ns O T)
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    (51 * blockSize Xoff c +
        24 * Refine.MassWeight.blockRowSum O Xoff Xmem c + 12) * r + 1 ≤
      200 * r * (Refine.MassWeight.blockWeight n G Xoff Xmem c + 1) + 1 := by
  calc
    _ ≤ (200 * (Refine.MassWeight.blockWeight n G Xoff Xmem c + 1)) * r + 1 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_right r (expandBlockCost_le_weight hcsr hmem)) 1
    _ = _ := by ring

end Expand

/-! ### The colour arrays of the next depth, addressed

`RamDriver.colourCom` writes one array per slot of the depth-`(j+1)`
palette, and every one of the three families addresses it by the
*numeric value* of the slot. So the first thing a walk over the phase
owes is that those numbers are pairwise distinct — a pass that wrote a
slot has to still hold it when the phase ends — and that is the
arithmetic of `Evaluator.slotOld`, `slotPd` and `slotPu`: the palette is
`Fin.castAdd`, `Fin.natAdd ∘ Fin.castAdd` and `Fin.natAdd ∘ Fin.natAdd`
of three blocks, so the three families occupy three intervals and each
is injective inside its own. -/

section Slots

/-- **The colour arrays are addressed injectively**: the depth and the
slot are both recoverable from the name. -/
theorem colName_inj {j c j' c' : ℕ} (h : colName j c = colName j' c') : j = j' ∧ c = c' := by
  simp only [colName, String.ext_iff] at h
  simp at h
  obtain ⟨h1, h2⟩ := RamDriverBase.append_cons_inj
    (RamDriverBase.underscore_not_mem_toDigits j)
    (RamDriverBase.underscore_not_mem_toDigits j') h
  exact ⟨RamDriverBase.toDigits_injective h1, RamDriverBase.toDigits_injective h2⟩

/-- Two colour arrays of different depths are different arrays. -/
theorem colName_ne_depth {j j' c c' : ℕ} (h : j ≠ j') : colName j c ≠ colName j' c' :=
  fun hc => h (colName_inj hc).1

/-- Two colour arrays at different slots of one depth are different. -/
theorem colName_ne_slot {j c c' : ℕ} (h : c ≠ c') : colName j c ≠ colName j c' :=
  fun hc => h (colName_inj hc).2

/-- A colour array is none of the driver's per-depth prefixed names,
since those carry no separator and every colour name has one. -/
theorem colName_ne_prefixed {j c : ℕ} {p : String} (hp : '_' ∉ p.toList) (k : ℕ) :
    colName j c ≠ p ++ toString k :=
  fun he => RamDriverFrames.underscore_notMem_prefixed hp k
    (he ▸ RamDriverFrames.underscore_mem_colName j c)

/-- And none of the fixed literals. -/
theorem colName_ne_lit {j c : ℕ} {q : String} (h : '_' ∉ q.toList) : colName j c ≠ q :=
  fun he => h (he ▸ RamDriverFrames.underscore_mem_colName j c)

theorem colName_ne_cluName (j c d : ℕ) : colName j c ≠ cluName d := by
  rw [cluName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_resName (j c d : ℕ) : colName j c ≠ resName d := by
  rw [resName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_batName (j c d : ℕ) : colName j c ≠ batName d := by
  rw [batName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_alvName (j c d : ℕ) : colName j c ≠ alvName d := by
  rw [alvName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_gamName (j c d : ℕ) : colName j c ≠ gamName d := by
  rw [gamName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_memName (j c d : ℕ) : colName j c ≠ memName d := by
  rw [memName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_ordName (j c d : ℕ) : colName j c ≠ ordName d := by
  rw [ordName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_xofName (j c d : ℕ) : colName j c ≠ xofName d := by
  rw [xofName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_xmmName (j c d : ℕ) : colName j c ≠ xmmName d := by
  rw [xmmName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_asgName (j c d : ℕ) : colName j c ≠ asgName d := by
  rw [asgName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_balName (j c d : ℕ) : colName j c ≠ balName d := by
  rw [balName]; exact colName_ne_prefixed (by decide) d

theorem colName_ne_balAltName (j c d : ℕ) : colName j c ≠ balAltName d := by
  rw [balAltName]; exact colName_ne_prefixed (by decide) d

/-! The three intervals of the palette. `sigL cap mb (j + 1)` is
`(sigL cap mb j + 1) + (mb * (cap + 1) + (sigL cap mb j + 1) * (cap + 1))`
by definition, and the three slot maps land in the three summands. -/

variable {cap mb j : ℕ}

/-- **An old slot is its own colour**: `Evaluator.slotOld` is
`Fin.castAdd`, whose value is the index it was given. -/
theorem oldIdx_eq {c : ℕ} (hc : c ≤ sigL cap mb j) : oldIdx cap mb j c = c := by
  rw [oldIdx, oldSlots, Evaluator.slotOld]
  simp [Nat.min_eq_left hc]

theorem oldIdx_lt (c : ℕ) : oldIdx cap mb j c < sigL cap mb j + 1 := by
  rw [oldIdx, oldSlots, Evaluator.slotOld]
  simp only [Fin.val_castAdd]
  omega

/-- The batch profiles sit above the old block. -/
theorem le_pdIdx (i : Fin mb) (a : ℕ) : sigL cap mb j + 1 ≤ pdIdx cap mb j i a := by
  rw [pdIdx, pdSlots, Evaluator.slotPd]
  simp only [Fin.val_natAdd]
  omega

theorem pdIdx_lt (i : Fin mb) (a : ℕ) :
    pdIdx cap mb j i a < sigL cap mb j + 1 + mb * (cap + 1) := by
  rw [pdIdx, pdSlots, Evaluator.slotPd]
  simp only [Fin.val_natAdd, Fin.val_castAdd]
  have := (finProdFinEquiv (i, (⟨min a cap, by omega⟩ : Fin (cap + 1)))).isLt
  omega

/-- And the colour profiles above both. -/
theorem le_puIdx (c b : ℕ) :
    sigL cap mb j + 1 + mb * (cap + 1) ≤ puIdx cap mb j c b := by
  rw [puIdx, puSlots, Evaluator.slotPu]
  simp only [Fin.val_natAdd]
  omega

/-- Every slot the phase addresses is a slot of the palette. -/
theorem oldIdx_lt_sigL (c : ℕ) : oldIdx cap mb j c < sigL cap mb (j + 1) :=
  (oldSlots cap mb j ⟨min c (sigL cap mb j), by omega⟩).isLt

theorem pdIdx_lt_sigL (i : Fin mb) (a : ℕ) : pdIdx cap mb j i a < sigL cap mb (j + 1) :=
  (pdSlots cap mb j i ⟨min a cap, by omega⟩).isLt

theorem puIdx_lt_sigL (c b : ℕ) : puIdx cap mb j c b < sigL cap mb (j + 1) :=
  (puSlots cap mb j ⟨min c (sigL cap mb j), by omega⟩ ⟨min b cap, by omega⟩).isLt

/-- The three families are pairwise disjoint. -/
theorem oldIdx_ne_pdIdx (c : ℕ) (i : Fin mb) (a : ℕ) :
    oldIdx cap mb j c ≠ pdIdx cap mb j i a := by
  have h₁ := oldIdx_lt (cap := cap) (mb := mb) (j := j) c
  have h₂ := le_pdIdx (cap := cap) (mb := mb) (j := j) i a
  omega

theorem oldIdx_ne_puIdx (c c' b : ℕ) : oldIdx cap mb j c ≠ puIdx cap mb j c' b := by
  have h₁ := oldIdx_lt (cap := cap) (mb := mb) (j := j) c
  have h₂ := le_puIdx (cap := cap) (mb := mb) (j := j) c' b
  omega

theorem pdIdx_ne_puIdx (i : Fin mb) (a c' b : ℕ) :
    pdIdx cap mb j i a ≠ puIdx cap mb j c' b := by
  have h₁ := pdIdx_lt (cap := cap) (mb := mb) (j := j) i a
  have h₂ := le_puIdx (cap := cap) (mb := mb) (j := j) c' b
  omega

/-- Inside a family the addressing is injective, up to the capping the
program text does. -/
theorem oldIdx_inj {c c' : ℕ} (hc : c ≤ sigL cap mb j) (hc' : c' ≤ sigL cap mb j)
    (h : oldIdx cap mb j c = oldIdx cap mb j c') : c = c' := by
  rwa [oldIdx_eq hc, oldIdx_eq hc'] at h

theorem pdIdx_inj {i i' : Fin mb} {a a' : ℕ} (ha : a ≤ cap) (ha' : a' ≤ cap)
    (h : pdIdx cap mb j i a = pdIdx cap mb j i' a') : i = i' ∧ a = a' := by
  rw [pdIdx, pdIdx, pdSlots, Evaluator.slotPd, Evaluator.slotPd] at h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h
  have h' : finProdFinEquiv (i, (⟨min a cap, by omega⟩ : Fin (cap + 1))) =
      finProdFinEquiv (i', (⟨min a' cap, by omega⟩ : Fin (cap + 1))) := Fin.ext (by omega)
  have h'' := finProdFinEquiv.injective h'
  rw [Prod.ext_iff] at h''
  refine ⟨h''.1, ?_⟩
  have := congrArg Fin.val h''.2
  simp only [Nat.min_eq_left ha, Nat.min_eq_left ha'] at this
  exact this

theorem puIdx_inj {c c' b b' : ℕ} (hc : c ≤ sigL cap mb j) (hc' : c' ≤ sigL cap mb j)
    (hb : b ≤ cap) (hb' : b' ≤ cap) (h : puIdx cap mb j c b = puIdx cap mb j c' b') :
    c = c' ∧ b = b' := by
  rw [puIdx, puIdx, puSlots, Evaluator.slotPu, Evaluator.slotPu] at h
  simp only [Fin.val_natAdd] at h
  have h' : finProdFinEquiv ((⟨min c (sigL cap mb j), by omega⟩ : Fin (sigL cap mb j + 1)),
        (⟨min b cap, by omega⟩ : Fin (cap + 1))) =
      finProdFinEquiv ((⟨min c' (sigL cap mb j), by omega⟩ : Fin (sigL cap mb j + 1)),
        (⟨min b' cap, by omega⟩ : Fin (cap + 1))) := Fin.ext (by omega)
  have h'' := finProdFinEquiv.injective h'
  rw [Prod.ext_iff] at h''
  have h1 := congrArg Fin.val h''.1
  have h2 := congrArg Fin.val h''.2
  simp only [Nat.min_eq_left hc, Nat.min_eq_left hc'] at h1
  simp only [Nat.min_eq_left hb, Nat.min_eq_left hb'] at h2
  exact ⟨h1, h2⟩

end Slots

/-! ### The chain, stage by stage

`chainCom_spec` above says what the *last* name of a chain holds, which
is all the ball of the descent needs: its family alternates between two
arrays, so nothing else survives. The colouring's three chains run
through pairwise distinct names, and every stage of them is a slot of
the palette — so what the colouring needs is that all of them are still
there when the chain ends, and that they are bits. -/

section Stages

variable {ns nt : ℕ} {G : SimpleGraph (Fin n)} {O T Msk : ℕ → ℕ} {msk : String}

/-- **The chain of expansions, every stage at once.** With the names of
the family pairwise distinct, `nm a` marks the `a`-neighbourhood of what
`nm 0` marked, for every `a ≤ r` together; and a chain that starts at a
bit array stays one, since one expansion writes either `1` or the
source's own cell. -/
theorem chainCom_stages {B : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hMB : ∀ k, k < n → Msk k < B) :
    ∀ (r : ℕ) (nm : ℕ → String) (Sr : ℕ → ℕ),
      (∀ a b, a ≤ r → b ≤ r → a ≠ b → nm a ≠ nm b) → (∀ a, a ≤ r → nm a ≠ msk) →
      (∀ a, a ≤ r → nm a ≠ "off") → (∀ a, a ≤ r → nm a ≠ "tgt") →
      (∀ k, k < n → Sr k ≤ 1) →
      Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
          σ.arrs "tgt" = arrOf nt T ∧ σ.arrs msk = arrOf n Msk ∧
          σ.arrs (nm 0) = arrOf n Sr ∧ (∀ a, 0 < a → a ≤ r → ∃ g, σ.arrs (nm a) = arrOf n g))
        (chainCom msk nm r)
        (fun _ σ' => (∀ a, a ≤ r → ∃ g, σ'.arrs (nm a) = arrOf n g ∧ (∀ k, k < n → g k ≤ 1) ∧
            markSet n g = ballOf (masked G Msk) a (markSet n Sr)) ∧
          σ'.vars "n" = n ∧ σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧
          σ'.arrs msk = arrOf n Msk)
        ((24 * ns + 44 * n + 6) * r + 1) := by
  intro r
  induction r with
  | zero =>
    intro nm Sr _ _ _ _ hSB
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hn, hoff, htgt, hmskA, hsrc, -⟩ := hσ
    refine ⟨σ, 1, by rw [chainCom_zero]; exact Run.skip, by omega, ?_, hn, hoff, htgt, hmskA⟩
    intro a ha
    have : a = 0 := by omega
    subst this
    exact ⟨Sr, hsrc, hSB, by rw [ballOf_zero]⟩
  | succ r ih =>
    intro nm Sr hne hmk hof htg hSB
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hn, hoff, htgt, hmskA, hsrc, hmem⟩ := hσ
    have hSB' : ∀ k, k < n → Sr k < B := fun k hk => lt_of_le_of_lt (hSB k hk) hB
    obtain ⟨g₁, hg₁⟩ := hmem 1 (by omega) (by omega)
    obtain ⟨σ₁, hr₁, ⟨⟨g, hgarr, hgval⟩, -, hn₁, hoff₁, htgt₁, hmsk₁, hsrc₁⟩, -, -, -, -⟩ :=
      ((expandCom_spec (dst := nm 1) (src := nm 0) hcsr hB hnB hnsB hnt hMB hSB'
        (hmk 1 (by omega)) (Ne.symm (hne 0 1 (by omega) (by omega) (by omega)))
        (hof 1 (by omega)) (htg 1 (by omega))).frame).run ⟨hn, hoff, htgt, hmskA, hsrc, g₁, hg₁⟩
    have hgbit : ∀ k, k < n → g k ≤ 1 := by
      intro k hk
      rw [hgval k hk]
      rcases expandVal_eq_or G Msk Sr k with h | h
      · rw [h]
      · rw [h]; exact hSB k hk
    obtain ⟨σ₂, hr₂, ⟨hstage, hn₂, hoff₂, htgt₂, hmsk₂⟩, -, hfa₂, -, -⟩ :=
      ((ih (fun a => nm (a + 1)) g
        (fun a b ha hb hab => hne (a + 1) (b + 1) (by omega) (by omega) (by omega))
        (fun a ha => hmk (a + 1) (by omega)) (fun a ha => hof (a + 1) (by omega))
        (fun a ha => htg (a + 1) (by omega)) hgbit).frame).run
        ⟨hn₁, hoff₁, htgt₁, hmsk₁, hgarr,
          fun a _ ha => exists_arrOf_run hr₁ (hmem (a + 1) (by omega) (by omega))⟩
    have hzero : σ₂.arrs (nm 0) = arrOf n Sr := by
      rw [hfa₂ (nm 0) ?_, hsrc₁]
      intro hc
      obtain ⟨b, hb, hbe⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ hc
      exact hne 0 (b + 2) (by omega) (by omega) (by omega) hbe
    refine ⟨σ₂, _, by rw [chainCom_succ]; exact hr₁.seq hr₂, by ring_nf; omega,
      ?_, hn₂, hoff₂, htgt₂, hmsk₂⟩
    intro a ha
    match a with
    | 0 => exact ⟨Sr, hzero, hSB, by rw [ballOf_zero]⟩
    | a + 1 =>
      obtain ⟨g', hg'arr, hg'bit, hg'mark⟩ := hstage a (by omega)
      refine ⟨g', hg'arr, hg'bit, ?_⟩
      rw [hg'mark, markSet_congr hgval, markSet_expandVal, ballOf_nbhd]

end Stages

/-! ### A fold of independent passes

Each of the colouring's three families is a fold of one pass per member,
and the members write disjoint sets of arrays: what one wrote is still
there when the fold ends. This is that argument once, over any list —
`RamDriver.foldRange` is the fold over `List.range` and the batch
profiles fold over `List.finRange`, and both are instances. -/

section Fold

/-- **A fold of passes that do not interfere.** Every member preserves
the phase's invariant `I` and leaves its own conclusion `R x`; a member
writes only arrays its own `Wr x` admits, and `R x` speaks only about
those. So the fold leaves every member's conclusion at once. -/
theorem foldr_family_spec {X : Type*} {B : ℕ} {body : X → Com} {I : Env → Prop}
    {R : X → Env → Prop} {Wr : X → String → Prop} {Kb : ℕ}
    (hwr : ∀ x, ∀ a ∈ (body x).warrs, Wr x a)
    (hstab : ∀ (x : X) (σ σ' : Env), R x σ → (∀ a, Wr x a → σ'.arrs a = σ.arrs a) → R x σ') :
    ∀ l : List X, l.Nodup → (∀ x ∈ l, Spec B I (body x) (fun _ σ' => I σ' ∧ R x σ') Kb) →
      (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ a, Wr x a → Wr y a → False) →
      Spec B I (l.foldr (fun x c => Com.seq (body x) c) .skip)
        (fun _ σ' => I σ' ∧ ∀ x ∈ l, R x σ') (Kb * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ _ _
    exact Spec.of_exists (fun σ hσ => ⟨σ, 1, Run.skip, by simp, hσ, by simp⟩)
  | cons x xs ih =>
    intro hnd hbody hdis
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨σ₁, hr₁, ⟨hI₁, hR₁⟩, -, -, -, -⟩ := ((hbody x (by simp)).frame).run hσ
    obtain ⟨σ₂, hr₂, ⟨hI₂, hR₂⟩, -, hfa₂, -, -⟩ :=
      ((ih hnd.of_cons (fun y hy => hbody y (by simp [hy]))
        (fun y hy z hz hyz => hdis y (by simp [hy]) z (by simp [hz]) hyz)).frame).run
        hI₁
    refine ⟨σ₂, _, hr₁.seq hr₂, by simp [List.length_cons]; ring_nf; omega, hI₂, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · refine hstab y σ₁ σ₂ hR₁ (fun a hax => hfa₂ a ?_)
      intro hc
      obtain ⟨z, hz, hzm⟩ := RamDriverFrames.mem_warrs_foldr body xs hc
      exact hdis y (by simp) z (by simp [hz]) (fun he => (List.nodup_cons.mp hnd).1 (he ▸ hz))
        a hax (hwr z a hzm)
    · exact hR₂ y hy'

end Fold

/-! ### The colouring of the next depth

`RamDriver.colourCom` is three folds — one per slot family of
`Lax3Proofs.FormulaTables` — and every member of every fold writes one
array of the depth-`(j+1)` palette and reads only what `ColPre` names.
So the phase is `foldr_family_spec` three times, at the three bodies
`RamDriverCluster.andCom_spec`/`copyCom_spec`, `fillCom_spec` followed
by a store followed by `chainCom_stages`, and `copyCom_spec` followed by
`chainCom_stages`. -/

section Colour

variable {B cap mb ns nt j : ℕ} {G : SimpleGraph (Fin n)} {O T C' : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
  {Xa Ra Wf : ℕ → ℕ}

/-- The arrays the three families write, off their syntax. -/
theorem mem_warrs_oldCom {a : String} (h : a ∈ (oldCom cap mb j).warrs) :
    ∃ c, a = colName (j + 1) (oldIdx cap mb j c) := by
  simp only [oldCom, Com.warrs, List.mem_append, RamDriverIO.copyCom_eq,
    RamDriverIO.warrs_fillCom, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | rfl
  · obtain ⟨b, -, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ _ h
    rw [RamDriverFrames.warrs_andCom] at hm
    exact ⟨b, List.eq_of_mem_singleton hm⟩
  · exact ⟨sigL cap mb j, rfl⟩

theorem mem_warrs_pdCom {a : String} (h : a ∈ (pdCom cap mb j).warrs) :
    ∃ (i : Fin mb) (b : ℕ), a = colName (j + 1) (pdIdx cap mb j i b) := by
  obtain ⟨i, -, hm⟩ := RamDriverFrames.mem_warrs_foldr _ (List.finRange mb) h
  simp only [Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    RamDriverIO.warrs_fillCom] at hm
  rcases hm with rfl | rfl | hm
  · exact ⟨i, 0, rfl⟩
  · exact ⟨i, 0, rfl⟩
  · obtain ⟨b, -, rfl⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ hm
    exact ⟨i, b + 1, rfl⟩

theorem mem_warrs_puCom {a : String} (h : a ∈ (puCom cap mb j).warrs) :
    ∃ c b, a = colName (j + 1) (puIdx cap mb j c b) := by
  obtain ⟨c, -, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ _ h
  simp only [Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom] at hm
  rcases hm with rfl | hm
  · exact ⟨c, 0, rfl⟩
  · obtain ⟨b, -, rfl⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ hm
    exact ⟨c, b + 1, rfl⟩

/-- **What the colouring reads.** The block structure, the depth's own
palette, the cluster indicator the old slots are cut by and the
cluster-restricted mask the two chains run in, the padded enumeration
the batch profiles are centred at, and the memory of the palette being
written. -/
def ColPre (n cap mb nt j : ℕ) (O T : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (Xa Ra Wf : ℕ → ℕ)
    (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
    σ.arrs (cluName j) = arrOf n Xa ∧ σ.arrs (resName j) = arrOf n Ra ∧
    (∀ c, c < sigL cap mb j → σ.arrs (colName j c) = arrOf n (C c)) ∧
    σ.arrs "wa" = arrOf mb Wf ∧
    ∀ s, s < sigL cap mb (j + 1) → ∃ g, σ.arrs (colName (j + 1) s) = arrOf n g

/-- **It survives every pass of the phase**, since each of them writes
colours of the next depth alone and none of the arrays it names is
one. -/
theorem colPre_run {K : ℕ} {c : Com} {σ σ' : Env}
    (h : ColPre n cap mb nt j O T C Xa Ra Wf σ) (hr : Run B c σ σ' K)
    (hw : ∀ a ∈ c.warrs, ∃ s, a = colName (j + 1) s) (hn : σ'.vars "n" = σ.vars "n") :
    ColPre n cap mb nt j O T C Xa Ra Wf σ' := by
  have key : ∀ a : String, (∀ s, a ≠ colName (j + 1) s) → σ'.arrs a = σ.arrs a := by
    intro a ha
    refine hr.frame_arr a (fun hc => ?_)
    obtain ⟨s, hs⟩ := hw a hc
    exact ha s hs
  obtain ⟨hnv, hoff, htgt, hclu, hres, hcol, hwa, hmem⟩ := h
  refine ⟨by rw [hn]; exact hnv,
    by rw [key "off" (fun s => Ne.symm (colName_ne_lit (by decide)))]; exact hoff,
    by rw [key "tgt" (fun s => Ne.symm (colName_ne_lit (by decide)))]; exact htgt,
    by rw [key _ (fun s => Ne.symm (colName_ne_cluName _ _ _))]; exact hclu,
    by rw [key _ (fun s => Ne.symm (colName_ne_resName _ _ _))]; exact hres,
    fun c hc => by rw [key _ (fun s => colName_ne_depth (by omega))]; exact hcol c hc,
    by rw [key "wa" (fun s => Ne.symm (colName_ne_lit (by decide)))]; exact hwa,
    fun s hs => exists_arrOf_run hr (hmem s hs)⟩

/-- The set a pointwise product marks. -/
theorem markSet_mul {f g : ℕ → ℕ} : markSet n (fun k => f k * g k) = markSet n f ∩ markSet n g := by
  ext v
  simp only [mem_markSet, Set.mem_inter_iff, ne_eq, Nat.mul_eq_zero, not_or]

/-! #### The relativized colours -/

/-- **One old slot.** The depth's colour, cut down to the cluster. -/
theorem oldBody_spec {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hCbit : ∀ c, c < sigL cap mb j → ∀ v, v < n → C c v ≤ 1)
    (hXbit : ∀ v, v < n → Xa v ≤ 1) {c : ℕ} (hc : c < sigL cap mb j) :
    Spec B (ColPre n cap mb nt j O T C Xa Ra Wf)
      (andCom (colName j c) (cluName j) (colName (j + 1) (oldIdx cap mb j c)))
      (fun _ σ' => ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧
        ∃ g, σ'.arrs (colName (j + 1) (oldIdx cap mb j c)) = arrOf n g ∧
          (∀ v, v < n → g v ≤ 1) ∧ markSet n g = markSet n (C c) ∩ markSet n Xa)
      (15 * n + 6) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  have hcol := hσ.2.2.2.2.2.1 c hc
  have hclu := hσ.2.2.2.1
  obtain ⟨g₀, hg₀⟩ := hσ.2.2.2.2.2.2.2 _ (oldIdx_lt_sigL c)
  obtain ⟨σ', hr, ⟨⟨g, hgarr, hgval⟩, -, hn', -, -⟩, -, -, -, -⟩ :=
    ((andCom_spec B n (colName j c) (cluName j) (colName (j + 1) (oldIdx cap mb j c))
      (C c) Xa (colName_ne_depth (by omega)) (colName_ne_cluName _ _ _).symm hB.n_lt
      (fun k hk => lt_of_le_of_lt (hCbit c hc k hk) hB.one_lt)
      (fun k hk => lt_of_le_of_lt (hXbit k hk) hB.one_lt)
      (fun k hk => by
        have h1 := hCbit c hc k hk
        have h2 := hXbit k hk
        have : C c k * Xa k ≤ 1 := by
          rcases Nat.eq_zero_or_pos (C c k) with h | h
          · simp [h]
          · have : C c k = 1 := by omega
            rw [this, one_mul]; exact h2
        exact lt_of_le_of_lt this hB.one_lt)).frame).run
      ⟨⟨g₀, hg₀⟩, hσ.1, hcol, hclu⟩
  refine ⟨σ', _, hr, le_rfl,
    colPre_run hσ hr (fun a ha => ⟨oldIdx cap mb j c, by
      rw [RamDriverFrames.warrs_andCom] at ha; exact List.eq_of_mem_singleton ha⟩)
      (by rw [hn', hσ.1]), g, hgarr, ?_, ?_⟩
  · intro v hv
    rw [hgval v hv]
    have h1 := hCbit c hc v hv
    have h2 := hXbit v hv
    rcases Nat.eq_zero_or_pos (C c v) with h | h
    · simp [h]
    · have : C c v = 1 := by omega
      rw [this, one_mul]; exact h2
  · rw [markSet_congr hgval, markSet_mul]

/-- **The marker slot.** The cluster itself. -/
theorem oldLast_spec {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hXbit : ∀ v, v < n → Xa v ≤ 1) :
    Spec B (ColPre n cap mb nt j O T C Xa Ra Wf)
      (copyCom (cluName j) (colName (j + 1) (oldIdx cap mb j (sigL cap mb j))))
      (fun _ σ' => ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧
        ∃ g, σ'.arrs (colName (j + 1) (oldIdx cap mb j (sigL cap mb j))) = arrOf n g ∧
          (∀ v, v < n → g v ≤ 1) ∧ markSet n g = markSet n Xa)
      (12 * n + 6) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨g₀, hg₀⟩ := hσ.2.2.2.2.2.2.2 _ (oldIdx_lt_sigL (sigL cap mb j))
  obtain ⟨σ', hr, ⟨⟨g, hgarr, hgval⟩, -, hn', -⟩, -, -, -, -⟩ :=
    ((copyCom_spec B n n (cluName j) (colName (j + 1) (oldIdx cap mb j (sigL cap mb j))) Xa
      (colName_ne_cluName _ _ _).symm hB.n_lt le_rfl
      (fun k hk => lt_of_le_of_lt (hXbit k hk) hB.one_lt)).frame).run
      ⟨⟨g₀, hg₀⟩, hσ.1, hσ.2.2.2.1⟩
  refine ⟨σ', _, hr, le_rfl,
    colPre_run hσ hr (fun a ha => ⟨oldIdx cap mb j (sigL cap mb j), by
      rw [RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom] at ha
      exact List.eq_of_mem_singleton ha⟩) (by rw [hn', hσ.1]),
    g, hgarr, fun v hv => by rw [hgval v hv]; exact hXbit v hv,
    markSet_congr hgval⟩

/-- **The relativized palette, discharged.** Every incoming colour cut
down to the cluster, and the cluster itself in the marker slot: this is
`Evaluator.relColoring` of the depth's own colouring, read off the
arrays the old family wrote. -/
theorem oldCom_spec {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hCbit : ∀ c, c < sigL cap mb j → ∀ v, v < n → C c v ≤ 1)
    (hXbit : ∀ v, v < n → Xa v ≤ 1) :
    Spec B (ColPre n cap mb nt j O T C Xa Ra Wf) (oldCom cap mb j)
      (fun _ σ' => ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧
        ∀ c : Fin (sigL cap mb j + 1), ∃ g,
          σ'.arrs (colName (j + 1) (oldIdx cap mb j (c : ℕ))) = arrOf n g ∧
          (∀ v, v < n → g v ≤ 1) ∧
          markSet n g = Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa) c)
      ((15 * n + 6) * sigL cap mb j + 1 + (12 * n + 6)) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨σ₁, hr₁, ⟨hI₁, hR₁⟩, -, -, -, -⟩ :=
    ((foldr_family_spec
      (body := fun c => andCom (colName j c) (cluName j) (colName (j + 1) (oldIdx cap mb j c)))
      (I := ColPre n cap mb nt j O T C Xa Ra Wf)
      (R := fun c σ => ∃ g, σ.arrs (colName (j + 1) (oldIdx cap mb j c)) = arrOf n g ∧
        (∀ v, v < n → g v ≤ 1) ∧ markSet n g = markSet n (C c) ∩ markSet n Xa)
      (Wr := fun c a => a = colName (j + 1) (oldIdx cap mb j c)) (Kb := 15 * n + 6)
      (fun _ a ha => by rw [RamDriverFrames.warrs_andCom] at ha; exact List.eq_of_mem_singleton ha)
      (fun _ _ _ hR hfr => by
        obtain ⟨g, h1, h2, h3⟩ := hR
        exact ⟨g, by rw [hfr _ rfl]; exact h1, h2, h3⟩)
      (List.range (sigL cap mb j)) (List.nodup_range)
      (fun x hx => oldBody_spec hB hCbit hXbit (List.mem_range.mp hx))
      (fun x hx y hy hxy a hax hay => hxy (oldIdx_inj
        (le_of_lt (List.mem_range.mp hx)) (le_of_lt (List.mem_range.mp hy))
        (colName_inj (hax ▸ hay : colName (j + 1) (oldIdx cap mb j x) =
          colName (j + 1) (oldIdx cap mb j y))).2))).frame).run hσ
  obtain ⟨σ₂, hr₂, ⟨hI₂, hlast⟩, -, hfa₂, -, -⟩ := ((oldLast_spec hB hXbit).frame).run hI₁
  refine ⟨σ₂, _, hr₁.seq hr₂, by simp only [List.length_range]; omega, hI₂, ?_⟩
  intro c
  refine Fin.lastCases ?_ ?_ c
  · obtain ⟨g, h1, h2, h3⟩ := hlast
    exact ⟨g, h1, h2, by rw [h3, Evaluator.relColoring_last]⟩
  · intro c₀
    obtain ⟨g, h1, h2, h3⟩ := hR₁ (c₀ : ℕ) (List.mem_range.mpr c₀.isLt)
    refine ⟨g, ?_, h2, by rw [h3, Evaluator.relColoring_castSucc]; rfl⟩
    rw [show ((Fin.castSucc c₀ : Fin (sigL cap mb j + 1)) : ℕ) = (c₀ : ℕ) from rfl,
      hfa₂ _ (fun hc => ?_)]
    · exact h1
    · rw [RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom] at hc
      exact absurd (oldIdx_inj (by omega) (by omega)
        (colName_inj (List.eq_of_mem_singleton hc)).2) (by omega)

/-! #### The batch profiles -/

/-- The cost of one member of a slot family: a flat pass, a store, and a
chain of `cap` expansions. -/
def slotCost (n ns cap : ℕ) : ℕ := (24 * ns + 44 * n + 6) * cap + 15 * n + 12

/-- **One batch profile.** The singleton of the padded entry, expanded
`cap` times in the cluster-restricted arena: every stage is the ball of
that radius around the entry. -/
theorem pdBody_spec (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hnt : ns ≤ nt) (hRaB : ∀ k, k < n → Ra k < B) {w : Fin mb → Fin n}
    (hWf : ∀ i : Fin mb, Wf (i : ℕ) = (w i : ℕ)) (i : Fin mb) :
    Spec B (ColPre n cap mb nt j O T C Xa Ra Wf)
      (.seq (fillCom (colName (j + 1) (pdIdx cap mb j i 0)) (.lit 0))
        (.seq (.store (colName (j + 1) (pdIdx cap mb j i 0)) (.get "wa" (.lit (i : ℕ)))
            (.lit 1))
          (chainCom (resName j) (fun a => colName (j + 1) (pdIdx cap mb j i a)) cap)))
      (fun _ σ' => ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧
        ∀ a, a ≤ cap → ∃ g, σ'.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n g ∧
          (∀ v, v < n → g v ≤ 1) ∧ markSet n g = ballOf (masked G Ra) a {w i})
      (slotCost n ns cap) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  -- the profile's own array, opened
  obtain ⟨g₀, hg₀⟩ := hσ.2.2.2.2.2.2.2 _ (pdIdx_lt_sigL i 0)
  obtain ⟨σ₁, hr₁, ⟨⟨g₁, hg₁arr, hg₁val⟩, -, hn₁⟩, -, -, -, -⟩ :=
    ((fillCom_spec B n (colName (j + 1) (pdIdx cap mb j i 0)) 0 hnB (by omega)).frame).run
      ⟨⟨g₀, hg₀⟩, hσ.1⟩
  have hI₁ : ColPre n cap mb nt j O T C Xa Ra Wf σ₁ :=
    colPre_run hσ hr₁ (fun a ha => ⟨pdIdx cap mb j i 0, by
      rw [RamDriverIO.warrs_fillCom] at ha; exact List.eq_of_mem_singleton ha⟩)
      (by rw [hn₁, hσ.1])
  -- the entry, marked
  have hwi : Wf (i : ℕ) < n := by rw [hWf i]; exact (w i).isLt
  have hidx : (Expr.get "wa" (.lit (i : ℕ))).evalB B σ₁ = some (Wf (i : ℕ)) :=
    evalB_get (evalB_lit (by have := i.isLt; have := hB.mb_lt; omega))
      (by rw [hI₁.2.2.2.2.2.2.1, getElem?_arrOf Wf i.isLt]) (by omega)
  have hlen : Wf (i : ℕ) < (σ₁.arrs (colName (j + 1) (pdIdx cap mb j i 0))).length := by
    rw [hg₁arr, length_arrOf]; exact hwi
  set σ₂ := σ₁.setArr (colName (j + 1) (pdIdx cap mb j i 0)) (Wf (i : ℕ)) 1 with hσ₂
  have hr₂ : Run B (.store (colName (j + 1) (pdIdx cap mb j i 0)) (.get "wa" (.lit (i : ℕ)))
      (.lit 1)) σ₁ σ₂ (1 + (Expr.get "wa" (.lit (i : ℕ))).size + (Expr.lit 1).size) :=
    Run.store hidx (evalB_lit (by omega)) hlen
  have hg₂ : σ₂.arrs (colName (j + 1) (pdIdx cap mb j i 0)) =
      arrOf n (upd g₁ (Wf (i : ℕ)) 1) := by
    rw [hσ₂]; simp [hg₁arr, set_arrOf_eq_upd]
  have hI₂ : ColPre n cap mb nt j O T C Xa Ra Wf σ₂ :=
    colPre_run hI₁ hr₂ (fun a ha => ⟨pdIdx cap mb j i 0, by
      simp only [Com.warrs, List.mem_singleton] at ha; exact ha⟩)
      (by rw [hσ₂]; simp)
  -- what the chain starts at
  have hSbit : ∀ k, k < n → upd g₁ (Wf (i : ℕ)) 1 k ≤ 1 := by
    intro k hk
    by_cases hke : k = Wf (i : ℕ)
    · rw [hke, upd_self]
    · rw [upd_of_ne _ hke, hg₁val k hk]
      omega
  have hSmark : markSet n (upd g₁ (Wf (i : ℕ)) 1) = {w i} := by
    ext v
    rw [mem_markSet, Set.mem_singleton_iff]
    constructor
    · intro hv
      by_cases hve : (v : ℕ) = Wf (i : ℕ)
      · exact Fin.ext (by rw [hve, hWf i])
      · exact absurd (by rw [upd_of_ne _ hve, hg₁val (v : ℕ) v.isLt]) hv
    · rintro rfl
      rw [show ((w i : Fin n) : ℕ) = Wf (i : ℕ) from (hWf i).symm, upd_self]
      omega
  -- the chain of expansions
  obtain ⟨σ₃, hr₃, ⟨hstage, hn₃, -, -, -⟩, -, -, -, -⟩ :=
    ((chainCom_stages (msk := resName j) (nt := nt) hcsr h1B hnB hB.ns_lt hnt hRaB cap
      (fun a => colName (j + 1) (pdIdx cap mb j i a)) (upd g₁ (Wf (i : ℕ)) 1)
      (fun a b ha hb hab hc => hab (pdIdx_inj ha hb (colName_inj hc).2).2)
      (fun a _ => colName_ne_resName _ _ _) (fun a _ => colName_ne_lit (by decide))
      (fun a _ => colName_ne_lit (by decide)) hSbit).frame).run
      ⟨hI₂.1, hI₂.2.1, hI₂.2.2.1, hI₂.2.2.2.2.1, hg₂,
        fun a _ _ => hI₂.2.2.2.2.2.2.2 _ (pdIdx_lt_sigL i a)⟩
  refine ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), ?_,
    colPre_run hI₂ hr₃ (fun a ha => by
      obtain ⟨b, -, hbe⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ ha
      exact ⟨pdIdx cap mb j i (b + 1), hbe⟩) (by rw [hn₃, hI₂.1]), ?_⟩
  · simp only [slotCost, Expr.size]
    omega
  · intro a ha
    obtain ⟨g, hgarr, hgbit, hgmark⟩ := hstage a ha
    exact ⟨g, hgarr, hgbit, by rw [hgmark, hSmark]⟩

/-- **The batch profiles, discharged.** -/
theorem pdCom_spec (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hnt : ns ≤ nt)
    (hRaB : ∀ k, k < n → Ra k < B) {w : Fin mb → Fin n}
    (hWf : ∀ i : Fin mb, Wf (i : ℕ) = (w i : ℕ)) :
    Spec B (ColPre n cap mb nt j O T C Xa Ra Wf) (pdCom cap mb j)
      (fun _ σ' => ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧
        ∀ (i : Fin mb) (a : ℕ), a ≤ cap → ∃ g,
          σ'.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n g ∧
          (∀ v, v < n → g v ≤ 1) ∧ markSet n g = ballOf (masked G Ra) a {w i})
      (slotCost n ns cap * mb + 1) := by
  have h := foldr_family_spec
    (body := fun i : Fin mb =>
      Com.seq (fillCom (colName (j + 1) (pdIdx cap mb j i 0)) (.lit 0))
        (Com.seq (.store (colName (j + 1) (pdIdx cap mb j i 0)) (.get "wa" (.lit (i : ℕ)))
            (.lit 1))
          (chainCom (resName j) (fun a => colName (j + 1) (pdIdx cap mb j i a)) cap)))
    (I := ColPre n cap mb nt j O T C Xa Ra Wf)
    (R := fun i σ => ∀ a, a ≤ cap → ∃ g,
      σ.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n g ∧
      (∀ v, v < n → g v ≤ 1) ∧ markSet n g = ballOf (masked G Ra) a {w i})
    (Wr := fun i a => ∃ b, b ≤ cap ∧ a = colName (j + 1) (pdIdx cap mb j i b))
    (Kb := slotCost n ns cap)
    (fun i a ha => by
      simp only [Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        RamDriverIO.warrs_fillCom] at ha
      rcases ha with rfl | rfl | ha
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨0, by omega, rfl⟩
      · obtain ⟨b, hb, hbe⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ ha
        exact ⟨b + 1, by omega, hbe⟩)
    (fun i σ σ' hR hfr a ha => by
      obtain ⟨g, h1, h2, h3⟩ := hR a ha
      exact ⟨g, by rw [hfr _ ⟨a, ha, rfl⟩]; exact h1, h2, h3⟩)
    (List.finRange mb) (List.nodup_finRange mb)
    (fun i _ => pdBody_spec hcsr hB hnt hRaB hWf i)
    (fun x _ y _ hxy a hax hay => by
      obtain ⟨b, hb, hbe⟩ := hax
      obtain ⟨b', hb', hbe'⟩ := hay
      exact hxy (pdIdx_inj hb hb' (colName_inj (hbe ▸ hbe')).2).1)
  rw [List.length_finRange] at h
  exact h.post (fun _ _ _ hq => ⟨hq.1, fun i a ha => hq.2 i (List.mem_finRange i) a ha⟩)

/-! #### The colour profiles -/

/-- The old slots of the next depth's palette, as the colour profiles
read them: what the relativized colour `c` marks is the phase's own
business, and the profiles only expand it. -/
def OldHeld (n cap mb j : ℕ) (Vo : ℕ → Set (Fin n)) (σ : Env) : Prop :=
  ∀ c, c < sigL cap mb j + 1 → ∃ g,
    σ.arrs (colName (j + 1) (oldIdx cap mb j c)) = arrOf n g ∧
    (∀ v, v < n → g v ≤ 1) ∧ markSet n g = Vo c

/-- The old slots survive a pass that writes colour profiles alone. -/
theorem oldHeld_run {K : ℕ} {c : Com} {σ σ' : Env} {Vo : ℕ → Set (Fin n)}
    (h : OldHeld n cap mb j Vo σ) (hr : Run B c σ σ' K)
    (hw : ∀ a ∈ c.warrs, ∃ s b, a = colName (j + 1) (puIdx cap mb j s b)) :
    OldHeld n cap mb j Vo σ' := by
  intro d hd
  obtain ⟨g, h1, h2, h3⟩ := h d hd
  refine ⟨g, ?_, h2, h3⟩
  rw [hr.frame_arr _ (fun hc => ?_)]
  · exact h1
  · obtain ⟨s, b, hs⟩ := hw _ hc
    exact oldIdx_ne_puIdx d s b (colName_inj hs).2

/-- **One colour profile.** The relativized colour class, expanded `cap`
times in the cluster-restricted arena. -/
theorem puBody_spec (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hnt : ns ≤ nt)
    (hRaB : ∀ k, k < n → Ra k < B) {Vo : ℕ → Set (Fin n)} {c : ℕ}
    (hc : c < sigL cap mb j + 1) :
    Spec B (fun σ => ColPre n cap mb nt j O T C Xa Ra Wf σ ∧ OldHeld n cap mb j Vo σ)
      (.seq (copyCom (colName (j + 1) (oldIdx cap mb j c)) (colName (j + 1) (puIdx cap mb j c 0)))
        (chainCom (resName j) (fun b => colName (j + 1) (puIdx cap mb j c b)) cap))
      (fun _ σ' => (ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧ OldHeld n cap mb j Vo σ') ∧
        ∀ b, b ≤ cap → ∃ g, σ'.arrs (colName (j + 1) (puIdx cap mb j c b)) = arrOf n g ∧
          (∀ v, v < n → g v ≤ 1) ∧ markSet n g = ballOf (masked G Ra) b (Vo c))
      (slotCost n ns cap) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hpre, hold⟩ := hσ
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  obtain ⟨g₀, hg₀arr, hg₀bit, hg₀mark⟩ := hold c hc
  obtain ⟨h₀, hh₀⟩ := hpre.2.2.2.2.2.2.2 _ (puIdx_lt_sigL c 0)
  obtain ⟨σ₁, hr₁, ⟨⟨g, hgarr, hgval⟩, -, hn₁, -⟩, -, -, -, -⟩ :=
    ((copyCom_spec B n n (colName (j + 1) (oldIdx cap mb j c))
      (colName (j + 1) (puIdx cap mb j c 0)) g₀
      (colName_ne_slot (oldIdx_ne_puIdx c c 0)) hnB le_rfl
      (fun k hk => lt_of_le_of_lt (hg₀bit k hk) h1B)).frame).run
      ⟨⟨h₀, hh₀⟩, hpre.1, hg₀arr⟩
  have hcopyw : ∀ a ∈ (copyCom (colName (j + 1) (oldIdx cap mb j c))
      (colName (j + 1) (puIdx cap mb j c 0))).warrs,
      ∃ s b, a = colName (j + 1) (puIdx cap mb j s b) := by
    intro a ha
    rw [RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom] at ha
    exact ⟨c, 0, List.eq_of_mem_singleton ha⟩
  have hI₁ : ColPre n cap mb nt j O T C Xa Ra Wf σ₁ :=
    colPre_run hpre hr₁ (fun a ha => by
      obtain ⟨s, b, hs⟩ := hcopyw a ha
      exact ⟨puIdx cap mb j s b, hs⟩) (by rw [hn₁, hpre.1])
  have hold₁ : OldHeld n cap mb j Vo σ₁ := oldHeld_run hold hr₁ hcopyw
  have hgbit : ∀ k, k < n → g k ≤ 1 := fun k hk => by rw [hgval k hk]; exact hg₀bit k hk
  obtain ⟨σ₂, hr₂, ⟨hstage, hn₂, -, -, -⟩, -, -, -, -⟩ :=
    ((chainCom_stages (msk := resName j) (nt := nt) hcsr h1B hnB hB.ns_lt hnt hRaB cap
      (fun b => colName (j + 1) (puIdx cap mb j c b)) g
      (fun a b ha hb hab hce => hab (puIdx_inj (by omega) (by omega) ha hb
        (colName_inj hce).2).2)
      (fun a _ => colName_ne_resName _ _ _) (fun a _ => colName_ne_lit (by decide))
      (fun a _ => colName_ne_lit (by decide)) hgbit).frame).run
      ⟨hI₁.1, hI₁.2.1, hI₁.2.2.1, hI₁.2.2.2.2.1, hgarr,
        fun b _ _ => hI₁.2.2.2.2.2.2.2 _ (puIdx_lt_sigL c b)⟩
  have hchainw : ∀ a ∈ (chainCom (resName j)
      (fun b => colName (j + 1) (puIdx cap mb j c b)) cap).warrs,
      ∃ s b, a = colName (j + 1) (puIdx cap mb j s b) := by
    intro a ha
    obtain ⟨b, -, hbe⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ ha
    exact ⟨c, b + 1, hbe⟩
  refine ⟨σ₂, _, hr₁.seq hr₂, by simp only [slotCost]; omega,
    ⟨colPre_run hI₁ hr₂ (fun a ha => by
        obtain ⟨s, b, hs⟩ := hchainw a ha
        exact ⟨puIdx cap mb j s b, hs⟩) (by rw [hn₂, hI₁.1]),
      oldHeld_run hold₁ hr₂ hchainw⟩, ?_⟩
  intro b hb
  obtain ⟨g', hg'arr, hg'bit, hg'mark⟩ := hstage b hb
  exact ⟨g', hg'arr, hg'bit, by rw [hg'mark, markSet_congr hgval, hg₀mark]⟩

/-- **The colour profiles, discharged.** -/
theorem puCom_spec (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hnt : ns ≤ nt)
    (hRaB : ∀ k, k < n → Ra k < B) {Vo : ℕ → Set (Fin n)} :
    Spec B (fun σ => ColPre n cap mb nt j O T C Xa Ra Wf σ ∧ OldHeld n cap mb j Vo σ)
      (puCom cap mb j)
      (fun _ σ' => (ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧ OldHeld n cap mb j Vo σ') ∧
        ∀ c, c < sigL cap mb j + 1 → ∀ b, b ≤ cap → ∃ g,
          σ'.arrs (colName (j + 1) (puIdx cap mb j c b)) = arrOf n g ∧
          (∀ v, v < n → g v ≤ 1) ∧ markSet n g = ballOf (masked G Ra) b (Vo c))
      (slotCost n ns cap * (sigL cap mb j + 1) + 1) := by
  have h := foldr_family_spec
    (body := fun c : ℕ =>
      Com.seq (copyCom (colName (j + 1) (oldIdx cap mb j c))
          (colName (j + 1) (puIdx cap mb j c 0)))
        (chainCom (resName j) (fun b => colName (j + 1) (puIdx cap mb j c b)) cap))
    (I := fun σ => ColPre n cap mb nt j O T C Xa Ra Wf σ ∧ OldHeld n cap mb j Vo σ)
    (R := fun c σ => ∀ b, b ≤ cap → ∃ g,
      σ.arrs (colName (j + 1) (puIdx cap mb j c b)) = arrOf n g ∧
      (∀ v, v < n → g v ≤ 1) ∧ markSet n g = ballOf (masked G Ra) b (Vo c))
    (Wr := fun c a => ∃ b, b ≤ cap ∧ a = colName (j + 1) (puIdx cap mb j c b))
    (Kb := slotCost n ns cap)
    (fun c a ha => by
      simp only [Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom] at ha
      rcases ha with rfl | ha
      · exact ⟨0, by omega, rfl⟩
      · obtain ⟨b, hb, hbe⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ ha
        exact ⟨b + 1, by omega, hbe⟩)
    (fun c σ σ' hR hfr b hb => by
      obtain ⟨g, h1, h2, h3⟩ := hR b hb
      exact ⟨g, by rw [hfr _ ⟨b, hb, rfl⟩]; exact h1, h2, h3⟩)
    (List.range (sigL cap mb j + 1)) (List.nodup_range)
    (fun c hc => puBody_spec hcsr hB hnt hRaB (List.mem_range.mp hc))
    (fun x hx y hy hxy a hax hay => by
      obtain ⟨b, hb, hbe⟩ := hax
      obtain ⟨b', hb', hbe'⟩ := hay
      exact hxy (puIdx_inj (by have := List.mem_range.mp hx; omega)
        (by have := List.mem_range.mp hy; omega) hb hb'
        (colName_inj (hbe ▸ hbe')).2).1)
  rw [List.length_range] at h
  exact h.post (fun _ _ _ hq => ⟨hq.1, fun c hc b hb => hq.2 c (List.mem_range.mpr hc) b hb⟩)

/-! #### The palette, assembled

The three families write the three blocks of `Evaluator.isoPalette`, and
every slot of the palette is in one of them — which is `slot_cases`, the
`Fin.addCases` decomposition the packing was built by. So the colouring
the arrays hold at the end is `Evaluator.isoColoring` slot by slot, and
that is `RamDriver.stepColoringP`. -/

/-- The cell function of an array, as the driver reads it back. -/
def cellsOf (σ : Env) (a : String) : ℕ → ℕ := fun k => (σ.arrs a).getD k 0

theorem cellsOf_eq {N : ℕ} {σ : Env} {a : String} {g : ℕ → ℕ} (h : σ.arrs a = arrOf N g)
    {k : ℕ} (hk : k < N) : cellsOf σ a k = g k := by
  rw [cellsOf, h, getD_arrOf g hk]

theorem arrOf_cellsOf {N : ℕ} {σ : Env} {a : String} {g : ℕ → ℕ} (h : σ.arrs a = arrOf N g) :
    σ.arrs a = arrOf N (cellsOf σ a) := by
  rw [h]
  exact (arrOf_congr (fun k hk => cellsOf_eq h hk)).symm

/-- **Every slot of the palette is in one of the three families.** -/
theorem slot_cases {L' m' cp : ℕ} (s : Fin (Evaluator.isoPalette L' m' cp)) :
    (∃ d : Fin L', s = Evaluator.slotOld d) ∨
      (∃ (i : Fin m') (a : Fin (cp + 1)), s = Evaluator.slotPd i a) ∨
      (∃ (d : Fin L') (b : Fin (cp + 1)), s = Evaluator.slotPu d b) := by
  refine Fin.addCases (fun d => Or.inl ⟨d, rfl⟩) (fun e => ?_) s
  refine Fin.addCases (fun f => ?_) (fun f => ?_) e
  · refine Or.inr (Or.inl ⟨(finProdFinEquiv.symm f).1, (finProdFinEquiv.symm f).2, ?_⟩)
    rw [Evaluator.slotPd, Prod.mk.eta, Equiv.apply_symm_apply]
  · refine Or.inr (Or.inr ⟨(finProdFinEquiv.symm f).1, (finProdFinEquiv.symm f).2, ?_⟩)
    rw [Evaluator.slotPu, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The relativized colour of a slot, addressed by its number. -/
noncomputable def relSlot (n cap mb j : ℕ) (C : ℕ → ℕ → ℕ) (X : Set (Fin n)) :
    ℕ → Set (Fin n) :=
  fun c => Evaluator.relColoring (colRead n C (sigL cap mb j)) X
    ⟨min c (sigL cap mb j), by omega⟩

theorem relSlot_val {X : Set (Fin n)} (c : Fin (sigL cap mb j + 1)) :
    relSlot n cap mb j C X (c : ℕ) =
      Evaluator.relColoring (colRead n C (sigL cap mb j)) X c := by
  rw [relSlot]
  congr 1
  exact Fin.ext (by simp [Nat.min_eq_left (Nat.lt_succ_iff.mp c.isLt)])

/-- The three slot maps, at the numbers the program text addresses. -/
theorem val_slotOld (d : Fin (sigL cap mb j + 1)) :
    ((oldSlots cap mb j d : Fin (sigL cap mb (j + 1))) : ℕ) = oldIdx cap mb j (d : ℕ) := by
  rw [oldIdx_eq (Nat.lt_succ_iff.mp d.isLt), oldSlots, Evaluator.slotOld, Fin.val_castAdd]

theorem val_slotPd (i : Fin mb) (a : Fin (cap + 1)) :
    ((pdSlots cap mb j i a : Fin (sigL cap mb (j + 1))) : ℕ) = pdIdx cap mb j i (a : ℕ) := by
  rw [pdIdx]
  congr 2
  exact (Fin.ext (by simp [Nat.min_eq_left (Nat.lt_succ_iff.mp a.isLt)])).symm

theorem val_slotPu (d : Fin (sigL cap mb j + 1)) (b : Fin (cap + 1)) :
    ((puSlots cap mb j d b : Fin (sigL cap mb (j + 1))) : ℕ) =
      puIdx cap mb j (d : ℕ) (b : ℕ) := by
  rw [puIdx]
  congr 2
  · exact (Fin.ext (by simp [Nat.min_eq_left (Nat.lt_succ_iff.mp d.isLt)])).symm
  · exact (Fin.ext (by simp [Nat.min_eq_left (Nat.lt_succ_iff.mp b.isLt)])).symm

/-- The cost of the colouring phase: the flat old-colour pass, followed
by the two expansion-profile families. -/
def colourCost (n ns cap mb L : ℕ) : ℕ :=
  (15 * n + 6) * L + (12 * n + 6) + slotCost n ns cap * (mb + L + 1) + 3

/-- **The colouring of the next depth, discharged.** The arrays of the
depth-`(j+1)` palette hold `Evaluator.isoColoring` of the
cluster-restricted arena at the relativized colouring and the padded
enumeration — which is `RamDriver.stepColoringP`. -/
theorem colourCom_spec (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hnt : ns ≤ nt) (hRaB : ∀ k, k < n → Ra k < B)
    (hCbit : ∀ c, c < sigL cap mb j → ∀ v, v < n → C c v ≤ 1)
    (hXbit : ∀ v, v < n → Xa v ≤ 1)
    {w : Fin mb → Fin n} (hWf : ∀ i : Fin mb, Wf (i : ℕ) = (w i : ℕ)) :
    Spec B (ColPre n cap mb nt j O T C Xa Ra Wf) (colourCom cap mb j)
      (fun _ σ' => ColPre n cap mb nt j O T C Xa Ra Wf σ' ∧
        (∀ s, s < sigL cap mb (j + 1) → ∀ v, v < n →
          cellsOf σ' (colName (j + 1) s) v ≤ 1) ∧
        colRead n (fun s => cellsOf σ' (colName (j + 1) s)) (sigL cap mb (j + 1)) =
          Evaluator.isoColoring (cap := cap) (masked G Ra)
            (Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa)) w)
      (colourCost n ns cap mb (sigL cap mb j)) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  -- the relativized colours
  obtain ⟨σ₁, hr₁, ⟨hI₁, hold₁⟩, -, -, -, -⟩ := ((oldCom_spec hB hCbit hXbit).frame).run hσ
  have hOld₁ : OldHeld n cap mb j (relSlot n cap mb j C (markSet n Xa)) σ₁ := by
    intro c hc
    obtain ⟨g, h1, h2, h3⟩ := hold₁ ⟨c, hc⟩
    exact ⟨g, h1, h2, by rw [h3, relSlot_val ⟨c, hc⟩]⟩
  -- the batch profiles
  obtain ⟨σ₂, hr₂, ⟨hI₂, hpd₂⟩, -, hfa₂, -, -⟩ :=
    ((pdCom_spec hcsr hB hnt hRaB hWf).frame).run hI₁
  have hOld₂ : OldHeld n cap mb j (relSlot n cap mb j C (markSet n Xa)) σ₂ := by
    intro c hc
    obtain ⟨g, h1, h2, h3⟩ := hOld₁ c hc
    refine ⟨g, ?_, h2, h3⟩
    rw [hfa₂ _ (fun hcc => ?_)]
    · exact h1
    · obtain ⟨i, b, hib⟩ := mem_warrs_pdCom hcc
      exact oldIdx_ne_pdIdx c i b (colName_inj hib).2
  -- the colour profiles
  obtain ⟨σ₃, hr₃, ⟨⟨hI₃, hOld₃⟩, hpu₃⟩, -, hfa₃, -, -⟩ :=
    ((puCom_spec hcsr hB hnt hRaB).frame).run ⟨hI₂, hOld₂⟩
  have hpd₃ : ∀ (i : Fin mb) (a : ℕ), a ≤ cap → ∃ g,
      σ₃.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n g ∧
      (∀ v, v < n → g v ≤ 1) ∧ markSet n g = ballOf (masked G Ra) a {w i} := by
    intro i a ha
    obtain ⟨g, h1, h2, h3⟩ := hpd₂ i a ha
    refine ⟨g, ?_, h2, h3⟩
    rw [hfa₃ _ (fun hcc => ?_)]
    · exact h1
    · obtain ⟨c, b, hcb⟩ := mem_warrs_puCom hcc
      exact pdIdx_ne_puIdx i a c b (colName_inj hcb).2
  -- every slot of the palette, in one of the three families
  have key : ∀ s : Fin (sigL cap mb (j + 1)), ∃ g,
      σ₃.arrs (colName (j + 1) (s : ℕ)) = arrOf n g ∧ (∀ v, v < n → g v ≤ 1) ∧
      markSet n g = Evaluator.isoColoring (cap := cap) (masked G Ra)
        (Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa)) w s := by
    intro s
    rcases slot_cases (L' := sigL cap mb j + 1) (m' := mb) (cp := cap) s with
      ⟨d, rfl⟩ | ⟨i, a, rfl⟩ | ⟨d, b, rfl⟩
    · obtain ⟨g, h1, h2, h3⟩ := hOld₃ (d : ℕ) d.isLt
      refine ⟨g, ?_, h2, ?_⟩
      · rw [show ((Evaluator.slotOld d : Fin (sigL cap mb (j + 1))) : ℕ) =
          oldIdx cap mb j (d : ℕ) from val_slotOld d]
        exact h1
      · rw [h3, relSlot_val d, Evaluator.isoColoring_slotOld]
    · obtain ⟨g, h1, h2, h3⟩ := hpd₃ i (a : ℕ) (Nat.lt_succ_iff.mp a.isLt)
      refine ⟨g, ?_, h2, ?_⟩
      · rw [show ((Evaluator.slotPd i a : Fin (sigL cap mb (j + 1))) : ℕ) =
          pdIdx cap mb j i (a : ℕ) from val_slotPd i a]
        exact h1
      · rw [h3, Evaluator.isoColoring_slotPd, ballOf_singleton]
    · obtain ⟨g, h1, h2, h3⟩ := hpu₃ (d : ℕ) d.isLt (b : ℕ) (Nat.lt_succ_iff.mp b.isLt)
      refine ⟨g, ?_, h2, ?_⟩
      · rw [show ((Evaluator.slotPu d b : Fin (sigL cap mb (j + 1))) : ℕ) =
          puIdx cap mb j (d : ℕ) (b : ℕ) from val_slotPu d b]
        exact h1
      · rw [h3, Evaluator.isoColoring_slotPu, relSlot_val d]
        rfl
  refine ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), ?_, hI₃, ?_, ?_⟩
  · simp only [colourCost]
    ring_nf
    exact le_rfl
  · intro s hs v hv
    obtain ⟨g, h1, h2, -⟩ := key ⟨s, hs⟩
    rw [cellsOf_eq h1 hv]
    exact h2 v hv
  · funext s
    obtain ⟨g, h1, -, h3⟩ := key s
    rw [← h3]
    exact markSet_congr (fun k hk => cellsOf_eq h1 hk)

/-! #### The scalars the phase moves

Six counters, all of them literals: so every name the turn is holding —
which is a prefixed name or `"m"` — crosses the phase. -/

theorem mem_wvars_foldr {X : Type*} (f : X → Com) :
    ∀ (l : List X) {y : String},
      y ∈ (l.foldr (fun x c => Com.seq (f x) c) .skip).wvars → ∃ x ∈ l, y ∈ (f x).wvars := by
  intro l
  induction l with
  | nil => intro y hy; exact absurd hy (by simp)
  | cons x xs ih =>
    intro y hy
    simp only [List.foldr_cons, Com.wvars, List.mem_append] at hy
    rcases hy with h | h
    · exact ⟨x, by simp, h⟩
    · obtain ⟨z, hz, hm⟩ := ih h
      exact ⟨z, by simp [hz], hm⟩

theorem mem_wvars_foldRange (f : ℕ → Com) (m : ℕ) {y : String}
    (h : y ∈ (foldRange f m).wvars) : ∃ b < m, y ∈ (f b).wvars := by
  obtain ⟨b, hb, hm⟩ := mem_wvars_foldr f (List.range m) h
  exact ⟨b, List.mem_range.mp hb, hm⟩

theorem mem_wvars_expandCom {msk src dst : String} :
    ∀ y ∈ (expandCom msk src dst).wvars,
      y ∈ (["i", "z", "hit", "w", "j", "jend"] : List String) := by
  have he : (expandCom msk src dst).wvars = (expandCom "a" "b" "c").wvars := rfl
  rw [he]
  decide

theorem mem_wvars_chainCom {msk y : String} {nm : ℕ → String} {r : ℕ}
    (h : y ∈ (chainCom msk nm r).wvars) :
    y ∈ (["i", "z", "hit", "w", "j", "jend"] : List String) := by
  obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ _ h
  exact mem_wvars_expandCom y hm

/-- **The colouring assigns six counters and nothing else.** -/
theorem mem_wvars_colourCom {y : String} (h : y ∈ (colourCom cap mb j).wvars) :
    y ∈ (["i", "z", "hit", "w", "j", "jend"] : List String) := by
  have hfill : ∀ (a : String) (e : Expr), ∀ y ∈ (fillCom a e).wvars,
      y ∈ (["i", "z", "hit", "w", "j", "jend"] : List String) := by
    intro a e y hy
    rw [RamDriverIO.wvars_fillCom] at hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · decide
    · rcases List.mem_cons.mp hy' with rfl | hy''
      · decide
      · exact absurd hy'' (by simp)
  simp only [colourCom, Com.wvars, List.mem_append] at h
  rcases h with h | h | h
  · simp only [oldCom, Com.wvars, List.mem_append, RamDriverIO.copyCom_eq] at h
    rcases h with h | h
    · obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ _ h
      rw [andCom] at hm
      exact hfill _ _ y hm
    · exact hfill _ _ y h
  · obtain ⟨i, -, hm⟩ := mem_wvars_foldr _ (List.finRange mb) h
    simp only [Com.wvars, List.mem_append, List.not_mem_nil, false_or] at hm
    rcases hm with hm | hm
    · exact hfill _ _ y hm
    · exact mem_wvars_chainCom hm
  · obtain ⟨c, -, hm⟩ := mem_wvars_foldRange _ _ h
    simp only [Com.wvars, List.mem_append, RamDriverIO.copyCom_eq] at hm
    rcases hm with hm | hm
    · exact hfill _ _ y hm
    · exact mem_wvars_chainCom hm

/-! #### The output tape -/

theorem noWrite_expandCom (msk src dst : String) : (expandCom msk src dst).NoWrite := by
  have he : (expandCom msk src dst).NoWrite = (expandCom "a" "b" "c").NoWrite := rfl
  rw [he]
  decide

theorem noWrite_foldr {X : Type*} {f : X → Com} (hf : ∀ x, (f x).NoWrite) :
    ∀ l : List X, (l.foldr (fun x c => Com.seq (f x) c) .skip).NoWrite := by
  intro l
  induction l with
  | nil => exact trivial
  | cons x xs ih => exact ⟨hf x, ih⟩

theorem noWrite_chainCom (msk : String) (nm : ℕ → String) (r : ℕ) :
    (chainCom msk nm r).NoWrite :=
  noWrite_foldr (fun _ => noWrite_expandCom _ _ _) _

theorem noWrite_colourCom (cap mb j : ℕ) : (colourCom cap mb j).NoWrite := by
  refine ⟨⟨noWrite_foldr (fun c => ?_) _, ?_⟩, noWrite_foldr (fun i => ?_) _,
    noWrite_foldr (fun c => ?_) _⟩
  · rw [andCom]; exact RamDriverIO.noWrite_fillCom _ _
  · rw [RamDriverIO.copyCom_eq]; exact RamDriverIO.noWrite_fillCom _ _
  · exact ⟨RamDriverIO.noWrite_fillCom _ _, trivial, noWrite_chainCom _ _ _⟩
  · exact ⟨by rw [RamDriverIO.copyCom_eq]; exact RamDriverIO.noWrite_fillCom _ _,
      noWrite_chainCom _ _ _⟩

/-! #### The obligation

The phase's *first* pass needs the cluster indicator to hold **bits**:
`oldCom` multiplies the depth's colour by it and the product has to be a
bit, which is what the obligation's own postcondition says. Wave D1
repaired `RamDriverCluster.BatchData` to carry exactly that — the
indicator's cells are `≤ 1` and not merely words — so the walk below
discharges the obligation directly, with no scaffold in between; and
`RamDriver.LevelPre`'s repaired colour clause supplies the depth's own
palette in the same form, so that too comes off the precondition rather
than out of a theorem hypothesis.

The counterexample the repair answers is the one wave C recorded: with a
cluster cell of value `2` the product `C c z * Xa z` is `2` at a marked
vertex of a coloured class, the postcondition's bit clause is refuted,
and with cells at the word bound the run itself vanishes. -/

variable {Ws : ℕ} {M Gm : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)} {w : Fin mb → Fin n}
  {Alv' Gam' : ℕ → ℕ}

/-- **The colouring of one cluster, walked.** -/
theorem colourStep {K : ℕ}
    (hK : colourCost n ns cap mb (sigL cap mb j) ≤ K) :
    ColourStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m X W w Alv' Gam' K := by
  intro hcsr d hB σ hσ
  obtain ⟨⟨hlev, hplayj, hheld⟩, ⟨hbat, hrange⟩, hwa, hplay1⟩ := hσ
  obtain ⟨Xa, hXaarr, hXs, hXbit⟩ := hbat.1
  obtain ⟨Ra, hRaarr, hRam, hRaB⟩ := hbat.2.2.1
  have hdep := hlev.2.2.2.2.2.2.2.2.2.2.1
  have hCbit : ∀ c, c < sigL cap mb j → ∀ v, v < n → C c v ≤ 1 :=
    hlev.2.2.2.2.2.2.2.2.1
  have hWf : ∀ i : Fin mb,
      (fun k => if h : k < mb then ((w ⟨k, h⟩ : Fin n) : ℕ) else 0) (i : ℕ) = (w i : ℕ) := by
    intro i
    simp only [dif_pos i.isLt, Fin.eta]
  have hpre : ColPre n cap mb Ws j O T C Xa Ra
      (fun k => if h : k < mb then ((w ⟨k, h⟩ : Fin n) : ℕ) else 0) σ :=
    ⟨hlev.1, hlev.2.1, hlev.2.2.1, hXaarr, hRaarr, hlev.2.2.2.2.2.1, hwa,
      fun s hs => hdep.col hs⟩
  obtain ⟨σ', hr, ⟨hpre', hbit', heq'⟩, hfv, hfa, -, hout⟩ :=
    ((colourCom_spec (nt := Ws) hcsr hB hlev.2.2.2.2.2.2.2.2.2.2.2.2.1.1 hRaB
      hCbit hXbit hWf).frame).run hpre
  -- the frames of the phase
  have hav : ∀ a : String, (∀ s, a ≠ colName (j + 1) s) → σ'.arrs a = σ.arrs a := by
    intro a ha
    refine hfa a (fun hc => ?_)
    obtain ⟨s, hs⟩ := RamDriverFrames.mem_warrs_colourCom cap mb j hc
    exact ha s hs
  have hvv : ∀ y : String, y ∉ (["i", "z", "hit", "w", "j", "jend"] : List String) →
      σ'.vars y = σ.vars y := fun y hy => hfv y (fun hc => hy (mem_wvars_colourCom hc))
  have hctr : ∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a) := fun a =>
    hvv _ (RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide))
  have hgama : ∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a) := fun a =>
    hav _ (fun s => Ne.symm (colName_ne_gamName _ _ _))
  have hresa : ∀ a : ℕ, σ'.arrs (resName a) = σ.arrs (resName a) := fun a =>
    hav _ (fun s => Ne.symm (colName_ne_resName _ _ _))
  have hpara : ∀ a : ℕ, σ'.arrs (parName a) = σ.arrs (parName a) := fun a =>
    hav _ (fun s => Ne.symm (by simpa [parName] using colName_ne_balName (j + 1) s a))
  have hturn' : TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' := by
    refine ⟨levelPre_congr hlev hr (hvv "n" (by decide)) (hvv "m" (by decide))
        (hvv "lw" (by decide))
        (hav "off" (fun s => Ne.symm (colName_ne_lit (by decide))))
        (hav "tgt" (fun s => Ne.symm (colName_ne_lit (by decide))))
        (hav _ (fun s => Ne.symm (colName_ne_alvName _ _ _))) (hgama j)
        (fun c' _ => hav _ (fun s => colName_ne_depth (by omega)))
        (fun a ha => hav a ?_)
        (hav _ (fun s => Ne.symm (colName_ne_memName _ _ _)))
        (hvv _ (RamDriverIO.notMem_of_append (p := "mm") (s := toString j) (by decide))),
      hplayj.congr (fun a _ => hctr a) (fun a _ => hresa a)
        (fun a _ => hgama a) (fun a _ => hpara a),
      coverHeld_congr hheld (hav _ (fun s => Ne.symm (colName_ne_ordName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_xofName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_xmmName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_asgName _ _ _)))
        (hvv _ (RamDriverIO.notMem_of_append (p := "xq") (s := toString j) (by decide)))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun s => Ne.symm (colName_ne_lit (by decide))
  refine ⟨σ', hr.mono hK, hturn',
    ⟨batchData_congr hbat (hav _ (fun s => Ne.symm (colName_ne_cluName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_batName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_resName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_alvName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_gamName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_memName _ _ _)))
        (hvv _ (RamDriverIO.notMem_of_append (p := "mm") (s := toString (j + 1)) (by decide))),
      hrange⟩,
    hplay1.congr (fun a _ => hctr a) (fun a _ => hresa a)
      (fun a _ => hgama a) (fun a _ => hpara a),
    hout (noWrite_colourCom cap mb j),
    hvv _ (RamDriverIO.notMem_of_append (p := "cu") (s := toString j) (by decide)),
    fun s => cellsOf σ' (colName (j + 1) s), fun c hc => ?_, hbit', ?_⟩
  · obtain ⟨g, hg⟩ := hpre'.2.2.2.2.2.2.2 c hc
    exact arrOf_cellsOf hg
  · rw [heq', stepColoringP, hRam, hXs]

end Colour

/-! ### The cluster, materialized

`RamDriver.clusterLoad` opens the cluster indicator and marks the block
of the current centre: a flat fill, the two offset reads of the cluster
arena, and one scan of the block. What it leaves is the fibre
`RamCover.CoverOut.block` names — and, since every cell it writes is a
literal, an indicator whose cells are *bits*, which is the clause
`RamDriverCluster.ColourStep` is short of. -/

section Cluster

variable {B cap mb ns nt j : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}

/-- **The cluster arena ends where the pass says it ends.** The stepwise
monotonicity of `RamCover.CoverOut`, summed. -/
theorem coverOut_off_le (h : RamCover.CoverOut G M π ord cap m Xoff Xmem asg) :
    ∀ c, c ≤ n → Xoff c ≤ m := by
  intro c hc
  have key : ∀ d, c + d ≤ n → Xoff c ≤ Xoff (c + d) := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact le_trans (ih (by omega)) (h.mono (c + d) (by omega))
  have hkey := key (n - c) (by omega)
  rw [show c + (n - c) = n by omega, h.last] at hkey
  exact hkey

/-- **A block index is at most the vertex it names.** The row is
strictly increasing (`RamCover.CoverOut.block_mono`), so its `k`-th
member is at least `k`. This is what keeps the emitted prefix inside the
child's `n`-cell member array, and what bounds a block's size by the
carrier's — the two facts the emission add-on needs and the old
repetition-free reading could not give (rebase E-mem). -/
theorem row_offset_le (hout : RamCover.CoverOut G M π ord cap m Xoff Xmem asg)
    {c : ℕ} (hc : c < n) : ∀ k, Xoff c + k < Xoff (c + 1) → k ≤ Xmem (Xoff c + k) := by
  intro k
  induction k with
  | zero => exact fun _ => Nat.zero_le _
  | succ i ih =>
      intro hk
      have h₁ : Xmem (Xoff c + i) < Xmem (Xoff c + (i + 1)) :=
        hout.block_mono c hc _ _ (by omega) (by omega) hk
      have h₂ := ih (by omega)
      omega

/-- What the scan of one block carries: the two pointers inside the
block, the indicator marking exactly the members already passed — and
(rebase E-mem) the emitted prefix of the child's member list, whose
write pointer `"bq"` counts the members already passed. -/
def CluScan (n j : ℕ) (Xoff Xmem : ℕ → ℕ) (c : ℕ) (σ : Env) : Prop :=
  σ.arrs (xmmName j) = arrOf (n * n) Xmem ∧
    σ.vars "pend" = Xoff (c + 1) ∧ Xoff c ≤ σ.vars "p" ∧ σ.vars "p" ≤ Xoff (c + 1) ∧
    σ.vars "bq" = σ.vars "p" - Xoff c ∧
    (∃ g, σ.arrs (memName (j + 1)) = arrOf n g ∧
      ∀ k, k < σ.vars "p" - Xoff c → g k = Xmem (Xoff c + k)) ∧
    ∃ g, σ.arrs (cluName j) = arrOf n g ∧ (∀ k, k < n → g k ≤ 1) ∧
      ∀ k, k < n → (g k ≠ 0 ↔ ∃ p, Xoff c ≤ p ∧ p < σ.vars "p" ∧ Xmem p = k)

/-- **The cluster is materialized, discharged.**

The load forms two kinds of value: the depth's own (`n`, the centre
index, the indicator), which are words by the value bound, and the
*block offsets* `Xoff c`, which are addresses into the cluster arena and
are words because the pass's exit pointer is (`hmB`). Under `WordBound`
that came off the carrier ceiling `n * n < B`; `hm` — the arena's
**length**, which the offsets index — is a separate clause and is
unchanged (rebase E-mem/W2). -/
theorem clusterLoad_spec {d c : ℕ} (hB : WordBoundK B n d ns cap mb) (hmB : m < B)
    (hout : RamCover.CoverOut G M π ord cap m Xoff Xmem asg) (hm : m ≤ n * n)
    (hc : c < n) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧
        σ.arrs (xmmName j) = arrOf (n * n) Xmem ∧ (∃ g, σ.arrs (cluName j) = arrOf n g) ∧
        (∃ g, σ.arrs (memName (j + 1)) = arrOf n g) ∧
        σ.vars (curName j) = c)
      (clusterLoad j)
      (fun σ σ' => ∃ Xa, σ'.arrs (cluName j) = arrOf n Xa ∧ (∀ k, k < n → Xa k ≤ 1) ∧
        markSet n Xa =
          {v : Fin n | RamCover.InCluster (masked G M) π cap (ord (σ.vars (curName j))) (v : ℕ)} ∧
        ∃ (Mm : ℕ → ℕ) (bs : ℕ), σ'.arrs (memName (j + 1)) = arrOf n Mm ∧
          σ'.vars "bq" = bs ∧ bs = blockSize Xoff c ∧ MemEnum n bs Mm Xa)
      (24 * blockSize Xoff c + 11 * n + 26) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hxof, hxmm, hclu, hmem₀, hcurEq⟩ := hσ
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  have hcur : σ.vars (curName j) < n := by rw [hcurEq]; exact hc
  have hoffB : ∀ q, q ≤ n → Xoff q < B := fun q hq =>
    lt_of_le_of_lt (coverOut_off_le hout q hq) hmB
  have hclumem : cluName j ≠ memName (j + 1) := by simp [cluName, memName, String.ext_iff]
  -- the indicator, opened
  obtain ⟨σ₁, hr₁, ⟨⟨g₁, hg₁arr, hg₁val⟩, -, hn₁⟩, hfv₁, hfa₁, -, -⟩ :=
    ((fillCom_spec B n (cluName j) 0 hnB (by omega)).frame).run ⟨hclu, hn⟩
  have hcur₁ : σ₁.vars (curName j) = c := by
    calc
      σ₁.vars (curName j) = σ.vars (curName j) := hfv₁ _ (by
        rw [RamDriverIO.wvars_fillCom]
        exact RamDriverIO.notMem_of_append (p := "cu") (s := toString j) (by decide))
      _ = c := hcurEq
  have hxof₁ : σ₁.arrs (xofName j) = arrOf (n + 1) Xoff := by
    rw [hfa₁ _ (by rw [RamDriverIO.warrs_fillCom]; simp [cluName, xofName, String.ext_iff])]
    exact hxof
  have hxmm₁ : σ₁.arrs (xmmName j) = arrOf (n * n) Xmem := by
    rw [hfa₁ _ (by rw [RamDriverIO.warrs_fillCom]; simp [cluName, xmmName, String.ext_iff])]
    exact hxmm
  have hmem₁ : ∃ g, σ₁.arrs (memName (j + 1)) = arrOf n g := by
    rw [hfa₁ _ (by rw [RamDriverIO.warrs_fillCom]; simpa using Ne.symm hclumem)]
    exact hmem₀
  -- the emission counter (rebase E-mem)
  set σ₁' := σ₁.setVar "bq" 0 with hσ₁'
  have hr₁' : Run B (.assign "bq" (.lit 0)) σ₁ σ₁' 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  -- the two offset reads
  have ev₁ : (Expr.var (curName j)).evalB B σ₁' = some c := by
    have hcv : σ₁'.vars (curName j) = c := by
      rw [hσ₁', vars_setVar, if_neg (by simp [curName, String.ext_iff]), hcur₁]
    have h := evalB_var (B := B) (x := curName j) (σ := σ₁') (by rw [hcv]; omega)
    rwa [hcv] at h
  have hxof₁' : σ₁'.arrs (xofName j) = arrOf (n + 1) Xoff := by rw [hσ₁', arrs_setVar]; exact hxof₁
  have e₁ : (Expr.get (xofName j) (.var (curName j))).evalB B σ₁' = some (Xoff c) :=
    evalB_get ev₁ (by rw [hxof₁', getElem?_arrOf Xoff (by omega)]) (hoffB c (by omega))
  set σ₂ := σ₁'.setVar "p" (Xoff c) with hσ₂
  have hr₂ : Run B (.assign "p" (.get (xofName j) (.var (curName j)))) σ₁' σ₂ 3 :=
    (Run.assign e₁).mono (by simp [Expr.size])
  have hcur₂ : σ₂.vars (curName j) = c := by
    rw [hσ₂, vars_setVar, if_neg (by simp [curName, String.ext_iff]), hσ₁', vars_setVar,
      if_neg (by simp [curName, String.ext_iff]), hcur₁]
  have ev₂ : (Expr.add (Expr.var (curName j)) (Expr.lit 1)).evalB B σ₂ = some (c + 1) := by
    have h : (Expr.add (Expr.var (curName j)) (Expr.lit 1)).evalB B σ₂ =
        some (σ₂.vars (curName j) + 1) :=
      evalB_bin (evalB_var (by rw [hcur₂]; omega)) (evalB_lit (by omega))
        (by rw [hcur₂]; simp; omega)
    rw [h, hcur₂]
  have e₂ : (Expr.get (xofName j) (.add (.var (curName j)) (.lit 1))).evalB B σ₂ =
      some (Xoff (c + 1)) :=
    evalB_get ev₂ (by rw [hσ₂, arrs_setVar, hxof₁', getElem?_arrOf Xoff (by omega)])
      (hoffB (c + 1) (by omega))
  set σ₃ := σ₂.setVar "pend" (Xoff (c + 1)) with hσ₃
  have hr₃ : Run B (.assign "pend" (.get (xofName j) (.add (.var (curName j)) (.lit 1))))
      σ₂ σ₃ 5 := (Run.assign e₂).mono (by simp [Expr.size])
  have hrLoad : Run B (Csr.loadRow (xofName j) (curName j) "p" "pend") σ₁' σ₃ 8 := hr₂.seq hr₃
  -- one member of the block: the indicator's bit, and the emission
  have hstep : ∀ ρ : Env, CluScan n j Xoff Xmem c ρ → ρ.vars "p" < Xoff (c + 1) →
      ∃ ρ' K', Run B (.seq (.store (cluName j) (.get (xmmName j) (.var "p")) (.lit 1))
          (.seq (.store (memName (j + 1)) (.var "bq") (.get (xmmName j) (.var "p")))
            (.seq (.assign "bq" (.add (.var "bq") (.lit 1)))
              (.assign "p" (.add (.var "p") (.lit 1)))))) ρ ρ' K' ∧
        CluScan n j Xoff Xmem c ρ' ∧ ρ'.vars "p" = ρ.vars "p" + 1 ∧ K' ≤ 20 := by
    intro ρ hρ hlt
    obtain ⟨hxmmρ, hpend, hlo, -, hbq, ⟨gm, hgmarr, hgmval⟩, g, hgarr, hgbit, hgval⟩ := hρ
    have hpm : ρ.vars "p" < n * n :=
      lt_of_lt_of_le hlt (le_trans (coverOut_off_le hout (c + 1) (by omega)) hm)
    -- the scan index is an *address* into the arena, so it is a word because the
    -- pass's exit pointer is, not because the carrier is (rebase E-mem/W2)
    have hpB : ρ.vars "p" + 1 < B := by
      have := coverOut_off_le hout (c + 1) (by omega)
      omega
    have hXm : Xmem (ρ.vars "p") < n :=
      hout.mem_lt _ (lt_of_lt_of_le hlt (coverOut_off_le hout (c + 1) (by omega)))
    -- the write pointer is inside the child's array: the row is sorted, so the
    -- `k`-th member is at least `k` (rebase E-mem)
    have hbqle : ρ.vars "bq" ≤ Xmem (ρ.vars "p") := by
      have h := row_offset_le hout hc (ρ.vars "p" - Xoff c) (by omega)
      rw [show Xoff c + (ρ.vars "p" - Xoff c) = ρ.vars "p" by omega] at h
      omega
    have hbqn : ρ.vars "bq" < n := by omega
    have hidx : (Expr.get (xmmName j) (.var "p")).evalB B ρ = some (Xmem (ρ.vars "p")) :=
      evalB_get (evalB_var (by omega)) (by rw [hxmmρ, getElem?_arrOf Xmem hpm]) (by omega)
    have hlen : Xmem (ρ.vars "p") < (ρ.arrs (cluName j)).length := by
      rw [hgarr, length_arrOf]; exact hXm
    set ρ₁ := ρ.setArr (cluName j) (Xmem (ρ.vars "p")) 1 with hρ₁
    have hp₁ : ρ₁.vars "p" = ρ.vars "p" := by rw [hρ₁, vars_setArr]
    have hb₁ : ρ₁.vars "bq" = ρ.vars "bq" := by rw [hρ₁, vars_setArr]
    have hpe₁ : (Expr.var "p").evalB B ρ₁ = some (ρ.vars "p") := by
      have h := evalB_var (B := B) (x := "p") (σ := ρ₁) (by rw [hp₁]; omega)
      rwa [hp₁] at h
    have hidx₁ : (Expr.get (xmmName j) (.var "p")).evalB B ρ₁ = some (Xmem (ρ.vars "p")) := by
      refine evalB_get hpe₁ ?_ (by omega)
      rw [hρ₁, arrs_setArr, if_neg (by simp [cluName, xmmName, String.ext_iff]), hxmmρ,
        getElem?_arrOf Xmem hpm]
    have hbqe₁ : (Expr.var "bq").evalB B ρ₁ = some (ρ.vars "bq") := by
      have h := evalB_var (B := B) (x := "bq") (σ := ρ₁) (by rw [hb₁]; omega)
      rwa [hb₁] at h
    have hlen₁ : ρ.vars "bq" < (ρ₁.arrs (memName (j + 1))).length := by
      rw [hρ₁, arrs_setArr, if_neg (Ne.symm hclumem), hgmarr, length_arrOf]; exact hbqn
    set ρ₂ := ρ₁.setArr (memName (j + 1)) (ρ.vars "bq") (Xmem (ρ.vars "p")) with hρ₂
    have hp₂ : ρ₂.vars "p" = ρ.vars "p" := by rw [hρ₂, vars_setArr, hp₁]
    have hb₂ : ρ₂.vars "bq" = ρ.vars "bq" := by rw [hρ₂, vars_setArr, hb₁]
    have hbe₂ : (Expr.var "bq").evalB B ρ₂ = some (ρ.vars "bq") := by
      have h := evalB_var (B := B) (x := "bq") (σ := ρ₂) (by rw [hb₂]; omega)
      rwa [hb₂] at h
    have hbqinc : (Expr.add (Expr.var "bq") (Expr.lit 1)).evalB B ρ₂ =
        some (ρ.vars "bq" + 1) := by
      have h := evalB_bin hbe₂ (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
        (show Bop.add.apply (ρ.vars "bq") 1 < B by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    set ρ₃ := ρ₂.setVar "bq" (ρ.vars "bq" + 1) with hρ₃
    have hp₃ : ρ₃.vars "p" = ρ.vars "p" := by
      rw [hρ₃, vars_setVar, if_neg (by decide), hp₂]
    have hpe₃ : (Expr.var "p").evalB B ρ₃ = some (ρ.vars "p") := by
      have h := evalB_var (B := B) (x := "p") (σ := ρ₃) (by rw [hp₃]; omega)
      rwa [hp₃] at h
    have hpinc : (Expr.add (Expr.var "p") (Expr.lit 1)).evalB B ρ₃ =
        some (ρ.vars "p" + 1) := by
      have h := evalB_bin hpe₃ (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
        (show Bop.add.apply (ρ.vars "p") 1 < B by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    set ρ₄ := ρ₃.setVar "p" (ρ.vars "p" + 1) with hρ₄
    have hrun : Run B (.seq (.store (cluName j) (.get (xmmName j) (.var "p")) (.lit 1))
        (.seq (.store (memName (j + 1)) (.var "bq") (.get (xmmName j) (.var "p")))
          (.seq (.assign "bq" (.add (.var "bq") (.lit 1)))
            (.assign "p" (.add (.var "p") (.lit 1)))))) ρ ρ₄ 20 :=
      ((Run.store hidx (evalB_lit (by omega)) hlen).seq
        ((Run.store hbqe₁ hidx₁ hlen₁).seq
          ((Run.assign hbqinc).seq (Run.assign hpinc)))).mono (by simp [Expr.size])
    have hp₄ : ρ₄.vars "p" = ρ.vars "p" + 1 := by rw [hρ₄, vars_setVar, if_pos rfl]
    have hbq₄ : ρ₄.vars "bq" = ρ.vars "bq" + 1 := by
      rw [hρ₄, vars_setVar, if_neg (by decide), hρ₃, vars_setVar, if_pos rfl]
    refine ⟨ρ₄, 20, hrun, ?_, hp₄, le_rfl⟩
    refine ⟨?_, ?_, by omega, by omega, by omega, ⟨upd gm (ρ.vars "bq") (Xmem (ρ.vars "p")), ?_,
      ?_⟩, upd g (Xmem (ρ.vars "p")) 1, ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr,
        if_neg (by simp [memName, xmmName, String.ext_iff]), hρ₁, arrs_setArr,
        if_neg (by simp [cluName, xmmName, String.ext_iff])]
      exact hxmmρ
    · rw [hρ₄, vars_setVar, if_neg (by decide), hρ₃, vars_setVar, if_neg (by decide),
        hρ₂, vars_setArr, hρ₁, vars_setArr]
      exact hpend
    · rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_pos rfl, hρ₁, arrs_setArr,
        if_neg (Ne.symm hclumem), hgmarr, set_arrOf_eq_upd]
    · intro k hk
      rw [hp₄] at hk
      by_cases hke : k = ρ.vars "bq"
      · rw [hke, upd_self, show Xoff c + ρ.vars "bq" = ρ.vars "p" by omega]
      · rw [upd_of_ne _ hke]
        exact hgmval k (by omega)
    · rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_neg hclumem, hρ₁,
        arrs_setArr, if_pos rfl, hgarr, set_arrOf_eq_upd]
    · by_cases hke : k = Xmem (ρ.vars "p")
      · rw [hke, upd_self]
      · rw [upd_of_ne _ hke]; exact hgbit k hk
    · rw [hp₄]
      by_cases hke : k = Xmem (ρ.vars "p")
      · rw [hke, upd_self]
        exact ⟨fun _ => ⟨ρ.vars "p", hlo, by omega, rfl⟩, fun _ => one_ne_zero⟩
      · rw [upd_of_ne _ hke, hgval k hk]
        constructor
        · rintro ⟨p, h1, h2, h3⟩
          exact ⟨p, h1, by omega, h3⟩
        · rintro ⟨p, h1, h2, h3⟩
          rcases Nat.lt_or_ge p (ρ.vars "p") with h' | h'
          · exact ⟨p, h1, h', h3⟩
          · exact absurd (by rw [← h3, show p = ρ.vars "p" by omega]) hke
  -- the scan of the block
  have hI₃ : CluScan n j Xoff Xmem c σ₃ := by
    have hpv : σ₃.vars "p" = Xoff c := by
      rw [hσ₃, vars_setVar, if_neg (by decide), hσ₂, vars_setVar, if_pos rfl]
    have hbqv : σ₃.vars "bq" = 0 := by
      rw [hσ₃, vars_setVar, if_neg (by decide), hσ₂, vars_setVar, if_neg (by decide),
        hσ₁', vars_setVar, if_pos rfl]
    obtain ⟨gm₀, hgm₀⟩ := hmem₁
    refine ⟨by rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, hσ₁', arrs_setVar]; exact hxmm₁,
      by rw [hσ₃, vars_setVar, if_pos rfl],
      by rw [hpv], by rw [hpv]; exact hout.mono c hc, by rw [hpv, hbqv]; omega,
      ⟨gm₀, by rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, hσ₁', arrs_setVar]; exact hgm₀,
        fun k hk => by rw [hpv] at hk; omega⟩,
      g₁, by rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, hσ₁', arrs_setVar]; exact hg₁arr,
      fun k hk => by rw [hg₁val k hk]; omega, fun k hk => ?_⟩
    rw [hg₁val k hk]
    constructor
    · intro hcc; exact absurd rfl hcc
    · rintro ⟨p, hp1, hp2, -⟩
      rw [hpv] at hp2
      omega
  obtain ⟨σ₄, hr₄, hI₄, hp₄⟩ :=
    (Csr.rowScan_spec B (24 * blockSize Xoff c + 4) (Xoff (c + 1)) 20 "p" "pend"
      (.seq (.store (cluName j) (.get (xmmName j) (.var "p")) (.lit 1))
        (.seq (.store (memName (j + 1)) (.var "bq") (.get (xmmName j) (.var "p")))
          (.seq (.assign "bq" (.add (.var "bq") (.lit 1)))
            (.assign "p" (.add (.var "p") (.lit 1))))))
      (CluScan n j Xoff Xmem c) (hoffB (c + 1) (by omega))
      (fun ρ hρ => ⟨hρ.2.1, hρ.2.2.2.1⟩) hstep (fun _ hρ => hρ)
      (fun ρ hρ => by
        have hlo := hρ.2.2.1
        simp only [blockSize]
        omega)).run hI₃
  -- the exit reading
  obtain ⟨-, -, hlo₄, -, hbq₄, ⟨gm, hgmarr, hgmval⟩, g, hgarr, hgbit, hgval⟩ := hI₄
  rw [hp₄] at hgval hbq₄ hgmval
  have hoffle : Xoff c ≤ Xoff (c + 1) := hout.mono c hc
  refine ⟨σ₄, _, hr₁.seq (hr₁'.seq (hrLoad.seq hr₄)), by omega, g, hgarr, hgbit, ?_,
    gm, Xoff (c + 1) - Xoff c, hgmarr, hbq₄, rfl, ?_, ?_, ?_, ?_⟩
  · ext v
    rw [mem_markSet, Set.mem_setOf_eq, hcurEq, hgval (v : ℕ) v.isLt]
    exact hout.block c hc (v : ℕ)
  · -- every emitted cell is a vertex
    intro k hk
    rw [hgmval k hk]
    exact hout.mem_lt _ (lt_of_lt_of_le (by omega) (coverOut_off_le hout (c + 1) (by omega)))
  · -- and the emission is sorted, because the block row is
    intro i k hik hk
    rw [hgmval i (by omega), hgmval k hk]
    exact hout.block_mono c hc _ _ (by omega) (by omega) (by omega)
  · -- everything emitted is in the cluster
    intro k hk
    have hlt : gm k < n := by
      rw [hgmval k hk]
      exact hout.mem_lt _ (lt_of_lt_of_le (by omega) (coverOut_off_le hout (c + 1) (by omega)))
    rw [hgval (gm k) hlt]
    exact ⟨Xoff c + k, by omega, by omega, (hgmval k hk).symm⟩
  · -- and every member of the cluster was emitted
    intro a ha hXa
    obtain ⟨q, hq1, hq2, hq3⟩ := (hgval a ha).mp hXa
    refine ⟨q - Xoff c, by omega, ?_⟩
    rw [hgmval (q - Xoff c) (by omega), show Xoff c + (q - Xoff c) = q by omega]
    exact hq3

/-! ### One retained parent cache -/

/-- A walk whose whole support survives a mask can be read in that
masked graph.  This is the reverse direction of `Walk.mapLe`, specialized
to the induced masks used by the retained cache. -/
theorem walk_masked_of_support {M R : ℕ → ℕ} {u v : Fin n}
    (p : (masked G M).Walk u v) (hR : ∀ z ∈ p.support, R (z : ℕ) ≠ 0) :
    ∃ q : (masked G R).Walk u v, q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
      obtain ⟨q, hq⟩ := ih (fun z hz => hR z (by simp [hz]))
      refine ⟨.cons (RamBfs.masked_adj.mpr ⟨(RamBfs.masked_adj.mp hab).1, ?_, ?_⟩) q, ?_⟩
      · exact hR a (by simp)
      · exact hR b (by simp)
      · simp [hq]

/-- The charge of preparing the raw block's distance cells and running
the block-priced parent search. -/
def cacheRoundCost (mm bw nb : ℕ) : ℕ :=
  Refine.ScatterDeadPass.memFillAtCost mm +
    Refine.BfsBlockPar.bfsBlockParK bw nb + 4

/-- **One round's retained parent cache, discharged.** The member list
may enumerate a superset `X` of the retained mask `R`; cleaning that list
is enough because the block engine's distance contract is restricted to
the live support of `R`. -/
theorem cacheRoundCom_specW {d s mm bw nb : ℕ} {O T R X Mem : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb) (hs : s < n) (hsR : R s ≠ 0)
    (hMem : MemEnum n mm Mem X)
    (hRX : ∀ z, z < n → R z ≠ 0 → X z ≠ 0)
    (hRB : ∀ z, z < n → R z < B) {A : Finset ℕ}
    (hA : ∀ v, v < n → R v ≠ 0 → WD G R (2 * cap) s v → v ∈ A)
    (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw)
    (hnb : A.card ≤ nb) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars (ctrName j) = s ∧
        σ.vars "bq" = mm ∧ σ.arrs (memName (j + 1)) = arrOf n Mem ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs (resName j) = arrOf n R ∧
        (∃ g, σ.arrs (pdsName j) = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g) ∧
        (∃ g, σ.arrs (parName j) = arrOf n g))
      (cacheRoundCom cap j)
      (fun _ σ' => DistCleanAt (pdsName j) n (2 * cap) R σ' ∧
        ∃ D P, σ'.arrs (parName j) = arrOf n P ∧
          RamBfsPaths.ParTree G R (2 * cap) s D P)
      (cacheRoundCost mm bw nb) := by
  have hnB := hB.n_lt
  have hnsB := hB.ns_lt
  have h1B := hB.one_lt
  have hdB : 2 * cap + 1 < B := by have := hB.1; omega
  have hmmB : mm < B := lt_of_le_of_lt hMem.card_le hnB
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hctr, hbq, hmem, hoff, htgt, hres, ⟨D₀, hpds⟩,
    hq, hqd, hpar⟩ := hσ
  -- install the source
  have evsrc : (Expr.var (ctrName j)).evalB B σ = some s := by
    have h := evalB_var (B := B) (x := ctrName j) (σ := σ) (by rw [hctr]; omega)
    rwa [hctr] at h
  set σ₁ := σ.setVar "src" s with hσ₁
  have hr₁ : Run B (.assign "src" (.var (ctrName j))) σ σ₁ 2 :=
    (Run.assign evsrc).mono (by simp [Expr.size])
  -- expose the raw block length as the temporary member count
  have hbq₁ : σ₁.vars "bq" = mm := by
    rw [hσ₁, vars_setVar, if_neg (by decide), hbq]
  have evbq : (Expr.var "bq").evalB B σ₁ = some mm := by
    have h := evalB_var (B := B) (x := "bq") (σ := σ₁) (by rw [hbq₁]; exact hmmB)
    rwa [hbq₁] at h
  set σ₂ := σ₁.setVar (mnumName (j + 1)) mm with hσ₂
  have hr₂ : Run B (.assign (mnumName (j + 1)) (.var "bq")) σ₁ σ₂ 2 :=
    (Run.assign evbq).mono (by simp [Expr.size])
  have hmm₂ : σ₂.vars (mnumName (j + 1)) = mm := by rw [hσ₂]; simp
  have hmem₂ : σ₂.arrs (memName (j + 1)) = arrOf n Mem := by
    rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]
    exact hmem
  have hpds₂ : σ₂.arrs (pdsName j) = arrOf n D₀ := by
    rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]
    exact hpds
  -- clean only the emitted block
  obtain ⟨σ₃, hr₃, ⟨D₁, hpds₃, hfill, -⟩, -, -⟩ :=
    (Refine.ScatterDeadPass.memFillAt_spec (B := B) (n := n) (j := j) (mm1 := mm)
      (c := 2 * cap + 1) (a := pdsName j) (Mem1 := Mem) (g₀ := D₀) (A := X)
      h1B hnB hdB (by simp [pdsName, balAltName, memName, String.ext_iff]) hMem).run
      (σ := σ₂) ⟨hmm₂, hmem₂, hpds₂⟩
  have hclean₃ : DistCleanAt (pdsName j) n (2 * cap) R σ₃ := by
    refine ⟨D₁, hpds₃, ?_⟩
    intro z hz hRz
    obtain ⟨k, hk, hMemz⟩ := hMem.2.2.2 z hz (hRX z hz hRz)
    rw [← hMemz]
    exact hfill k hk
  have hfa₃ : ∀ a : String, a ≠ pdsName j → σ₃.arrs a = σ₂.arrs a := by
    intro a ha
    exact hr₃.frame_arr a (by
      rw [Refine.ScatterDeadPass.warrs_memFillAt]
      simp [ha])
  have hfv₃ : ∀ y : String, y ≠ "ac" → y ≠ "ax" → σ₃.vars y = σ₂.vars y := by
    intro y hya hyx
    exact hr₃.frame_var y
      (Refine.ScatterDeadPass.notMem_wvars_memFillAt j (pdsName j) (2 * cap + 1) hya hyx)
  have hn₃ : σ₃.vars "n" = n := by
    rw [hfv₃ "n" (by decide) (by decide), hσ₂, vars_setVar,
      if_neg (by simp [mnumName, String.ext_iff]), hσ₁, vars_setVar,
      if_neg (by decide)]
    exact hn
  have hsrc₃ : σ₃.vars "src" = s := by
    rw [hfv₃ "src" (by decide) (by decide), hσ₂, vars_setVar,
      if_neg (by simp [mnumName, String.ext_iff]), hσ₁, vars_setVar, if_pos rfl]
  have harr₃ : ∀ a : String, a ≠ pdsName j → σ₃.arrs a = σ.arrs a := by
    intro a ha
    rw [hfa₃ a ha, hσ₂, arrs_setVar, hσ₁, arrs_setVar]
  -- run the retained parent engine
  obtain ⟨σ₄, hr₄, hclean₄, D, P, hpar₄, htree⟩ :=
    (cacheBfsCom_specW (j := j) hcsr hs hsR hnB hnsB hnt hdB hRB hA hbw hnb).run
      (σ := σ₃) ⟨hn₃, hsrc₃,
        by rw [harr₃ "off" (by simp [pdsName, balAltName, String.ext_iff])]; exact hoff,
        by rw [harr₃ "tgt" (by simp [pdsName, balAltName, String.ext_iff])]; exact htgt,
        by rw [harr₃ _ (by simp [resName, pdsName, balAltName, String.ext_iff])]; exact hres,
        hclean₃,
        by rw [harr₃ "q" (by simp [pdsName, balAltName, String.ext_iff])]; exact hq,
        by rw [harr₃ "qd" (by simp [pdsName, balAltName, String.ext_iff])]; exact hqd,
        by rw [harr₃ _ (by simp [parName, balName, pdsName, balAltName, String.ext_iff])]; exact hpar⟩
  refine ⟨σ₄, _, hr₁.seq (hr₂.seq (hr₃.seq hr₄)), ?_, hclean₄, D, P, hpar₄, htree⟩
  simp only [cacheRoundCost]
  omega

/-! ### The child's member list (rebase E-mem)

`clusterLoad` emitted the *block row* — the parent cluster's member
list, in the row's own order, `"bq"` cells of it. The child's list is
that row filtered by the child's own mask and compacted in place, which
is `RamDriver.memFilterCom`. The pass walks `"bq"` cells, never the
carrier, and it is *stable*, so the child list inherits the row's order:
sortedness is a supply chain whose first link is
`RamCover.CoverOut.block_mono`, and whose refutation, if that link ever
breaks, is `Refine.MemThreadProbe.unsorted_emission_refuted`.

The while is `Csr.scan "mk" "bq"`, so `Csr.rowScan_spec` carries it; the
only content is the invariant below. -/

/-- What the filter's scan carries: the read pointer inside the block,
the write pointer behind it, the raw list still untouched above the read
pointer — and the emitted prefix, sound, complete and strictly
increasing against the part of the raw list already read. -/
def MemFilt (n j bs : ℕ) (Mm A : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "bq" = bs ∧ σ.vars "mk" ≤ bs ∧ σ.vars (mnumName j) ≤ σ.vars "mk" ∧
    σ.arrs (alvName j) = arrOf n A ∧
    ∃ g, σ.arrs (memName j) = arrOf n g ∧
      (∀ i, σ.vars "mk" ≤ i → i < n → g i = Mm i) ∧
      (∀ q, q < σ.vars (mnumName j) → ∃ p, p < σ.vars "mk" ∧ g q = Mm p ∧ A (Mm p) ≠ 0) ∧
      (∀ p, p < σ.vars "mk" → A (Mm p) ≠ 0 → ∃ q, q < σ.vars (mnumName j) ∧ g q = Mm p) ∧
      (∀ q₁ q₂, q₁ < q₂ → q₂ < σ.vars (mnumName j) → g q₁ < g q₂)

/-- **The filter pass, discharged.** From a raw list of `bs` cells that
is repetition-free and increasing and contains every vertex the mask
`A` marks, the pass leaves a `MemEnum` of `A` in the live prefix.

The completeness hypothesis `hcov` is where "the child is inside the
block" is spent: `RamDriverCluster.DescendStep`'s own clause says the
next depth's mask marks only cluster members, and `clusterLoad_spec`
says the raw list is exactly the cluster.

**The cost is charged at the block**, not at the carrier: `23·bs + 8`,
the two-counter head's `4 + 4` plus `19 + 4` per block cell — the taken
branch's store and bump, plus the scan's own test. The probe's measured
`21·bs + 8` (`Refine.MemThreadProbe.filterClock`) is the clock of one
particular block, two of whose three members survive the filter; `23` is
the uniform per-cell bound the walk can carry, and the two agree on the
all-alive block. -/
theorem memFilter_spec {bs : ℕ} {Mm A : ℕ → ℕ} (hnB : n < B) (hbsn : bs ≤ n)
    (hMmlt : ∀ k, k < bs → Mm k < n)
    (hMmmono : ∀ i k, i < k → k < bs → Mm i < Mm k)
    (hAB : ∀ k, k < n → A k < B)
    (hcov : ∀ a, a < n → A a ≠ 0 → ∃ k, k < bs ∧ Mm k = a) :
    Spec B (fun σ => σ.arrs (memName j) = arrOf n Mm ∧ σ.vars "bq" = bs ∧
        σ.arrs (alvName j) = arrOf n A)
      (memFilterCom j)
      (fun _ σ' => ∃ (Mem' : ℕ → ℕ) (mm' : ℕ), σ'.arrs (memName j) = arrOf n Mem' ∧
        σ'.vars (mnumName j) = mm' ∧ MemEnum n mm' Mem' A ∧ ∀ z, z < mm' → Mem' z < B)
      (23 * bs + 8) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hmem, hbq, halv⟩ := hσ
  have hbsB : bs < B := by omega
  -- the two counters
  set σ₁ := σ.setVar "mk" 0 with hσ₁
  have hr₁ : Run B (.assign "mk" (.lit 0)) σ σ₁ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  set σ₂ := σ₁.setVar (mnumName j) 0 with hσ₂
  have hr₂ : Run B (.assign (mnumName j) (.lit 0)) σ₁ σ₂ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hmknum : ("mk" : String) ≠ mnumName j := by simp [mnumName, String.ext_iff]
  have hmvnum : ("mv" : String) ≠ mnumName j := by simp [mnumName, String.ext_iff]
  have hbqnum : ("bq" : String) ≠ mnumName j := by simp [mnumName, String.ext_iff]
  have hmemalv : memName j ≠ alvName j := by simp [memName, alvName, String.ext_iff]
  -- one block cell: read it, keep it if the child's mask keeps it, step on
  have hstep : ∀ ρ : Env, MemFilt n j bs Mm A ρ → ρ.vars "mk" < bs →
      ∃ ρ' K', Run B (.seq (.assign "mv" (.get (memName j) (.var "mk")))
          (.seq (.ite (.lt (.lit 0) (.get (alvName j) (.var "mv")))
              (.seq (.store (memName j) (.var (mnumName j)) (.var "mv"))
                (.assign (mnumName j) (.add (.var (mnumName j)) (.lit 1))))
              .skip)
            (.assign "mk" (.add (.var "mk") (.lit 1))))) ρ ρ' K' ∧
        MemFilt n j bs Mm A ρ' ∧ ρ'.vars "mk" = ρ.vars "mk" + 1 ∧ K' ≤ 19 := by
    intro ρ hρ hlt
    obtain ⟨hbqρ, hmkρ, hmmρ, halvρ, g, hgarr, hsuf, hsound, hcomp, hmono⟩ := hρ
    set mk := ρ.vars "mk" with hmk
    set mm := ρ.vars (mnumName j) with hmm
    have hmkn : mk < n := by omega
    have hgmk : g mk = Mm mk := hsuf mk le_rfl hmkn
    have hvn : Mm mk < n := hMmlt mk hlt
    -- the read
    have hmke : (Expr.var "mk").evalB B ρ = some mk := by
      have h := evalB_var (B := B) (x := "mk") (σ := ρ) (by omega)
      rwa [← hmk] at h
    have hread : (Expr.get (memName j) (.var "mk")).evalB B ρ = some (Mm mk) :=
      evalB_get hmke (by rw [hgarr, getElem?_arrOf g hmkn, hgmk]) (by omega)
    set ρ₁ := ρ.setVar "mv" (Mm mk) with hρ₁
    have hr'₁ : Run B (.assign "mv" (.get (memName j) (.var "mk"))) ρ ρ₁ 3 :=
      (Run.assign hread).mono (by simp [Expr.size])
    have hmv₁ : ρ₁.vars "mv" = Mm mk := by rw [hρ₁, vars_setVar, if_pos rfl]
    have hmk₁ : ρ₁.vars "mk" = mk := by rw [hρ₁, vars_setVar, if_neg (by decide)]
    have hmm₁ : ρ₁.vars (mnumName j) = mm := by
      rw [hρ₁, vars_setVar, if_neg (Ne.symm hmvnum)]
    have hbq₁ : ρ₁.vars "bq" = bs := by rw [hρ₁, vars_setVar, if_neg (by decide)]; exact hbqρ
    have hmem₁ : ρ₁.arrs (memName j) = arrOf n g := by rw [hρ₁, arrs_setVar]; exact hgarr
    have halv₁ : ρ₁.arrs (alvName j) = arrOf n A := by rw [hρ₁, arrs_setVar]; exact halvρ
    have hcond : (Cond.lt (.lit 0) (.get (alvName j) (.var "mv"))).evalB B ρ₁ =
        some (decide (0 < A (Mm mk))) := by
      refine evalB_condLt (evalB_lit (by omega)) ?_
      refine evalB_get ?_ (by rw [halv₁, getElem?_arrOf A hvn]) (hAB _ hvn)
      have h := evalB_var (B := B) (x := "mv") (σ := ρ₁) (by rw [hmv₁]; omega)
      rwa [hmv₁] at h
    -- the tail: step the read pointer
    have htail : ∀ τ : Env, τ.vars "mk" = mk →
        ∃ τ' , Run B (.assign "mk" (.add (.var "mk") (.lit 1))) τ τ' 4 ∧
          τ' = τ.setVar "mk" (mk + 1) := by
      intro τ hτ
      have he : (Expr.add (Expr.var "mk") (.lit 1)).evalB B τ = some (mk + 1) := by
        have h := evalB_bin (evalB_var (B := B) (x := "mk") (σ := τ) (by rw [hτ]; omega))
          (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
          (show Bop.add.apply (τ.vars "mk") 1 < B by rw [Bop.apply_add, hτ]; omega)
        rw [Bop.apply_add, hτ] at h
        exact h
      exact ⟨_, (Run.assign he).mono (by simp [Expr.size]), rfl⟩
    by_cases hkeep : 0 < A (Mm mk)
    · -- the cell survives: store it at the write pointer and bump
      have hmmn : mm < n := by omega
      have hmme₁ : (Expr.var (mnumName j)).evalB B ρ₁ = some mm := by
        have h := evalB_var (B := B) (x := mnumName j) (σ := ρ₁) (by rw [hmm₁]; omega)
        rwa [hmm₁] at h
      have hmve₁ : (Expr.var "mv").evalB B ρ₁ = some (Mm mk) := by
        have h := evalB_var (B := B) (x := "mv") (σ := ρ₁) (by rw [hmv₁]; omega)
        rwa [hmv₁] at h
      have hlen₁ : mm < (ρ₁.arrs (memName j)).length := by
        rw [hmem₁, length_arrOf]; exact hmmn
      set ρ₂ := ρ₁.setArr (memName j) mm (Mm mk) with hρ₂
      have hmm₂ : ρ₂.vars (mnumName j) = mm := by rw [hρ₂, vars_setArr]; exact hmm₁
      have hmme₂ : (Expr.add (Expr.var (mnumName j)) (.lit 1)).evalB B ρ₂ = some (mm + 1) := by
        have h := evalB_bin (evalB_var (B := B) (x := mnumName j) (σ := ρ₂) (by rw [hmm₂]; omega))
          (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
          (show Bop.add.apply (ρ₂.vars (mnumName j)) 1 < B by rw [Bop.apply_add, hmm₂]; omega)
        rw [Bop.apply_add, hmm₂] at h
        exact h
      set ρ₃ := ρ₂.setVar (mnumName j) (mm + 1) with hρ₃
      have hmk₃ : ρ₃.vars "mk" = mk := by
        rw [hρ₃, vars_setVar, if_neg hmknum, hρ₂, vars_setArr, hmk₁]
      obtain ⟨ρ₄, hr'₄, hρ₄⟩ := htail ρ₃ hmk₃
      have hmk₄ : ρ₄.vars "mk" = mk + 1 := by rw [hρ₄, vars_setVar, if_pos rfl]
      have hmm₄ : ρ₄.vars (mnumName j) = mm + 1 := by
        rw [hρ₄, vars_setVar, if_neg (Ne.symm hmknum), hρ₃, vars_setVar, if_pos rfl]
      have hbq₄ : ρ₄.vars "bq" = bs := by
        rw [hρ₄, vars_setVar, if_neg (by decide), hρ₃, vars_setVar, if_neg hbqnum,
          hρ₂, vars_setArr]
        exact hbq₁
      have hmem₄ : ρ₄.arrs (memName j) = arrOf n (upd g mm (Mm mk)) := by
        rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_pos rfl, hmem₁,
          set_arrOf_eq_upd]
      have halv₄ : ρ₄.arrs (alvName j) = arrOf n A := by
        rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_neg (Ne.symm hmemalv)]
        exact halv₁
      refine ⟨ρ₄, 19, ((hr'₁.seq ((Run.ite_true (by rw [hcond]; simp [hkeep])
        ((Run.store hmme₁ hmve₁ hlen₁).seq (Run.assign hmme₂))).seq hr'₄))).mono
          (by simp [Expr.size, Cond.size]), ?_, hmk₄, le_rfl⟩
      refine ⟨hbq₄, by omega, by omega, halv₄, upd g mm (Mm mk), hmem₄, ?_, ?_, ?_, ?_⟩
      · intro i hi hin
        rw [hmk₄] at hi
        have hne : i ≠ mm := by omega
        rw [upd_of_ne _ hne]
        exact hsuf i (by omega) hin
      · intro q hq
        rw [hmm₄] at hq
        rw [hmk₄]
        by_cases hqm : q = mm
        · exact ⟨mk, by omega, by rw [hqm, upd_self], by omega⟩
        · obtain ⟨p, hp1, hp2, hp3⟩ := hsound q (by omega)
          exact ⟨p, by omega, by rw [upd_of_ne _ hqm]; exact hp2, hp3⟩
      · intro p hp hAp
        rw [hmk₄] at hp
        rw [hmm₄]
        by_cases hpm : p = mk
        · exact ⟨mm, by omega, by rw [upd_self, hpm]⟩
        · obtain ⟨q, hq1, hq2⟩ := hcomp p (by omega) hAp
          have hne : q ≠ mm := by omega
          exact ⟨q, by omega, by rw [upd_of_ne _ hne]; exact hq2⟩
      · intro q₁ q₂ h12 hq2
        rw [hmm₄] at hq2
        by_cases hq2m : q₂ = mm
        · have hne : q₁ ≠ mm := by omega
          rw [hq2m, upd_self, upd_of_ne _ hne]
          obtain ⟨p, hp1, hp2, -⟩ := hsound q₁ (by omega)
          rw [hp2]
          exact hMmmono p mk hp1 hlt
        · have hne : q₁ ≠ mm := by omega
          rw [upd_of_ne _ hne, upd_of_ne _ hq2m]
          exact hmono q₁ q₂ h12 (by omega)
    · -- the cell dies: the read pointer alone moves
      obtain ⟨ρ₄, hr'₄, hρ₄⟩ := htail ρ₁ hmk₁
      have hA0 : A (Mm mk) = 0 := by omega
      have hmk₄ : ρ₄.vars "mk" = mk + 1 := by rw [hρ₄, vars_setVar, if_pos rfl]
      have hmm₄ : ρ₄.vars (mnumName j) = mm := by
        rw [hρ₄, vars_setVar, if_neg (Ne.symm hmknum)]; exact hmm₁
      have hbq₄ : ρ₄.vars "bq" = bs := by
        rw [hρ₄, vars_setVar, if_neg (by decide)]; exact hbq₁
      have hmem₄ : ρ₄.arrs (memName j) = arrOf n g := by rw [hρ₄, arrs_setVar]; exact hmem₁
      have halv₄ : ρ₄.arrs (alvName j) = arrOf n A := by rw [hρ₄, arrs_setVar]; exact halv₁
      refine ⟨ρ₄, 19, ((hr'₁.seq ((Run.ite_false (by rw [hcond]; simp [hkeep])
        Run.skip).seq hr'₄))).mono (by simp [Expr.size, Cond.size]), ?_, hmk₄, le_rfl⟩
      refine ⟨hbq₄, by omega, by omega, halv₄, g, hmem₄, ?_, ?_, ?_, ?_⟩
      · intro i hi hin
        rw [hmk₄] at hi
        exact hsuf i (by omega) hin
      · intro q hq
        rw [hmm₄] at hq
        rw [hmk₄]
        obtain ⟨p, hp1, hp2, hp3⟩ := hsound q hq
        exact ⟨p, by omega, hp2, hp3⟩
      · intro p hp hAp
        rw [hmk₄] at hp
        rw [hmm₄]
        have hpm : p ≠ mk := by
          rintro rfl
          exact hAp hA0
        exact hcomp p (by omega) hAp
      · intro q₁ q₂ h12 hq2
        rw [hmm₄] at hq2
        exact hmono q₁ q₂ h12 hq2
  -- the scan, entered at both counters zero
  have hI₂ : MemFilt n j bs Mm A σ₂ := by
    have hmk₂ : σ₂.vars "mk" = 0 := by
      rw [hσ₂, vars_setVar, if_neg hmknum, hσ₁, vars_setVar, if_pos rfl]
    have hmm₂ : σ₂.vars (mnumName j) = 0 := by rw [hσ₂, vars_setVar, if_pos rfl]
    have hbq₂ : σ₂.vars "bq" = bs := by
      rw [hσ₂, vars_setVar, if_neg hbqnum, hσ₁, vars_setVar, if_neg (by decide)]
      exact hbq
    refine ⟨hbq₂, by omega, by omega, ?_, Mm, ?_, fun i _ _ => rfl, ?_, ?_, ?_⟩
    · rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact halv
    · rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact hmem
    · intro q hq; rw [hmm₂] at hq; omega
    · intro p hp; rw [hmk₂] at hp; omega
    · intro q₁ q₂ _ hq2; rw [hmm₂] at hq2; omega
  obtain ⟨σ₃, hr₃, hI₃, hmk₃⟩ :=
    (Csr.rowScan_spec B (23 * bs + 4) bs 19 "mk" "bq"
      (.seq (.assign "mv" (.get (memName j) (.var "mk")))
        (.seq (.ite (.lt (.lit 0) (.get (alvName j) (.var "mv")))
            (.seq (.store (memName j) (.var (mnumName j)) (.var "mv"))
              (.assign (mnumName j) (.add (.var (mnumName j)) (.lit 1))))
            .skip)
          (.assign "mk" (.add (.var "mk") (.lit 1)))))
      (MemFilt n j bs Mm A) hbsB (fun ρ hρ => ⟨hρ.1, hρ.2.1⟩) hstep (fun _ hρ => hρ)
      (fun ρ hρ => by
        have h : (19 + 4) * (bs - ρ.vars "mk") ≤ 23 * bs :=
          Nat.mul_le_mul le_rfl (by omega)
        omega)).run hI₂
  -- the exit reading
  obtain ⟨-, -, hmmle, -, g, hgarr, -, hsound, hcomp, hmono⟩ := hI₃
  rw [hmk₃] at hsound hcomp
  refine ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), by omega, g, σ₃.vars (mnumName j), hgarr, rfl,
    ⟨fun k hk => ?_, fun i k hik hk => hmono i k hik hk, fun k hk => ?_, fun a ha hAa => ?_⟩,
    fun z hz => ?_⟩
  · obtain ⟨p, hp1, hp2, -⟩ := hsound k hk
    rw [hp2]; exact hMmlt p hp1
  · obtain ⟨p, -, hp2, hp3⟩ := hsound k hk
    rw [hp2]; exact hp3
  · obtain ⟨p, hp1, hp2⟩ := hcov a ha hAa
    obtain ⟨q, hq1, hq2⟩ := hcomp p hp1 (by rw [hp2]; exact hAa)
    exact ⟨q, hq1, by rw [hq2, hp2]⟩
  · obtain ⟨p, hp1, hp2, -⟩ := hsound z hz
    rw [hp2]
    exact lt_trans (hMmlt p hp1) hnB

/-! ### A standalone materialised game ball

This discharged expansion remains as a reusable specification of the
former descent pass. It runs in the *game* mask and leaves `balName j`
holding the `2·cap`-ball of the connector. `descendCom` no longer calls
it: the executable retains the cover cluster directly, and the cover
theory proves that cluster is contained in this mathematical ball. -/

/-- The chain's reading of a ball: `ballOf` measures from the member,
`ball` from the centre, and `WithinDist` is symmetric. -/
theorem ballOf_singleton_eq_ball (A : SimpleGraph (Fin n)) (r : ℕ) (u : Fin n) :
    ballOf A r {u} = ball A r u := by
  rw [ballOf_singleton]
  ext x
  rw [Set.mem_setOf_eq, mem_ball]
  exact ⟨withinDist_symm, withinDist_symm⟩

/-- The cost of the ball's chain. -/
def ballCost (n ns cap : ℕ) : ℕ := (24 * ns + 44 * n + 6) * (2 * cap) + 11 * n + 12

/-- **The standalone materialised game ball, discharged.** -/
theorem ballCom_spec {Gm : ℕ → ℕ} {O T : ℕ → ℕ} (hcsr : CsrGraph G ns O T)
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hnt : ns ≤ nt) (hGmB : ∀ k, k < n → Gm k < B)
    {v : Fin n} :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf nt T ∧ σ.arrs (gamName j) = arrOf n Gm ∧
        (∃ g, σ.arrs (balName j) = arrOf n g) ∧ (∃ g, σ.arrs (balAltName j) = arrOf n g) ∧
        σ.vars (ctrName j) = (v : ℕ))
      (.seq (fillCom (balName j) (.lit 0))
        (.seq (.store (balName j) (.var (ctrName j)) (.lit 1))
          (chainCom (gamName j) (ballStage j) (2 * cap))))
      (fun _ σ' => (∃ g, σ'.arrs (balName j) = arrOf n g ∧ (∀ k, k < n → g k ≤ 1) ∧
          markSet n g = ball (masked G Gm) (2 * cap) v) ∧
        σ'.vars "n" = n ∧ σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧
        σ'.arrs (gamName j) = arrOf n Gm)
      (ballCost n ns cap) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hoff, htgt, hgam, hbal, halt, hctr⟩ := hσ
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  have hbg : balName j ≠ gamName j := by simp [balName, gamName, String.ext_iff]
  -- the ball's array, opened at the connector
  obtain ⟨σ₁, hr₁, ⟨⟨g₁, hg₁arr, hg₁val⟩, -, hn₁⟩, hfv₁, hfa₁, -, -⟩ :=
    ((fillCom_spec B n (balName j) 0 hnB (by omega)).frame).run ⟨hbal, hn⟩
  have hav₁ : ∀ a : String, a ≠ balName j → σ₁.arrs a = σ.arrs a := fun a ha =>
    hfa₁ a (by rw [RamDriverIO.warrs_fillCom]; simpa using ha)
  have hctr₁ : σ₁.vars (ctrName j) = (v : ℕ) := by
    rw [hfv₁ _ (by
      rw [RamDriverIO.wvars_fillCom]
      exact RamDriverIO.notMem_of_append (p := "ctr") (s := toString j) (by decide))]
    exact hctr
  have hidx : (Expr.var (ctrName j)).evalB B σ₁ = some (v : ℕ) := by
    have h := evalB_var (B := B) (x := ctrName j) (σ := σ₁) (by rw [hctr₁]; omega)
    rwa [hctr₁] at h
  have hlen : (v : ℕ) < (σ₁.arrs (balName j)).length := by
    rw [hg₁arr, length_arrOf]; exact v.isLt
  set σ₂ := σ₁.setArr (balName j) (v : ℕ) 1 with hσ₂
  have hr₂ : Run B (.store (balName j) (.var (ctrName j)) (.lit 1)) σ₁ σ₂ 3 :=
    (Run.store hidx (evalB_lit (by omega)) hlen).mono (by simp [Expr.size])
  have hg₂ : σ₂.arrs (balName j) = arrOf n (upd g₁ (v : ℕ) 1) := by
    rw [hσ₂]; simp [hg₁arr, set_arrOf_eq_upd]
  have hSB : ∀ k, k < n → upd g₁ (v : ℕ) 1 k ≤ 1 := by
    intro k hk
    by_cases hke : k = (v : ℕ)
    · rw [hke, upd_self]
    · rw [upd_of_ne _ hke, hg₁val k hk]; omega
  have hSmark : markSet n (upd g₁ (v : ℕ) 1) = {v} := by
    ext u
    rw [mem_markSet, Set.mem_singleton_iff]
    constructor
    · intro hu
      by_cases hue : (u : ℕ) = (v : ℕ)
      · exact Fin.ext hue
      · exact absurd (by rw [upd_of_ne _ hue, hg₁val (u : ℕ) u.isLt]) hu
    · rintro rfl
      rw [upd_self]
      omega
  -- the chain, in the game mask
  have hoff₂ : σ₂.arrs "off" = arrOf (n + 1) O := by
    rw [hσ₂, arrs_setArr, if_neg (by simp [balName, String.ext_iff]),
      hav₁ "off" (by simp [balName, String.ext_iff])]
    exact hoff
  have htgt₂ : σ₂.arrs "tgt" = arrOf nt T := by
    rw [hσ₂, arrs_setArr, if_neg (by simp [balName, String.ext_iff]),
      hav₁ "tgt" (by simp [balName, String.ext_iff])]
    exact htgt
  have hgam₂ : σ₂.arrs (gamName j) = arrOf n Gm := by
    rw [hσ₂, arrs_setArr, if_neg (Ne.symm hbg), hav₁ _ (Ne.symm hbg)]
    exact hgam
  have hn₂ : σ₂.vars "n" = n := by rw [hσ₂, vars_setArr]; exact hn₁
  have halt₂ : ∃ g, σ₂.arrs (balAltName j) = arrOf n g := by
    obtain ⟨ga, hga⟩ := halt
    refine ⟨ga, ?_⟩
    rw [hσ₂, arrs_setArr, if_neg (by simp [balName, balAltName, String.ext_iff]),
      hav₁ _ (by simp [balName, balAltName, String.ext_iff])]
    exact hga
  have hstages : ∀ a, 0 < a → a ≤ 2 * cap → ∃ g, σ₂.arrs (ballStage j a) = arrOf n g := by
    intro a _ _
    rw [ballStage]
    split
    · exact ⟨upd g₁ (v : ℕ) 1, hg₂⟩
    · exact halt₂
  obtain ⟨σ₃, hr₃, ⟨g, hgarr, hgB, hgmark⟩, hn₃, hoff₃, htgt₃, hgam₃⟩ :=
    (chainCom_spec (msk := gamName j) (Msk := Gm) (nt := nt) hcsr h1B hnB hB.ns_lt hnt
      hGmB (2 * cap)
      (ballStage j) (upd g₁ (v : ℕ) 1) (fun a => ballStage_ne j a)
      (fun a => by rw [ballStage]; split <;> simp [balName, balAltName, gamName, String.ext_iff])
      (fun a => by rw [ballStage]; split <;> simp [balName, balAltName, String.ext_iff])
      (fun a => by rw [ballStage]; split <;> simp [balName, balAltName, String.ext_iff])
      hSB).run
      ⟨hn₂, hoff₂, htgt₂, hgam₂, by rw [ballStage_zero]; exact hg₂, hstages⟩
  refine ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), by simp only [ballCost]; omega,
    ⟨g, by rw [← ballStage_two_mul j cap]; exact hgarr, hgB, ?_⟩, hn₃, hoff₃, htgt₃, hgam₃⟩
  rw [hgmark, hSmark, ballOf_singleton_eq_ball]

end Cluster

/-! ### A flat pass that reads its own destination

`RamDriver.descendCom`'s last pass is
`subCom (gamName (j + 1)) (batName j) (gamName (j + 1))`: the source and
the destination are the same array. The pass is correct — a flat pass
writes cell `i` from cell `i` of everything it reads, so no cell is read
after it is written — but `RamDriverCluster.fill_spec` cannot see that.
Its readers are a `RamDriverCluster.Frozen` family, which is an equation
about the *whole* array and is false of the destination halfway through
the loop, and `subCom_spec` therefore asks `a ≠ dst`.

The repair is one invariant: below the counter the array holds the new
value, at and above it the old one. `SelfBelow` is that invariant,
`selfFill_spec` the pass, and `subSelfCom_spec` the mask operation the
driver's last pass is. The old value is a *parameter*, so the cell
expression may read it, which is exactly what the aliasing pass needs
and what `Frozen` cannot express.

Nothing else in the driver aliases, so this is stated once and used
once. -/

section SelfFill

variable {B : ℕ}

/-- **The invariant of an in-place flat pass.** The array has the
carrier's length throughout; below the counter it holds the new cell
function, at and above it the old one. -/
def SelfBelow (a x : String) (N : ℕ) (g₀ F : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ g, σ.arrs a = arrOf N g ∧ σ.vars x ≤ N ∧
    (∀ k, k < σ.vars x → g k = F k) ∧ (∀ k, σ.vars x ≤ k → g k = g₀ k)

theorem SelfBelow.le {a x : String} {N : ℕ} {g₀ F : ℕ → ℕ} {σ : Env}
    (h : SelfBelow a x N g₀ F σ) : σ.vars x ≤ N := h.choose_spec.2.1

/-- The cell the counter stands on still holds the old value: this is
what lets the cell expression read the destination. -/
theorem SelfBelow.get {a x : String} {N : ℕ} {g₀ F : ℕ → ℕ} {σ : Env}
    (h : SelfBelow a x N g₀ F σ) : σ.arrs a = arrOf N h.choose ∧
      ∀ k, σ.vars x ≤ k → h.choose k = g₀ k :=
  ⟨h.choose_spec.1, h.choose_spec.2.2.2⟩

/-- **The exit reading**: the counter at the end means the whole array
holds the new cell function. -/
theorem SelfBelow.done {a x : String} {N : ℕ} {g₀ F : ℕ → ℕ} {σ : Env}
    (h : SelfBelow a x N g₀ F σ) (hx : σ.vars x = N) :
    ∃ g, σ.arrs a = arrOf N g ∧ ∀ k, k < N → g k = F k :=
  ⟨h.choose, h.choose_spec.1, fun k hk => h.choose_spec.2.2.1 k (by rw [hx]; exact hk)⟩

/-- **A flat pass that may read the cell it is about to write.** The
shape of `RamDriverCluster.fill_spec`, with the destination's *entering*
cell function carried by the invariant instead of frozen. -/
theorem selfFill_spec (N : ℕ) (a : String) (e : Expr) (g₀ F : ℕ → ℕ)
    (l : List (String × ℕ × (ℕ → ℕ))) (ha : ∀ p ∈ l, p.1 ≠ a) (hNB : N < B)
    (he : ∀ σ : Env, Frozen l σ → SelfBelow a "i" N g₀ F σ → σ.vars "i" < N →
      e.evalB B σ = some (F (σ.vars "i"))) :
    Spec B (fun σ => σ.arrs a = arrOf N g₀ ∧ σ.vars "n" = N ∧ Frozen l σ)
      (fillUpto a (.var "n") e)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf N g ∧ ∀ k, k < N → g k = F k) ∧
        σ'.vars "i" = N ∧ σ'.vars "n" = N ∧ Frozen l σ')
      ((10 + e.size) * N + 6) := by
  have hbody : Spec B
      (fun σ => (SelfBelow a "i" N g₀ F σ ∧ σ.vars "n" = N ∧ Frozen l σ) ∧ σ.vars "i" < N)
      (Fill.put a "i" e)
      (fun σ σ' => (SelfBelow a "i" N g₀ F σ' ∧ σ'.vars "n" = N ∧ Frozen l σ') ∧
        σ'.vars "i" = σ.vars "i" + 1)
      (6 + e.size) := by
    rintro σ ⟨⟨hbel, hn, hfr⟩, hlt⟩
    obtain ⟨g, harr, hle, hlow, hhigh⟩ := hbel
    have hev := he σ hfr ⟨g, harr, hle, hlow, hhigh⟩ hlt
    have hiB : σ.vars "i" < B := by omega
    refine ⟨(σ.setArr a (σ.vars "i") (F (σ.vars "i"))).setVar "i" (σ.vars "i" + 1), ?_, ?_, by simp⟩
    · refine (Run.seq (Run.store (evalB_var hiB) hev (by rw [harr, length_arrOf]; omega))
        (Run.assign (evalB_bin (evalB_var (by rw [vars_setArr]; exact hiB))
          (evalB_lit (by omega)) ?_))).mono (by simp [Expr.size]; omega)
      simp only [Bop.apply_add, vars_setArr]
      omega
    · refine ⟨⟨upd g (σ.vars "i") (F (σ.vars "i")), by
        simp [harr, set_arrOf_eq_upd], by simp; omega, fun k hk => ?_, fun k hk => ?_⟩,
        by simp [hn], fun p hp => ?_⟩
      · rw [vars_setVar, if_pos rfl] at hk
        by_cases hke : k = σ.vars "i"
        · rw [hke, upd_self]
        · rw [upd_of_ne _ hke]; exact hlow k (by omega)
      · rw [vars_setVar, if_pos rfl] at hk
        rw [upd_of_ne _ (by omega)]
        exact hhigh k (by omega)
      · rw [arrs_setVar, arrs_setArr, if_neg (ha p hp)]
        exact hfr p hp
  refine ((Spec.forRangeZero "i" "n"
    (fun σ => SelfBelow a "i" N g₀ F σ ∧ σ.vars "n" = N ∧ Frozen l σ) N (6 + e.size) hNB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2.1) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨harr, hn, hfr⟩
    refine ⟨⟨g₀, by rw [arrs_setVar]; exact harr, by simp, ?_, ?_⟩,
      by simp [hn], fun p hp => by rw [arrs_setVar]; exact hfr p hp⟩
    · intro k hk
      rw [vars_setVar, if_pos rfl] at hk
      exact absurd hk (by omega)
    · intro k _; rfl
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2, hq.2, hq.1.2.1, hq.1.2.2⟩

/-- **The mask conjunction, in place**: `RamDriver.andCom` with its first
source and its destination the same array, which is what the last pass of
`RamDriver.batchCom` is — the batch cut down to the retained cluster. -/
theorem andSelfCom_spec (N : ℕ) (b dst : String) (ga gb : ℕ → ℕ)
    (hbd : b ≠ dst) (hNB : N < B) (haB : ∀ k, k < N → ga k < B)
    (hbB : ∀ k, k < N → gb k < B) (habB : ∀ k, k < N → ga k * gb k < B) :
    Spec B (fun σ => σ.arrs dst = arrOf N ga ∧ σ.vars "n" = N ∧ σ.arrs b = arrOf N gb)
      (andCom dst b dst)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf N h ∧ ∀ k, k < N → h k = ga k * gb k) ∧
        σ'.vars "i" = N ∧ σ'.vars "n" = N ∧ σ'.arrs b = arrOf N gb)
      (15 * N + 6) := by
  refine ((selfFill_spec N dst _ ga (fun k => ga k * gb k) [(b, N, gb)]
    (by rintro p hp; rcases List.mem_singleton.mp hp with rfl; exact hbd) hNB ?_).pre ?_).post ?_
      |>.mono (by simp [Expr.size])
  · intro σ hfr hbel hlt
    obtain ⟨g, harr, -, -, hhigh⟩ := hbel
    have hb : σ.arrs b = arrOf N gb := hfr (b, N, gb) (by simp)
    have hgi : g (σ.vars "i") = ga (σ.vars "i") := hhigh _ le_rfl
    exact evalB_bin
      (evalB_get (evalB_var (by omega)) (by rw [harr, getElem?_arrOf g hlt, hgi]) (haB _ hlt))
      (evalB_get (evalB_var (by omega)) (by rw [hb, getElem?_arrOf gb hlt]) (hbB _ hlt))
      (by simpa using habB _ hlt)
  · rintro σ ⟨harr, hn, hb⟩
    exact ⟨harr, hn, by rintro p hp; rcases List.mem_singleton.mp hp with rfl; exact hb⟩
  · rintro σ σ' - ⟨hg, hi, hn, hfr⟩
    exact ⟨hg, hi, hn, hfr (b, N, gb) (by simp)⟩

/-- **The mask difference, in place**: `RamDriver.subCom` with its first
source and its destination the same array, which is what
`RamDriver.descendCom`'s last pass is. -/
theorem subSelfCom_spec (N : ℕ) (b dst : String) (ga gb : ℕ → ℕ)
    (hbd : b ≠ dst) (hNB : N < B) (h1B : 1 < B)
    (haB : ∀ k, k < N → ga k < B) (hbB : ∀ k, k < N → gb k < B) :
    Spec B (fun σ => σ.arrs dst = arrOf N ga ∧ σ.vars "n" = N ∧ σ.arrs b = arrOf N gb)
      (subCom dst b dst)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf N h ∧ ∀ k, k < N → h k = ga k * (1 - gb k)) ∧
        σ'.vars "i" = N ∧ σ'.vars "n" = N ∧ σ'.arrs b = arrOf N gb)
      (17 * N + 6) := by
  refine ((selfFill_spec N dst _ ga (fun k => ga k * (1 - gb k)) [(b, N, gb)]
    (by rintro p hp; rcases List.mem_singleton.mp hp with rfl; exact hbd) hNB ?_).pre ?_).post ?_
      |>.mono (by simp [Expr.size])
  · intro σ hfr hbel hlt
    obtain ⟨g, harr, -, -, hhigh⟩ := hbel
    have hb : σ.arrs b = arrOf N gb := hfr (b, N, gb) (by simp)
    have hgi : g (σ.vars "i") = ga (σ.vars "i") := hhigh _ le_rfl
    have hbnd : ga (σ.vars "i") * (1 - gb (σ.vars "i")) < B := by
      have hle : ga (σ.vars "i") * (1 - gb (σ.vars "i")) ≤ ga (σ.vars "i") := by
        calc ga (σ.vars "i") * (1 - gb (σ.vars "i")) ≤ ga (σ.vars "i") * 1 :=
              Nat.mul_le_mul_left _ (by omega)
          _ = ga (σ.vars "i") := by ring
      exact lt_of_le_of_lt hle (haB _ hlt)
    refine evalB_bin
      (evalB_get (evalB_var (by omega)) (by rw [harr, getElem?_arrOf g hlt, hgi]) (haB _ hlt))
      (evalB_bin (evalB_lit h1B)
        (evalB_get (evalB_var (by omega)) (by rw [hb, getElem?_arrOf gb hlt]) (hbB _ hlt))
        (by simp only [Bop.apply_sub]; omega)) ?_
    simp only [Bop.apply_mul]
    exact hbnd
  · rintro σ ⟨harr, hn, hb⟩
    exact ⟨harr, hn, by rintro p hp; rcases List.mem_singleton.mp hp with rfl; exact hb⟩
  · rintro σ σ' - ⟨hg, hi, hn, hfr⟩
    exact ⟨hg, hi, hn, hfr (b, N, gb) (by simp)⟩

end SelfFill

/-! ### The scalars the descent moves

The array side of the descent's frame is
`RamDriverFrames.underscore_notMem_warrs_descendCom`; this is the scalar
side. Every scalar `descendCom` assigns is either the depth's own
connector — which the descent is *supposed* to move — or one of the
nineteen counters below, none of which is a prefixed name and none of
which any clause of a depth's state speaks about. The search's own
scalars are the fiddly part, and they are read off `bfsParCom`'s syntax
once: the radius is a construction-time constant, so `bfsParCom r`'s
scalar set does not depend on it, and neither does `ancestorStep`'s on
the round it is taken at. -/

section Scalars

/-- The counters of the descent's passes: the flat passes' `i`, the
block scans' `p`/`pend` and `j`/`jend`, the expansion's `z`/`hit`/`w`,
the search's queue and relaxation scalars, and the extraction's
`cur`/`pl`/`plen`; `pc`/`pi` are the cached parent pointer and counter. -/
def descendScalars : List String :=
  ["i", "p", "pend", "z", "hit", "j", "jend", "w", "src", "tv", "tail", "head",
    "sc", "v", "dv", "dn", "cur", "pl", "plen", "pc", "pi", "bq", "mk", "mv",
    "ac", "ax", "ri", "u", "du"]

theorem wvars_andCom (a b dst : String) : (andCom a b dst).wvars = ["i", "i"] :=
  RamDriverIO.wvars_fillCom _ _

theorem wvars_subCom (a b dst : String) : (subCom a b dst).wvars = ["i", "i"] :=
  RamDriverIO.wvars_fillCom _ _

/-- One earlier round's scalars do not depend on the round, on the depth
or on the cap: every name in the pass is a literal of the program text. -/
theorem wvars_ancestorStep (cap j a : ℕ) :
    (ancestorStep cap j a).wvars = (ancestorStep 0 0 0).wvars := rfl

theorem mem_wvars_ancestorStep_zero :
    ∀ y ∈ (ancestorStep 0 0 0).wvars, y ∈ descendScalars := by decide

theorem mem_wvars_ancestorStep {cap j a : ℕ} {y : String}
    (h : y ∈ (ancestorStep cap j a).wvars) : y ∈ descendScalars :=
  mem_wvars_ancestorStep_zero y (by rwa [wvars_ancestorStep] at h)

theorem wvars_markParentsCom (cap j a : ℕ) :
    (markParentsCom cap j a).wvars = (markParentsCom 0 0 0).wvars := rfl

theorem mem_wvars_markParentsCom_zero :
    ∀ y ∈ (markParentsCom 0 0 0).wvars, y ∈ descendScalars := by decide

theorem mem_wvars_markParentsCom {cap j a : ℕ} {y : String}
    (h : y ∈ (markParentsCom cap j a).wvars) : y ∈ descendScalars :=
  mem_wvars_markParentsCom_zero y (by rwa [wvars_markParentsCom] at h)

theorem bq_notMem_wvars_markParentsCom (cap j a : ℕ) :
    "bq" ∉ (markParentsCom cap j a).wvars := by
  rw [wvars_markParentsCom]
  decide

theorem wvars_cacheBfsCom (cap j : ℕ) :
    (cacheBfsCom cap j).wvars = (Refine.BfsBlockPar.bfsBlockParCom 0).wvars := by
  rw [cacheBfsCom, Refine.ScatterBlock.renCom_wvars]
  rfl

theorem mem_wvars_cacheBfsCom_zero :
    ∀ y ∈ (Refine.BfsBlockPar.bfsBlockParCom 0).wvars, y ∈ descendScalars := by decide

theorem mem_wvars_cacheBfsCom {cap j : ℕ} {y : String}
    (h : y ∈ (cacheBfsCom cap j).wvars) : y ∈ descendScalars :=
  mem_wvars_cacheBfsCom_zero y (by rwa [wvars_cacheBfsCom] at h)

theorem bq_notMem_wvars_cacheBfsCom (cap j : ℕ) :
    "bq" ∉ (cacheBfsCom cap j).wvars := by
  rw [wvars_cacheBfsCom]
  decide

theorem mem_wvars_memFillAt {j c : ℕ} {a y : String}
    (h : y ∈ (memFillAt j a c).wvars) : y = "ac" ∨ y = "ax" := by
  simp [memFillAt, Com.wvars] at h
  tauto

theorem bq_notMem_wvars_memFillAt (j : ℕ) (a : String) (c : ℕ) :
    "bq" ∉ (memFillAt j a c).wvars := by
  intro h
  rcases mem_wvars_memFillAt h with h | h <;> exact absurd h (by decide)

theorem mem_wvars_cacheRoundCom {cap j : ℕ} {y : String}
    (h : y ∈ (cacheRoundCom cap j).wvars) :
    y = mnumName (j + 1) ∨ y ∈ descendScalars := by
  simp only [cacheRoundCom, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, false_or] at h
  rcases h with rfl | rfl | hm | hb
  · exact Or.inr (by decide)
  · exact Or.inl rfl
  · rcases mem_wvars_memFillAt hm with rfl | rfl <;> exact Or.inr (by decide)
  · exact Or.inr (mem_wvars_cacheBfsCom hb)

theorem bq_notMem_wvars_cacheRoundCom (cap j : ℕ) :
    "bq" ∉ (cacheRoundCom cap j).wvars := by
  intro h
  simp only [cacheRoundCom, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, false_or] at h
  rcases h with h | h | hm | hb
  · exact absurd h (by decide)
  · exact absurd h (by simp [mnumName, String.ext_iff])
  · exact bq_notMem_wvars_memFillAt j (pdsName j) (2 * cap + 1) hm
  · exact bq_notMem_wvars_cacheBfsCom cap j hb

theorem wvars_clusterLoad (j : ℕ) : (clusterLoad j).wvars = (clusterLoad 0).wvars := rfl

theorem mem_wvars_clusterLoad_zero : ∀ y ∈ (clusterLoad 0).wvars, y ∈ descendScalars := by decide

theorem mem_wvars_clusterLoad {j : ℕ} {y : String} (h : y ∈ (clusterLoad j).wvars) :
    y ∈ descendScalars :=
  mem_wvars_clusterLoad_zero y (by rwa [wvars_clusterLoad] at h)

theorem mem_descendScalars_i : "i" ∈ descendScalars := by decide

/-- **The emission counter crosses the batch phase** (rebase E-mem).
`"bq"` counts the block row `clusterLoad` emitted, and the filter pass
at the end of the descent still needs it; the batch phase writes its own
counters and not this one. -/
theorem bq_notMem_wvars_ancestorStep (cap j a : ℕ) : "bq" ∉ (ancestorStep cap j a).wvars := by
  rw [wvars_ancestorStep]
  decide

/-- **The batch phase assigns counters only.** -/
theorem mem_wvars_batchCom {cap j : ℕ} {y : String} (h : y ∈ (batchCom cap j).wvars) :
    y ∈ descendScalars := by
  simp only [batchCom, Com.wvars, List.mem_append, List.not_mem_nil, false_or, or_false,
    RamDriverIO.wvars_fillCom, wvars_andCom, List.mem_cons] at h
  rcases h with (rfl | rfl) | h | (rfl | rfl)
  · exact mem_descendScalars_i
  · exact mem_descendScalars_i
  · obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ _ h
    exact mem_wvars_ancestorStep hm
  · exact mem_descendScalars_i
  · exact mem_descendScalars_i

theorem bq_notMem_wvars_batchCom (cap j : ℕ) : "bq" ∉ (batchCom cap j).wvars := by
  intro h
  simp only [batchCom, Com.wvars, List.mem_append, List.not_mem_nil, false_or, or_false,
    RamDriverIO.wvars_fillCom, wvars_andCom, List.mem_cons] at h
  rcases h with (h | h) | h | (h | h)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ _ h
    exact bq_notMem_wvars_ancestorStep cap j b hm
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem mem_wvars_batchCachedCom {cap j : ℕ} {y : String}
    (h : y ∈ (batchCachedCom cap j).wvars) : y ∈ descendScalars := by
  simp only [batchCachedCom, Com.wvars, List.mem_append, List.not_mem_nil, false_or,
    or_false, RamDriverIO.wvars_fillCom, wvars_andCom, List.mem_cons] at h
  rcases h with (rfl | rfl) | h | (rfl | rfl)
  · exact mem_descendScalars_i
  · exact mem_descendScalars_i
  · obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ _ h
    exact mem_wvars_markParentsCom hm
  · exact mem_descendScalars_i
  · exact mem_descendScalars_i

theorem bq_notMem_wvars_batchCachedCom (cap j : ℕ) :
    "bq" ∉ (batchCachedCom cap j).wvars := by
  intro h
  simp only [batchCachedCom, Com.wvars, List.mem_append, List.not_mem_nil, false_or,
    or_false, RamDriverIO.wvars_fillCom, wvars_andCom, List.mem_cons] at h
  rcases h with (h | h) | h | (h | h)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ _ h
    exact bq_notMem_wvars_markParentsCom cap j b hm
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **What the descent assigns**: the depth's own connector and nothing
but counters. -/
theorem mem_wvars_descendCom {cap j : ℕ} {y : String} (h : y ∈ (descendCom cap j).wvars) :
    y = ctrName j ∨ y = mnumName (j + 1) ∨ y ∈ descendScalars := by
  simp only [descendCom, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, false_or, wvars_andCom, wvars_subCom,
    RamDriverFrames.wvars_memFilterCom] at h
  rcases h with rfl | hcl | (rfl | rfl) | hc | hb | (rfl | rfl) |
    (rfl | rfl) | (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (mem_wvars_clusterLoad hcl))
  · exact Or.inr (Or.inr mem_descendScalars_i)
  · exact Or.inr (Or.inr mem_descendScalars_i)
  · rcases mem_wvars_cacheRoundCom hc with rfl | hs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hs)
  · exact Or.inr (Or.inr (mem_wvars_batchCachedCom hb))
  -- the child's filter: two counters and the child's own member count
  all_goals first
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (by decide))

end Scalars

/-! ### Marking a path buffer

`RamDriver.markPath` is the one loop of the descent that writes through
an *indirection*: the cell it stores into is named by the buffer the
extraction pass filled, not by the counter. So what it owes is one range
condition per turn — the buffer's entries are vertices — and what it
leaves is the union of what the indicator marked with the set the buffer
names. -/

section MarkPath

/-- The vertices the first `i` cells of a buffer name. -/
def bufBelow (N i : ℕ) (Buf : ℕ → ℕ) : Set (Fin N) := {z : Fin N | ∃ t < i, (z : ℕ) = Buf t}

theorem bufBelow_zero (N : ℕ) (Buf : ℕ → ℕ) : bufBelow N 0 Buf = ∅ := by
  ext z
  simp only [bufBelow, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  intro t
  simp

/-- One more cell adds one more vertex. -/
theorem bufBelow_succ {N i : ℕ} (Buf : ℕ → ℕ) (h : Buf i < N) :
    bufBelow N (i + 1) Buf = bufBelow N i Buf ∪ {(⟨Buf i, h⟩ : Fin N)} := by
  ext z
  simp only [bufBelow, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rcases Nat.lt_or_ge t i with h' | h'
    · exact Or.inl ⟨t, h', hz⟩
    · exact Or.inr (Fin.ext (by rw [hz, show t = i by omega]))
  · rintro (⟨t, ht, hz⟩ | rfl)
    · exact ⟨t, by omega, hz⟩
    · exact ⟨i, by omega, rfl⟩

/-- At the exit the loop has passed every cell the buffer's length
clause names. -/
theorem bufBelow_succ_eq (N L : ℕ) (Buf : ℕ → ℕ) :
    bufBelow N (L + 1) Buf = RamBfsPaths.bufSet N L Buf := by
  ext z
  simp only [bufBelow, Set.mem_setOf_eq, RamBfsPaths.mem_bufSet]
  exact ⟨fun ⟨t, ht, hz⟩ => ⟨t, by omega, hz⟩, fun ⟨t, ht, hz⟩ => ⟨t, by omega, hz⟩⟩

/-- Storing a one adds the cell's own vertex to what the mask marks. -/
theorem markSet_upd_one {N : ℕ} (f : ℕ → ℕ) {k : ℕ} (hk : k < N) :
    markSet N (upd f k 1) = markSet N f ∪ {(⟨k, hk⟩ : Fin N)} := by
  ext z
  simp only [mem_markSet, Set.mem_union, Set.mem_singleton_iff]
  by_cases hz : (z : ℕ) = k
  · rw [hz, upd_self]
    exact ⟨fun _ => Or.inr (Fin.ext hz), fun _ => one_ne_zero⟩
  · rw [upd_of_ne _ hz]
    exact ⟨Or.inl, fun h => h.elim id (fun hc => absurd (by rw [hc]) hz)⟩

/-- What the marking loop carries: the buffer, the counted bound, and the
indicator with the cells already passed marked in it. -/
def MarkInv (N d L : ℕ) (bat : String) (Buf Wa : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs "path" = arrOf (d + 1) Buf ∧ σ.vars "plen" = L + 1 ∧ σ.vars "i" ≤ L + 1 ∧
    ∃ Wa' : ℕ → ℕ, σ.arrs bat = arrOf N Wa' ∧ (∀ k, k < N → Wa' k ≤ 1) ∧
      markSet N Wa' = markSet N Wa ∪ bufBelow N (σ.vars "i") Buf

/-- **One turn of the marking loop.** -/
theorem markBody_spec {B N d L : ℕ} {bat : String} {Buf Wa : ℕ → ℕ}
    (hbat : bat ≠ "path") (hLd : L ≤ d) (hdB : d + 1 < B) (hNB : N < B) (h1B : 1 < B)
    (hbuf : ∀ t, t ≤ L → Buf t < N) :
    Spec B (fun σ => MarkInv N d L bat Buf Wa σ ∧ σ.vars "i" < L + 1)
      (.seq (.store bat (.get "path" (.var "i")) (.lit 1))
        (.assign "i" (.add (.var "i") (.lit 1))))
      (fun σ σ' => MarkInv N d L bat Buf Wa σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 8 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hpath, hplen, hile, Wa', harr, hbit, hmark⟩, hlt⟩ := hσ
  have hiB : σ.vars "i" < B := by omega
  have hBuf : Buf (σ.vars "i") < N := hbuf _ (by omega)
  have hidx : (Expr.get "path" (.var "i")).evalB B σ = some (Buf (σ.vars "i")) :=
    evalB_get (evalB_var hiB) (by rw [hpath, getElem?_arrOf Buf (by omega)]) (by omega)
  have hlen : Buf (σ.vars "i") < (σ.arrs bat).length := by
    rw [harr, length_arrOf]; exact hBuf
  set τ := (σ.setArr bat (Buf (σ.vars "i")) 1).setVar "i" (σ.vars "i" + 1) with hτ
  have hi' : τ.vars "i" = σ.vars "i" + 1 := by rw [hτ]; simp
  refine ⟨τ, 8, ((Run.store hidx (evalB_lit (by omega)) hlen).seq
      (Run.assign (evalB_bin (evalB_var (by simp; omega))
        (evalB_lit (by omega)) (by simp; omega)))).mono (by simp [Expr.size]), le_rfl,
    ⟨?_, ?_, by rw [hi']; omega, upd Wa' (Buf (σ.vars "i")) 1, ?_, ?_, ?_⟩, hi'⟩
  · rw [hτ]
    simp only [arrs_setVar, arrs_setArr, if_neg (Ne.symm hbat)]
    exact hpath
  · rw [hτ]; simpa using hplen
  · rw [hτ]
    simp [harr, set_arrOf_eq_upd]
  · intro k hk
    by_cases hke : k = Buf (σ.vars "i")
    · rw [hke, upd_self]
    · rw [upd_of_ne _ hke]; exact hbit k hk
  · rw [markSet_upd_one Wa' hBuf, hmark, hi', bufBelow_succ Buf hBuf, Set.union_assoc]

/-- **The marking pass, discharged.** The indicator ends marking what it
marked together with the vertices the buffer's first `pl + 1` cells
name. -/
theorem markPath_spec {B N d L : ℕ} {bat : String} {Buf Wa : ℕ → ℕ}
    (hbat : bat ≠ "path") (hLd : L ≤ d) (hdB : d + 1 < B) (hNB : N < B) (h1B : 1 < B)
    (hbuf : ∀ t, t ≤ L → Buf t < N) (hbit : ∀ k, k < N → Wa k ≤ 1) :
    Spec B (fun σ => σ.arrs "path" = arrOf (d + 1) Buf ∧ σ.arrs bat = arrOf N Wa ∧
        σ.vars "pl" = L)
      (markPath bat)
      (fun _ σ' => ∃ Wa' : ℕ → ℕ, σ'.arrs bat = arrOf N Wa' ∧ (∀ k, k < N → Wa' k ≤ 1) ∧
        markSet N Wa' = markSet N Wa ∪ RamBfsPaths.bufSet N L Buf)
      (12 * d + 22) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hpath, harr, hpl⟩ := hσ
  have hr₁ : Run B (.assign "i" (.lit 0)) σ (σ.setVar "i" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  set σ₁ := σ.setVar "i" 0 with hσ₁
  have hpl₁ : σ₁.vars "pl" = L := by rw [hσ₁, vars_setVar, if_neg (by decide)]; exact hpl
  have hev₂ : (Expr.add (Expr.var "pl") (Expr.lit 1)).evalB B σ₁ = some (L + 1) := by
    have h : (Expr.add (Expr.var "pl") (Expr.lit 1)).evalB B σ₁ =
        some (σ₁.vars "pl" + 1) :=
      evalB_bin (evalB_var (by rw [hpl₁]; omega)) (evalB_lit (by omega))
        (by rw [hpl₁]; simp; omega)
    rw [h, hpl₁]
  have hr₂ : Run B (.assign "plen" (.add (.var "pl") (.lit 1))) σ₁ (σ₁.setVar "plen" (L + 1)) 4 :=
    (Run.assign hev₂).mono (by simp [Expr.size])
  set σ₂ := σ₁.setVar "plen" (L + 1) with hσ₂
  have hI₂ : MarkInv N d L bat Buf Wa σ₂ := by
    refine ⟨by rw [hσ₂, hσ₁]; simpa using hpath, by rw [hσ₂]; simp,
      by rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁]; simp,
      Wa, by rw [hσ₂, hσ₁]; simpa using harr, hbit, ?_⟩
    rw [show σ₂.vars "i" = 0 by rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁]; simp,
      bufBelow_zero, Set.union_empty]
  obtain ⟨σ₃, hr₃, hI₃, hi₃⟩ :=
    (Spec.forRange (B := B) (P := MarkInv N d L bat Buf Wa) "i" "plen"
      (MarkInv N d L bat Buf Wa) (L + 1) 8 (12 * (L + 1) + 4)
      (fun τ hτ => by have := hτ.2.2.1; omega) (fun τ hτ => by rw [hτ.2.1]; omega)
      (fun τ hτ => hτ.2.1) (fun τ hτ => hτ.2.2.1)
      (markBody_spec hbat hLd hdB hNB h1B hbuf) (fun _ hτ => hτ)
      (fun τ _ => by
        have : (8 + 4) * (L + 1 - τ.vars "i") ≤ 12 * (L + 1) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        omega)).run hI₂
  obtain ⟨-, -, -, Wa', harr', hbit', hmark'⟩ := hI₃
  refine ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), by omega, Wa', harr', hbit', ?_⟩
  rw [hmark', hi₃, bufBelow_succ_eq]

end MarkPath

/-! ### One earlier round

`RamDriver.ancestorStep` copies the round's own game mask into the
search's arena, searches from the round's connector, and — under the
guard — walks the parents back and marks them. What the recorded game
asks of the turn is a walk *in that round's arena*, which is why the
copy is of `gamName a` and not of the depth's own mask, and the guard's
false branch owes nothing at all: a sentinel distance is a proof of
`¬ WithinDist`, which is the very hypothesis the game's walk clause is
guarded by. -/

section Ancestor

variable {ns nt : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! The three write sets the pass is built from, off the syntax. The two
searches' sets do not depend on the radius, which is a construction-time
constant. -/

theorem warrs_bfsPar (d : ℕ) :
    (RamBfsPaths.bfsParCom d).warrs = ["dist", "dist", "par", "q", "dist", "par", "q"] := rfl

theorem wvars_bfsPar (d : ℕ) :
    (RamBfsPaths.bfsParCom d).wvars =
      ["i", "i", "tail", "tail", "head", "sc", "v", "dv", "dn", "j", "jend", "w",
        "tail", "sc", "j", "head"] := rfl

theorem warrs_extractPath : RamBfsPaths.extractPathCom.warrs = ["path"] := rfl

/-- The cost of one earlier round: a copy, a capped search, and — at
most — the walk back with the marking of its buffer. -/
def ancestorCost (n ns cap : ℕ) : ℕ := 67 * n + 48 * ns + 56 * cap + 103

/-- **One earlier round's contribution, discharged.** The batch grows by
a set of at most `2·cap + 1` vertices, and — whenever the round's own
arena puts its connector within `2·cap` of the depth's — that set holds
the support of a walk between the two in that arena. -/
theorem ancestorStep_spec {B cap mb j a : ℕ} (hcsr : CsrGraph G ns O T)
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hnt : ns ≤ nt) {u v : Fin n} {Ga Wa : ℕ → ℕ}
    (hGaB : ∀ z, z < n → Ga z < B) (hbit : ∀ k, k < n → Wa k ≤ 1) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf nt T ∧
        σ.vars (ctrName a) = (u : ℕ) ∧ σ.vars (ctrName j) = (v : ℕ) ∧
        σ.arrs (gamName a) = arrOf n Ga ∧ σ.arrs (batName j) = arrOf n Wa ∧
        (∃ g, σ.arrs "alv" = arrOf n g) ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "par" = arrOf n g) ∧
        (∃ g, σ.arrs "path" = arrOf (2 * cap + 1) g))
      (ancestorStep cap j a)
      (fun _ σ' => ∃ (Wa' : ℕ → ℕ) (S : Set (Fin n)),
        σ'.arrs (batName j) = arrOf n Wa' ∧ (∀ k, k < n → Wa' k ≤ 1) ∧
        markSet n Wa' = markSet n Wa ∪ S ∧ S.ncard ≤ 2 * cap + 1 ∧
        (WithinDist (masked G Ga) (2 * cap) u v →
          ∃ p : (masked G Ga).Walk u v, p.length ≤ 2 * cap ∧
            {z : Fin n | z ∈ p.support} ⊆ S))
      (ancestorCost n ns cap) := by
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  have hnsB := hB.ns_lt
  have hdB : 2 * cap + 1 < B := by have := hB.1; omega
  have hbatpath : batName j ≠ "path" := by simp [batName, String.ext_iff]
  have hbatalv : batName j ≠ "alv" := by simp [batName, String.ext_iff]
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hoff, htgt, hctra, hctrj, hgam, hbat, halv, hdist, hq, hpar, hpath⟩ := hσ
  have huB : (u : ℕ) < B := by have := u.isLt; omega
  have hvB : (v : ℕ) < B := by have := v.isLt; omega
  -- the two scalars the search is handed
  have hev₁ : (Expr.var (ctrName a)).evalB B σ = some (u : ℕ) := by
    have h := evalB_var (B := B) (x := ctrName a) (σ := σ) (by rw [hctra]; exact huB)
    rwa [hctra] at h
  set σ₁ := σ.setVar "src" (u : ℕ) with hσ₁
  have hr₁ : Run B (.assign "src" (.var (ctrName a))) σ σ₁ 2 :=
    (Run.assign hev₁).mono (by simp [Expr.size])
  have hev₂ : (Expr.var (ctrName j)).evalB B σ₁ = some (v : ℕ) := by
    have hc : σ₁.vars (ctrName j) = (v : ℕ) := by
      rw [hσ₁, vars_setVar, if_neg (by simp [ctrName, String.ext_iff])]; exact hctrj
    have h := evalB_var (B := B) (x := ctrName j) (σ := σ₁) (by rw [hc]; exact hvB)
    rwa [hc] at h
  set σ₂ := σ₁.setVar "tv" (v : ℕ) with hσ₂
  have hr₂ : Run B (.assign "tv" (.var (ctrName j))) σ₁ σ₂ 2 :=
    (Run.assign hev₂).mono (by simp [Expr.size])
  have harrs₂ : ∀ b : String, σ₂.arrs b = σ.arrs b := by
    intro b; rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]
  have hn₂ : σ₂.vars "n" = n := by
    rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁, vars_setVar, if_neg (by decide)]; exact hn
  have hsrc₂ : σ₂.vars "src" = (u : ℕ) := by
    rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁]; simp
  have htv₂ : σ₂.vars "tv" = (v : ℕ) := by rw [hσ₂]; simp
  -- the round's arena, copied into the search's
  obtain ⟨σ₃, hr₃, ⟨⟨g₃, halv₃, hval₃⟩, -, hn₃, -⟩, hfv₃, hfa₃, -, -⟩ :=
    ((copyCom_spec B n n (gamName a) "alv" Ga (by simp [gamName, String.ext_iff]) hnB le_rfl
      hGaB).frame).run (σ := σ₂) ⟨by rw [harrs₂]; exact halv, hn₂, by rw [harrs₂]; exact hgam⟩
  have hav₃ : ∀ b : String, b ≠ "alv" → σ₃.arrs b = σ₂.arrs b :=
    fun b hb => hfa₃ b (by simp [RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom, hb])
  have hvv₃ : ∀ y : String, y ≠ "i" → σ₃.vars y = σ₂.vars y :=
    fun y hy => hfv₃ y (by simp [RamDriverIO.copyCom_eq, RamDriverIO.wvars_fillCom, hy])
  have halvGa : σ₃.arrs "alv" = arrOf n Ga := by rw [halv₃]; exact arrOf_congr hval₃
  -- the search, in that arena
  obtain ⟨σ₄, hr₄, ⟨D, P, hdist₄, hpar₄, hdisteq, hT⟩, hfv₄, hfa₄, -, -⟩ :=
    ((RamBfsPaths.bfsPar_specW (M := Ga) (d := 2 * cap) (nt := nt) hcsr u.isLt hnB hnsB hnt
      hdB hGaB).frame).run
      (σ := σ₃) ⟨hn₃, by rw [hvv₃ "src" (by decide)]; exact hsrc₂,
        by rw [hav₃ "off" (by decide), harrs₂]; exact hoff,
        by rw [hav₃ "tgt" (by decide), harrs₂]; exact htgt, halvGa,
        by rw [hav₃ "dist" (by decide), harrs₂]; exact hdist,
        by rw [hav₃ "q" (by decide), harrs₂]; exact hq,
        by rw [hav₃ "par" (by decide), harrs₂]; exact hpar⟩
  have hav₄ : ∀ b : String, b ≠ "dist" → b ≠ "par" → b ≠ "q" → σ₄.arrs b = σ₃.arrs b :=
    fun b h1 h2 h3 => hfa₄ b (by rw [warrs_bfsPar]; simp [h1, h2, h3])
  have hvv₄ : ∀ y : String, y ≠ "i" → y ≠ "tail" → y ≠ "head" → y ≠ "sc" → y ≠ "v" →
      y ≠ "dv" → y ≠ "dn" → y ≠ "j" → y ≠ "jend" → y ≠ "w" → σ₄.vars y = σ₃.vars y :=
    fun y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => hfv₄ y (by
      rw [wvars_bfsPar]; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10])
  have htv₄ : σ₄.vars "tv" = (v : ℕ) := by
    rw [hvv₄ "tv" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hvv₃ "tv" (by decide)]
    exact htv₂
  have hbat₄ : σ₄.arrs (batName j) = arrOf n Wa := by
    rw [hav₄ _ (by simp [batName, String.ext_iff]) (by simp [batName, String.ext_iff])
      (by simp [batName, String.ext_iff]), hav₃ _ hbatalv, harrs₂]
    exact hbat
  have hpath₄ : ∃ g, σ₄.arrs "path" = arrOf (2 * cap + 1) g := by
    rw [hav₄ "path" (by decide) (by decide) (by decide), hav₃ "path" (by decide), harrs₂]
    exact hpath
  -- the guard
  have hvn : (v : ℕ) < n := v.isLt
  have hDv : D (v : ℕ) ≤ 2 * cap + 1 := hT.cap _ hvn
  have hcond : (Cond.lt (.get "dist" (.var "tv")) (.lit (2 * cap + 1))).evalB B σ₄ =
      some (decide (D (v : ℕ) < 2 * cap + 1)) :=
    evalB_condLt (evalB_get (evalB_var (by rw [htv₄]; omega))
      (by rw [hdist₄, htv₄, getElem?_arrOf D hvn]) (by omega)) (evalB_lit (by omega))
  by_cases hreach : D (v : ℕ) ≤ 2 * cap
  · -- the search found the connector: the walk back is marked
    obtain ⟨σ₅, hr₅, ⟨hpl₅, Buf, hpath₅, hbuf₅⟩, -, hfa₅, -, -⟩ :=
      ((RamBfsPaths.extractPath_spec hT hnB hdB hvn hreach).frame).run
        (σ := σ₄) ⟨htv₄, hdist₄, hpar₄, hpath₄⟩
    have hbat₅ : σ₅.arrs (batName j) = arrOf n Wa := by
      rw [hfa₅ _ (by rw [warrs_extractPath]; simp [hbatpath])]; exact hbat₄
    have hbufn : ∀ t, t ≤ D (v : ℕ) → Buf t < n := by
      intro t ht
      rw [hbuf₅ t ht]
      exact hT.chain_lt hvn hreach t (by omega)
    obtain ⟨σ₆, hr₆, Wa', hbat₆, hbit₆, hmark₆⟩ :=
      (markPath_spec (B := B) (N := n) (d := 2 * cap) (L := D (v : ℕ)) (bat := batName j)
        hbatpath hreach hdB hnB h1B hbufn hbit).run (σ := σ₅) ⟨hpath₅, hbat₅, hpl₅⟩
    -- what the buffer names is the support of the walk the tree records
    obtain ⟨p, hplen, hpsup⟩ := hT.walk u.isLt (D (v : ℕ)) hreach v rfl
    have hSeq : RamBfsPaths.bufSet n (D (v : ℕ)) Buf = {z : Fin n | z ∈ p.support} := by
      rw [RamBfsPaths.bufSet_congr hbuf₅, ← hpsup]
    refine ⟨σ₆, _, hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq
        (Run.ite_true (by rw [hcond]; simp; omega) (hr₅.seq hr₆))))), ?_,
      Wa', RamBfsPaths.bufSet n (D (v : ℕ)) Buf, hbat₆, hbit₆, hmark₆, ?_, fun _ => ?_⟩
    · simp only [ancestorCost, size_condLt, Expr.size]
      omega
    · rw [hSeq]
      exact RamBfsPaths.ncard_support_le p (by omega)
    · exact ⟨p, by omega, by rw [hSeq]⟩
  · -- the search did not: the round owes nothing
    refine ⟨σ₄, _, hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq
        (Run.ite_false (by rw [hcond]; simp; omega) Run.skip)))), ?_,
      Wa, ∅, hbat₄, hbit, by rw [Set.union_empty], by simp, fun hw => ?_⟩
    · simp only [ancestorCost, size_condLt, Expr.size]
      omega
    · exact absurd ((hdisteq v (2 * cap) le_rfl).mpr hw) hreach

end Ancestor

/-! ### The batch of the round

`RamDriver.batchCom` opens the indicator, stores the connector, folds one
`RamDriver.ancestorStep` over every earlier round, and cuts the result
down to the ball. The fold is *accumulating* — every turn writes the same
array — so it is not an instance of `foldr_family_spec`; what carries it
is the invariant below, which is exactly the four things
`RamDriver.playRec_succ` asks of the batch, at the rounds taken so far.

The invariant was falsified before it was proved, on the four instances
its clauses are sharp at: a round whose search fails (the size clause has
to hold with `∅` added), a round whose walk leaves the ball (the walk
clause has to be stated *intersected* with the ball, which is why the
last pass is the `andCom` and not a plain copy), the empty fold (the
connector alone, `1 + 0 · (2·cap + 1)`), and the full fold at `j = ℓ`
(`1 + ℓ · (2·cap + 1) ≤ mb` fails by one unless `mb = ℓ · (2·cap + 1)`
is read with `j < ℓ`, which is why both are hypotheses of the theorem
and not clauses of the obligation). -/

section Batch

variable {ns nt : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

theorem warrs_ancestorStep (cap j a : ℕ) :
    (ancestorStep cap j a).warrs =
      ["alv", "dist", "dist", "par", "q", "dist", "par", "q", "path", batName j] := rfl

/-- The memory and the scalars every turn of the fold reads: the block
structure, the search's six arrays, the depth's own connector, and the
connector and the game mask of every earlier round. -/
def BatchEnv (cap nt j : ℕ) (O T : ℕ → ℕ) (U : ℕ → Fin n) (Gam : ℕ → ℕ → ℕ)
    (v : Fin n) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
    (∃ g, σ.arrs "alv" = arrOf n g) ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
    (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "par" = arrOf n g) ∧
    (∃ g, σ.arrs "path" = arrOf (2 * cap + 1) g) ∧
    σ.vars (ctrName j) = (v : ℕ) ∧
    (∀ a, a < j → σ.vars (ctrName a) = (U a : ℕ)) ∧
    (∀ a, a < j → σ.arrs (gamName a) = arrOf n (Gam a))

/-- **The environment crosses a turn.** Every array a turn writes is
either the batch indicator or one of the search's scratch arrays, whose
*length* is all the clause asks; every scalar it assigns is a counter. -/
theorem batchEnv_run {B K cap j : ℕ} {c : Com} {σ σ' : Env}
    {U : ℕ → Fin n} {Gam : ℕ → ℕ → ℕ} {v : Fin n}
    (h : BatchEnv cap nt j O T U Gam v σ) (hr : Run B c σ σ' K)
    (hv : ∀ y : String, y ∈ c.wvars → y ∈ descendScalars)
    (ha : ∀ b : String, b ∈ c.warrs →
      b = batName j ∨ b ∈ (["alv", "dist", "q", "par", "path"] : List String)) :
    BatchEnv cap nt j O T U Gam v σ' := by
  obtain ⟨hn, hoff, htgt, halv, hdist, hq, hpar, hpath, hctrj, hctr, hgam⟩ := h
  have hlit : ∀ b : String, b ≠ batName j →
      b ∉ (["alv", "dist", "q", "par", "path"] : List String) → σ'.arrs b = σ.arrs b := by
    intro b h1 h2
    exact hr.frame_arr b (fun hc => (ha b hc).elim h1 h2)
  refine ⟨?_, ?_, ?_, exists_arrOf_run hr halv, exists_arrOf_run hr hdist,
    exists_arrOf_run hr hq, exists_arrOf_run hr hpar, exists_arrOf_run hr hpath, ?_, ?_, ?_⟩
  · rw [hr.frame_var "n" (fun hc => by have := hv "n" hc; revert this; decide)]; exact hn
  · rw [hlit "off" (by simp [batName, String.ext_iff]) (by decide)]; exact hoff
  · rw [hlit "tgt" (by simp [batName, String.ext_iff]) (by decide)]; exact htgt
  · rw [hr.frame_var _ (fun hc => by
      have := hv _ hc
      exact RamDriverIO.notMem_of_append (p := "ctr") (s := toString j) (by decide) this)]
    exact hctrj
  · intro a hja
    rw [hr.frame_var _ (fun hc => by
      have := hv _ hc
      exact RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide) this)]
    exact hctr a hja
  · intro a hja
    rw [hlit _ (by simp [gamName, batName, String.ext_iff])
      (by simp [gamName, String.ext_iff])]
    exact hgam a hja

/-- **What the fold has done by round `s`.** The batch indicator holds
bits, it holds the connector, it has at most one buffer per round taken,
and for every round taken whose arena reaches the connector it holds the
support of a walk between the two in that arena. -/
def BatchMark (cap j : ℕ) (G : SimpleGraph (Fin n)) (U : ℕ → Fin n) (Gam : ℕ → ℕ → ℕ)
    (v : Fin n) (s : ℕ) (σ : Env) : Prop :=
  ∃ Wa : ℕ → ℕ, σ.arrs (batName j) = arrOf n Wa ∧ (∀ k, k < n → Wa k ≤ 1) ∧
    v ∈ markSet n Wa ∧ (markSet n Wa).ncard ≤ 1 + s * (2 * cap + 1) ∧
    ∀ a, a < s → WithinDist (masked G (Gam a)) (2 * cap) (U a) v →
      ∃ p : (masked G (Gam a)).Walk (U a) v, p.length ≤ 2 * cap ∧
        {z : Fin n | z ∈ p.support} ⊆ markSet n Wa

/-- **The fold over the earlier rounds, discharged.** -/
theorem batchFold_spec {B cap mb j : ℕ} (hcsr : CsrGraph G ns O T) (hnt : ns ≤ nt)
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) {U : ℕ → Fin n} {Gam : ℕ → ℕ → ℕ} {v : Fin n}
    (hGamB : ∀ a, a < j → ∀ z, z < n → Gam a z < B) :
    ∀ (r s : ℕ), s + r ≤ j →
      Spec B (fun σ => BatchEnv cap nt j O T U Gam v σ ∧ BatchMark cap j G U Gam v s σ)
        (foldRange (fun b => ancestorStep cap j (s + b)) r)
        (fun _ σ' => BatchEnv cap nt j O T U Gam v σ' ∧
          BatchMark cap j G U Gam v (s + r) σ')
        (ancestorCost n ns cap * r + 1) := by
  intro r
  induction r with
  | zero =>
    intro s _
    exact Spec.of_exists (fun σ hσ => ⟨σ, 1, Run.skip, by omega, hσ.1, hσ.2⟩)
  | succ r ih =>
    intro s hsr
    have hsj : s < j := by omega
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨henv, Wa, hbat, hbit, hvW, hcard, hwalk⟩ := hσ
    obtain ⟨hn, hoff, htgt, halv, hdist, hq, hpar, hpath, hctrj, hctr, hgam⟩ := henv
    obtain ⟨σ₁, hr₁, ⟨Wa', S, hbat₁, hbit₁, hmark₁, hcard₁, hwalk₁⟩, -, -, -, -⟩ :=
      ((ancestorStep_spec (a := s + 0) (j := j) (u := U s) (Ga := Gam s) hcsr hB hnt
        (hGamB s hsj) hbit).frame).run (σ := σ)
        ⟨hn, hoff, htgt, hctr s hsj, hctrj, hgam s hsj, hbat, halv, hdist, hq, hpar, hpath⟩
    have henv₁ : BatchEnv cap nt j O T U Gam v σ₁ :=
      batchEnv_run ⟨hn, hoff, htgt, halv, hdist, hq, hpar, hpath, hctrj, hctr, hgam⟩ hr₁
        (fun _ hy => mem_wvars_ancestorStep hy)
        (fun b hb => by
          rw [warrs_ancestorStep] at hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | exact Or.inl rfl | exact Or.inr (by decide))
    have hsub : markSet n Wa ⊆ markSet n Wa' := by rw [hmark₁]; exact Set.subset_union_left
    have hmk₁ : BatchMark cap j G U Gam v (s + 1) σ₁ := by
      refine ⟨Wa', hbat₁, hbit₁, hsub hvW, ?_, ?_⟩
      · rw [hmark₁]
        calc (markSet n Wa ∪ S).ncard ≤ (markSet n Wa).ncard + S.ncard :=
              Set.ncard_union_le _ _
          _ ≤ (1 + s * (2 * cap + 1)) + (2 * cap + 1) := Nat.add_le_add hcard hcard₁
          _ = 1 + (s + 1) * (2 * cap + 1) := by ring
      · intro a ha hwd
        rcases Nat.lt_or_ge a s with h' | h'
        · obtain ⟨p, hp, hps⟩ := hwalk a h' hwd
          exact ⟨p, hp, subset_trans hps hsub⟩
        · have hae : a = s := by omega
          subst hae
          obtain ⟨p, hp, hps⟩ := hwalk₁ hwd
          exact ⟨p, hp, subset_trans hps (by rw [hmark₁]; exact Set.subset_union_right)⟩
    have hshift : (fun b => ancestorStep cap j (s + (b + 1))) =
        (fun b => ancestorStep cap j (s + 1 + b)) := by
      funext b; congr 1; omega
    obtain ⟨σ₂, hr₂, henv₂, hmk₂⟩ :=
      (ih (s + 1) (by omega)).run (σ := σ₁) ⟨henv₁, hmk₁⟩
    have hr₂' : Run B (foldRange (fun b => ancestorStep cap j (s + (b + 1))) r) σ₁ σ₂
        (ancestorCost n ns cap * r + 1) := by rw [hshift]; exact hr₂
    have hrun : Run B (foldRange (fun b => ancestorStep cap j (s + b)) (r + 1)) σ σ₂
        (ancestorCost n ns cap + (ancestorCost n ns cap * r + 1)) := by
      rw [foldRange_succ]; exact hr₁.seq hr₂'
    refine ⟨σ₂, _, hrun, by ring_nf; omega, henv₂, ?_⟩
    have hre : s + 1 + r = s + (r + 1) := by omega
    rwa [hre] at hmk₂

/-! #### The cached fold -/

theorem warrs_markParentsCom (cap j a : ℕ) :
    (markParentsCom cap j a).warrs = [batName j] := rfl

/-- A cached parent walk changes only the batch array and its three local
scalars, so all retained cache records cross it. -/
theorem cachedRounds_markParents_run {B K cap j a : ℕ} {M : ℕ → ℕ} {σ σ' : Env}
    (h : CachedRounds cap G j M σ) (hrun : Run B (markParentsCom cap j a) σ σ' K) :
    CachedRounds cap G j M σ' := by
  refine h.congr ?_ ?_ ?_ ?_
  · intro b hb
    rw [hrun.frame_var (ctrName b) (by
      simp [markParentsCom, markParentStep, Com.wvars, ctrName, String.ext_iff])]
  · intro b hb
    rw [hrun.frame_arr (resName b) (by
      rw [warrs_markParentsCom]
      simp [resName, batName, String.ext_iff])]
  · intro b hb
    rw [hrun.frame_arr (gamName b) (by
      rw [warrs_markParentsCom]
      simp [gamName, batName, String.ext_iff])]
  · intro b hb
    rw [hrun.frame_arr (parName b) (by
      rw [warrs_markParentsCom]
      simp [parName, balName, batName, String.ext_iff])]

/-- The retained cache crosses any batch-local pass: such a pass writes
only the batch indicator and unprefixed descent counters. -/
theorem cachedRounds_batch_run {B K cap j : ℕ} {M : ℕ → ℕ} {c : Com} {σ σ' : Env}
    (h : CachedRounds cap G j M σ) (hrun : Run B c σ σ' K)
    (hv : ∀ y : String, y ∈ c.wvars → y ∈ descendScalars)
    (ha : ∀ b : String, b ∈ c.warrs → b = batName j) :
    CachedRounds cap G j M σ' := by
  refine h.congr ?_ ?_ ?_ ?_
  · intro a ha'
    rw [hrun.frame_var (ctrName a) (fun hc => by
      have hm := hv _ hc
      exact RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide) hm)]
  · intro a ha'
    rw [hrun.frame_arr (resName a) (fun hc => by
      have hm := ha _ hc
      simp [resName, batName, String.ext_iff] at hm)]
  · intro a ha'
    rw [hrun.frame_arr (gamName a) (fun hc => by
      have hm := ha _ hc
      simp [gamName, batName, String.ext_iff] at hm)]
  · intro a ha'
    rw [hrun.frame_arr (parName a) (fun hc => by
      have hm := ha _ hc
      simp [parName, balName, batName, String.ext_iff] at hm)]

/-- **The fold now consumes retained trees.** Every turn adds at most one
capped parent chain and obtains its walk by mapping the cached tree's
walk into the game mask recorded for that round. -/
theorem batchCachedFold_spec {B cap mb j : ℕ} {d : ℕ}
    (hB : WordBoundK B n d ns cap mb) {U : ℕ → Fin n} {Gam : ℕ → ℕ → ℕ}
    {M : ℕ → ℕ} {v : Fin n} (hMv : M (v : ℕ) ≠ 0) :
    ∀ (r s : ℕ), s + r ≤ j →
      Spec B (fun σ => BatchEnv cap nt j O T U Gam v σ ∧
          CachedRounds cap G j M σ ∧ BatchMark cap j G U Gam v s σ)
        (foldRange (fun b => markParentsCom cap j (s + b)) r)
        (fun _ σ' => BatchEnv cap nt j O T U Gam v σ' ∧
          CachedRounds cap G j M σ' ∧ BatchMark cap j G U Gam v (s + r) σ')
        (markParentsK cap * r + 1) := by
  have hnB := hB.n_lt
  have h1B := hB.one_lt
  have hdB : 2 * cap + 1 < B := by have := hB.1; omega
  intro r
  induction r with
  | zero =>
      intro s _
      exact Spec.of_exists (fun σ hσ => ⟨σ, 1, Run.skip, by omega, hσ.1, hσ.2.1, hσ.2.2⟩)
  | succ r ih =>
      intro s hsr
      have hsj : s < j := by omega
      refine Spec.of_exists (fun σ hσ => ?_)
      obtain ⟨henv, hcache, Wa, hbat, hbit, hvW, hcard, hwalk⟩ := hσ
      obtain ⟨hn, hoff, htgt, halv, hdist, hq, hpar, hpath, hctrj, hctr, hgam⟩ := henv
      obtain ⟨u, R, Ga, D, P, hctra, hresa, hgama, hpara, hT, hRG, hdt⟩ :=
        hcache.target hsj v.isLt hMv
      have hu : u = U s := by
        apply Fin.ext
        rw [← hctra, hctr s hsj]
      subst u
      have hGaEq : ∀ z, z < n → Ga z = Gam s z := by
        intro z hz
        apply eq_of_arrOf_eq (N := n) (by rw [← hgama, ← hgam s hsj]) hz
      have hGaMask : masked G Ga = masked G (Gam s) := masked_congr hGaEq
      have hle : masked G R ≤ masked G (Gam s) := by
        rw [← hGaMask]
        exact hRG
      obtain ⟨σ₁, hr₁, Wa', hbat₁, hbit₁, hmark₁, hcard₁, p, hp, hpsup⟩ :=
        (markParentsCom_spec (j := j) (a := s) hT (U s).isLt v.isLt hdt hnB hdB h1B
          hbit).run (σ := σ) ⟨hctrj, hpara, hbat⟩
      have henv₁ : BatchEnv cap nt j O T U Gam v σ₁ :=
        batchEnv_run ⟨hn, hoff, htgt, halv, hdist, hq, hpar, hpath, hctrj, hctr, hgam⟩ hr₁
          (fun _ hy => mem_wvars_markParentsCom hy)
          (fun b hb => Or.inl (by
            rw [warrs_markParentsCom] at hb
            exact List.eq_of_mem_singleton hb))
      have hcache₁ : CachedRounds cap G j M σ₁ := cachedRounds_markParents_run hcache hr₁
      let p' : (masked G (Gam s)).Walk (U s) v := p.mapLe hle
      have hp' : p'.length ≤ 2 * cap := by
        exact (SimpleGraph.Walk.length_map _ p).le.trans hp
      have hpsup' : {z : Fin n | z ∈ p'.support} =
          RamBfsPaths.bufSet n (2 * cap) (RamBfsPaths.parIter P (v : ℕ)) := by
        rw [show p' = p.mapLe hle by rfl,
          SimpleGraph.Walk.support_mapLe_eq_support hle p, hpsup]
      have hsub : markSet n Wa ⊆ markSet n Wa' := by
        rw [hmark₁]
        exact Set.subset_union_left
      have hmk₁ : BatchMark cap j G U Gam v (s + 1) σ₁ := by
        refine ⟨Wa', hbat₁, hbit₁, hsub hvW, ?_, ?_⟩
        · rw [hmark₁]
          calc (markSet n Wa ∪ RamBfsPaths.bufSet n (2 * cap)
                    (RamBfsPaths.parIter P (v : ℕ))).ncard ≤
                (markSet n Wa).ncard +
                  (RamBfsPaths.bufSet n (2 * cap)
                    (RamBfsPaths.parIter P (v : ℕ))).ncard := Set.ncard_union_le _ _
            _ ≤ (1 + s * (2 * cap + 1)) + (2 * cap + 1) := Nat.add_le_add hcard hcard₁
            _ = 1 + (s + 1) * (2 * cap + 1) := by ring
        · intro a ha hwd
          rcases Nat.lt_or_ge a s with has | has
          · obtain ⟨q, hq, hqs⟩ := hwalk a has hwd
            exact ⟨q, hq, subset_trans hqs hsub⟩
          · have hae : a = s := by omega
            subst hae
            exact ⟨p', hp', by rw [hmark₁, hpsup']; exact Set.subset_union_right⟩
      have hshift : (fun b => markParentsCom cap j (s + (b + 1))) =
          (fun b => markParentsCom cap j (s + 1 + b)) := by
        funext b
        congr 1
        omega
      obtain ⟨σ₂, hr₂, henv₂, hcache₂, hmk₂⟩ :=
        (ih (s + 1) (by omega)).run (σ := σ₁) ⟨henv₁, hcache₁, hmk₁⟩
      have hr₂' : Run B (foldRange (fun b => markParentsCom cap j (s + (b + 1))) r) σ₁ σ₂
          (markParentsK cap * r + 1) := by rw [hshift]; exact hr₂
      have hrun : Run B (foldRange (fun b => markParentsCom cap j (s + b)) (r + 1)) σ σ₂
          (markParentsK cap + (markParentsK cap * r + 1)) := by
        rw [foldRange_succ]
        exact hr₁.seq hr₂'
      refine ⟨σ₂, _, hrun, by ring_nf; omega, henv₂, hcache₂, ?_⟩
      have hre : s + 1 + r = s + (r + 1) := by omega
      rwa [hre] at hmk₂

/-- The cached batch phase replaces one graph search per earlier round
by one fixed-length parent-chain walk. -/
def batchCachedCost (n cap j : ℕ) : ℕ := markParentsK cap * j + 26 * n + 16

/-- **The executable cached batch, discharged.** Retained parent trees
supply the same short walks as the search-based batch while crossing all
cache records unchanged. -/
theorem batchCachedCom_spec {B cap mb j : ℕ} {d : ℕ}
    (hB : WordBoundK B n d ns cap mb) {U : ℕ → Fin n} {Gam : ℕ → ℕ → ℕ}
    {M Cut : ℕ → ℕ} {v : Fin n} (hMv : M (v : ℕ) ≠ 0)
    (hCutB : ∀ k, k < n → Cut k < B) (hvCut : Cut (v : ℕ) ≠ 0) :
    Spec B (fun σ => BatchEnv cap nt j O T U Gam v σ ∧
        CachedRounds cap G j M σ ∧ (∃ g, σ.arrs (batName j) = arrOf n g) ∧
        σ.arrs (cluName j) = arrOf n Cut)
      (batchCachedCom cap j)
      (fun _ σ' => BatchEnv cap nt j O T U Gam v σ' ∧
        CachedRounds cap G j M σ' ∧ σ'.arrs (cluName j) = arrOf n Cut ∧
        ∃ Wa : ℕ → ℕ, σ'.arrs (batName j) = arrOf n Wa ∧ (∀ k, k < n → Wa k < B) ∧
          markSet n Wa ⊆ markSet n Cut ∧ v ∈ markSet n Wa ∧
          (markSet n Wa).ncard ≤ 1 + j * (2 * cap + 1) ∧
          ∀ a, a < j → WithinDist (masked G (Gam a)) (2 * cap) (U a) v →
            ∃ p : (masked G (Gam a)).Walk (U a) v, p.length ≤ 2 * cap ∧
              {z : Fin n | z ∈ p.support} ∩ markSet n Cut ⊆ markSet n Wa)
      (batchCachedCost n cap j) := by
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  have hcutbat : cluName j ≠ batName j := by simp [cluName, batName, String.ext_iff]
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨henv, hcache, hbat₀, hcut⟩ := hσ
  have hvn : (v : ℕ) < n := v.isLt
  -- the indicator, opened
  obtain ⟨σ₁, hr₁, ⟨g₁, harr₁, hval₁⟩, -, -⟩ :=
    (fillCom_spec B n (batName j) 0 hnB (by omega)).run ⟨hbat₀, henv.1⟩
  have henv₁ : BatchEnv cap nt j O T U Gam v σ₁ :=
    batchEnv_run henv hr₁ (fun y hy => by
        rw [RamDriverIO.wvars_fillCom] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> exact mem_descendScalars_i)
      (fun b hb => Or.inl (by
        rw [RamDriverIO.warrs_fillCom] at hb; exact List.eq_of_mem_singleton hb))
  have hcache₁ : CachedRounds cap G j M σ₁ :=
    cachedRounds_batch_run hcache hr₁ (fun y hy => by
        rw [RamDriverIO.wvars_fillCom] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> exact mem_descendScalars_i)
      (fun b hb => by
        rw [RamDriverIO.warrs_fillCom] at hb
        exact List.eq_of_mem_singleton hb)
  -- the connector, stored
  have hctr₁ : σ₁.vars (ctrName j) = (v : ℕ) := henv₁.2.2.2.2.2.2.2.2.1
  have hlen₁ : (v : ℕ) < (σ₁.arrs (batName j)).length := by rw [harr₁, length_arrOf]; exact hvn
  have hev : (Expr.var (ctrName j)).evalB B σ₁ = some (v : ℕ) := by
    have h := evalB_var (B := B) (x := ctrName j) (σ := σ₁) (by rw [hctr₁]; omega)
    rwa [hctr₁] at h
  set σ₂ := σ₁.setArr (batName j) (v : ℕ) 1 with hσ₂
  have hr₂ : Run B (.store (batName j) (.var (ctrName j)) (.lit 1)) σ₁ σ₂ 3 :=
    (Run.store hev (evalB_lit (by omega)) hlen₁).mono (by simp [Expr.size])
  have harr₂ : σ₂.arrs (batName j) = arrOf n (upd g₁ (v : ℕ) 1) := by
    rw [hσ₂]; simp [harr₁, set_arrOf_eq_upd]
  have hzero : markSet n g₁ = ∅ := by
    ext z
    simp only [mem_markSet, Set.mem_empty_iff_false, iff_false, not_not]
    exact hval₁ _ z.isLt
  have hmark₂ : markSet n (upd g₁ (v : ℕ) 1) = {v} := by
    rw [markSet_upd_one g₁ hvn, hzero, Set.empty_union]
  have henv₂ : BatchEnv cap nt j O T U Gam v σ₂ :=
    batchEnv_run henv₁ hr₂ (fun y hy => by simp only [Com.wvars] at hy; exact absurd hy (by simp))
      (fun b hb => Or.inl (by simp only [Com.warrs] at hb; exact List.eq_of_mem_singleton hb))
  have hcache₂ : CachedRounds cap G j M σ₂ :=
    cachedRounds_batch_run hcache₁ hr₂
      (fun y hy => by simp only [Com.wvars] at hy; exact absurd hy (by simp))
      (fun b hb => by simp only [Com.warrs] at hb; exact List.eq_of_mem_singleton hb)
  have hmk₂ : BatchMark cap j G U Gam v 0 σ₂ := by
    refine ⟨upd g₁ (v : ℕ) 1, harr₂, ?_, by rw [hmark₂]; exact rfl, ?_, fun a ha => absurd ha
      (by omega)⟩
    · intro k hk
      by_cases hke : k = (v : ℕ)
      · rw [hke, upd_self]
      · rw [upd_of_ne _ hke, hval₁ k hk]; omega
    · rw [hmark₂, Set.ncard_singleton]; omega
  -- the cached fold over the earlier rounds
  have hfold : (foldRange (fun b => markParentsCom cap j (0 + b)) j) =
      foldRange (fun a => markParentsCom cap j a) j := by
    congr 1
    funext b
    congr 1
    omega
  obtain ⟨σ₃, hr₃, henv₃, hcache₃, Wf, hbat₃, hbit₃, hvf, hcard₃, hwalk₃⟩ :=
    (batchCachedFold_spec hB hMv j 0 (by omega)).run (σ := σ₂) ⟨henv₂, hcache₂, hmk₂⟩
  rw [hfold] at hr₃
  rw [Nat.zero_add] at hcard₃ hwalk₃
  have hcut₃ : σ₃.arrs (cluName j) = arrOf n Cut := by
    rw [hr₃.frame_arr _ (fun hc => ?_)]
    · rw [hr₂.frame_arr _ (by simp [Com.warrs, hcutbat]),
        hr₁.frame_arr _ (by rw [RamDriverIO.warrs_fillCom]; simp [hcutbat])]
      exact hcut
    · obtain ⟨b, -, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ _ hc
      rw [warrs_markParentsCom] at hm
      exact hcutbat (List.eq_of_mem_singleton hm)
  -- the cut to the retained cluster
  obtain ⟨σ₄, hr₄, ⟨Wa, hbat₄, hval₄⟩, -, -, hcut₄⟩ :=
    (andSelfCom_spec (B := B) n (cluName j) (batName j) Wf Cut hcutbat hnB
      (fun k hk => by have := hbit₃ k hk; omega) hCutB
      (fun k hk => by
        have h1 := hbit₃ k hk
        have h2 := hCutB k hk
        calc Wf k * Cut k ≤ 1 * Cut k := Nat.mul_le_mul_right _ h1
          _ = Cut k := by ring
          _ < B := h2)).run (σ := σ₃) ⟨hbat₃, henv₃.1, hcut₃⟩
  have henv₄ : BatchEnv cap nt j O T U Gam v σ₄ :=
    batchEnv_run henv₃ hr₄ (fun y hy => by
        rw [wvars_andCom] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> exact mem_descendScalars_i)
      (fun b hb => Or.inl (by
        rw [RamDriverFrames.warrs_andCom] at hb; exact List.eq_of_mem_singleton hb))
  have hcache₄ : CachedRounds cap G j M σ₄ :=
    cachedRounds_batch_run hcache₃ hr₄ (fun y hy => by
        rw [wvars_andCom] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> exact mem_descendScalars_i)
      (fun b hb => by
        rw [RamDriverFrames.warrs_andCom] at hb
        exact List.eq_of_mem_singleton hb)
  have hmarkeq : markSet n Wa = markSet n Wf ∩ markSet n Cut := by
    rw [markSet_congr hval₄, markSet_mul]
  refine ⟨σ₄, _, hr₁.seq (hr₂.seq (hr₃.seq hr₄)), ?_, henv₄, hcache₄, hcut₄, Wa,
    hbat₄, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [batchCachedCost]; omega
  · intro k hk
    rw [hval₄ k hk]
    have h1 := hbit₃ k hk
    have h2 := hCutB k hk
    calc Wf k * Cut k ≤ 1 * Cut k := Nat.mul_le_mul_right _ h1
      _ = Cut k := by ring
      _ < B := h2
  · rw [hmarkeq]; exact Set.inter_subset_right
  · rw [hmarkeq]; exact ⟨hvf, hvCut⟩
  · rw [hmarkeq]
    exact le_trans (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)) hcard₃
  · intro a ha hwd
    obtain ⟨p, hp, hps⟩ := hwalk₃ a ha hwd
    exact ⟨p, hp, by rw [hmarkeq]; exact Set.inter_subset_inter_left _ hps⟩

/-- The cost of the batch phase. -/
def batchCost (n ns cap j : ℕ) : ℕ := ancestorCost n ns cap * j + 26 * n + 16

/-- **The executable batch of the round, discharged.** What the
indicator ends marking is the connector together with the part inside
the retained set of one short walk per earlier round the round's own
arena reaches. -/
theorem batchCom_spec {B cap mb j : ℕ} (hcsr : CsrGraph G ns O T) (hnt : ns ≤ nt)
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) {U : ℕ → Fin n} {Gam : ℕ → ℕ → ℕ} {v : Fin n}
    {Cut : ℕ → ℕ} (hGamB : ∀ a, a < j → ∀ z, z < n → Gam a z < B)
    (hCutB : ∀ k, k < n → Cut k < B) (hvCut : Cut (v : ℕ) ≠ 0) :
    Spec B (fun σ => BatchEnv cap nt j O T U Gam v σ ∧
        (∃ g, σ.arrs (batName j) = arrOf n g) ∧ σ.arrs (cluName j) = arrOf n Cut)
      (batchCom cap j)
      (fun _ σ' => BatchEnv cap nt j O T U Gam v σ' ∧
        σ'.arrs (cluName j) = arrOf n Cut ∧
        ∃ Wa : ℕ → ℕ, σ'.arrs (batName j) = arrOf n Wa ∧ (∀ k, k < n → Wa k < B) ∧
          markSet n Wa ⊆ markSet n Cut ∧ v ∈ markSet n Wa ∧
          (markSet n Wa).ncard ≤ 1 + j * (2 * cap + 1) ∧
          ∀ a, a < j → WithinDist (masked G (Gam a)) (2 * cap) (U a) v →
            ∃ p : (masked G (Gam a)).Walk (U a) v, p.length ≤ 2 * cap ∧
              {z : Fin n | z ∈ p.support} ∩ markSet n Cut ⊆ markSet n Wa)
      (batchCost n ns cap j) := by
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  have hcutbat : cluName j ≠ batName j := by simp [cluName, batName, String.ext_iff]
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨henv, hbat₀, hcut⟩ := hσ
  have hvn : (v : ℕ) < n := v.isLt
  -- the indicator, opened
  obtain ⟨σ₁, hr₁, ⟨g₁, harr₁, hval₁⟩, -, -⟩ :=
    (fillCom_spec B n (batName j) 0 hnB (by omega)).run ⟨hbat₀, henv.1⟩
  have henv₁ : BatchEnv cap nt j O T U Gam v σ₁ :=
    batchEnv_run henv hr₁ (fun y hy => by
        rw [RamDriverIO.wvars_fillCom] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> exact mem_descendScalars_i)
      (fun b hb => Or.inl (by
        rw [RamDriverIO.warrs_fillCom] at hb; exact List.eq_of_mem_singleton hb))
  -- the connector, stored
  have hctr₁ : σ₁.vars (ctrName j) = (v : ℕ) := henv₁.2.2.2.2.2.2.2.2.1
  have hlen₁ : (v : ℕ) < (σ₁.arrs (batName j)).length := by rw [harr₁, length_arrOf]; exact hvn
  have hev : (Expr.var (ctrName j)).evalB B σ₁ = some (v : ℕ) := by
    have h := evalB_var (B := B) (x := ctrName j) (σ := σ₁) (by rw [hctr₁]; omega)
    rwa [hctr₁] at h
  set σ₂ := σ₁.setArr (batName j) (v : ℕ) 1 with hσ₂
  have hr₂ : Run B (.store (batName j) (.var (ctrName j)) (.lit 1)) σ₁ σ₂ 3 :=
    (Run.store hev (evalB_lit (by omega)) hlen₁).mono (by simp [Expr.size])
  have harr₂ : σ₂.arrs (batName j) = arrOf n (upd g₁ (v : ℕ) 1) := by
    rw [hσ₂]; simp [harr₁, set_arrOf_eq_upd]
  have hzero : markSet n g₁ = ∅ := by
    ext z
    simp only [mem_markSet, Set.mem_empty_iff_false, iff_false, not_not]
    exact hval₁ _ z.isLt
  have hmark₂ : markSet n (upd g₁ (v : ℕ) 1) = {v} := by
    rw [markSet_upd_one g₁ hvn, hzero, Set.empty_union]
  have henv₂ : BatchEnv cap nt j O T U Gam v σ₂ :=
    batchEnv_run henv₁ hr₂ (fun y hy => by simp only [Com.wvars] at hy; exact absurd hy (by simp))
      (fun b hb => Or.inl (by simp only [Com.warrs] at hb; exact List.eq_of_mem_singleton hb))
  have hmk₂ : BatchMark cap j G U Gam v 0 σ₂ := by
    refine ⟨upd g₁ (v : ℕ) 1, harr₂, ?_, by rw [hmark₂]; exact rfl, ?_, fun a ha => absurd ha
      (by omega)⟩
    · intro k hk
      by_cases hke : k = (v : ℕ)
      · rw [hke, upd_self]
      · rw [upd_of_ne _ hke, hval₁ k hk]; omega
    · rw [hmark₂, Set.ncard_singleton]; omega
  -- the fold over the earlier rounds
  have hfold : (foldRange (fun b => ancestorStep cap j (0 + b)) j) =
      foldRange (fun a => ancestorStep cap j a) j := by
    congr 1
    funext b
    congr 1
    omega
  obtain ⟨σ₃, hr₃, henv₃, Wf, hbat₃, hbit₃, hvf, hcard₃, hwalk₃⟩ :=
    (batchFold_spec hcsr hnt hB hGamB j 0 (by omega)).run (σ := σ₂) ⟨henv₂, hmk₂⟩
  rw [hfold] at hr₃
  rw [Nat.zero_add] at hcard₃ hwalk₃
  have hcut₃ : σ₃.arrs (cluName j) = arrOf n Cut := by
    rw [hr₃.frame_arr _ (fun hc => ?_)]
    · rw [hr₂.frame_arr _ (by simp [Com.warrs, hcutbat]),
        hr₁.frame_arr _ (by rw [RamDriverIO.warrs_fillCom]; simp [hcutbat])]
      exact hcut
    · obtain ⟨b, -, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ _ hc
      rw [warrs_ancestorStep] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      revert hm
      simp [cluName, batName, String.ext_iff]
  -- the cut to the retained cluster
  obtain ⟨σ₄, hr₄, ⟨Wa, hbat₄, hval₄⟩, -, -, hcut₄⟩ :=
    (andSelfCom_spec (B := B) n (cluName j) (batName j) Wf Cut hcutbat hnB
      (fun k hk => by have := hbit₃ k hk; omega) hCutB
      (fun k hk => by
        have h1 := hbit₃ k hk
        have h2 := hCutB k hk
        calc Wf k * Cut k ≤ 1 * Cut k := Nat.mul_le_mul_right _ h1
          _ = Cut k := by ring
          _ < B := h2)).run (σ := σ₃) ⟨hbat₃, henv₃.1, hcut₃⟩
  have henv₄ : BatchEnv cap nt j O T U Gam v σ₄ :=
    batchEnv_run henv₃ hr₄ (fun y hy => by
        rw [wvars_andCom] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> exact mem_descendScalars_i)
      (fun b hb => Or.inl (by
        rw [RamDriverFrames.warrs_andCom] at hb; exact List.eq_of_mem_singleton hb))
  have hmarkeq : markSet n Wa = markSet n Wf ∩ markSet n Cut := by
    rw [markSet_congr hval₄, markSet_mul]
  refine ⟨σ₄, _, hr₁.seq (hr₂.seq (hr₃.seq hr₄)), ?_, henv₄, hcut₄, Wa, hbat₄, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [batchCost]; omega
  · intro k hk
    rw [hval₄ k hk]
    have h1 := hbit₃ k hk
    have h2 := hCutB k hk
    calc Wf k * Cut k ≤ 1 * Cut k := Nat.mul_le_mul_right _ h1
      _ = Cut k := by ring
      _ < B := h2
  · rw [hmarkeq]; exact Set.inter_subset_right
  · rw [hmarkeq]; exact ⟨hvf, hvCut⟩
  · rw [hmarkeq]
    exact le_trans (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)) hcard₃
  · intro a ha hwd
    obtain ⟨p, hp, hps⟩ := hwalk₃ a ha hwd
    exact ⟨p, hp, by rw [hmarkeq]; exact Set.inter_subset_inter_left _ hps⟩

end Batch

/-! ### What the descent writes

The array side of the descent's frame, sharpened from
`RamDriverFrames.underscore_notMem_warrs_descendCom` — which separates
the prefixed names from the colours and the tables — to the twelve names
the pass actually writes. The two masks of the *next* depth are among
them, so the frame has to tell `alvName j` from `alvName (j + 1)`, which
is the one place in the driver where a name's depth has to be read back
off the name. -/

section DescendFrame

/-- **A prefixed name determines its depth.** -/
theorem prefixed_inj {p : String} {a b : ℕ} (h : p ++ toString a = p ++ toString b) : a = b := by
  refine RamDriverBase.toString_inj ?_
  rw [String.ext_iff] at h ⊢
  simpa using h

theorem alvName_ne_succ (j : ℕ) : alvName j ≠ alvName (j + 1) := fun h => by
  simp only [alvName] at h
  have := prefixed_inj h
  omega

theorem gamName_ne_succ {a j : ℕ} (h : a ≤ j) : gamName a ≠ gamName (j + 1) := fun hc => by
  simp only [gamName] at hc
  have := prefixed_inj hc
  omega

/-- The member list is depth-indexed like the two masks (rebase E-mem):
what the descent writes is the *child's*, so the parent's crosses. -/
theorem memName_ne_succ (j : ℕ) : memName j ≠ memName (j + 1) := fun h => by
  simp only [memName] at h
  have := prefixed_inj h
  omega

theorem mnumName_ne_succ (j : ℕ) : mnumName j ≠ mnumName (j + 1) := fun h => by
  simp only [mnumName] at h
  have := prefixed_inj h
  omega

theorem mem_warrs_ancestorStep' {cap j a : ℕ} {b : String}
    (h : b ∈ (ancestorStep cap j a).warrs) :
    b = batName j ∨ b ∈ (["alv", "dist", "q", "par", "path"] : List String) := by
  rw [warrs_ancestorStep] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr (by decide)

theorem mem_warrs_batchCom {cap j : ℕ} {b : String} (h : b ∈ (batchCom cap j).warrs) :
    b = batName j ∨ b ∈ (["alv", "dist", "q", "par", "path"] : List String) := by
  simp only [batchCom, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, RamDriverIO.warrs_fillCom, RamDriverFrames.warrs_andCom] at h
  rcases h with rfl | rfl | hf | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · obtain ⟨b', -, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ _ hf
    exact mem_warrs_ancestorStep' hm
  · exact Or.inl rfl

theorem mem_warrs_bfsBlockParCom_zero :
    ∀ b ∈ (Refine.BfsBlockPar.bfsBlockParCom 0).warrs,
      b ∈ (["dist", "par", "q", "qd"] : List String) := by decide

theorem mem_warrs_cacheBfsCom {cap j : ℕ} {b : String}
    (h : b ∈ (cacheBfsCom cap j).warrs) :
    b = balAltName j ∨ b = balName j ∨ b = "q" ∨ b = "qd" := by
  rw [cacheBfsCom, Refine.ScatterBlock.renCom_warrs, List.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  rw [RamDriverFrames.warrs_bfsBlockParCom] at ha
  have hm := mem_warrs_bfsBlockParCom_zero a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact Or.inl (by
      simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff])
  · exact Or.inr (Or.inl (by
      simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]))
  · exact Or.inr (Or.inr (Or.inl (by
      simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff])))
  · exact Or.inr (Or.inr (Or.inr (by
      simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff])))

theorem mem_warrs_cacheRoundCom {cap j : ℕ} {b : String}
    (h : b ∈ (cacheRoundCom cap j).warrs) :
    b = balAltName j ∨ b = balName j ∨ b = "q" ∨ b = "qd" := by
  have h' : b = pdsName j ∨ b ∈ (cacheBfsCom cap j).warrs := by
    simpa [cacheRoundCom, Com.warrs, RamDriverFrames.warrs_memFillAt_cacheframe] using h
  rcases h' with rfl | h'
  · exact Or.inl (by simp [pdsName])
  · exact mem_warrs_cacheBfsCom h'

theorem mem_warrs_batchCachedCom {cap j : ℕ} {b : String}
    (h : b ∈ (batchCachedCom cap j).warrs) : b = batName j := by
  simp only [batchCachedCom, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, RamDriverIO.warrs_fillCom, RamDriverFrames.warrs_andCom] at h
  rcases h with rfl | rfl | hf | rfl
  · rfl
  · rfl
  · obtain ⟨a, -, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ _ hf
    rw [warrs_markParentsCom] at hm
    exact List.eq_of_mem_singleton hm
  · rfl

/-- The arrays the descent writes. -/
def descendArrs (j : ℕ) : List String :=
  [cluName j, resName j, balName j, balAltName j, batName j, alvName (j + 1), gamName (j + 1),
    memName (j + 1), "alv", "dist", "q", "qd", "par", "path"]

theorem mem_warrs_descendCom' {cap j : ℕ} {b : String} (h : b ∈ (descendCom cap j).warrs) :
    b ∈ descendArrs j := by
  simp only [descendCom, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, false_or, RamDriverFrames.warrs_clusterLoad, RamDriverFrames.warrs_andCom,
    RamDriverFrames.warrs_subCom, RamDriverFrames.warrs_memFilterCom] at h
  rcases h with (rfl | rfl | rfl) | rfl | hc | hb | rfl | rfl | rfl | rfl
  · exact by simp [descendArrs]
  · exact by simp [descendArrs]
  · exact by simp [descendArrs]
  · exact by simp [descendArrs]
  · rcases mem_warrs_cacheRoundCom hc with rfl | rfl | rfl | rfl <;>
      simp [descendArrs]
  · rw [mem_warrs_batchCachedCom hb]
    simp [descendArrs]
  · exact by simp [descendArrs]
  · exact by simp [descendArrs]
  · exact by simp [descendArrs]
  · exact by simp [descendArrs]

theorem notMem_warrs_descendCom {cap j : ℕ} {b : String} (h : b ∉ descendArrs j) :
    b ∉ (descendCom cap j).warrs := fun hc => h (mem_warrs_descendCom' hc)

end DescendFrame

/-! ### The descent, discharged

The descent passes composed. Their content is the two mask equations
`RamDriver.masked_step` and `RamDriver.masked_mul`, the cluster-truncated
batch phase above, and the in-place difference `subSelfCom_spec` was
written for. The former ball-expansion slot is now a constant-cost
`skip`; cover geometry supplies its semantic inclusion.

Two facts come from *outside* the turn and are hypotheses of the theorem
rather than clauses of `RamDriverCluster.DescendStep`, in the manner of
`RamDriverCluster.clusterStepImplements`'s `hcap`: that `mb` is
`ℓ · (2·cap + 1)` and that the depth is below `ℓ`. Together they give
`1 + j · (2·cap + 1) ≤ mb`, the size bound on the batch, and
`RamDriverCluster.levelImplements` has both where it applies the
obligation. -/

section Descend

variable {ns : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

theorem ctrName_ne {a b : ℕ} (h : a ≠ b) : ctrName a ≠ ctrName b := fun hc => by
  simp only [ctrName] at hc
  exact h (prefixed_inj hc)

theorem ctrName_notMem_descendScalars (a : ℕ) : ctrName a ∉ descendScalars :=
  RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide)

/-- Building the current cache leaves every strictly earlier cache
untouched: its only depth-indexed destination is the current parent
array. -/
theorem cachedRounds_cacheRound_run {B K cap j : ℕ} {M : ℕ → ℕ} {σ σ' : Env}
    (h : CachedRounds cap G j M σ) (hrun : Run B (cacheRoundCom cap j) σ σ' K) :
    CachedRounds cap G j M σ' := by
  refine h.congr ?_ ?_ ?_ ?_
  · intro a ha
    rw [hrun.frame_var (ctrName a) (fun hc => by
      rcases mem_wvars_cacheRoundCom hc with hm | hm
      · simpa [ctrName, mnumName, String.ext_iff] using hm
      · exact (ctrName_notMem_descendScalars a) hm)]
  · intro a ha
    rw [hrun.frame_arr (resName a) (fun hc => by
      rcases mem_warrs_cacheRoundCom hc with hm | hm | hm | hm <;>
        simpa [resName, balName, balAltName, String.ext_iff] using hm)]
  · intro a ha
    rw [hrun.frame_arr (gamName a) (fun hc => by
      rcases mem_warrs_cacheRoundCom hc with hm | hm | hm | hm <;>
        simpa [gamName, balName, balAltName, String.ext_iff] using hm)]
  · intro a ha
    rw [hrun.frame_arr (parName a) (fun hc => by
      rcases mem_warrs_cacheRoundCom hc with hm | hm | hm | hm
      · simpa [parName, balName, balAltName, String.ext_iff] using hm
      · have : a = j := prefixed_inj (p := "bal") (by simpa only [parName, balName] using hm)
        omega
      · simpa [parName, balName, String.ext_iff] using hm
      · simpa [parName, balName, String.ext_iff] using hm)]

/-- **A letter does not occur in a decimal representation**, which is
`RamDriverBase.underscore_not_mem_toDigits` at any character no digit
is. -/
theorem notMem_toDigits {c : Char} (hc : ∀ d, d < 10 → Nat.digitChar d ≠ c) :
    ∀ a : ℕ, c ∉ Nat.toDigits 10 a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i hlt
      simp only [List.mem_singleton]
      exact fun h => hc _ hlt h.symm
    · rename_i hge
      have hpos : 0 < a := by omega
      simp only [List.mem_append, not_or]
      refine ⟨ih (a / 10) (Nat.div_lt_self hpos (by omega)), ?_⟩
      simp only [List.mem_singleton]
      exact fun h => hc _ (Nat.mod_lt _ (by omega)) h.symm

theorem toList_toString (a : ℕ) : (toString a).toList = Nat.toDigits 10 a := by
  rw [Nat.toString_eq_repr, RamDriverBase.repr_eq_ofList]
  simp

theorem decimalDigits_inj {a b : ℕ} (h : Nat.toDigits 10 a = Nat.toDigits 10 b) : a = b := by
  apply RamDriverBase.toString_inj
  apply String.toList_inj.mp
  simpa only [toList_toString] using h

/-- The centre cursor is not the extraction's own cursor: the driver's
name is `cu` followed by a numeral, and `cur` is `cu` followed by a
letter. This is the one collision in the descent's scalar frame — every
other counter differs from a prefixed name inside the first three
characters. -/
theorem curName_ne_cur (a : ℕ) : curName a ≠ "cur" := by
  intro h
  have hl : ("cu" : String) ++ toString a = "cu" ++ "r" := by
    rw [← curName, h]; decide
  have h2 : Nat.toDigits 10 a = ['r'] := by
    rw [← toList_toString]
    have := congrArg String.toList hl
    simpa using this
  exact notMem_toDigits (c := 'r') (fun d hd => by interval_cases d <;> decide) a
    (by rw [h2]; simp)

theorem curName_notMem_descendScalars (a : ℕ) : curName a ∉ descendScalars := by
  simp only [descendScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    curName_ne_cur a, ?_, ?_⟩ <;> simp [curName, String.ext_iff]

theorem xpName_notMem_descendScalars (a : ℕ) : xpName a ∉ descendScalars :=
  RamDriverIO.notMem_of_append (p := "xq") (s := toString a) (by decide)

theorem noWrite_ancestorStep (cap j a : ℕ) : (ancestorStep cap j a).NoWrite := by
  have he : (ancestorStep cap j a).NoWrite = (ancestorStep 0 0 0).NoWrite := rfl
  rw [he]
  decide

theorem noWrite_batchCom (cap j : ℕ) : (batchCom cap j).NoWrite :=
  ⟨RamDriverIO.noWrite_fillCom _ _, trivial,
    noWrite_foldr (fun a => noWrite_ancestorStep cap j a) _,
    by rw [andCom]; exact RamDriverIO.noWrite_fillCom _ _⟩

theorem noWrite_bfsBlockParCom (d : ℕ) :
    (Refine.BfsBlockPar.bfsBlockParCom d).NoWrite := by
  have he : (Refine.BfsBlockPar.bfsBlockParCom d).NoWrite =
      (Refine.BfsBlockPar.bfsBlockParCom 0).NoWrite := rfl
  rw [he]
  decide

theorem noWrite_cacheBfsCom (cap j : ℕ) : (cacheBfsCom cap j).NoWrite := by
  rw [cacheBfsCom]
  exact Refine.ScatterBlock.renCom_noWrite _ (noWrite_bfsBlockParCom (2 * cap))

theorem noWrite_memFillAt (j : ℕ) (a : String) (c : ℕ) :
    (memFillAt j a c).NoWrite := by
  have he : (memFillAt j a c).NoWrite = (memFillAt 0 "a" 0).NoWrite := rfl
  rw [he]
  decide

theorem noWrite_cacheRoundCom (cap j : ℕ) : (cacheRoundCom cap j).NoWrite :=
  ⟨trivial, trivial, noWrite_memFillAt j (pdsName j) (2 * cap + 1),
    noWrite_cacheBfsCom cap j⟩

theorem noWrite_markParentsCom (cap j a : ℕ) : (markParentsCom cap j a).NoWrite := by
  have he : (markParentsCom cap j a).NoWrite = (markParentsCom 0 0 0).NoWrite := rfl
  rw [he]
  decide

theorem noWrite_batchCachedCom (cap j : ℕ) : (batchCachedCom cap j).NoWrite :=
  ⟨RamDriverIO.noWrite_fillCom _ _, trivial,
    noWrite_foldr (fun a => noWrite_markParentsCom cap j a) _,
    by rw [andCom]; exact RamDriverIO.noWrite_fillCom _ _⟩

theorem noWrite_clusterLoad (j : ℕ) : (clusterLoad j).NoWrite := by
  have he : (clusterLoad j).NoWrite = (clusterLoad 0).NoWrite := rfl
  rw [he]
  decide

theorem noWrite_memFilterCom (j : ℕ) : (memFilterCom j).NoWrite := by
  have he : (memFilterCom j).NoWrite = (memFilterCom 0).NoWrite := rfl
  rw [he]
  decide

theorem noWrite_descendCom (cap j : ℕ) : (descendCom cap j).NoWrite :=
  ⟨trivial, noWrite_clusterLoad j, by rw [andCom]; exact RamDriverIO.noWrite_fillCom _ _,
    noWrite_cacheRoundCom cap j,
    noWrite_batchCachedCom cap j,
    by rw [subCom]; exact RamDriverIO.noWrite_fillCom _ _,
    by rw [andCom]; exact RamDriverIO.noWrite_fillCom _ _,
    ⟨by rw [subCom]; exact RamDriverIO.noWrite_fillCom _ _, noWrite_memFilterCom (j + 1)⟩⟩

/-- **The size-indexed descent cost.** The cluster scan, the retained
parent search, and the member filter are all read at the turn's block
weight `s`.  The cached batch replaces `j` graph searches by `j`
fixed-length parent walks, so its only round-dependent term is
`markParentsK cap * j`.

**Rebase E-mem.** Two addends moved. The block scan carries the member
emission (`8` per block cell inside the scan, `16 → 24`), and the
filter pass adds `23·bs + 8` at the end, read at `bs ≤ n`
(`RamDriver.MemEnum.card_le`). The whole member thread remains inside
the turn's descend slot; no new slot appears. -/
def descendCostSize (n ns cap j s : ℕ) : ℕ :=
  193 * s + 75 * n + 135 + batchCachedCost n cap j

/-- The carrier reading of the size-indexed descent cost. -/
def descendCost (n ns cap j : ℕ) : ℕ := descendCostSize n ns cap j n

/-- **The descent, discharged.** -/
theorem descendStep {B cap mb Ws ℓ j k K : ℕ} {M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    (hcsrS : RamElim.CsrSimple G ns O T)
    (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hK : descendCostSize n ns cap j
      (Refine.MassWeight.blockWeight n G Xoff Xmem k) ≤ K) :
    DescendStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m k K := by
  classical
  intro hcsr d hB hkn halive
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hlev, hplay, hheld⟩, hcurEq⟩ := hσ
  have hcur : σ.vars (curName j) < n := by rw [hcurEq]; exact hkn
  obtain ⟨hn, hoff, htgt, halvj, hgamj, hcolj, hMB, hGmB, hCbit, hmem, hdep, hmvar, hom⟩ := hlev
  obtain ⟨hordA, hxof, hxmm, hasgA, hxp, hmn, hmB, hordlt, hcout⟩ := hheld
  have h1B := hB.one_lt
  have hnB := hB.n_lt
  have hnsB := hB.ns_lt
  obtain ⟨cc, hcc⟩ : ∃ cc, σ.vars (curName j) = cc := ⟨_, rfl⟩
  rw [hcc] at hcur
  have hcck : cc = k := by rw [← hcurEq, hcc]
  have hordc : ord cc < n := hordlt cc hcur
  -- the depth's connector, as a vertex
  obtain ⟨vc, hvc⟩ : ∃ vc : Fin n, (vc : ℕ) = ord cc := ⟨⟨ord cc, hordc⟩, rfl⟩
  -- the rounds the state records, as two total functions
  obtain ⟨rounds, hrec, hle, hplayR, hcached⟩ := hplay
  have hplay₀ : PlayRec B cap G j M Gm σ := ⟨rounds, hrec, hle, hplayR, hcached⟩
  have hex : ∀ a : ℕ, ∃ (u : Fin n) (Ga : ℕ → ℕ), a < j →
      σ.vars (ctrName a) = (u : ℕ) ∧ σ.arrs (gamName a) = arrOf n Ga ∧
        ∀ z, z < n → Ga z < B := by
    intro a
    by_cases ha : a < j
    · obtain ⟨u, Ga, h1, h2, h3⟩ := hrec.get a ha
      exact ⟨u, Ga, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨vc, fun _ => 0, fun hcon => absurd hcon ha⟩
  choose U Gam hUG using hex
  -- the memory the passes address
  have hclu₀ : ∃ g, σ.arrs (cluName j) = arrOf n g := hdep.get (p := (cluName j, n)) j (by simp)
  have hres₀ : ∃ g, σ.arrs (resName j) = arrOf n g := hdep.get (p := (resName j, n)) j (by simp)
  have hbat₀ : ∃ g, σ.arrs (batName j) = arrOf n g := hdep.get (p := (batName j, n)) j (by simp)
  have halv1₀ : ∃ g, σ.arrs (alvName (j + 1)) = arrOf n g :=
    hdep.get (p := (alvName (j + 1), n)) (j + 1) (by simp)
  have hgam1₀ : ∃ g, σ.arrs (gamName (j + 1)) = arrOf n g :=
    hdep.get (p := (gamName (j + 1), n)) (j + 1) (by simp)
  have hmem1₀ : ∃ g, σ.arrs (memName (j + 1)) = arrOf n g :=
    hdep.get (p := (memName (j + 1), n)) (j + 1) (by simp)
  have halvS₀ : ∃ g, σ.arrs "alv" = arrOf n g := hmem.1.get (p := ("alv", n)) (by simp)
  have hdistS₀ : ∃ g, σ.arrs "dist" = arrOf n g := hmem.1.get (p := ("dist", n)) (by simp)
  have hqS₀ : ∃ g, σ.arrs "q" = arrOf n g := hmem.1.get (p := ("q", n)) (by simp)
  have hqdS₀ : ∃ g, σ.arrs "qd" = arrOf n g := hmem.1.get (p := ("qd", n)) (by simp)
  have hparS₀ : ∃ g, σ.arrs "par" = arrOf n g := hmem.1.get (p := ("par", n)) (by simp)
  have hpathS₀ : ∃ g, σ.arrs "path" = arrOf (2 * cap + 1) g :=
    hmem.1.get (p := ("path", 2 * cap + 1)) (by simp)
  have hpds₀ : ∃ g, σ.arrs (pdsName j) = arrOf n g :=
    hdep.get (p := (pdsName j, n)) j (by simp [pdsName])
  have hparj₀ : ∃ g, σ.arrs (parName j) = arrOf n g :=
    hdep.get (p := (parName j, n)) j (by simp [parName])
  -- P1: the connector is read out of the ordering
  have hev₁ : (Expr.get (ordName j) (.var (curName j))).evalB B σ = some (ord cc) := by
    have hc0 : (Expr.var (curName j)).evalB B σ = some cc := by
      have h := evalB_var (B := B) (x := curName j) (σ := σ) (by rw [hcc]; omega)
      rwa [hcc] at h
    exact evalB_get hc0 (by rw [hordA, getElem?_arrOf ord hcur]) (by omega)
  set σ₁ := σ.setVar (ctrName j) (ord cc) with hσ₁
  have hr₁ : Run B (.assign (ctrName j) (.get (ordName j) (.var (curName j)))) σ σ₁ 3 :=
    (Run.assign hev₁).mono (by simp [Expr.size])
  have harrs₁ : ∀ b : String, σ₁.arrs b = σ.arrs b := fun b => by rw [hσ₁, arrs_setVar]
  have hvars₁ : ∀ y : String, y ≠ ctrName j → σ₁.vars y = σ.vars y := fun y hy => by
    rw [hσ₁, vars_setVar, if_neg hy]
  have hctr₁ : σ₁.vars (ctrName j) = (vc : ℕ) := by rw [hσ₁]; simp [hvc]
  have hcurne : curName j ≠ ctrName j := by simp [curName, ctrName, String.ext_iff]
  have hcur₁ : σ₁.vars (curName j) = cc := by rw [hvars₁ _ hcurne, hcc]
  -- P2: the cluster, materialized
  obtain ⟨σ₂, hr₂, ⟨Xa, hclu₂, hXbit, hXmark, Mm, bs, hmemA₂, hbq₂, hbsEq, hMmE⟩,
      hfv₂, hfa₂, -, -⟩ :=
    ((clusterLoad_spec (j := j) (c := cc) hB hmB hcout hmn hcur).frame).run (σ := σ₁)
      ⟨by rw [hvars₁ "n" (by simp [ctrName, String.ext_iff]), hn],
        by rw [harrs₁]; exact hxof, by rw [harrs₁]; exact hxmm, by rw [harrs₁]; exact hclu₀,
        by rw [harrs₁]; exact hmem1₀,
        hcur₁⟩
  rw [hcur₁] at hXmark
  have hav₂ : ∀ b : String, b ≠ cluName j → b ≠ memName (j + 1) → σ₂.arrs b = σ₁.arrs b :=
    fun b hb hb' => hfa₂ b (by rw [RamDriverFrames.warrs_clusterLoad]; simp [hb, hb'])
  have hvv₂ : ∀ y : String, y ∉ descendScalars → σ₂.vars y = σ₁.vars y :=
    fun y hy => hfv₂ y (fun hcon => hy (mem_wvars_clusterLoad hcon))
  have hctrs : ctrName j ∉ descendScalars := ctrName_notMem_descendScalars j
  -- P3: the cluster-restricted mask
  have hXB : ∀ k, k < n → M k * Xa k < B := by
    intro k hk
    calc M k * Xa k ≤ M k * 1 := Nat.mul_le_mul_left _ (hXbit k hk)
      _ = M k := by ring
      _ < B := hMB k hk
  obtain ⟨σ₃, hr₃, ⟨⟨Ra, hres₃, hRaval⟩, -, hn₃, -, hclu₃⟩, hfv₃, hfa₃, -, -⟩ :=
    ((andCom_spec B n (alvName j) (cluName j) (resName j) M Xa
      (by simp [alvName, resName, String.ext_iff]) (by simp [cluName, resName, String.ext_iff])
      hnB hMB (fun k hk => by have := hXbit k hk; omega) hXB).frame).run (σ := σ₂)
      ⟨by rw [hav₂ _ (by simp [cluName, resName, String.ext_iff])
          (by simp [memName, resName, String.ext_iff]), harrs₁]; exact hres₀,
        by rw [hvv₂ "n" (by decide), hvars₁ "n" (by simp [ctrName, String.ext_iff])]; exact hn,
        by rw [hav₂ _ (by simp [alvName, cluName, String.ext_iff])
          (by simp [alvName, memName, String.ext_iff]), harrs₁]; exact halvj,
        hclu₂⟩
  have hav₃ : ∀ b : String, b ≠ resName j → σ₃.arrs b = σ₂.arrs b :=
    fun b hb => hfa₃ b (by rw [RamDriverFrames.warrs_andCom]; simp [hb])
  have hvv₃ : ∀ y : String, y ≠ "i" → σ₃.vars y = σ₂.vars y :=
    fun y hy => hfv₃ y (by rw [wvars_andCom]; simp [hy])
  have hRaB : ∀ k, k < n → Ra k < B := fun k hk => by rw [hRaval k hk]; exact hXB k hk
  have hvX : vc ∈ markSet n Xa := by
    rw [hXmark]
    exact ⟨hordc, by rw [hvc]; exact hordc, by
      simpa only [hvc] using RamCover.self_mem_wreach (masked G M) π (2 * cap)
        (⟨ord cc, hordc⟩ : Fin n)⟩
  have hMvc : M (ord cc) ≠ 0 := by rw [hcck]; exact halive
  have hXvc : Xa (ord cc) ≠ 0 := by
    change Xa (vc : ℕ) ≠ 0 at hvX
    simpa only [hvc] using hvX
  have hRvc : Ra (ord cc) ≠ 0 := by
    rw [hRaval _ hordc]
    exact Nat.mul_ne_zero hMvc hXvc
  have hRaX : ∀ z, z < n → Ra z ≠ 0 → Xa z ≠ 0 := by
    intro z hz hRz hXz
    rw [hRaval z hz, hXz, Nat.mul_zero] at hRz
    exact hRz rfl
  have hRaM : ∀ z, z < n → Ra z ≠ 0 → M z ≠ 0 := by
    intro z hz hRz hMz
    rw [hRaval z hz, hMz, Nat.zero_mul] at hRz
    exact hRz rfl
  -- Every weak-reachability witness defining the cover cluster has a suffix
  -- wholly inside that cluster, hence wholly inside the retained mask `Ra`.
  have hRcov : ∀ z, z < n → Ra z ≠ 0 → WD G Ra (2 * cap) (ord cc) z := by
    intro z hz hRz
    have hclz : RamCover.InCluster (masked G M) π cap (ord cc) z := by
      have hzX := hRaX z hz hRz
      change (⟨z, hz⟩ : Fin n) ∈ markSet n Xa at hzX
      rw [hXmark] at hzX
      exact hzX
    obtain ⟨p, hp, hps⟩ :=
      RamCover.exists_walk_support_inCluster (A := masked G M) (π := π) hordc hz hclz
    have hpR : ∀ y ∈ p.support, Ra (y : ℕ) ≠ 0 := by
      intro y hy
      have hycl : y ∈ Refine.MassMath.clusterAt G M π ord cap cc := hps y hy
      have hyM : M (y : ℕ) ≠ 0 :=
        Refine.MassAlive.clusterAt_subset_alive hMvc hycl
      have hyX : Xa (y : ℕ) ≠ 0 := by
        have hyX' : y ∈ markSet n Xa := by
          rw [hXmark]
          exact hps y hy
        exact hyX'
      rw [hRaval _ y.isLt]
      exact Nat.mul_ne_zero hyM hyX
    obtain ⟨q, hq⟩ := walk_masked_of_support p hpR
    exact ⟨hordc, hz, q, by rw [hq]; exact hp⟩
  -- The finite search support is the current cover block.  Its listed rows
  -- and its cardinality are each paid by this block's graph weight.
  let I : Finset ℕ := Finset.Ico (Xoff cc) (Xoff (cc + 1))
  let A : Finset ℕ := I.image Xmem
  have hA : ∀ v, v < n → Ra v ≠ 0 → WD G Ra (2 * cap) (ord cc) v → v ∈ A := by
    intro v hv hRv _
    have hvcl : RamCover.InCluster (masked G M) π cap (ord cc) v := by
      have hvX := hRaX v hv hRv
      change (⟨v, hv⟩ : Fin n) ∈ markSet n Xa at hvX
      rw [hXmark] at hvX
      exact hvX
    obtain ⟨p, hp₁, hp₂, hpv⟩ := (hcout.block cc hcur v).mpr hvcl
    exact Finset.mem_image.mpr ⟨p, Finset.mem_Ico.mpr ⟨hp₁, hp₂⟩, hpv⟩
  have hginj : Set.InjOn Xmem (I : Set ℕ) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_Ico.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_Ico.mp (Finset.mem_coe.mp hq)
    exact hcout.block_inj cc hcur p q hp'.1 hp'.2 hq'.1 hq'.2 hpq
  have hmemlt : ∀ p, Xoff cc ≤ p → p < Xoff (cc + 1) → Xmem p < n :=
    fun p hp hp' => Refine.MassWeight.mem_lt_of_coverOut hcout hcur hp hp'
  have hrowA : (∑ v ∈ A, Csr.rowLen O v) =
      Refine.MassWeight.blockRowSum O Xoff Xmem cc := by
    simp only [A, I]
    rw [Refine.MassWeight.blockRowSum,
      Finset.sum_image (g := Xmem) (f := fun v => Csr.rowLen O v) hginj]
  have hrowW : Refine.MassWeight.blockRowSum O Xoff Xmem cc ≤
      Refine.MassWeight.blockWeight n G Xoff Xmem k := by
    rw [Refine.MassWeight.blockRowSum_eq_blockDegSum hcsrS hmemlt, ← hcck]
    exact Refine.MassWeight.blockDegSum_le_blockWeight G Xoff Xmem hmemlt
  have hcardW : A.card ≤ Refine.MassWeight.blockWeight n G Xoff Xmem k := by
    calc
      A.card ≤ I.card := Finset.card_image_le
      _ = Refine.MassMath.blockSize Xoff cc := by simp [I, Refine.MassMath.blockSize]
      _ ≤ Refine.MassWeight.blockWeight n G Xoff Xmem k := by
        rw [← hcck]
        exact Refine.MassWeight.blockSize_le_blockWeight G Xoff Xmem hmemlt
  have hcached₃ : CachedRounds cap G j M σ₃ := by
    refine hcached.congr ?_ ?_ ?_ ?_
    · intro a ha
      rw [hvv₃ _ (by simp [ctrName, String.ext_iff]),
        hvv₂ _ (ctrName_notMem_descendScalars a),
        hvars₁ _ (ctrName_ne (by omega))]
    · intro a ha
      rw [hav₃ _ (fun hc => by
          have : a = j := prefixed_inj (p := "res") (by simpa only [resName] using hc)
          omega),
        hav₂ _ (by simp [resName, cluName, String.ext_iff])
          (by simp [resName, memName, String.ext_iff]), harrs₁]
    · intro a ha
      rw [hav₃ _ (by simp [gamName, resName, String.ext_iff]),
        hav₂ _ (by simp [gamName, cluName, String.ext_iff])
          (by simp [gamName, memName, String.ext_iff]), harrs₁]
    · intro a ha
      rw [hav₃ _ (by simp [parName, balName, resName, String.ext_iff]),
        hav₂ _ (by simp [parName, balName, cluName, String.ext_iff])
          (by simp [parName, balName, memName, String.ext_iff]), harrs₁]
  -- P4: retain the current cluster's capped parent tree.
  obtain ⟨σ₄, hr₄, -, Dp, Pp, hpar₄, htree₄⟩ :=
    (cacheRoundCom_specW (j := j) (G := G) (O := O) (T := T) (R := Ra) (X := Xa)
      (Mem := Mm) hcsr hom.1.1 hB hordc hRvc hMmE hRaX hRaB (A := A) hA
      (by rw [hrowA]) hcardW).run (σ := σ₃)
      ⟨hn₃, by
          rw [hvv₃ _ (by simp [ctrName, String.ext_iff]), hvv₂ _ hctrs]
          simpa only [hvc] using hctr₁,
        by rw [hvv₃ "bq" (by decide)]; exact hbq₂,
        by rw [hav₃ _ (by simp [memName, resName, String.ext_iff])]; exact hmemA₂,
        by
          rw [hav₃ "off" (by simp [resName, String.ext_iff]),
            hav₂ "off" (by simp [cluName, String.ext_iff])
              (by simp [memName, String.ext_iff]), harrs₁]
          exact hoff,
        by
          rw [hav₃ "tgt" (by simp [resName, String.ext_iff]),
            hav₂ "tgt" (by simp [cluName, String.ext_iff])
              (by simp [memName, String.ext_iff]), harrs₁]
          exact htgt,
        hres₃,
        exists_arrOf_run (hr₁.seq (hr₂.seq hr₃)) hpds₀,
        exists_arrOf_run (hr₁.seq (hr₂.seq hr₃)) hqS₀,
        exists_arrOf_run (hr₁.seq (hr₂.seq hr₃)) hqdS₀,
        exists_arrOf_run (hr₁.seq (hr₂.seq hr₃)) hparj₀⟩
  have hav₄ : ∀ b : String, b ≠ balAltName j → b ≠ balName j → b ≠ "q" → b ≠ "qd" →
      σ₄.arrs b = σ₃.arrs b := fun b h₁ h₂ h₃ h₄ =>
    hr₄.frame_arr b (fun hc => by
      rcases mem_warrs_cacheRoundCom hc with h | h | h | h
      · exact h₁ h
      · exact h₂ h
      · exact h₃ h
      · exact h₄ h)
  have hvv₄ : ∀ y : String, y ≠ mnumName (j + 1) → y ∉ descendScalars →
      σ₄.vars y = σ₃.vars y := fun y h₁ h₂ =>
    hr₄.frame_var y (fun hc => by
      rcases mem_wvars_cacheRoundCom hc with h | h
      · exact h₁ h
      · exact h₂ h)
  have hcached₄ : CachedRounds cap G j M σ₄ :=
    cachedRounds_cacheRound_run hcached₃ hr₄
  -- P5: mark the earlier cached parent chains and cut them to the cluster.
  have henv₄ : BatchEnv cap Ws j O T U Gam vc σ₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hvv₄ "n" (by simp [mnumName, String.ext_iff]) (by decide),
        hvv₃ "n" (by decide), hvv₂ "n" (by decide),
        hvars₁ "n" (by simp [ctrName, String.ext_iff])]
      exact hn
    · rw [hav₄ "off" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide),
        hav₃ "off" (by simp [resName, String.ext_iff]),
        hav₂ "off" (by simp [cluName, String.ext_iff]) (by simp [memName, String.ext_iff]),
        harrs₁]
      exact hoff
    · rw [hav₄ "tgt" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide),
        hav₃ "tgt" (by simp [resName, String.ext_iff]),
        hav₂ "tgt" (by simp [cluName, String.ext_iff]) (by simp [memName, String.ext_iff]),
        harrs₁]
      exact htgt
    · exact exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) halvS₀
    · exact exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) hdistS₀
    · exact exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) hqS₀
    · exact exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) hparS₀
    · exact exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) hpathS₀
    · rw [hvv₄ (ctrName j) (by simp [ctrName, mnumName, String.ext_iff]) hctrs,
        hvv₃ (ctrName j) (by simp [ctrName, String.ext_iff]),
        hvv₂ (ctrName j) hctrs]
      exact hctr₁
    · intro a ha
      rw [hvv₄ (ctrName a) (by simp [ctrName, mnumName, String.ext_iff])
          (ctrName_notMem_descendScalars a),
        hvv₃ (ctrName a) (by simp [ctrName, String.ext_iff]),
        hvv₂ (ctrName a) (ctrName_notMem_descendScalars a),
        hvars₁ (ctrName a) (ctrName_ne (by omega))]
      exact (hUG a ha).1
    · intro a ha
      rw [hav₄ _ (by simp [gamName, balAltName, String.ext_iff])
          (by simp [gamName, balName, String.ext_iff])
          (by simp [gamName, String.ext_iff]) (by simp [gamName, String.ext_iff]),
        hav₃ _ (by simp [gamName, resName, String.ext_iff]),
        hav₂ _ (by simp [gamName, cluName, String.ext_iff])
          (by simp [gamName, memName, String.ext_iff]), harrs₁]
      exact (hUG a ha).2.1
  have hMvc' : M (vc : ℕ) ≠ 0 := by simpa only [hvc] using hMvc
  obtain ⟨σ₅, hr₅, henv₅, -, hclu₅, Wa, hbat₅, hWaB, hWsub, hvW, hWcard, hWwalk⟩ :=
    (batchCachedCom_spec (nt := Ws) (G := G) hB (U := U) (Gam := Gam) (M := M)
      (v := vc) hMvc' (fun k hk => by have := hXbit k hk; omega) hvX).run
      (σ := σ₄)
      ⟨henv₄, hcached₄, by
        rw [hav₄ _ (by simp [batName, balAltName, String.ext_iff])
            (by simp [batName, balName, String.ext_iff])
            (by simp [batName, String.ext_iff]) (by simp [batName, String.ext_iff]),
          hav₃ _ (by simp [batName, resName, String.ext_iff]),
          hav₂ _ (by simp [batName, cluName, String.ext_iff])
          (by simp [batName, memName, String.ext_iff]), harrs₁]
        exact hbat₀, by
          rw [hav₄ _ (by simp [cluName, balAltName, String.ext_iff])
            (by simp [cluName, balName, String.ext_iff])
            (by simp [cluName, String.ext_iff]) (by simp [cluName, String.ext_iff])]
          exact hclu₃⟩
  have hav₅ : ∀ b : String, b ≠ batName j → σ₅.arrs b = σ₄.arrs b :=
    fun b hb => hr₅.frame_arr b (fun hc => hb (mem_warrs_batchCachedCom hc))
  have hres₅ : σ₅.arrs (resName j) = arrOf n Ra := by
    rw [hav₅ _ (by simp [resName, batName, String.ext_iff]),
      hav₄ _ (by simp [resName, balAltName, String.ext_iff])
        (by simp [resName, balName, String.ext_iff])
        (by simp [resName, String.ext_iff]) (by simp [resName, String.ext_iff])]
    exact hres₃
  have hgam₅ : σ₅.arrs (gamName j) = arrOf n Gm := by
    rw [hav₅ _ (by simp [gamName, batName, String.ext_iff]),
      hav₄ _ (by simp [gamName, balAltName, String.ext_iff])
        (by simp [gamName, balName, String.ext_iff])
        (by simp [gamName, String.ext_iff]) (by simp [gamName, String.ext_iff]),
      hav₃ _ (by simp [gamName, resName, String.ext_iff]),
      hav₂ _ (by simp [gamName, cluName, String.ext_iff])
        (by simp [gamName, memName, String.ext_iff]), harrs₁]
    exact hgamj
  have hgam1₅ : ∃ g, σ₅.arrs (gamName (j + 1)) = arrOf n g :=
    exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))) hgam1₀
  have halv1₅ : ∃ g, σ₅.arrs (alvName (j + 1)) = arrOf n g :=
    exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))) halv1₀
  -- P6: the work mask of the next depth
  obtain ⟨σ₆, hr₆, ⟨⟨Alv', halv₆, hAlvval⟩, -, hn₆, hres₆, hbat₆⟩, hfv₆, hfa₆, -, -⟩ :=
    ((subCom_spec B n (resName j) (batName j) (alvName (j + 1)) Ra Wa
      (by simp [resName, alvName, String.ext_iff]) (by simp [batName, alvName, String.ext_iff])
      hnB hRaB hWaB h1B (fun k hk => by
        have h1 := hRaB k hk
        calc Ra k * (1 - Wa k) ≤ Ra k * 1 := Nat.mul_le_mul_left _ (by omega)
          _ = Ra k := by ring
          _ < B := h1)).frame).run (σ := σ₅) ⟨halv1₅, henv₅.1, hres₅, hbat₅⟩
  have hav₆ : ∀ b : String, b ≠ alvName (j + 1) → σ₆.arrs b = σ₅.arrs b :=
    fun b hb => hfa₆ b (by rw [RamDriverFrames.warrs_subCom]; simp [hb])
  -- P7: the game mask of the next depth, retained only on this cover cluster
  obtain ⟨σ₇, hr₇, ⟨⟨Gt, hgt₇, hGtval⟩, -, hn₇, hgam₇, -⟩, hfv₇, hfa₇, -, -⟩ :=
    ((andCom_spec B n (gamName j) (cluName j) (gamName (j + 1)) Gm Xa
      (fun hc => gamName_ne_succ (le_refl j) hc) (by simp [cluName, gamName, String.ext_iff])
      hnB hGmB (fun k hk => by have := hXbit k hk; omega) (fun k hk => by
        have h1 := hGmB k hk
        calc Gm k * Xa k ≤ Gm k * 1 := Nat.mul_le_mul_left _ (hXbit k hk)
          _ = Gm k := by ring
          _ < B := h1)).frame).run (σ := σ₆)
      ⟨by rw [hav₆ _ (by simp [gamName, alvName, String.ext_iff])]; exact hgam1₅, hn₆,
        by rw [hav₆ _ (by simp [gamName, alvName, String.ext_iff])]; exact hgam₅,
        by
          rw [hav₆ _ (by simp [cluName, alvName, String.ext_iff])]
          exact hclu₅⟩
  have hav₇ : ∀ b : String, b ≠ gamName (j + 1) → σ₇.arrs b = σ₆.arrs b :=
    fun b hb => hfa₇ b (by rw [RamDriverFrames.warrs_andCom]; simp [hb])
  -- P8: and by the batch, in place
  obtain ⟨σ₈, hr₈, ⟨⟨Gam', hgam₈, hGamval⟩, -, hn₈, hbat₈⟩, hfv₈, hfa₈, -, -⟩ :=
    ((subSelfCom_spec (B := B) n (batName j) (gamName (j + 1)) Gt Wa
      (by simp [batName, gamName, String.ext_iff]) hnB h1B
      (fun k hk => by
        rw [hGtval k hk]
        have h1 := hGmB k hk
        calc Gm k * Xa k ≤ Gm k * 1 := Nat.mul_le_mul_left _ (hXbit k hk)
          _ = Gm k := by ring
          _ < B := h1)
      hWaB).frame).run (σ := σ₇)
      ⟨hgt₇, hn₇, by rw [hav₇ _ (by simp [batName, gamName, String.ext_iff]),
        hav₆ _ (by simp [batName, alvName, String.ext_iff])]; exact hbat₅⟩
  have hav₈ : ∀ b : String, b ≠ gamName (j + 1) → σ₈.arrs b = σ₇.arrs b :=
    fun b hb => hfa₈ b (by rw [RamDriverFrames.warrs_subCom]; simp [hb])
  have halv₈ : σ₈.arrs (alvName (j + 1)) = arrOf n Alv' := by
    rw [hav₈ _ (by simp [alvName, gamName, String.ext_iff]),
      hav₇ _ (by simp [alvName, gamName, String.ext_iff])]
    exact halv₆
  -- P9: the child's member list (rebase E-mem) — the block row `clusterLoad`
  -- emitted, filtered by the child mask `subCom` has just written
  have hmem₈ : σ₈.arrs (memName (j + 1)) = arrOf n Mm := by
    rw [hav₈ _ (by simp [memName, gamName, String.ext_iff]),
      hav₇ _ (by simp [memName, gamName, String.ext_iff]),
      hav₆ _ (by simp [memName, alvName, String.ext_iff]),
      hav₅ _ (by simp [memName, batName, String.ext_iff]),
      hav₄ _ (by simp [memName, balAltName, String.ext_iff])
        (by simp [memName, balName, String.ext_iff])
        (by simp [memName, String.ext_iff]) (by simp [memName, String.ext_iff]),
      hav₃ _ (by simp [memName, resName, String.ext_iff])]
    exact hmemA₂
  have hbq₈ : σ₈.vars "bq" = bs := by
    rw [hfv₈ _ (by rw [wvars_subCom]; simp), hfv₇ _ (by rw [wvars_andCom]; simp),
      hfv₆ _ (by rw [wvars_subCom]; simp),
      hr₅.frame_var "bq" (bq_notMem_wvars_batchCachedCom cap j),
      hr₄.frame_var "bq" (bq_notMem_wvars_cacheRoundCom cap j), hvv₃ _ (by decide)]
    exact hbq₂
  -- the child is inside the block: its mask is the cluster indicator with two
  -- more masks multiplied in, so the raw row lists every one of its members
  have hAlvB : ∀ k, k < n → Alv' k < B := by
    intro k hk
    rw [hAlvval k hk]
    have h1 := hRaB k hk
    calc Ra k * (1 - Wa k) ≤ Ra k * 1 := Nat.mul_le_mul_left _ (by omega)
      _ = Ra k := by ring
      _ < B := h1
  have hbsn : bs ≤ n := hMmE.card_le
  have hAlvXa : ∀ a, a < n → Alv' a ≠ 0 → Xa a ≠ 0 := by
    intro a ha hAa hXa
    exact hAa (by rw [hAlvval a ha, hRaval a ha, hXa]; ring)
  obtain ⟨σ₉, hr₉, ⟨Mem', mm', hmemA₉, hmnum₉, hMemE, hMemB⟩, hfv₉, hfa₉, -, -⟩ :=
    ((memFilter_spec (j := j + 1) (bs := bs) (Mm := Mm) (A := Alv') hnB
      hMmE.card_le hMmE.1 hMmE.2.1 hAlvB
      (fun a ha hAa => hMmE.2.2.2 a ha (hAlvXa a ha hAa))).frame).run (σ := σ₈)
      ⟨hmem₈, hbq₈, halv₈⟩
  have hav₉ : ∀ b : String, b ≠ memName (j + 1) → σ₉.arrs b = σ₈.arrs b :=
    fun b hb => hfa₉ b (by rw [RamDriverFrames.warrs_memFilterCom]; simp [hb])
  have hvv₉ : ∀ y : String, y ≠ "mk" → y ≠ mnumName (j + 1) → y ≠ "mv" →
      σ₉.vars y = σ₈.vars y :=
    fun y h1 h2 h3 => hfv₉ y (by
      rw [RamDriverFrames.wvars_memFilterCom]; simp [h1, h2, h3])
  -- the composite run and its frame
  have hrun : Run B (descendCom cap j) σ σ₉ _ :=
    hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq (hr₇.seq (hr₈.seq hr₉)))))))
  have hfa : ∀ b : String, b ∉ descendArrs j → σ₉.arrs b = σ.arrs b :=
    fun b hb => hrun.frame_arr b (notMem_warrs_descendCom hb)
  have hfv : ∀ y : String, y ≠ ctrName j → y ≠ mnumName (j + 1) → y ∉ descendScalars →
      σ₉.vars y = σ.vars y :=
    fun y h1 hmm h2 => hrun.frame_var y (fun hc =>
      (mem_wvars_descendCom hc).elim h1 (fun hc' => hc'.elim hmm h2))
  have hfu : ∀ b : String, '_' ∈ b.toList → σ₉.arrs b = σ.arrs b :=
    fun b hb => hrun.frame_arr b (fun hc =>
      RamDriverFrames.underscore_notMem_warrs_descendCom cap j b hc hb)
  -- the six arrays the descent leaves, chased to the exit
  have hclu₉ : σ₉.arrs (cluName j) = arrOf n Xa := by
    rw [hav₉ _ (by simp [cluName, memName, String.ext_iff]),
      hav₈ _ (by simp [cluName, gamName, String.ext_iff]),
      hav₇ _ (by simp [cluName, gamName, String.ext_iff]),
      hav₆ _ (by simp [cluName, alvName, String.ext_iff])]
    exact hclu₅
  have hres₉ : σ₉.arrs (resName j) = arrOf n Ra := by
    rw [hav₉ _ (by simp [resName, memName, String.ext_iff]),
      hav₈ _ (by simp [resName, gamName, String.ext_iff]),
      hav₇ _ (by simp [resName, gamName, String.ext_iff])]
    exact hres₆
  have hpar₉ : σ₉.arrs (parName j) = arrOf n Pp := by
    rw [hav₉ _ (by simp [parName, balName, memName, String.ext_iff]),
      hav₈ _ (by simp [parName, balName, gamName, String.ext_iff]),
      hav₇ _ (by simp [parName, balName, gamName, String.ext_iff]),
      hav₆ _ (by simp [parName, balName, alvName, String.ext_iff]),
      hav₅ _ (by simp [parName, balName, batName, String.ext_iff])]
    exact hpar₄
  have halv₉ : σ₉.arrs (alvName (j + 1)) = arrOf n Alv' := by
    rw [hav₉ _ (by simp [alvName, memName, String.ext_iff])]
    exact halv₈
  have hgam₉ : σ₉.arrs (gamName (j + 1)) = arrOf n Gam' := by
    rw [hav₉ _ (by simp [gamName, memName, String.ext_iff])]
    exact hgam₈
  have hbat₉ : σ₉.arrs (batName j) = arrOf n Wa := by
    rw [hav₉ _ (by simp [batName, memName, String.ext_iff])]
    exact hbat₈
  have hctr₉ : σ₉.vars (ctrName j) = (vc : ℕ) := by
    rw [hvv₉ _ (by simp [ctrName, String.ext_iff]) (by simp [ctrName, mnumName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]),
      hfv₈ _ (by rw [wvars_subCom]; simp [ctrName, String.ext_iff]),
      hfv₇ _ (by rw [wvars_andCom]; simp [ctrName, String.ext_iff]),
      hfv₆ _ (by rw [wvars_subCom]; simp [ctrName, String.ext_iff])]
    exact henv₅.2.2.2.2.2.2.2.2.1
  -- the sets the descent produced
  have hXiff : ∀ z : Fin n, z ∈ markSet n Xa ↔ Xa (z : ℕ) ≠ 0 := fun _ => Iff.rfl
  have hWiff : ∀ z : Fin n, z ∈ markSet n Wa ↔ Wa (z : ℕ) ≠ 0 := fun _ => Iff.rfl
  have hResEq : masked G Ra =
      Lax12.UniformQuasiWideness.deleteVerts (masked G M) (markSet n Xa)ᶜ := by
    rw [masked_congr hRaval]
    exact masked_mul M Xa hXiff
  have hAlvEq : masked G Alv' =
      Lax12.UniformQuasiWideness.deleteVerts
        (Lax12.UniformQuasiWideness.deleteVerts (masked G M) (markSet n Xa)ᶜ)
        (markSet n Wa) := by
    rw [masked_congr (M := Alv') (M' := fun a => M a * Xa a * (1 - Wa a))
      (fun k hk => by rw [hAlvval k hk, hRaval k hk])]
    exact masked_step M Xa Wa hXiff hWiff
  -- **the pointwise mask clause** (wave R1.8-T1, design §2.4): the same cell
  -- arithmetic the graph equation above is derived from, kept as the equivalence
  -- it is. It is a statement about the array the walk *stored* — `hAlvval` is
  -- `subCom_spec`'s reading of `alvName (j + 1)`, `hRaval` is `andCom_spec`'s of
  -- `resName j` — so no recomputation is involved.
  have hAlvPt : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 ↔
      (M (v : ℕ) ≠ 0 ∧ v ∈ markSet n Xa ∧ v ∉ markSet n Wa) := by
    intro v
    rw [hAlvval (v : ℕ) v.isLt, hRaval (v : ℕ) v.isLt, mask_cell_ne_zero M Xa Wa (v : ℕ)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun hc => hc h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by by_contra hc; exact h3 hc⟩
  have hGamEq : masked G Gam' =
      Lax12.UniformQuasiWideness.deleteVerts
        (Lax12.UniformQuasiWideness.deleteVerts (masked G Gm) (markSet n Xa)ᶜ)
        (markSet n Wa) := by
    rw [masked_congr (M := Gam') (M' := fun a => Gm a * Xa a * (1 - Wa a))
      (fun k hk => by rw [hGamval k hk, hGtval k hk])]
    exact masked_step Gm Xa Wa hXiff hWiff
  -- **the connector is in its own cluster** (wave R1.8-T3-flip (c2a)); `hvX`
  -- was established before the batch because it is now also the retained-set
  -- premise of that executable pass.
  have hXball : markSet n Xa ⊆ ball (masked G M) (2 * cap) vc := by
    rw [hXmark]
    have h := RamCover.inCluster_subset_ball (masked G M) π (r := cap) hordc
    rwa [show (⟨ord cc, hordc⟩ : Fin n) = vc from Fin.ext hvc.symm] at h
  have hGamB' : ∀ k, k < n → Gam' k < B := by
    intro k hk
    rw [hGamval k hk, hGtval k hk]
    have h1 := hGmB k hk
    calc Gm k * Xa k * (1 - Wa k) ≤ Gm k * 1 * 1 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (hXbit k hk)) (by omega)
      _ = Gm k := by ring
      _ < B := h1
  -- the names the depth's own state is held at
  have hnalv : alvName j ∉ descendArrs j := by
    simp only [descendArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, alvName_ne_succ j, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [alvName, cluName, resName, balName, balAltName, batName, gamName, memName,
        String.ext_iff]
  have hnmem : memName j ∉ descendArrs j := by
    simp only [descendArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, memName_ne_succ j, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [memName, cluName, resName, balName, balAltName, batName, alvName, gamName,
        String.ext_iff]
  have hngam : ∀ a, a ≤ j → gamName a ∉ descendArrs j := by
    intro a ha
    simp only [descendArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, gamName_ne_succ ha, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [alvName, cluName, resName, balName, balAltName, batName, gamName, memName,
        String.ext_iff]
  have hnres : ∀ a, a < j → resName a ∉ descendArrs j := by
    intro a ha
    have hne : resName a ≠ resName j := fun hc => by
      have : a = j := prefixed_inj (p := "res") (by simpa only [resName] using hc)
      omega
    have hned : Nat.toDigits 10 a ≠ Nat.toDigits 10 j := fun hc => by
      have := decimalDigits_inj hc
      omega
    simp [descendArrs, hne, alvName, cluName, resName, balName, balAltName, batName,
      gamName, memName, String.ext_iff, hned]
  have hnpar : ∀ a, a < j → parName a ∉ descendArrs j := by
    intro a ha
    have hne : balName a ≠ balName j := fun hc => by
      have := prefixed_inj (p := "bal") hc
      omega
    have hned : Nat.toDigits 10 a ≠ Nat.toDigits 10 j := fun hc => by
      have := decimalDigits_inj hc
      omega
    simp [descendArrs, parName, hne, alvName, cluName, resName, balName, balAltName,
      batName, gamName, memName, String.ext_iff, hned]
  have hzero : ∀ b ∈ (["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"] : List String),
      σ₉.arrs b = σ.arrs b := by
    intro b hb
    refine hfa b ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [descendArrs, cluName, resName, balName, balAltName, batName, alvName, gamName,
        memName, String.ext_iff]
  have hturn₉ : TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ₉ := by
    refine ⟨levelPre_congr ⟨hn, hoff, htgt, halvj, hgamj, hcolj, hMB, hGmB, hCbit, hmem, hdep,
        hmvar, hom⟩ hrun (hfv "n" (by simp [ctrName, String.ext_iff]) (by simp [mnumName, String.ext_iff]) (by decide))
        (hfv "m" (by simp [ctrName, String.ext_iff]) (by simp [mnumName, String.ext_iff]) (by decide))
        (hfv "lw" (by simp [ctrName, String.ext_iff]) (by simp [mnumName, String.ext_iff]) (by decide))
        (hfa "off" (by simp [descendArrs, cluName, resName, balName, balAltName, batName,
          alvName, gamName, memName, String.ext_iff]))
        (hfa "tgt" (by simp [descendArrs, cluName, resName, balName, balAltName, batName,
          alvName, gamName, memName, String.ext_iff]))
        (hfa _ hnalv) (hfa _ (hngam j (le_refl j)))
        (fun c' _ => hfu _ (RamDriverFrames.underscore_mem_colName j c')) hzero
        (hfa _ hnmem)
        (hfv _ (by simp [mnumName, ctrName, String.ext_iff]) (mnumName_ne_succ j)
          (RamDriverIO.notMem_of_append (p := "mm") (s := toString j) (by decide))),
      hplay₀.congr
        (fun a ha => hfv (ctrName a) (ctrName_ne (by omega))
          (by simp [ctrName, mnumName, String.ext_iff]) (ctrName_notMem_descendScalars a))
        (fun a ha => hfa (resName a) (hnres a ha))
        (fun a ha => hfa (gamName a) (hngam a (by omega)))
        (fun a ha => hfa (parName a) (hnpar a ha)),
      coverHeld_congr ⟨hordA, hxof, hxmm, hasgA, hxp, hmn, hmB, hordlt, hcout⟩
        (hfa _ (by simp [descendArrs, ordName, cluName, resName, balName, balAltName, batName,
          alvName, gamName, memName, String.ext_iff]))
        (hfa _ (by simp [descendArrs, xofName, cluName, resName, balName, balAltName, batName,
          alvName, gamName, memName, String.ext_iff]))
        (hfa _ (by simp [descendArrs, xmmName, cluName, resName, balName, balAltName, batName,
          alvName, gamName, memName, String.ext_iff]))
        (hfa _ (by simp [descendArrs, asgName, cluName, resName, balName, balAltName, batName,
          alvName, gamName, memName, String.ext_iff]))
        (hfv (xpName j) (by simp [xpName, ctrName, String.ext_iff])
          (by simp [xpName, mnumName, String.ext_iff]) (xpName_notMem_descendScalars j))⟩
  -- everything the obligation asks for
  refine ⟨σ₉, _, hrun, ?_, hturn₉, hrun.out_eq (noWrite_descendCom cap j),
    by rw [hfv (curName j) hcurne (by simp [curName, mnumName, String.ext_iff])
      (curName_notMem_descendScalars j)], ?_, markSet n Xa, markSet n Wa, Alv', Gam', ?_,
      ⟨vc, hvW, hvX⟩, ?_, ?_, ?_, ⟨⟨Xa, hclu₉, rfl, hXbit⟩, ⟨Wa, hbat₉, rfl, hWaB⟩, ⟨Ra, hres₉, hResEq, hRaB⟩,
        halv₉, hAlvB, hAlvEq, hAlvPt, hgam₉, hGamB', Mem', mm', hmemA₉, hmnum₉, hMemE, hMemB⟩, ?_⟩
  · have hbsw : blockSize Xoff cc ≤
        Refine.MassWeight.blockWeight n G Xoff Xmem k := by
      rw [← hcck]
      exact Refine.MassWeight.blockSize_le_blockWeight G Xoff Xmem
        (fun p hp hp' => Refine.MassWeight.mem_lt_of_coverOut hcout hcur hp hp')
    simp only [descendCostSize, batchCachedCost, cacheRoundCost,
      Refine.ScatterDeadPass.memFillAtCost, Refine.BfsBlockPar.bfsBlockParK] at hK ⊢
    rw [hbsEq] at *
    omega
  · exact exists_arrOf_run hrun (hmem.1.get (p := ("wa", mb)) (by simp))
  · intro v' hv'
    rw [hXmark]
    have hcov := hcout.asg_cover (v' : ℕ) v'.isLt
    rw [hv', hcc] at hcov
    exact hcov
  · refine le_trans hWcard ?_
    rw [hmb]
    calc
      1 + j * (2 * cap + 1) ≤ (j + 1) * (2 * cap + 1) := by
        rw [Nat.add_mul, one_mul]
        omega
      _ ≤ ℓ * (2 * cap + 1) := Nat.mul_le_mul_right _ (by omega)
  · -- **the descend clause** (§5.3, restated at the inclusion for G2/E6): every
    -- vertex the next depth's arena marks lies in this turn's cluster — its mask is
    -- the cluster indicator with two more masks multiplied in. The old cardinality
    -- reading is `Refine.ArenaBlock.arenaSize_le_ncard` +
    -- `ncard_clusterAt_le_blockSize` downstream; the weighted reading is
    -- `Refine.MassWeight.arenaWeight_le_blockWeight`.
    rw [hcc]
    have hsub : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ markSet n Xa := by
      intro v hv hc
      refine hv ?_
      rw [hAlvval (v : ℕ) v.isLt, hRaval (v : ℕ) v.isLt, hc]
      ring
    intro v hv
    have hvXa := hsub v hv
    rw [hXmark] at hvXa
    exact hvXa
  · -- **the cluster clause** (wave R1.8-T3-flip (c1c)): the cluster indicator IS
    -- the turn's cluster, which is what `clusterLoad` materialized — so the
    -- inclusion is `hXmark` read forwards. The consumer is
    -- `RamDriverCluster.clusterStepImplements`'s `hXalive`: at an alive centre a
    -- cluster is alive-homogeneous (`Refine.MassAlive.clusterAt_subset_alive`),
    -- and at a dead one the identity genuinely fails
    -- (`Refine.MassAlive.clusterAt_dead`), which is why the alive antecedent
    -- rides on `RamDriver.ClusterStepImplements` and not here.
    rw [hcc]
    intro v hv
    rw [hXmark] at hv
    exact hv
  · have hXgameBall : markSet n Xa ⊆ ball (masked G Gm) (2 * cap) vc := by
      intro z hz
      exact ball_mono_graph vc hle (hXball hz)
    have hRM : masked G Ra ≤ masked G M := by
      intro x y hxy
      rw [RamBfs.masked_adj] at hxy ⊢
      exact ⟨hxy.1, hRaM _ x.isLt hxy.2.1, hRaM _ y.isLt hxy.2.2⟩
    have hRGm : masked G Ra ≤ masked G Gm := le_trans hRM hle
    have hAlvM : ∀ z, z < n → Alv' z ≠ 0 → M z ≠ 0 := by
      intro z hz hAz
      exact (hAlvPt ⟨z, hz⟩).mp hAz |>.1
    have hAlvR : ∀ z, z < n → Alv' z ≠ 0 → Ra z ≠ 0 := by
      intro z hz hAz hRz
      rw [hAlvval z hz, hRz, Nat.zero_mul] at hAz
      exact hAz rfl
    refine playRec_succ (X := markSet n Xa)
      hplay₀
      (fun a ha => hfv (ctrName a) (ctrName_ne (by omega))
        (by simp [ctrName, mnumName, String.ext_iff]) (ctrName_notMem_descendScalars a))
      (fun a ha => hfa (resName a) (hnres a ha))
      (fun a ha => hfa (gamName a) (hngam a (by omega)))
      (fun a ha => hfa (parName a) (hnpar a ha)) hAlvM hctr₉
      (by rw [hfa _ (hngam j (le_refl j))]; exact hgamj) hGmB
      hres₉ hpar₉ (by simpa only [hvc] using htree₄)
      (by simpa only [hvc] using hRcov) hRGm hAlvR
      hXgameBall hvW ?_ (by rw [hGamEq])
      (by
        rw [hAlvEq, hGamEq]
        exact Evaluator.deleteVerts_mono_graph (Evaluator.deleteVerts_mono_graph hle))
    intro u A hround hwd
    obtain ⟨a, haj, hua, Ga', hGa', hGa'B, hAeq⟩ := hround
    have hUa : u = U a := Fin.ext (by rw [← hua, (hUG a haj).1])
    have hGeq : masked G Ga' = masked G (Gam a) :=
      masked_congr (fun k hk => eq_of_arrOf_eq (hGa'.symm.trans (hUG a haj).2.1) hk)
    subst hAeq
    subst hUa
    rw [hGeq] at hwd ⊢
    obtain ⟨p, hp, hps⟩ := hWwalk a haj hwd
    exact ⟨p, hp, hps⟩

end Descend

end Lax3Proofs.RamDriverDescend
