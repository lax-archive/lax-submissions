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
    (j : ℕ) : lv s j ≠ t := by
  intro h
  refine hne (lv_inj hlen (j := j) (k := 0) ?_).1
  rw [lv_zero]
  exact h

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

/-- **The isolation's output family**: the level's own regions with the
slot count in the pass's own cell. `isolateCom_specW` forbids
`nsO = nmI.nS`, so this cell cannot be the level's; `arenaStW_setVar_nS`
(§3) is the one scalar move that closes the gap. -/
def prepOut (j : ℕ) : ArenaNames := { arenaNames (j + 1) with nS := pcNo }

/-- **The isolation's output family is the deliverable's**, up to that
one cell: routing the restrict stage into `pcOi`/`pcTi` and the isolate
stage into the level's own CSR pair leaves exactly the slot-count cell
to move. -/
theorem isolate_out_names (j : ℕ) :
    ({ prepMid j with off := (arenaNames (j + 1)).off, tgt := (arenaNames (j + 1)).tgt, nS := pcNo } : ArenaNames) = prepOut j := rfl

@[simp] theorem prepOut_nN (j : ℕ) : (prepOut j).nN = (arenaNames (j + 1)).nN :=
  rfl
@[simp] theorem prepOut_nS (j : ℕ) : (prepOut j).nS = pcNo := rfl
@[simp] theorem prepOut_off (j : ℕ) :
    (prepOut j).off = (arenaNames (j + 1)).off := rfl
@[simp] theorem prepOut_tgt (j : ℕ) :
    (prepOut j).tgt = (arenaNames (j + 1)).tgt := rfl
@[simp] theorem prepOut_col (j : ℕ) :
    (prepOut j).col = (arenaNames (j + 1)).col := rfl
@[simp] theorem prepOut_up (j : ℕ) :
    (prepOut j).up = (arenaNames (j + 1)).up := rfl
@[simp] theorem prepOut_hist (j : ℕ) :
    (prepOut j).hist = (arenaNames (j + 1)).hist := rfl

end Names

/-! ## §2 The seams the composition needs -/

section Seams

/-- **The slot-count cell, moved.** `isolateCom_specW` leaves its output
arena at `{nmI with off := oaO, tgt := taO, nS := nsO}` and *forbids*
`nsO = nmI.nS`, so the deliverable's cell can never be the one the stage
writes. This is the one scalar move that closes it: `setVar` touches no
array, so the whole windowed contract transports on the cell alone.

Unstated by anything landed; without it the isolate stage cannot hand
over to `ArenaStW (arenaNames (j+1)) …` at all. -/
theorem arenaStW_setVar_nS {Λ n₀ ℓp hb : ℕ} {nm : ArenaNames}
    {A : Impl.MArena Λ n₀ ℓp} {nsO : String} {σ : Env}
    (hnn : nm.nN ≠ nm.nS)
    (h : ArenaStW ({ nm with nS := nsO } : ArenaNames) hb A σ) :
    ArenaStW nm hb A (σ.setVar nm.nS (σ.vars nsO)) := by
  set τ : Env := σ.setVar nm.nS (σ.vars nsO) with hτ
  have hns : τ.vars nm.nS = σ.vars nsO := by
    rw [hτ, vars_setVar, if_pos rfl]
  have hnN : τ.vars nm.nN = σ.vars nm.nN := by
    rw [hτ, vars_setVar, if_neg hnn]
  have harr : ∀ b, τ.arrs b = σ.arrs b := fun b => by rw [hτ, arrs_setVar]
  -- the two contracts read the *same* window family: the name record
  -- differs only in `nS`, which `arenaWs` never inspects
  have hfit : FitsW (arenaWs nm Λ ℓp hb A.N (σ.vars nsO)) σ := h.fits
  have hst : ArenaSt ({ nm with nS := nsO } : ArenaNames) hb A
      (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nsO)) σ) := h.st
  have harrw : ∀ b, (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nsO)) τ).arrs b
      = (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nsO)) σ).arrs b :=
    fun b => arrs_winA_eq_of_arrs_eq (harr b)
  have hvv : (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nsO)) τ).vars nm.nS
      = σ.vars nsO := by
    simp only [vars_winA]
    exact hns
  constructor
  · show FitsW (arenaWs nm Λ ℓp hb A.N (τ.vars nm.nS)) τ
    rw [hns]
    intro b m hbm
    rw [harr b]
    exact hfit b m hbm
  · show ArenaSt nm hb A (winA (arenaWs nm Λ ℓp hb A.N (τ.vars nm.nS)) τ)
    rw [hns]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show τ.vars nm.nN = A.N
      rw [hnN]
      exact hst.n_eq
    · rw [hvv]
      exact graphCsr_of_eq (ns := σ.vars nsO) hst.csr (harrw _) (harrw _)
    · exact ⟨by rw [harrw]; exact hst.col.1,
        fun v c => by rw [harrw]; exact hst.col.2 v c⟩
    · exact ⟨by rw [harrw]; exact hst.up.1,
        fun v => by rw [harrw]; exact hst.up.2 v⟩
    · exact histArr_congr_arrs hst.hist (harrw _)

open Classical in
/-- **The palette move, at the two states the pass actually has.**
`arenaStW_recol` (`SolveMachPrepAll` §3) reads the four unchanged
regions *and* the new colour cells at one state; but the colour writer
**destroys** the old `ColBits`, so `ArenaStW nm hb A σ'` is false at the
state where the new cells hold, and the landed lemma cannot be applied
where the composition needs it. This is the two-state form: the four
regions and the two cells read at the pre-write state, the colour cells
at the post-write state.

(`arenaStW_recol` is recovered by taking `σ' := σ`.) -/
theorem arenaStW_recol_frame {Λ Λ' n₀ ℓp hb : ℕ} {nm : ArenaNames}
    {A : Impl.MArena Λ n₀ ℓp} {col' : Coloring A.N Λ'} {σ σ' : Env}
    (h : ArenaStW nm hb A σ)
    (hnd5 : ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String).Nodup)
    (hnN : σ'.vars nm.nN = σ.vars nm.nN) (hnS : σ'.vars nm.nS = σ.vars nm.nS)
    (hoff : σ'.arrs nm.off = σ.arrs nm.off)
    (htgt : σ'.arrs nm.tgt = σ.arrs nm.tgt)
    (hup : σ'.arrs nm.up = σ.arrs nm.up)
    (hhist : σ'.arrs nm.hist = σ.arrs nm.hist)
    (hlen : A.N * Λ' ≤ (σ'.arrs nm.col).length)
    (hcells : ∀ (v : Fin A.N) (c : Fin Λ'),
      (σ'.arrs nm.col).getD ((v : ℕ) * Λ' + (c : ℕ)) 0
        = if v ∈ col' c then 1 else 0) :
    ArenaStW nm hb (recol (Λ' := Λ') A col') σ' := by
  have hnd5C := hnd5
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd5C
  obtain ⟨⟨hot', hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd5C
  -- the four windows that do not move
  have hwoff : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.off
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.off := by
    rw [arenaWs_off, arenaWs_off]
  have hwtgt : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.tgt
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.tgt := by
    rw [arenaWs_tgt (Ne.symm hot'), arenaWs_tgt (Ne.symm hot')]
  have hwup : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.up
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.up := by
    rw [arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu),
      arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu)]
  have hwhist : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.hist
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.hist := by
    rw [arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh),
      arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh)]
  have hwcol : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.col
      = some (A.N * Λ') := arenaWs_col (Ne.symm hoc) (Ne.symm htc)
  -- the four arrays, read through the new window family at `σ'`
  have hAoff : (winA (arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS)) σ').arrs nm.off
      = (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ).arrs nm.off := by
    rw [arrs_winA_congr hwoff σ', arrs_winA_eq_of_arrs_eq hoff]
  have hAtgt : (winA (arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS)) σ').arrs nm.tgt
      = (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ).arrs nm.tgt := by
    rw [arrs_winA_congr hwtgt σ', arrs_winA_eq_of_arrs_eq htgt]
  have hAup : (winA (arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS)) σ').arrs nm.up
      = (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ).arrs nm.up := by
    rw [arrs_winA_congr hwup σ', arrs_winA_eq_of_arrs_eq hup]
  have hAhist : (winA (arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS)) σ').arrs nm.hist
      = (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ).arrs nm.hist := by
    rw [arrs_winA_congr hwhist σ', arrs_winA_eq_of_arrs_eq hhist]
  constructor
  · show FitsW (arenaWs nm Λ' ℓp hb A.N (σ'.vars nm.nS)) σ'
    rw [hnS]
    intro b m hbm
    rcases arenaWs_some_elim hbm with rfl | rfl | rfl | rfl | rfl
    · rw [hoff]; exact h.fits _ m (by rw [← hwoff]; exact hbm)
    · rw [htgt]; exact h.fits _ m (by rw [← hwtgt]; exact hbm)
    · rw [hwcol] at hbm; cases hbm; exact hlen
    · rw [hup]; exact h.fits _ m (by rw [← hwup]; exact hbm)
    · rw [hhist]; exact h.fits _ m (by rw [← hwhist]; exact hbm)
  · show ArenaSt nm hb (recol (Λ' := Λ') A col')
      (winA (arenaWs nm Λ' ℓp hb A.N (σ'.vars nm.nS)) σ')
    have hvv : (winA (arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS)) σ').vars nm.nS
        = σ.vars nm.nS := by
      simp only [vars_winA]
      exact hnS
    rw [hnS]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show σ'.vars nm.nN = A.N
      rw [hnN]
      exact h.st.n_eq
    · rw [hvv]
      exact graphCsr_of_eq (ns := σ.vars nm.nS) h.st.csr hAoff hAtgt
    · refine ⟨length_arrs_winA hwcol hlen, fun v c => ?_⟩
      have hidx : (v : ℕ) * Λ' + (c : ℕ) < A.N * Λ' := by
        have h1 : (v : ℕ) + 1 ≤ A.N := v.2
        have h2 : (c : ℕ) + 1 ≤ Λ' := c.2
        calc (v : ℕ) * Λ' + (c : ℕ) < (v : ℕ) * Λ' + Λ' := by omega
          _ = ((v : ℕ) + 1) * Λ' := by ring
          _ ≤ A.N * Λ' := Nat.mul_le_mul_right _ h1
      rw [arrs_winA_some hwcol, getD_take_of_lt hidx]
      exact hcells v c
    · exact ⟨by rw [hAup]; exact h.st.up.1,
        fun v => by rw [hAup]; exact h.st.up.2 v⟩
    · exact histArr_congr_arrs h.st.hist hAhist

end Seams

section DriverSeams

variable {L n₀ : ℕ}

open Classical in
/-- **Seam (a): the restricted child's channel region, as the batch
builder reads it.** `restrictCom_specW` hands over the *whole* windowed
contract at the restricted child; `mkBatchCom_batch` asks only for the
channel region, in the `≤` form, at the family `childHistTab`. The two
meet definitionally — `childHistTab` *is* the restricted arena's `hist`
field — so this is `histArrW_of_arenaStW` at the driver's objects; the
carrier identification `(restrict …).N = childN` is `rfl`
(`Impl.restrict_N_eq_childN`). -/
theorem histArrW_childHistTab (S : Setup L) {Λ ℓpj hb : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (htab : Fin A.N → Fin ℓpj → List (Fin A.N))
    {nm : ArenaNames} {σ : Env}
    (h : ArenaStW nm hb ((Impl.ofArena A htab).restrict (cluster S A π u)) σ)
    (hho : nm.hist ≠ nm.off) (hht : nm.hist ≠ nm.tgt)
    (hhc : nm.hist ≠ nm.col) (hhu : nm.hist ≠ nm.up) :
    HistArrW nm.hist ℓpj hb (childHistTab S A π u htab) σ :=
  histArrW_of_arenaStW h hho hht hhc hhu

open Classical in
/-- **Seam (b): the profile tables, as the colour writer reads them.**
`profilesCom_specW` leaves its two families as *readings of the regions*
(`fun j v => (σ.arrs (pdF j)).getD v 0`); `colWriteCom_machChild` asks
for the same regions to hold exactly those values, at
`Dc c x.castSucc` on the padded index. Both directions are `rfl` — the
only content is the name freshness and the allocations, which the
level's scratch descriptor owns.

Stating it makes the `castSucc` reindexing explicit: the writer reads
the *first* `cN` entries of each `pu` region, the marker row's cell
`cN` never. -/
theorem colWrite_tables_of_profiles {cN mb Λr : ℕ} {ca : String}
    {pdF puF : ℕ → String} {σ : Env}
    (hpdne : ∀ j : Fin mb, pdF (j : ℕ) ≠ ca)
    (hpune : ∀ c : Fin Λr, puF (c : ℕ) ≠ ca)
    (hpdlen : ∀ j : Fin mb, cN ≤ (σ.arrs (pdF (j : ℕ))).length)
    (hpulen : ∀ c : Fin Λr, cN ≤ (σ.arrs (puF (c : ℕ))).length) :
    (∀ j : Fin mb, pdF (j : ℕ) ≠ ca ∧ cN ≤ (σ.arrs (pdF (j : ℕ))).length ∧
        ∀ x : Fin cN, (σ.arrs (pdF (j : ℕ))).getD (x : ℕ) 0
          = (fun (j : Fin mb) (v : Fin cN) =>
              (σ.arrs (pdF (j : ℕ))).getD (v : ℕ) 0) j x) ∧
      (∀ c : Fin Λr, puF (c : ℕ) ≠ ca ∧ cN ≤ (σ.arrs (puF (c : ℕ))).length ∧
        ∀ x : Fin cN, (σ.arrs (puF (c : ℕ))).getD (x : ℕ) 0
          = (fun (c : Fin Λr) (v : Fin (cN + 1)) =>
              (σ.arrs (puF (c : ℕ))).getD (v : ℕ) 0) c x.castSucc) :=
  ⟨fun j => ⟨hpdne j, hpdlen j, fun _ => rfl⟩,
   fun c => ⟨hpune c, hpulen c, fun _ => rfl⟩⟩

end DriverSeams

end Lax3Proofs.Prog
