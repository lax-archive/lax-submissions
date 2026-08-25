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
proposition about string literals, and §6 discharges the whole
discipline once.

Most of the pass's own arrays and scalars carry level tag `0`
(`"pc.·"`): the frame clause `ChildLoadPartsScr` demands is agreement
on `ca j :: co j :: cm j :: levelArrays j`, and a base outside
`{sa.·, sv.·, sl.·}` misses that pool at *every* level, so a shared
name is safe wherever the clause it carries is length-only.

The **rank scratch is the exception** and is tagged per level
(`pcRa j`). Its clause is not length-only: `restrictCom_specW` restores
the scratch on `take A.N` and says nothing about the tail, so a shared
scratch could not carry a clean window down the recursion at all — see
`pcRa`'s own docstring and `prepScr_down`. The three profile table
families are `lv`-indexed too, but by their *slot*, not by the level.

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
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
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
def pcLa : String := lv "pc.l" 0
/-- Array family: the rank scratch — the one array `restrictCom`
dirties and cleans, **one per level**.

Level-tagging it is not cosmetic. `restrictCom_specW` restores the
scratch only on `take A.N` and says nothing about the tail, so a
*shared* scratch cannot carry a clean-window clause down the recursion:
`centrePrep_of_childLoadScr`'s `hscrDown : ∀ σ, Scr j σ → Scr (j+1) σ`
would have to produce a clean window at the child's carrier out of a
clean window at the parent's, with the array in between dirtied and
only partly restored. With one scratch per level the deeper arrays are
outside the pass's write set entirely, so the deep half of the
descriptor rides `Run`'s frame and `hscrDown` costs one `take`
(`prepScr_down`). -/
def pcRa : ℕ → String := lv "pc.r"
/-- Array: the **pre-isolation** child CSR offsets. `restrictCom` builds
the child here, not in the level's own region, because `isolateCom`
needs a fresh output pair and the deliverable is stated at
`arenaNames (j+1)`. -/
def pcOi : String := lv "pc.o" 0
/-- Array: the pre-isolation child CSR targets. -/
def pcTi : String := lv "pc.t" 0
/-- Array: the batch bit vector — one region for the scan and the
isolation both (`range_batchFn_eq_batchSet`). -/
def pcBb : String := lv "pc.b" 0
/-- Array: the padded batch index region, at length exactly `S.width`. -/
def pcBi : String := lv "pc.i" 0
/-- Array: the BFS distance region. -/
def pcDa : String := lv "pc.d" 0
/-- Array: the supports pass's least-parent region. -/
def pcPa : String := lv "pc.p" 0
/-- Array: the profiles stage's per-class bit scratch. -/
def pcXb : String := lv "pc.x" 0
/-- Array: the profiles stage's `vsrc` offset scratch. -/
def pcVo : String := lv "pc.v" 0

/-- Array family: the batch distance tables, one per padded slot. -/
def pcPd : ℕ → String := lv "pf.d"
/-- Array family: the per-class `vsrc` target regions. -/
def pcVt : ℕ → String := lv "pf.v"
/-- Array family: the virtual-source distance tables, one per
relativised colour. -/
def pcPu : ℕ → String := lv "pf.u"

/-- Scalar: the cluster row's base offset. -/
def pcCb : String := lv "pc.a" 0
/-- Scalar: the cluster row / connector scan counter. -/
def pcCt : String := lv "pc.c" 0
/-- Scalar: the connector's own child name. -/
def pcCc : String := lv "pc.e" 0
/-- Scalar: the batch builder's column cursor. -/
def pcEc : String := lv "pc.f" 0
/-- Scalar: the batch builder's entry cursor. -/
def pcIc : String := lv "pc.g" 0
/-- Scalar: the batch builder's row length. -/
def pcLn : String := lv "pc.h" 0
/-- Scalar: the batch builder's slot base. -/
def pcBs : String := lv "pc.j" 0
/-- Scalar: the batch builder's carrier cursor. -/
def pcAv : String := lv "pc.k" 0
/-- Scalar: the batch builder's emit cursor. -/
def pcSc : String := lv "pc.m" 0
/-- Scalar: the round count, a compile-time constant (`= j`). -/
def pcJr : String := lv "pc.n" 0
/-- Scalar: the schedule's batch width. -/
def pcMw : String := lv "pc.q" 0
/-- Scalar: the colour writer's row base. -/
def pcW : String := lv "pc.w" 0
/-- Scalar: the colour writer's distance cursor. -/
def pcDd : String := lv "pc.s" 0
/-- Scalar: the colour writer's carrier cursor. -/
def pcVv : String := lv "pc.u" 0
/-- Scalar: the isolation's output slot count. -/
def pcNo : String := lv "pc.y" 0

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

/-! ## §3 The command -/

section Program

variable {L : ℕ}

/-- The restrict stage's three schedule cells (`|S|` is already in
`"rs.k"` — the cluster-row copy put it there). -/
def prepRestrictCells (S : Setup L) (ℓp hbf : ℕ → ℕ) (j : ℕ) : Com :=
  .seq (.assign "rs.l" (.lit (S.pal j)))
    (.seq (.assign "rs.p" (.lit (ℓp j))) (.assign "rs.h" (.lit (hbf j))))

/-- The batch builder's two schedule cells: the round count — the level
constant, by the round-count pin — and the batch width. -/
def prepBatchCells (S : Setup L) (j : ℕ) : Com :=
  .seq (.assign pcJr (.lit j)) (.assign pcMw (.lit S.width))

/-- The BFS's four input cells. The source is the connector's own child
name, which the connector scan left in `pcCc`; the radius is `2R`,
never `R`. -/
def prepBfsCells (S : Setup L) (j : ℕ) : Com :=
  .seq (.assign "bf.n" (.var (arenaNames (j + 1)).nN))
    (.seq (.assign "bf.m" (.var (arenaNames (j + 1)).nS))
      (.seq (.assign "bf.r" (.lit (2 * S.R))) (.assign "bf.v" (.var pcCc))))

/-- The supports pass's six input cells. The written column is `j` —
the round-count pin's value of `A.hist.length`, a compile-time
constant — and the radius is again `2R`. -/
def prepSupCells (S : Setup L) (ℓp hbf : ℕ → ℕ) (j : ℕ) : Com :=
  .seq (.assign "sp.n" (.var (arenaNames (j + 1)).nN))
    (.seq (.assign "sp.m" (.var (arenaNames (j + 1)).nS))
      (.seq (.assign "sp.r" (.lit (2 * S.R)))
        (.seq (.assign "sp.l" (.lit (ℓp j)))
          (.seq (.assign "sp.h" (.lit (hbf j))) (.assign "sp.p" (.lit j))))))

/-- The profiles stage's name family at the pass's own regions: the
**pre-isolation** child CSR (`pcOi`/`pcTi`), the child's colour rows at
the parent palette, and the padded batch index region. -/
def prepProfNames (j : ℕ) : ProfNames :=
  ⟨pcOi, pcTi, (arenaNames (j + 1)).col, pcBi, pcXb, pcVo,
    (arenaNames (j + 1)).nN, (arenaNames (j + 1)).nS, pcPd, pcVt, pcPu⟩

/-- **The child-building pass, as one command.** Nine stages in
`SolveMachPrepAll` §0's order, with the constant-many input loads
spliced between them and one closing scalar move (§2's
`arenaStW_setVar_nS`).

Two orderings are forced: `mkBatchCom` reads the channel region **as
`restrictCom` leaves it**, so it precedes `supportsCom`, which patches
a column of it; and `profilesCom` reads the colour region at the
*parent's* palette, so it precedes `colWriteCom`, which rewrites it at
`isoPal`. -/
def prepC (S : Setup L) (ℓp hbf : ℕ → ℕ) (co cm : ℕ → String) (j : ℕ) : Com :=
  .seq (clusterRowCom (co j) (cm j) pcLa (ctrName j) pcCb "rs.k" pcCt)
    (.seq (centreIdxCom pcLa (ctrName j) "rs.k" pcCc pcCt)
      (.seq (prepRestrictCells S ℓp hbf j)
        (.seq (restrictCom (arenaNames j) (prepMid j) pcLa (pcRa j))
          (.seq (prepBatchCells S j)
            (.seq (mkBatchCom (arenaNames (j + 1)).hist pcBb pcBi pcCc
                (arenaNames (j + 1)).nN pcJr pcMw pcEc pcIc pcLn pcBs pcAv
                pcSc (ℓp j) (hbf j))
              (.seq (prepBfsCells S j)
                (.seq (bfsCom pcOi pcTi pcDa)
                  (.seq (prepSupCells S ℓp hbf j)
                    (.seq (supportsCom pcOi pcTi pcDa pcPa
                        (arenaNames (j + 1)).hist)
                      (.seq (profilesCom (prepProfNames j) S.width (S.pal j)
                          S.R)
                        (.seq (colWriteCom (arenaNames (j + 1)).col
                            (arenaNames (j + 1)).nN pcPd pcPu pcW pcDd pcVv
                            (relPal (S.pal j)) S.width S.R)
                          (.seq (isolateCom (prepMid j)
                              (arenaNames (j + 1)).off (arenaNames (j + 1)).tgt
                              pcNo pcBb)
                            (.assign (arenaNames (j + 1)).nS
                              (.var pcNo))))))))))))))

end Program

/-! ## §4 The budget, loads included -/

/-- **The pass's constant-many input loads.** Sixteen assignments — the
restrict stage's three schedule cells, the batch builder's two, the
BFS's four, the supports pass's six, and the closing slot-count move —
each `.assign x e` with `e.size = 1`, so `1 + 1` words apiece.

`prepPassK`'s docstring says these "ride the slack `prepPassK_le`
leaves". `prepPassK_load_le` below is that claim, discharged: the slack
is real, and it lives in `restrictK`'s own per-member charge, so the
schedule constant `4` does **not** move. -/
def prepLoadK : ℕ := 32

/-- The cluster-row copy, the connector scan **and** the pass's sixteen
input loads together still fit `restrictK`'s per-member charge — `31`
per member against the `132` already charged, with the `56` constant
absorbed by the `45 + 132·|S|` the restrict stage already pays. The
child's carrier is never empty (`childN_pos`), which is where `1 ≤ cN`
comes from. -/
theorem clusterRowK_centreIdxK_load_le_restrictK (dS cN Λc ℓp hb : ℕ)
    (hcN : 1 ≤ cN) :
    clusterRowK cN + centreIdxK cN + prepLoadK ≤ restrictK dS cN Λc ℓp hb := by
  have h : 132 * cN ≤ cN * (20 * Λc + (36 * hb + 42) * ℓp + 132) := by
    have h' : cN * 132 ≤ cN * (20 * Λc + (36 * hb + 42) * ℓp + 132) :=
      Nat.mul_le_mul_left cN (by omega)
    omega
  unfold clusterRowK centreIdxK prepLoadK restrictK
  omega

/-- The whole pass, loads included, is still four `prepStageK`s. -/
theorem prepPassK_load_le_prepStageK (cN cns dS Λc ℓp hb mb R : ℕ)
    (hcN : 1 ≤ cN) :
    prepPassK cN cns dS Λc ℓp hb mb R + prepLoadK
      ≤ 4 * prepStageK cN cns dS cN Λc ℓp hb mb R := by
  have h0 := clusterRowK_centreIdxK_load_le_restrictK dS cN Λc ℓp hb hcN
  have h2 : restrictK dS cN Λc ℓp hb
      ≤ prepStageK cN cns dS cN Λc ℓp hb mb R := by
    unfold prepStageK; omega
  have h3 := mkBatchK_le_prepStageK cN cns dS Λc ℓp hb mb R hcN
  have h4 := colWriteK_le_prepStageK cN cns dS cN Λc ℓp hb mb R
  unfold prepPassK
  omega

/-- **The pass's budget fits §7's envelope, loads included** — verbatim
`prepPassK_le`'s conclusion with `prepLoadK` added to the left: the
same `restrictK` column plus the same schedule constant times the
child's weight `‖B₀‖ + 1`, and **no `A.N` term**. The loads cost
nothing the shape can see. -/
theorem prepPassK_load_le (cN cns dS Λc ℓp hb mb R : ℕ) (hcN : 1 ≤ cN) :
    prepPassK cN cns dS Λc ℓp hb mb R + prepLoadK
      ≤ 4 * restrictK dS cN Λc ℓp hb
        + 4 * (800 * (R + 1) * (mb + Λc + 2) * (cN + cns + 1)) := by
  have h1 := prepPassK_load_le_prepStageK cN cns dS Λc ℓp hb mb R hcN
  have h2 := prepStageK_le cN cns dS cN Λc ℓp hb mb R
  omega

section Charge

variable {L n₀ : ℕ}

open Classical in
/-- **The pass's budget at the driver's own dimensions** — the `KP` the
composition instantiates. Every figure is the *child's* except
`restrictK`'s `dS`, which is §6.1's own parent-degree column: the
cluster's carrier `childN`, the child graph's slot count, the parent
degree sum over the cluster, and the schedule's `(ℓp j, hbf j, width,
R)` at the **relativised** palette (the colour writer emits `Λ+1`
class blocks, so `prepPassK`'s single `Λc` slot must be `relPal`, not
`S.pal j` — at which `restrictK` and `profilesK` are then over-, never
under-, charged). -/
noncomputable def prepKP (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp hbf : ℕ → ℕ) : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ :=
  fun _ j A m =>
    if h : m < A.N then
      prepPassK (childN S A ((ord A.N A.G).order) ⟨m, h⟩)
        (∑ v : Fin (childN S A ((ord A.N A.G).order) ⟨m, h⟩),
          (preG S A ((ord A.N A.G).order) ⟨m, h⟩).degree v)
        (Impl.degSum A.G (cluster S A ((ord A.N A.G).order) ⟨m, h⟩))
        (relPal (S.pal j)) (ℓp j) (hbf j) S.width S.R + prepLoadK
    else 0

open Classical in
@[simp] theorem prepKP_apply (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp hbf : ℕ → ℕ) (k j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    prepKP (n₀ := n₀) S ord ℓp hbf k j A (u : ℕ)
      = prepPassK (childN S A ((ord A.N A.G).order) u)
          (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
            (preG S A ((ord A.N A.G).order) u).degree v)
          (Impl.degSum A.G (cluster S A ((ord A.N A.G).order) u))
          (relPal (S.pal j)) (ℓp j) (hbf j) S.width S.R + prepLoadK := by
  rw [prepKP, dif_pos u.2]

open Classical in
/-- **The instantiated budget fits §7's envelope.** `restrictK` at the
parent-degree column, plus a schedule constant times the child's own
weight. There is **no `A.N` term**: `childN`, the child's slot count and
`Impl.degSum A.G (cluster …)` are all charged per child, and §6.1's
`Θ(A.N²)` scratch trap is avoided because `prepC` never wipes a
carrier-sized region at the parent's dimension. -/
theorem prepKP_le (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp hbf : ℕ → ℕ) (k j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    prepKP (n₀ := n₀) S ord ℓp hbf k j A (u : ℕ)
      ≤ 4 * restrictK (Impl.degSum A.G (cluster S A ((ord A.N A.G).order) u))
            (childN S A ((ord A.N A.G).order) u) (relPal (S.pal j)) (ℓp j)
            (hbf j)
        + 4 * (800 * (S.R + 1) * (S.width + relPal (S.pal j) + 2)
            * (childN S A ((ord A.N A.G).order) u
              + (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
                  (preG S A ((ord A.N A.G).order) u).degree v) + 1)) := by
  rw [prepKP_apply]
  exact prepPassK_load_le _ _ _ _ _ _ _ _ (childN_pos S A _ u)

end Charge

/-! ## §5 The level's scratch descriptor

**The recurring trap, discharged.** An exact-length or allocation
clause in a stage's *precondition* is a binding requirement on whoever
establishes it, and IMP+ `store` is `List.set`, so **no run changes an
array's length**: every length the pass needs must already hold in the
state it is handed. `ChildLoadPartsScr`'s frame clause
(`∀ b, (σ'.arrs b).length = (σ.arrs b).length`) then makes it
impossible for the pass to repair one. `PrepAlloc` is the complete list
of what the nine stages demand, read off their preconditions, at the
**root's** dimensions so that the clause is data-independent:

* `profilesCom_specW` asks the batch index region at length **exactly**
  `S.width` — an equality, `BatchWidthScr`, not a `≤`;
* everything else is a `≤`, but the child's own five regions have to be
  sized for the level-`(j+1)` palette (`n₀ * S.pal (i+1)`), not the
  parent's, because the **colour writer** rewrites them at `isoPal`
  after `restrictCom` filled them at `S.pal i`.
-/

section Descriptor

variable {L : ℕ}

/-- The truncation of a zero block is a zero block. -/
theorem take_arrOf {n m : ℕ} (f : ℕ → ℕ) (h : m ≤ n) :
    (arrOf n f).take m = arrOf m f := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < m
  · rw [List.getElem?_take_of_lt hi, getElem?_arrOf f (lt_of_lt_of_le hi h),
      getElem?_arrOf f hi]
  · rw [List.getElem?_eq_none (by rw [List.length_take, length_arrOf]; omega),
      List.getElem?_eq_none (by rw [length_arrOf]; omega)]

/-- A clean window shrinks. -/
theorem take_eq_arrOf_of_le {l : List ℕ} {n m : ℕ}
    (h : l.take n = arrOf n (fun _ => 0)) (hm : m ≤ n) :
    l.take m = arrOf m (fun _ => 0) := by
  have h1 : (l.take n).take m = l.take m := by
    rw [List.take_take, Nat.min_eq_left hm]
  rw [← h1, h, take_arrOf _ hm]

/-- **Every allocation the nine stages ask for**, at level `i`, read off
their preconditions and stated at the root's dimensions. -/
def PrepAlloc (S : Setup L) (ℓp hbf : ℕ → ℕ) (n₀ : ℕ) (i : ℕ)
    (σ : Env) : Prop :=
  -- the child's own six regions (`restrictCom`, `colWriteCom`, the block)
  n₀ + 1 ≤ (σ.arrs (arenaNames (i + 1)).off).length ∧
  n₀ * n₀ ≤ (σ.arrs (arenaNames (i + 1)).tgt).length ∧
  n₀ * S.pal (i + 1) ≤ (σ.arrs (arenaNames (i + 1)).col).length ∧
  n₀ ≤ (σ.arrs (arenaNames (i + 1)).up).length ∧
  n₀ * ℓp i * (hbf i + 1) ≤ (σ.arrs (arenaNames (i + 1)).hist).length ∧
  n₀ * (levelFml S (i + 1)).length ≤ (σ.arrs (arenaNames (i + 1)).tab).length ∧
  -- the pre-isolation CSR pair `restrictCom` builds into
  n₀ + 1 ≤ (σ.arrs pcOi).length ∧ n₀ * n₀ ≤ (σ.arrs pcTi).length ∧
  -- the pass's own scratch regions
  n₀ ≤ (σ.arrs pcLa).length ∧ n₀ ≤ (σ.arrs (pcRa i)).length ∧
  n₀ ≤ (σ.arrs pcBb).length ∧ n₀ ≤ (σ.arrs pcDa).length ∧
  n₀ ≤ (σ.arrs pcPa).length ∧ n₀ ≤ (σ.arrs pcXb).length ∧
  n₀ + 2 ≤ (σ.arrs pcVo).length ∧
  -- the profiles stage's three table families
  (∀ t < S.width, n₀ ≤ (σ.arrs (pcPd t)).length) ∧
  (∀ c < S.pal i, n₀ * n₀ + 2 * n₀ ≤ (σ.arrs (pcVt c)).length) ∧
  (∀ c < S.pal i + 1, n₀ + 1 ≤ (σ.arrs (pcPu c)).length)

/-- Allocations are length-only: they ride every pass's frame. -/
theorem prepAlloc_len {S : Setup L} {ℓp hbf : ℕ → ℕ} {n₀ i : ℕ} {σ σ' : Env}
    (h : PrepAlloc S ℓp hbf n₀ i σ)
    (hlen : ∀ b, (σ'.arrs b).length = (σ.arrs b).length) :
    PrepAlloc S ℓp hbf n₀ i σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun t ht => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · rw [hlen]; exact h1
  · rw [hlen]; exact h2
  · rw [hlen]; exact h3
  · rw [hlen]; exact h4
  · rw [hlen]; exact h5
  · rw [hlen]; exact h6
  · rw [hlen]; exact h7
  · rw [hlen]; exact h8
  · rw [hlen]; exact h9
  · rw [hlen]; exact h10
  · rw [hlen]; exact h11
  · rw [hlen]; exact h12
  · rw [hlen]; exact h13
  · rw [hlen]; exact h14
  · rw [hlen]; exact h15
  · rw [hlen]; exact h16 t ht
  · rw [hlen]; exact h17 c hc
  · rw [hlen]; exact h18 c hc

/-- **The level's scratch descriptor**, concretely. Four clauses beyond
the allocations:

* the **deep** rank scratches are clean on the whole root window — they
  are outside the pass's write set, so this rides `Run`'s frame;
* **this** level's rank scratch is clean on this level's carrier window
  — verbatim `restrictCom_specW`'s content pre- and postcondition;
* every level's carrier cell is below the root's carrier — the one
  scalar fact that lets `hscrDown` shrink a deep clean window to the
  child's, and a fact the pass re-establishes (`childN ≤ A.N ≤ n₀`);
* the batch index region is at length exactly `S.width`. -/
def prepScr (S : Setup L) (ℓp hbf : ℕ → ℕ) (n₀ : ℕ) : ℕ → Env → Prop :=
  fun j σ =>
    (∀ i, j ≤ i → PrepAlloc S ℓp hbf n₀ i σ) ∧
    (∀ i, j < i → (σ.arrs (pcRa i)).take n₀ = arrOf n₀ (fun _ => 0)) ∧
    RankScr (pcRa j) (arenaNames j).nN σ ∧
    (∀ i, σ.vars (arenaNames i).nN ≤ n₀) ∧
    BatchWidthScr pcBi S.width σ

/-- **`hscrDown`, discharged for the concrete descriptor.** The deep
half restricts; the child's own clean window is the deep one shrunk to
the child's carrier, which is legal because every carrier cell is below
the root's. This is the clause the *landed* `centrePrep_of_childLoadScr`
asks for, and it is exactly why the rank scratch is level-indexed. -/
theorem prepScr_down (S : Setup L) (ℓp hbf : ℕ → ℕ) (n₀ j : ℕ) (σ : Env)
    (h : prepScr S ℓp hbf n₀ j σ) : prepScr S ℓp hbf n₀ (j + 1) σ := by
  obtain ⟨halloc, hdeep, -, hcell, hbw⟩ := h
  refine ⟨fun i hi => halloc i (by omega), fun i hi => hdeep i (by omega),
    ?_, hcell, hbw⟩
  exact take_eq_arrOf_of_le (hdeep (j + 1) (by omega)) (hcell (j + 1))

/-- **`htabLen`, discharged for the concrete descriptor**: the child's
table region is allocated at the root's carrier times the child level's
schedule family. -/
theorem prepScr_htabLen (S : Setup L) (ℓp hbf : ℕ → ℕ) (n₀ j : ℕ) (σ : Env)
    (h : prepScr S ℓp hbf n₀ j σ) :
    n₀ * (levelFml S (j + 1)).length
      ≤ (σ.arrs (arenaNames (j + 1)).tab).length :=
  (h.1 j le_rfl).2.2.2.2.2.1

/-- The descriptor's own allocations, at this level. -/
theorem prepScr_alloc {S : Setup L} {ℓp hbf : ℕ → ℕ} {n₀ j : ℕ} {σ : Env}
    (h : prepScr S ℓp hbf n₀ j σ) : PrepAlloc S ℓp hbf n₀ j σ :=
  h.1 j le_rfl

/-- The clean rank window this level's restrict stage consumes. -/
theorem prepScr_rank {S : Setup L} {ℓp hbf : ℕ → ℕ} {n₀ j : ℕ} {σ : Env}
    (h : prepScr S ℓp hbf n₀ j σ) : RankScr (pcRa j) (arenaNames j).nN σ :=
  h.2.2.1

/-- The batch index region's exact length — `profilesCom_specW`'s one
equality precondition. -/
theorem prepScr_batchWidth {S : Setup L} {ℓp hbf : ℕ → ℕ} {n₀ j : ℕ}
    {σ : Env} (h : prepScr S ℓp hbf n₀ j σ) :
    (σ.arrs pcBi).length = S.width := h.2.2.2.2

/-- **The descriptor is re-establishable by the pass** — the shape
`ChildLoadPartsScr`'s added conjunct takes. Everything but the two
content clauses rides lengths and the frame; the level's own clean
window is `restrictCom_specW`'s own postcondition, and the carrier-cell
bound is `childN ≤ A.N ≤ n₀`. -/
theorem prepScr_out {S : Setup L} {ℓp hbf : ℕ → ℕ} {n₀ j : ℕ} {σ σ' : Env}
    (h : prepScr S ℓp hbf n₀ j σ)
    (hlen : ∀ b, (σ'.arrs b).length = (σ.arrs b).length)
    (hdeep : ∀ i, j < i → σ'.arrs (pcRa i) = σ.arrs (pcRa i))
    (hrank : RankScr (pcRa j) (arenaNames j).nN σ')
    (hcell : ∀ i, σ'.vars (arenaNames i).nN ≤ n₀) :
    prepScr S ℓp hbf n₀ j σ' := by
  obtain ⟨halloc, hdp, -, -, hbw⟩ := h
  refine ⟨fun i hi => prepAlloc_len (halloc i hi) hlen, ?_, hrank, hcell, ?_⟩
  · intro i hi
    rw [hdeep i hi]
    exact hdp i hi
  · rw [BatchWidthScr, hlen pcBi]
    exact hbw

end Descriptor

/-! ## §6 The name discipline, discharged

The nine stage contracts between them ask for about sixty
disequalities, five `Nodup`/`Pairwise` bundles, a `ProfNames.Ok`, and
eight `∉ <stage scalars>` clauses. At the pool of §1 every one of them
is either a **base clash** between two four-character `lv` bases or a
**level clash** at one base, so the whole discipline is
`lv_ne_of_base_ne` / `lv_ne_of_level_ne` / `lv_notMem` and `decide`.

This section discharges it once, so that the composition never has to
argue about a name again. -/

section NameDiscipline

variable {L : ℕ}

/-- The level's own five regions are pairwise distinct — the
`hnd5`/`hnd5P` side condition of `restrictCom_specW`,
`supportsCom_specW`, `isolateCom_specW`, `profilesCom_specW` and
`arenaStW_recol_frame`. -/
theorem arenaNames_nodup5 (k : ℕ) :
    ([(arenaNames k).off, (arenaNames k).tgt, (arenaNames k).col,
      (arenaNames k).up, (arenaNames k).hist] : List String).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or, not_false_eq_true]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

/-- The same at the pass's intermediate family — the pre-isolation
child, whose CSR pair is the pass's own scratch. -/
theorem prepMid_nodup5 (j : ℕ) :
    ([(prepMid j).off, (prepMid j).tgt, (prepMid j).col, (prepMid j).up,
      (prepMid j).hist] : List String).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or, not_false_eq_true]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

/-- `restrictCom_specW`'s `hpair`: the child's five output regions and
the rank scratch, pairwise distinct. -/
theorem prep_restrict_pairwise (j : ℕ) :
    ([(prepMid j).off, (prepMid j).tgt, (prepMid j).col, (prepMid j).up,
      (prepMid j).hist, pcRa j] : List String).Pairwise (· ≠ ·) := by
  show ([(prepMid j).off, (prepMid j).tgt, (prepMid j).col, (prepMid j).up,
    (prepMid j).hist, pcRa j] : List String).Nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or, not_false_eq_true]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩,
    ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

/-- `restrictCom_specW`'s `hdisj`: the child's output regions and the
rank scratch miss the parent's regions and the cluster region. The only
non-base clashes are `col`/`up`/`hist` at levels `j+1` versus `j`. -/
theorem prep_restrict_disj (j : ℕ) :
    ∀ x ∈ ([(prepMid j).off, (prepMid j).tgt, (prepMid j).col,
        (prepMid j).up, (prepMid j).hist, pcRa j] : List String),
      ∀ y ∈ ([(arenaNames j).off, (arenaNames j).tgt, (arenaNames j).col,
        (arenaNames j).up, (arenaNames j).hist, pcLa] : List String),
      x ≠ y := by
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact lv_ne_of_base_ne (by rfl) (by decide) _ _
        | exact lv_ne_of_level_ne (by rfl) (by omega)

/-- The cluster region misses the parent's five — `restrictCom_specW`'s
`hla5`. -/
theorem prep_la_notMem5 (j : ℕ) :
    pcLa ∉ ([(arenaNames j).off, (arenaNames j).tgt, (arenaNames j).col,
      (arenaNames j).up, (arenaNames j).hist] : List String) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

/-- The BFS distance region misses the child's five —
`bfsCom_specW`'s `hda5` and `supportsCom_specW`'s. -/
theorem prep_da_notMem5 (j : ℕ) :
    pcDa ∉ ([(prepMid j).off, (prepMid j).tgt, (prepMid j).col,
      (prepMid j).up, (prepMid j).hist] : List String) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

/-- The supports pass's parent region misses the child's five. -/
theorem prep_pa_notMem5 (j : ℕ) :
    pcPa ∉ ([(prepMid j).off, (prepMid j).tgt, (prepMid j).col,
      (prepMid j).up, (prepMid j).hist] : List String) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

/-- The batch bit region misses the child's five — `isolateCom_specW`'s
`hba5`. -/
theorem prep_bb_notMem5 (j : ℕ) :
    pcBb ∉ ([(prepMid j).off, (prepMid j).tgt, (prepMid j).col,
      (prepMid j).up, (prepMid j).hist] : List String) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

/-- The isolation's two output regions miss the pre-isolation family —
`isolateCom_specW`'s `hoaO5`/`htaO5`. The clash with the pass's own
CSR pair is a base clash; with `col`/`up`/`hist` of level `j+1` it is a
base clash too, because the outputs are `sa.o`/`sa.t` at that level. -/
theorem prep_oaO_notMem5 (j : ℕ) :
    (arenaNames (j + 1)).off ∉ ([(prepMid j).off, (prepMid j).tgt,
      (prepMid j).col, (prepMid j).up, (prepMid j).hist] : List String) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

theorem prep_taO_notMem5 (j : ℕ) :
    (arenaNames (j + 1)).tgt ∉ ([(prepMid j).off, (prepMid j).tgt,
      (prepMid j).col, (prepMid j).up, (prepMid j).hist] : List String) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_of_base_ne (by rfl) (by decide) _ _

end NameDiscipline
end Lax3Proofs.Prog
