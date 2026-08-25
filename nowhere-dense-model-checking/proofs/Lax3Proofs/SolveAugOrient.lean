import Lax3Proofs.SolveAugFrameProg
import Lax3Proofs.SolveAugEmitCom

set_option autoImplicit false

/-!
# F6c12-5a-ii — `AugBaseOrientIn`, the base orientation as a CSR

`SolveAugCompose` §6 splits the augmentation's base pass into three and
`SolveAugFrameProg` discharges the first (`AugBaseAdjIn`).  This file is
the third: **`AugBaseOrientIn` is met by a concrete `Com` at a concrete
budget**, turning the deletable adjacency region of `A.G` together with
the rank array of `selPerm sel A.G` into an in-neighbour CSR of
`baseOr A.G (selPerm sel A.G)` — which is `selChain sel A.G 0`
(`selChain_zero`, `rfl`).

`AugBasePeelIn` is **not** discharged here and nothing about it is
asserted.

## Nothing landed concluded an `InNCsr` before this

`SolveAugFrat` *defines* `InNCsr` and only ever reads it — `InNCsr.rows`,
`InNCsr.ns_eq`, and `FratCsrAt`/`fratCsrAt_fratCom`, where it sits in a
**pre**condition.  `SolveAugTrans` defines its windowed twin `TrInCsr`,
and the one landed theorem concluding a `TrInCsr` (`trInCsr_emit`) does
so from an abstract row family `E` and read-back hypotheses, not from a
program.  The three landed build programs
`bldOffCom`/`bldDegCom`/`bldMateCom` go source-CSR → deletable
adjacency, which is neither this input nor this output shape.  So the
count / prefix-sum / scatter below is a fresh construction, and §2's
`inNCsr_winA_of_trInCsr` is the first route from a machine state to
`InNCsr` anywhere in the tower.

## What `orCom` is

Three sweeps over the region, in the shape of `transposeIn_tpCom`'s
counting sort but with the cursor a **scalar**, since a row of the
output is filled by the outer turn that owns it:

* `orCntCom` — one outer turn a vertex, one inner turn a source slot:
  `cn[v]` ends at `#{u ∈ N(v) : π u < π v}`, the in-degree of `v` in
  `baseOr G π`.  The row bounds are `ao[v]` and `ao[v+1]`; the live
  prefix at the empty deleted set *is* the whole row, so the degree
  array `bdg` is never read (`deleteVerts_empty`).
* `orOffCom` — one turn a vertex: `io[i] := acc; acc += cn[i]`, then
  `io[nN] := acc` and `nA := acc`.  The arc count is a *result* of the
  pass, so the cell it lands in is written here, not read.
* `orScatCom` — one outer turn a vertex, one inner turn a source slot:
  the cursor starts at `io[v]` and each qualifying neighbour is appended
  to row `v` of `it`.

## Why it is correct, in one line each

* **The count** is a bijection between the source slots of row `v`
  carrying a rank-smaller neighbour and `(baseOr G π).inN v`
  (`orCnt_row`): the region's `sound` maps a slot to a neighbour, its
  `complete` maps a neighbour back, and `slot_injOn` says a neighbour
  occupies one slot.
* **The scatter's invariant is an address, not a set**
  (`transposeIn_tpCom`'s Finding 2): the second clause of `OrScSt` (and
  of `OrScRow`, its partial form for the row being filled) says that the
  qualifying source slot `q` of row `v` lands at
  `inOff D v + orCnt … (offF v) q`.  Since the cursor is the row's own
  clock, that address is where the write happens, and completeness of
  the row is immediate.
* **Injectivity is derived, not carried** — the row has exactly
  `(D.inN v).card` slots, every slot holds an in-neighbour and every
  in-neighbour is in a slot, so the slot map is injective by pigeonhole
  (`Finset.injOn_of_surjOn_of_card_le`).  Carrying it would have added a
  clause to every one of the `2·arcCount D` scatter steps.

## The budget

`orK N a = 70·N + 86·a + 25` at `a = arcCount (baseOr A.G π)`: the count
sweep `28` a vertex and `20` a source slot, the prefix sweep `16` a
vertex, the scatter `26` a vertex and `23` a source slot; a vertex's
source row is its `A.G`-degree, and the degree sum is `2·a`
(`sum_ncard_neighborSet_eq_two_mul_arcCount`, `SolveAugFrameProg` §1),
which is where the two slot constants double into `40 + 46 = 86`.

Against `augChainCost_le_selChainCharge`'s `bn ≤ k`, `ba ≤ 3k`: this
pass alone closes at `k = 70` (`86 ≤ 210`), and next to the landed
`AugBaseAdjIn` (`81`, `116`) the two together are `151` and `202`, so
`202 ≤ 3·151 = 453` with `251` of arc coefficient left for
`AugBasePeelIn`.

## Findings

1. **`augStInN` (`SolveAugCompose` §7) is not producible by any pass.**
   `InNCsr` is stated through `Lib.Csr`, whose first two clauses pin the
   two array lengths **exactly** (`arrOf (n+1) off`, `arrOf ns tgt`),
   while a pass gets `N + 1 ≤ length` and `ns ≤ length` — and the output
   slot count `arcCount D` is *computed by this pass*, so no allocation
   can have been made exactly that long.  This is `SolveAugFrat`'s own
   Finding 3 about `GraphCsr`, present again in the region §7 nominates
   for `AugSt`.  Nothing is *false*: `InNCsr` also sits in the
   precondition of the landed `FratCsrAt`, so producer and consumer move
   together, and the standing repair is `SolveGlueLoad.CsrPrefix`'s —
   assert the exact-length relation of the **truncation**, and reach the
   consumer through `SolveChainWin.specWindow` at the same window.
   `augStInNW` below is `augStInN` read that way, and it is what this
   pass delivers, together with the un-windowed `TrInCsr`, which has the
   windowed convention built into its own clauses and is the shape
   `TransposeIn` consumes.
2. **The program reads neither the degree nor the mate array.**  At
   `S = ∅` the live prefix of a row is the whole row
   (`deleteVerts_empty`), so `ao[v+1]` bounds the scan; `bdg` and `bmt`
   appear only in the proof, where `DelAdjSt`'s degree clause is what
   turns a slot index into a neighbour.  One array read a vertex instead
   of two, and two fewer names in the pass's frame.
3. **No figure needs a cell.**  The carrier is `nN`; the source slot
   count is `ao[nN]`, the region's own last offset; the output slot
   count is produced, not consumed.  So the pass is meetable in IMP+,
   which reads no array length (`Imp.lean:158`), for the same reason
   `TransposeIn` is.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (getD_eq_getElem)
open Lax3Proofs.Augmentation (Orientation baseOr baseOr_orients mem_baseOr)
open Lax3Proofs.CoverRoutine (MinDegSel selPerm selChain)

/-! ## §0 Small array and run helpers

`SolveAugEmitCom` §0's shapes, which are `private` there. -/

private theorem getD_set_self₃ {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem getD_set_of_ne₃ {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

private theorem getElem?_set_of_ne₃ {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c)[q]? = l[q]? := List.getElem?_set_ne h

private theorem getElem?_of_lt₃ (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem evB_var₃ {B : ℕ} {y : String} {σ : Env} {c : ℕ} (hy : σ.vars y = c)
    (hc : c < B) : (Expr.var y).evalB B σ = some c := by
  rw [← hy] at hc ⊢; exact evalB_var hc

private theorem evB_lit₃ {B c : ℕ} {σ : Env} (hc : c < B) :
    (Expr.lit c).evalB B σ = some c := evalB_lit hc

private theorem evB_add₃ {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (hab : a + b < B) :
    (Expr.add e f).evalB B σ = some (a + b) := evalB_bin he hf (by simpa using hab)

private theorem evB_get₃ {B : ℕ} {a : String} {i : Expr} {σ : Env} {q c : ℕ}
    (hi : i.evalB B σ = some q) (hq : (σ.arrs a)[q]? = some c) (hc : c < B) :
    (Expr.get a i).evalB B σ = some c := evalB_get hi hq hc

private theorem run_assign₃ {B : ℕ} {x : String} {e : Expr} {σ : Env} {c K : ℕ}
    (he : e.evalB B σ = some c) (hK : 1 + e.size ≤ K) :
    Run B (.assign x e) σ (σ.setVar x c) K := (Run.assign he).mono hK

private theorem run_store₃ {B : ℕ} {a : String} {i e : Expr} {σ : Env} {q c K : ℕ}
    (hi : i.evalB B σ = some q) (he : e.evalB B σ = some c)
    (hq : q < (σ.arrs a).length) (hK : 1 + i.size + e.size ≤ K) :
    Run B (.store a i e) σ (σ.setArr a q c) K := (Run.store hi he hq).mono hK

/-- The truncation of a long enough array to a window whose entries are
known is that window's `arrOf`. -/
private theorem take_eq_arrOf {l : List ℕ} {m : ℕ} {f : ℕ → ℕ} (hm : m ≤ l.length)
    (hf : ∀ i, i < m → l[i]? = some (f i)) : l.take m = arrOf m f := by
  refine List.ext_getElem? (fun i => ?_)
  by_cases hi : i < m
  · rw [List.getElem?_take_of_lt hi, hf i hi, getElem?_arrOf f hi]
  · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
      List.getElem?_eq_none (by rw [length_arrOf]; omega)]

/-! ## §1 The in-neighbour CSR's arithmetic

`SolveAugEmit`'s `outDegAt`/`outOff` at the untransposed relation: the
in-degrees and their prefix sums, which are the offsets the pass writes
and the addresses the scatter fills. -/

variable {n : ℕ}

/-- The in-degree at a plain index, `0` off the carrier. -/
def inDegAt (D : Orientation n) (v : ℕ) : ℕ :=
  if h : v < n then (D.inN ⟨v, h⟩).card else 0

/-- The in-neighbour CSR's offsets: the prefix sums of the in-degrees. -/
def inOff (D : Orientation n) (v : ℕ) : ℕ := ∑ a ∈ Finset.range v, inDegAt D a

theorem inOff_zero (D : Orientation n) : inOff D 0 = 0 := by simp [inOff]

theorem inOff_succ (D : Orientation n) (v : ℕ) :
    inOff D (v + 1) = inOff D v + inDegAt D v := Finset.sum_range_succ _ _

theorem inDegAt_coe (D : Orientation n) (v : Fin n) :
    inDegAt D (v : ℕ) = (D.inN v).card := by rw [inDegAt, dif_pos v.isLt]

/-- The in-neighbours at a plain index, as plain indices — the row of
the CSR the pass writes, stated without a `Fin` so that a loop
invariant can name it. -/
def inNAt (D : Orientation n) (v : ℕ) : Finset ℕ :=
  if h : v < n then (D.inN ⟨v, h⟩).image (fun w : Fin n => (w : ℕ)) else ∅

theorem mem_inNAt {D : Orientation n} {v u : ℕ} (hv : v < n) :
    u ∈ inNAt D v ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN ⟨v, hv⟩ := by
  rw [inNAt, dif_pos hv, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w.isLt, by simpa using hw⟩
  · rintro ⟨hu, hmem⟩; exact ⟨⟨u, hu⟩, hmem, rfl⟩

theorem lt_of_mem_inNAt {D : Orientation n} {v u : ℕ} (h : u ∈ inNAt D v) : u < n := by
  by_cases hv : v < n
  · exact (mem_inNAt hv).1 h |>.fst
  · rw [inNAt, dif_neg hv] at h; exact absurd h (by simp)

theorem card_inNAt (D : Orientation n) (v : ℕ) : (inNAt D v).card = inDegAt D v := by
  by_cases hv : v < n
  · rw [inNAt, dif_pos hv, inDegAt, dif_pos hv,
      Finset.card_image_of_injective _ Fin.val_injective]
  · rw [inNAt, dif_neg hv, inDegAt, dif_neg hv, Finset.card_empty]

/-- **The in-neighbour CSR has exactly `arcCount D` slots.** -/
theorem inOff_last (D : Orientation n) : inOff D n = arcCount D := by
  rw [inOff, ← Fin.sum_univ_eq_sum_range (fun v => inDegAt D v) n]
  exact Finset.sum_congr rfl fun v _ => inDegAt_coe D v

theorem inOff_mono (D : Orientation n) {a b : ℕ} (hab : a ≤ b) : inOff D a ≤ inOff D b := by
  refine Finset.sum_le_sum_of_subset (fun x hx => ?_)
  simp only [Finset.mem_range] at hx ⊢
  omega

theorem inOff_le_arcCount (D : Orientation n) {k : ℕ} (hk : k ≤ n) :
    inOff D k ≤ arcCount D := by
  have := inOff_mono D hk
  rwa [inOff_last] at this

/-- Every slot of the output lies in exactly one row — what makes the
rows tile the slot space. -/
theorem exists_inRow (D : Orientation n) : ∀ k, ∀ p, p < inOff D k →
    ∃ v, v < k ∧ inOff D v ≤ p ∧ p < inOff D (v + 1) := by
  intro k
  induction k with
  | zero => intro p hp; rw [inOff_zero] at hp; omega
  | succ k ih =>
      intro p hp
      rcases Nat.lt_or_ge p (inOff D k) with h | h
      · obtain ⟨v, hv1, hv2, hv3⟩ := ih p h
        exact ⟨v, by omega, hv2, hv3⟩
      · exact ⟨k, by omega, h, hp⟩

theorem inDegAt_le_arcCount (D : Orientation n) (i : ℕ) : inDegAt D i ≤ arcCount D := by
  rcases Nat.lt_or_ge i n with h | h
  · have h1 : inOff D (i + 1) = inOff D i + inDegAt D i := inOff_succ D i
    have h2 : inOff D (i + 1) ≤ arcCount D := inOff_le_arcCount D (by omega)
    omega
  · rw [inDegAt, dif_neg (by omega)]
    exact Nat.zero_le _

/-- The rank of a vertex at a plain index, `0` off the carrier — what
the rank array holds. -/
def rankAt {N : ℕ} (π : Equiv.Perm (Fin N)) (i : ℕ) : ℕ :=
  if h : i < N then ((π ⟨i, h⟩ : Fin N) : ℕ) else 0

theorem rankAt_coe {N : ℕ} (π : Equiv.Perm (Fin N)) (v : Fin N) :
    rankAt π (v : ℕ) = (π v : ℕ) := by
  rw [rankAt, dif_pos v.isLt]

theorem rankAt_lt {N : ℕ} (π : Equiv.Perm (Fin N)) {i : ℕ} (h : i < N) : rankAt π i < N := by
  rw [rankAt, dif_pos h]; exact (π ⟨i, h⟩).isLt

/-! ## §2 From a machine state to an `InNCsr`

`TrInCsr` (`SolveAugTrans.lean:127`) is the windowed in-neighbour CSR:
offsets and targets are functions, the two allocations are `≥` their
extents.  `InNCsr` (`SolveAugFrat.lean:144`) is the same data behind
`Lib.Csr`, whose first two clauses pin the two lengths **exactly**.  The
bridge is `SolveGlueLoad.CsrPrefix`'s: the exact relation holds of the
*truncation* (Finding 1). -/

/-- The window an in-neighbour CSR of extent `ns` on a carrier of `nv`
is read at. -/
def inWs (o t : String) (nv ns : ℕ) : String → Option ℕ :=
  fun b => if b = o then some (nv + 1) else if b = t then some ns else none

theorem inWs_o (o t : String) (nv ns : ℕ) : inWs o t nv ns o = some (nv + 1) := by
  simp [inWs]

theorem inWs_t {o t : String} (h : t ≠ o) (nv ns : ℕ) : inWs o t nv ns t = some ns := by
  simp [inWs, h]

/-- **A `TrInCsr` is an `InNCsr` of its truncation** — the first route
from a machine state to `InNCsr` in the tower.  Every clause of `Csr` is
a clause of `TrInCsr` except the two exact lengths, and those are what
the window supplies. -/
theorem inNCsr_winA_of_trInCsr {o t : String} {ns : ℕ} {D : Orientation n}
    {off tgt : ℕ → ℕ} {σ : Env} (hto : t ≠ o) (h : TrInCsr o t D ns off tgt σ) :
    InNCsr o t D ns (winA (inWs o t n ns) σ) := by
  have hrow : ∀ w : Fin n, ∀ k, k < Csr.rowLen off (w : ℕ) →
      off (w : ℕ) ≤ off (w : ℕ) + k ∧ off (w : ℕ) + k < off ((w : ℕ) + 1) := by
    intro w k hk
    have hs := h.step w
    rw [Csr.rowLen] at hk
    exact ⟨Nat.le_add_right _ _, by omega⟩
  refine ⟨off, tgt, ⟨?_, ?_, ?_, h.last, h.tgtLt⟩, h.zero, ?_, ?_⟩
  · rw [arrs_winA_some (inWs_o o t n ns) σ]
    exact take_eq_arrOf h.offLen (fun i hi => h.offGet i (by omega))
  · rw [arrs_winA_some (inWs_t hto n ns) σ]
    exact take_eq_arrOf h.tgtLen (fun p hp => h.tgtGet p hp)
  · intro i hi
    have hs : off (i + 1) = off i + (D.inN ⟨i, hi⟩).card := h.step ⟨i, hi⟩
    omega
  · -- the rows have no duplicates: two slots of a row holding the same
    -- target are the same slot
    intro w
    rw [Csr.row, arrOf]
    refine List.Nodup.map_on ?_ (List.nodup_range)
    intro a ha b hb hab
    simp only [List.mem_range] at ha hb
    obtain ⟨ha1, ha2⟩ := hrow w a ha
    obtain ⟨hb1, hb2⟩ := hrow w b hb
    have := h.inj w _ _ ha1 ha2 hb1 hb2 hab
    omega
  · -- row `w` lists exactly the in-neighbours of `w`
    intro w u
    rw [Csr.row, arrOf]
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨h1, h2⟩ := hrow w k hk
      have hlt : tgt (off (w : ℕ) + k) < n := h.tgtLt _ (h.row_lt_ns h2)
      exact ⟨hlt, h.sound w _ h1 h2 hlt⟩
    · rintro ⟨hu, hmem⟩
      obtain ⟨p, hp1, hp2, hp3⟩ := h.complete w ⟨u, hu⟩ hmem
      have hs := h.step w
      refine ⟨p - off (w : ℕ), by rw [Csr.rowLen]; omega, ?_⟩
      rw [show off (w : ℕ) + (p - off (w : ℕ)) = p from by omega]
      exact hp3

/-! ## §3 The region, digested

`DelAdjSt` at the empty deleted set, `RankArr` and the three output
allocations, read once into plain functions — the shape the three sweeps
carry.  It is `TpFrame`'s role for the transpose, with `TrInCsr`
replaced by the deletable region because that is what the base pass is
handed. -/

/-- The degree at a plain index, `0` off the carrier. -/
noncomputable def degAt {N : ℕ} (G : SimpleGraph (Fin N)) (i : ℕ) : ℕ :=
  if h : i < N then (G.neighborSet ⟨i, h⟩).ncard else 0

/-- The region's offsets are the degree prefix sums. -/
theorem offF_eq_sum {N : ℕ} {G : SimpleGraph (Fin N)} {offF : ℕ → ℕ} (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    ∀ k, k ≤ N → offF k = ∑ i ∈ Finset.range k, degAt G i := by
  intro k
  induction k with
  | zero => intro _; simp [h0]
  | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have hs : offF (k + 1) = offF k + (G.neighborSet ⟨k, hkN⟩).ncard := hstep ⟨k, hkN⟩
      rw [Finset.sum_range_succ, ← ih (by omega), hs, degAt, dif_pos hkN]

/-- **The region's slot space is twice the base orientation's arc
count** — `SolveAugFrameProg` §1's handshake, read at the region's own
last offset. -/
theorem offF_last_eq {N : ℕ} {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)}
    {offF : ℕ → ℕ} (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    offF N = 2 * arcCount (baseOr G π) := by
  rw [offF_eq_sum h0 hstep N le_rfl,
    ← Fin.sum_univ_eq_sum_range (fun i => degAt G i) N,
    show ∑ v : Fin N, degAt G (v : ℕ) = ∑ v : Fin N, (G.neighborSet v).ncard from
      Finset.sum_congr rfl fun v _ => by rw [degAt, dif_pos v.isLt]]
  exact sum_ncard_neighborSet_eq_two_mul_arcCount (baseOr_orients G π)

/-- A neighbourhood is no bigger than the carrier. -/
theorem ncard_neighborSet_le {N : ℕ} (G : SimpleGraph (Fin N)) (v : Fin N) :
    (G.neighborSet v).ncard ≤ N := by
  have h : (G.neighborSet v).ncard ≤ (Set.univ : Set (Fin N)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.finite_univ)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h

/-- The slot space fits in a word: it is at most `N²`. -/
theorem two_mul_arcCount_le_sq {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) : 2 * arcCount (baseOr G π) ≤ N * N := by
  rw [← sum_ncard_neighborSet_eq_two_mul_arcCount (baseOr_orients G π)]
  calc ∑ v : Fin N, (G.neighborSet v).ncard ≤ ∑ _v : Fin N, N :=
        Finset.sum_le_sum fun v _ => ncard_neighborSet_le G v
    _ = N * N := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- **What the orientation pass reads and never writes**: the
adjacency region of `G` and the rank array of `π`, digested into an
offset function and a slot function, together with the three
allocations the pass writes into. -/
structure OrFrame (nN ao aj ra io it cn : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (σ : Env) : Prop where
  /-- The carrier size, in its cell. -/
  carrier : σ.vars nN = N
  /-- The offsets are anchored. -/
  off0 : offF 0 = 0
  /-- One row per vertex, of exactly its degree. -/
  offStep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard
  /-- The offset region holds at least `N + 1` cells. -/
  aoLen : N + 1 ≤ (σ.arrs ao).length
  /-- Reading an offset. -/
  offGet : ∀ i, i ≤ N → (σ.arrs ao)[i]? = some (offF i)
  /-- The slot region holds at least the slot space. -/
  ajLen : offF N ≤ (σ.arrs aj).length
  /-- Reading a slot. -/
  ajGet : ∀ p, p < offF N → (σ.arrs aj)[p]? = some (ajF p)
  /-- Every slot of row `v` holds a neighbour of `v`. -/
  sound : ∀ (v : Fin N) (p : ℕ), offF (v : ℕ) ≤ p → p < offF ((v : ℕ) + 1) →
    ∃ w : Fin N, G.Adj v w ∧ ajF p = (w : ℕ)
  /-- Every neighbour of `v` sits in a slot of row `v`. -/
  complete : ∀ v w : Fin N, G.Adj v w →
    ∃ p, offF (v : ℕ) ≤ p ∧ p < offF ((v : ℕ) + 1) ∧ ajF p = (w : ℕ)
  /-- No two slots of one row hold the same neighbour. -/
  inj : ∀ (v : Fin N) (p r : ℕ), offF (v : ℕ) ≤ p → p < offF ((v : ℕ) + 1) →
    offF (v : ℕ) ≤ r → r < offF ((v : ℕ) + 1) → ajF p = ajF r → p = r
  /-- The rank region holds at least the carrier. -/
  raLen : N ≤ (σ.arrs ra).length
  /-- Reading a rank. -/
  raGet : ∀ i, i < N → (σ.arrs ra)[i]? = some (rankAt π i)
  /-- The output offsets fit. -/
  ioLen : N + 1 ≤ (σ.arrs io).length
  /-- The output targets fit. -/
  itLen : arcCount (baseOr G π) ≤ (σ.arrs it).length
  /-- The counters fit. -/
  cnLen : N ≤ (σ.arrs cn).length

namespace OrFrame

variable {nN ao aj ra io it cn : String} {N : ℕ} {G : SimpleGraph (Fin N)}
  {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ} {σ : Env}

/-- The offsets are monotone below `N`. -/
theorem mono (h : OrFrame nN ao aj ra io it cn G π offF ajF σ) :
    ∀ j, j ≤ N → ∀ i, i ≤ j → offF i ≤ offF j := offF_mono h.offStep

/-- Every offset is inside the slot space. -/
theorem off_le (h : OrFrame nN ao aj ra io it cn G π offF ajF σ) {i : ℕ} (hi : i ≤ N) :
    offF i ≤ offF N := h.mono N le_rfl i hi

/-- The slot space is twice the arc count of the base orientation. -/
theorem slots (h : OrFrame nN ao aj ra io it cn G π offF ajF σ) :
    offF N = 2 * arcCount (baseOr G π) := offF_last_eq h.off0 h.offStep

/-- The pass writes only the three output regions, so the frame
transports along agreement on everything else. -/
theorem of_eq (h : OrFrame nN ao aj ra io it cn G π offF ajF σ) {σ' : Env}
    (hv : σ'.vars nN = σ.vars nN)
    (hao : σ'.arrs ao = σ.arrs ao) (haj : σ'.arrs aj = σ.arrs aj)
    (hra : σ'.arrs ra = σ.arrs ra)
    (hio : (σ'.arrs io).length = (σ.arrs io).length)
    (hit : (σ'.arrs it).length = (σ.arrs it).length)
    (hcn : (σ'.arrs cn).length = (σ.arrs cn).length) :
    OrFrame nN ao aj ra io it cn G π offF ajF σ' :=
  { h with
    carrier := by rw [hv]; exact h.carrier
    aoLen := by rw [hao]; exact h.aoLen
    offGet := by rw [hao]; exact h.offGet
    ajLen := by rw [haj]; exact h.ajLen
    ajGet := by rw [haj]; exact h.ajGet
    raLen := by rw [hra]; exact h.raLen
    raGet := by rw [hra]; exact h.raGet
    ioLen := by rw [hio]; exact h.ioLen
    itLen := by rw [hit]; exact h.itLen
    cnLen := by rw [hcn]; exact h.cnLen }

end OrFrame

/-- **The frame, from the landed regions.**  Hazard: `deleteVerts G ∅`
is not syntactically `G`, so every `S = ∅` clause is discharged as
literally stated, through `deleteVerts_empty`.  Its consequence is
Finding 2: the live prefix of a row is the whole row, so the degree
array is never read. -/
theorem orFrame_of_region {nN ao aj dg mt ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {σ : Env}
    (hcar : σ.vars nN = N)
    (hdel : DelAdjSt ao aj dg mt G ∅ σ) (hra : RankArr ra π σ)
    (hio : N + 1 ≤ (σ.arrs io).length)
    (hit : arcCount (baseOr G π) ≤ (σ.arrs it).length)
    (hcn : N ≤ (σ.arrs cn).length) :
    ∃ offF, OrFrame nN ao aj ra io it cn G π offF (fun p => (σ.arrs aj).getD p 0) σ := by
  classical
  have hinjOn := fun v : Fin N => DelAdjSt.slot_injOn hdel (v := v) (by simp)
  have hraL := hra.1
  obtain ⟨offF, h0, hstep, haoL, haoG, hajL, -, hdgL, -, hdeg, hslot, hcomp⟩ := hdel
  have hdegv : ∀ v : Fin N, (σ.arrs dg).getD (v : ℕ) 0 = (G.neighborSet v).ncard := by
    intro v
    rw [hdeg v (by simp), Lax3Proofs.Impl.deleteVerts_empty]
  have hmono : ∀ j, j ≤ N → ∀ i, i ≤ j → offF i ≤ offF j := offF_mono hstep
  refine ⟨offF, ?_⟩
  refine
    { carrier := hcar
      off0 := h0
      offStep := hstep
      aoLen := haoL
      offGet := ?_
      ajLen := hajL
      ajGet := ?_
      sound := ?_
      complete := ?_
      inj := ?_
      raLen := hra.1
      raGet := ?_
      ioLen := hio
      itLen := hit
      cnLen := hcn }
  · intro i hi
    rw [← haoG i hi]
    exact getElem?_of_lt₃ _ _ (by omega)
  · intro p hp
    exact getElem?_of_lt₃ _ _ (by omega)
  · intro v p hp1 hp2
    have hs := hstep v
    have ht : p - offF (v : ℕ) < (σ.arrs dg).getD (v : ℕ) 0 := by rw [hdegv v]; omega
    obtain ⟨w, hadj, hval, -⟩ := hslot v (by simp) _ ht
    refine ⟨w, ?_, ?_⟩
    · rwa [Lax3Proofs.Impl.deleteVerts_empty] at hadj
    · rw [show offF (v : ℕ) + (p - offF (v : ℕ)) = p from by omega] at hval
      exact hval
  · intro v w hadj
    obtain ⟨t, ht, hval⟩ := hcomp v (by simp) w
      (by rwa [Lax3Proofs.Impl.deleteVerts_empty])
    have hs := hstep v
    rw [hdegv v] at ht
    exact ⟨offF (v : ℕ) + t, Nat.le_add_right _ _, by omega, hval⟩
  · intro v p r hp1 hp2 hr1 hr2 hpr
    obtain ⟨offF', h0', hstep', hinj⟩ := hinjOn v
    have heq : ∀ i, i ≤ N → offF i = offF' i := offF_unique h0 h0' hstep hstep'
    have hv : offF' (v : ℕ) = offF (v : ℕ) := (heq _ (by omega)).symm
    have hs := hstep v
    have hd := hdegv v
    have h1 : p - offF (v : ℕ) ∈ {t : ℕ | t < (σ.arrs dg).getD (v : ℕ) 0} := by
      simp only [Set.mem_setOf_eq, hd]; omega
    have h2 : r - offF (v : ℕ) ∈ {t : ℕ | t < (σ.arrs dg).getD (v : ℕ) 0} := by
      simp only [Set.mem_setOf_eq, hd]; omega
    have := hinj h1 h2 (by
      simp only [hv, show offF (v : ℕ) + (p - offF (v : ℕ)) = p from by omega,
        show offF (v : ℕ) + (r - offF (v : ℕ)) = r from by omega]
      exact hpr)
    omega
  · intro i hi
    have := hra.2 ⟨i, hi⟩
    rw [rankAt, dif_pos hi, ← this]
    exact getElem?_of_lt₃ _ _ (by omega)

/-! ## §4 What the count sweep counts

The qualifying slots of a source row — the neighbours of `v` that
precede it in the ranking — are in bijection with `(baseOr G π).inN v`.
This is the only real content of the count phase. -/

/-- The qualifying slots of `[lo, hi)`: those whose neighbour outranks
`rv`. -/
def orCnt (ajF : ℕ → ℕ) {N : ℕ} (π : Equiv.Perm (Fin N)) (rv lo hi : ℕ) : ℕ :=
  ((Finset.Ico lo hi).filter (fun q => rankAt π (ajF q) < rv)).card

theorem orCnt_self (ajF : ℕ → ℕ) {N : ℕ} (π : Equiv.Perm (Fin N)) (rv lo : ℕ) :
    orCnt ajF π rv lo lo = 0 := by simp [orCnt]

theorem orCnt_succ (ajF : ℕ → ℕ) {N : ℕ} (π : Equiv.Perm (Fin N)) (rv lo hi : ℕ)
    (h : lo ≤ hi) :
    orCnt ajF π rv lo (hi + 1)
      = orCnt ajF π rv lo hi + (if rankAt π (ajF hi) < rv then 1 else 0) := by
  have hins : Finset.Ico lo (hi + 1) = insert hi (Finset.Ico lo hi) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [orCnt, orCnt, hins, Finset.filter_insert]
  by_cases hc : rankAt π (ajF hi) < rv
  · rw [if_pos hc, if_pos hc, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg hc, if_neg hc, Nat.add_zero]

theorem orCnt_mono (ajF : ℕ → ℕ) {N : ℕ} (π : Equiv.Perm (Fin N)) (rv lo : ℕ)
    {a b : ℕ} (hab : a ≤ b) : orCnt ajF π rv lo a ≤ orCnt ajF π rv lo b := by
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro x hx
  simp only [Finset.mem_Ico] at hx ⊢
  omega

theorem orCnt_le (ajF : ℕ → ℕ) {N : ℕ} (π : Equiv.Perm (Fin N)) (rv lo hi : ℕ) :
    orCnt ajF π rv lo hi ≤ hi - lo := by
  have := Finset.card_filter_le (Finset.Ico lo hi) (fun q => rankAt π (ajF q) < rv)
  simpa [orCnt] using this

/-- **The count is the in-degree.**  The qualifying slots of row `v` and
the in-neighbours of `v` in `baseOr G π` are in bijection: the region's
`sound` sends a slot to a neighbour, its `complete` sends a neighbour
back, and `inj` says a neighbour occupies one slot. -/
theorem orCnt_row {nN ao aj ra io it cn : String} {N : ℕ} {G : SimpleGraph (Fin N)}
    {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ} {σ : Env}
    (h : OrFrame nN ao aj ra io it cn G π offF ajF σ) (v : Fin N) :
    orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) (offF ((v : ℕ) + 1))
      = ((baseOr G π).inN v).card := by
  classical
  have hinj : Set.InjOn ajF
      ↑((Finset.Ico (offF (v : ℕ)) (offF ((v : ℕ) + 1))).filter
        (fun q => rankAt π (ajF q) < rankAt π (v : ℕ))) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at ha hb
    exact h.inj v a b ha.1.1 ha.1.2 hb.1.1 hb.1.2 hab
  have himg : ((Finset.Ico (offF (v : ℕ)) (offF ((v : ℕ) + 1))).filter
        (fun q => rankAt π (ajF q) < rankAt π (v : ℕ))).image ajF
      = ((baseOr G π).inN v).image (fun w : Fin N => (w : ℕ)) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨q, ⟨⟨hq1, hq2⟩, hrk⟩, rfl⟩
      obtain ⟨w, hadj, hw⟩ := h.sound v q hq1 hq2
      refine ⟨w, ?_, hw.symm⟩
      rw [mem_baseOr]
      refine ⟨hadj.symm, ?_⟩
      rw [Fin.lt_def, ← rankAt_coe π w, ← rankAt_coe π v, ← hw]
      exact hrk
    · rintro ⟨w, hw, rfl⟩
      rw [mem_baseOr] at hw
      obtain ⟨hadj, hlt⟩ := hw
      obtain ⟨q, hq1, hq2, hq3⟩ := h.complete v w hadj.symm
      refine ⟨q, ⟨⟨hq1, hq2⟩, ?_⟩, hq3⟩
      rw [hq3, rankAt_coe, rankAt_coe]
      exact Fin.lt_def.1 hlt
  calc orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) (offF ((v : ℕ) + 1))
      = ((Finset.Ico (offF (v : ℕ)) (offF ((v : ℕ) + 1))).filter
          (fun q => rankAt π (ajF q) < rankAt π (v : ℕ))).card := rfl
    _ = (((Finset.Ico (offF (v : ℕ)) (offF ((v : ℕ) + 1))).filter
          (fun q => rankAt π (ajF q) < rankAt π (v : ℕ))).image ajF).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ = (((baseOr G π).inN v).image (fun w : Fin N => (w : ℕ))).card := by rw [himg]
    _ = ((baseOr G π).inN v).card :=
        Finset.card_image_of_injective _ Fin.val_injective

/-! ## §5 The program

Three sweeps.  Nothing reads an array length: the carrier is the cell
`nN`, the source slot count is `ao[nN]` (never needed, since each row is
bounded by `ao[v+1]`), and the output slot count is produced by the
prefix sweep into `nA` (Finding 3). -/

/-- The pass's scratch scalars: the vertex counter, the slot pointer and
its row end, the row accumulator, the rank of the current head, the
neighbour read out of a slot, the running sum, and the output cursor. -/
def orScalars : List String :=
  ["or.v", "or.j", "or.f", "or.d", "or.r", "or.u", "or.a", "or.c"]

private theorem orScalars_ne {y : String} (h : y ∉ orScalars) :
    y ≠ "or.v" ∧ y ≠ "or.j" ∧ y ≠ "or.f" ∧ y ≠ "or.d" ∧ y ≠ "or.r" ∧
      y ≠ "or.u" ∧ y ≠ "or.a" ∧ y ≠ "or.c" := by
  simp only [orScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- The names the pass keeps apart: it writes `io`, `it` and `cn`, and
reads `ao`, `aj` and `ra`. -/
structure OrNames (ao aj ra io it cn : String) : Prop where
  /-- The counters are not the region's offsets. -/
  cn_ao : cn ≠ ao
  /-- The counters are not the region's slots. -/
  cn_aj : cn ≠ aj
  /-- The counters are not the ranks. -/
  cn_ra : cn ≠ ra
  /-- The output offsets are not the region's offsets. -/
  io_ao : io ≠ ao
  /-- The output offsets are not the region's slots. -/
  io_aj : io ≠ aj
  /-- The output offsets are not the ranks. -/
  io_ra : io ≠ ra
  /-- The output offsets are not the counters. -/
  io_cn : io ≠ cn
  /-- The output targets are not the region's offsets. -/
  it_ao : it ≠ ao
  /-- The output targets are not the region's slots. -/
  it_aj : it ≠ aj
  /-- The output targets are not the ranks. -/
  it_ra : it ≠ ra
  /-- The output targets are not the counters. -/
  it_cn : it ≠ cn
  /-- The two output regions are distinct. -/
  it_io : it ≠ io

/-- One inner turn of the count: read the neighbour, bump the row
accumulator if it outranks the head, advance. -/
def orCntIn (aj ra : String) : Com :=
  .seq (.assign "or.u" (.get aj (.var "or.j")))
    (.seq (.ite (.lt (.get ra (.var "or.u")) (.var "or.r"))
        (.assign "or.d" (.add (.var "or.d") (.lit 1))) .skip)
      (.assign "or.j" (.add (.var "or.j") (.lit 1))))

/-- One outer turn of the count: load the head's row and its rank, scan
the row, store the in-degree. -/
def orCntOut (ao aj ra cn : String) : Com :=
  .seq (.assign "or.j" (.get ao (.var "or.v")))
    (.seq (.assign "or.f" (.get ao (.add (.var "or.v") (.lit 1))))
      (.seq (.assign "or.r" (.get ra (.var "or.v")))
        (.seq (.assign "or.d" (.lit 0))
          (.seq (Csr.scan "or.j" "or.f" (orCntIn aj ra))
            (.seq (.store cn (.var "or.v") (.var "or.d"))
              (.assign "or.v" (.add (.var "or.v") (.lit 1))))))))

/-- **The count sweep**: `cn[v]` ends at `v`'s in-degree in
`baseOr G π`. -/
def orCntCom (nN ao aj ra cn : String) : Com :=
  .seq (.assign "or.v" (.lit 0)) (Csr.scan "or.v" nN (orCntOut ao aj ra cn))

/-- **The prefix sweep**: the in-degrees become the row starts, and the
total — the arc count — lands in `nA` and in the last offset. -/
def orOffCom (nN nA io cn : String) : Com :=
  .seq (.assign "or.a" (.lit 0))
    (.seq
      (.seq (.assign "or.v" (.lit 0))
        (Csr.scan "or.v" nN
          (.seq (.store io (.var "or.v") (.var "or.a"))
            (.seq (.assign "or.a" (.add (.var "or.a") (.get cn (.var "or.v"))))
              (.assign "or.v" (.add (.var "or.v") (.lit 1)))))))
      (.seq (.store io (.var nN) (.var "or.a")) (.assign nA (.var "or.a"))))

/-- One inner turn of the scatter: read the neighbour, and if it
outranks the head append it to the head's row. -/
def orScatIn (aj ra it : String) : Com :=
  .seq (.assign "or.u" (.get aj (.var "or.j")))
    (.seq (.ite (.lt (.get ra (.var "or.u")) (.var "or.r"))
        (.seq (.store it (.var "or.c") (.var "or.u"))
          (.assign "or.c" (.add (.var "or.c") (.lit 1)))) .skip)
      (.assign "or.j" (.add (.var "or.j") (.lit 1))))

/-- One outer turn of the scatter: the cursor starts at the row's own
offset, so no cursor array exists. -/
def orScatOut (ao aj ra io it : String) : Com :=
  .seq (.assign "or.j" (.get ao (.var "or.v")))
    (.seq (.assign "or.f" (.get ao (.add (.var "or.v") (.lit 1))))
      (.seq (.assign "or.r" (.get ra (.var "or.v")))
        (.seq (.assign "or.c" (.get io (.var "or.v")))
          (.seq (Csr.scan "or.j" "or.f" (orScatIn aj ra it))
            (.assign "or.v" (.add (.var "or.v") (.lit 1)))))))

/-- **The scatter**: heads in increasing order, each head's whole row
before the next. -/
def orScatCom (nN ao aj ra io it : String) : Com :=
  .seq (.assign "or.v" (.lit 0)) (Csr.scan "or.v" nN (orScatOut ao aj ra io it))

/-- **The orientation pass**: count, prefix-sum, scatter. -/
def orCom (nN nA ao aj ra io it cn : String) : Com :=
  .seq (orCntCom nN ao aj ra cn)
    (.seq (orOffCom nN nA io cn) (orScatCom nN ao aj ra io it))

/-- **The pass's budget** at `(N, a)` with `a = arcCount (baseOr G π)`:
`28` a vertex in the count sweep, `16` in the prefix sweep and `26` in
the scatter; `20` a source slot in the count and `23` in the scatter,
and the source slot space is `2a`. -/
def orK (N a : ℕ) : ℕ := 70 * N + 86 * a + 25

/-! ## §6 The count sweep -/

/-- The carried state of one outer turn of the count: the frame, the
counters below the head, the head's row bounds and rank, and the row
accumulator at the pointer. -/
private def OrCntI (nN ao aj ra io it cn : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (k : ℕ) (σ : Env) : Prop :=
  OrFrame nN ao aj ra io it cn G π offF ajF σ ∧
    (∀ i, i < k → (σ.arrs cn).getD i 0 = inDegAt (baseOr G π) i) ∧
    σ.vars "or.v" = k ∧ σ.vars "or.f" = offF (k + 1) ∧
    σ.vars "or.r" = rankAt π k ∧
    offF k ≤ σ.vars "or.j" ∧ σ.vars "or.j" ≤ offF (k + 1) ∧
    σ.vars "or.d" = orCnt ajF π (rankAt π k) (offF k) (σ.vars "or.j")

/-- The carried state of the count's outer scan. -/
private def OrCntO (nN ao aj ra io it cn : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (σ : Env) : Prop :=
  OrFrame nN ao aj ra io it cn G π offF ajF σ ∧ σ.vars "or.v" ≤ N ∧
    ∀ i, i < σ.vars "or.v" → (σ.arrs cn).getD i 0 = inDegAt (baseOr G π) i

/-- The rank test, run once: the `ite` both sweeps turn on, with its
branch cost bounded and its effect named. -/
private theorem orTest {B : ℕ} {ra : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {u r : ℕ} {σ : Env} {c d : Com} {Kb : ℕ} {Q : Env → Prop}
    (hu : σ.vars "or.u" = u) (hr : σ.vars "or.r" = r) (huN : u < N) (hNB : N < B)
    (hrB : r < B)
    (hraG : ∀ i, i < N → (σ.arrs ra)[i]? = some (rankAt π i))
    (ht : rankAt π u < r → ∃ σ' K', Run B c σ σ' K' ∧ K' ≤ Kb ∧ Q σ')
    (hf : ¬ rankAt π u < r → ∃ σ' K', Run B d σ σ' K' ∧ K' ≤ Kb ∧ Q σ') :
    ∃ σ' K', Run B (.ite (.lt (.get ra (.var "or.u")) (.var "or.r")) c d) σ σ' K' ∧
      K' ≤ 5 + Kb ∧ Q σ' := by
  have hrk : rankAt π u < N := rankAt_lt π huN
  have hev : (Cond.lt (.get ra (.var "or.u")) (.var "or.r")).evalB B σ
      = some (decide (rankAt π u < r)) :=
    evalB_condLt (evB_get₃ (evB_var₃ hu (by omega)) (hraG u huN) (by omega))
      (evB_var₃ hr hrB)
  by_cases hc : rankAt π u < r
  · obtain ⟨σ', K', hrun, hK, hQ⟩ := ht hc
    refine ⟨σ', 1 + 4 + K', ?_, by omega, hQ⟩
    have h := Run.ite_true (b := Cond.lt (.get ra (.var "or.u")) (.var "or.r")) (d := d)
      (by rw [hev]; simp [hc]) hrun
    simpa using h
  · obtain ⟨σ', K', hrun, hK, hQ⟩ := hf hc
    refine ⟨σ', 1 + 4 + K', ?_, by omega, hQ⟩
    have h := Run.ite_false (b := Cond.lt (.get ra (.var "or.u")) (.var "or.r")) (c := c)
      (by rw [hev]; simp [hc]) hrun
    simpa using h

/-- Writing a scalar's own value changes nothing — what the untaken
branch of the rank test leaves. -/
private theorem setVar_self (σ : Env) (x : String) : σ.setVar x (σ.vars x) = σ := by
  obtain ⟨vs, as, i, o⟩ := σ
  simp only [Env.setVar]
  congr 1
  funext y
  by_cases h : y = x
  · rw [if_pos h, h]
  · rw [if_neg h]

/-- **One inner turn of the count**, at `16`. -/
private theorem orCntIn_step {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    {k : ℕ} {σ : Env} (hnN : nN ∉ orScalars) (hk : k < N) (hB : N * N + N < B)
    (hI : OrCntI nN ao aj ra io it cn G π offF ajF k σ)
    (hlt : σ.vars "or.j" < offF (k + 1)) :
    ∃ σ' K', Run B (orCntIn aj ra) σ σ' K' ∧
      OrCntI nN ao aj ra io it cn G π offF ajF k σ' ∧
      σ'.vars "or.j" = σ.vars "or.j" + 1 ∧ K' ≤ 16 := by
  obtain ⟨-, hj0, -, hd0, -, hu0, -, -⟩ := orScalars_ne hnN
  obtain ⟨hfr, hcnv, hvv, hfv, hrv, hj1, hj2, hdv⟩ := hI
  obtain ⟨j, hjeq⟩ : ∃ j, σ.vars "or.j" = j := ⟨_, rfl⟩
  rw [hjeq] at hj1 hj2 hdv hlt
  have hslots : offF N = 2 * arcCount (baseOr G π) := hfr.slots
  have harc : 2 * arcCount (baseOr G π) ≤ N * N := two_mul_arcCount_le_sq G π
  have hoff1 : offF (k + 1) ≤ offF N := hfr.off_le (by omega)
  have hNB : N < B := by omega
  have hoffB : offF N < B := by omega
  have hrkB : rankAt π k < B := by have := rankAt_lt π hk; omega
  obtain ⟨w, -, hw⟩ := hfr.sound ⟨k, hk⟩ j hj1 hlt
  have huN : ajF j < N := by rw [hw]; exact w.isLt
  have hcle : orCnt ajF π (rankAt π k) (offF k) j ≤ j - offF k :=
    orCnt_le ajF π (rankAt π k) (offF k) j
  -- `or.u := aj[or.j]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "or.u" (ajF j) := ⟨_, rfl⟩
  have r1 : Run B (.assign "or.u" (.get aj (.var "or.j"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign₃ (evB_get₃ (evB_var₃ hjeq (by omega))
      (hfr.ajGet j (by omega)) (by omega)) (by simp)
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  have h1u : σ1.vars "or.u" = ajF j := by rw [hσ1]; simp
  have h1r : σ1.vars "or.r" = rankAt π k := by rw [hσ1]; simp [hrv]
  have h1d : σ1.vars "or.d" = orCnt ajF π (rankAt π k) (offF k) j := by
    rw [hσ1]; simp [hdv]
  have h1j : σ1.vars "or.j" = j := by rw [hσ1]; simp [hjeq]
  -- the rank test
  have htrue : rankAt π (ajF j) < rankAt π k →
      ∃ τ K', Run B (.assign "or.d" (.add (.var "or.d") (.lit 1))) σ1 τ K' ∧ K' ≤ 4 ∧
        τ = σ1.setVar "or.d" (orCnt ajF π (rankAt π k) (offF k) j
          + (if rankAt π (ajF j) < rankAt π k then 1 else 0)) := by
    intro hc
    exact ⟨_, 4, run_assign₃ (evB_add₃ (evB_var₃ h1d (by omega)) (evB_lit₃ (by omega))
      (by omega)) (by simp), le_rfl, by rw [if_pos hc]⟩
  have hfalse : ¬ rankAt π (ajF j) < rankAt π k →
      ∃ τ K', Run B .skip σ1 τ K' ∧ K' ≤ 4 ∧
        τ = σ1.setVar "or.d" (orCnt ajF π (rankAt π k) (offF k) j
          + (if rankAt π (ajF j) < rankAt π k then 1 else 0)) := by
    intro hc
    refine ⟨σ1, 1, Run.skip, by omega, ?_⟩
    rw [if_neg hc, Nat.add_zero, ← h1d, setVar_self]
  obtain ⟨σ2, K2, r2, hK2, hσ2⟩ := orTest h1u h1r huN hNB hrkB
    (by rw [h1a]; exact hfr.raGet) htrue hfalse
  -- `or.j := or.j + 1`
  have h2j : σ2.vars "or.j" = j := by rw [hσ2]; simp [h1j]
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "or.j" (j + 1) := ⟨_, rfl⟩
  have r3 : Run B (.assign "or.j" (.add (.var "or.j") (.lit 1))) σ2 σ3 4 := by
    rw [hσ3]
    exact run_assign₃ (evB_add₃ (evB_var₃ h2j (by omega)) (evB_lit₃ (by omega))
      (by omega)) (by simp)
  have h3a : σ3.arrs = σ.arrs := by rw [hσ3, hσ2, hσ1]; simp
  refine ⟨σ3, 3 + (K2 + 4), r1.seq (r2.seq r3),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hσ3]; simp [hjeq], by omega⟩
  · exact hfr.of_eq (by rw [hσ3, hσ2, hσ1]; simp [hj0, hd0, hu0]) (by rw [h3a])
      (by rw [h3a]) (by rw [h3a]) (by rw [h3a]) (by rw [h3a]) (by rw [h3a])
  · intro i hi; rw [h3a]; exact hcnv i hi
  · rw [hσ3, hσ2, hσ1]; simp [hvv]
  · rw [hσ3, hσ2, hσ1]; simp [hfv]
  · rw [hσ3, hσ2, hσ1]; simp [hrv]
  · rw [hσ3]; simp; omega
  · rw [hσ3]; simp; omega
  · rw [hσ3, hσ2]
    simp only [vars_setVar, String.reduceEq, if_false, if_true, h1d]
    rw [orCnt_succ ajF π (rankAt π k) (offF k) j hj1]

/-- **The count's inner scan**: `20` a source slot. -/
private theorem orCntIn_scan {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    {k : ℕ} (hnN : nN ∉ orScalars) (hk : k < N) (hB : N * N + N < B)
    (hoffB : offF (k + 1) < B) :
    Spec B (fun σ => OrCntI nN ao aj ra io it cn G π offF ajF k σ ∧
        σ.vars "or.j" = offF k)
      (Csr.scan "or.j" "or.f" (orCntIn aj ra))
      (fun _ σ' => OrCntI nN ao aj ra io it cn G π offF ajF k σ' ∧
        σ'.vars "or.j" = offF (k + 1))
      (20 * (offF (k + 1) - offF k) + 4) :=
  Csr.rowScan_spec B _ (offF (k + 1)) 16 "or.j" "or.f" (orCntIn aj ra)
    (fun σ => OrCntI nN ao aj ra io it cn G π offF ajF k σ) hoffB
    (fun _ hI => ⟨hI.2.2.2.1, hI.2.2.2.2.2.2.1⟩)
    (fun _ hI hlt => orCntIn_step hnN hk hB hI hlt)
    (fun _ h => h.1) (fun _ h => by simp only [h.2]; omega)

/-- **One outer turn of the count**: load the row and the head's rank,
scan the row, store the in-degree. -/
private theorem orCntOut_step {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    {σ : Env} (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars)
    (hB : N * N + N < B)
    (hO : OrCntO nN ao aj ra io it cn G π offF ajF σ) (hlt : σ.vars "or.v" < N) :
    ∃ σ' K', Run B (orCntOut ao aj ra cn) σ σ' K' ∧
      OrCntO nN ao aj ra io it cn G π offF ajF σ' ∧
      σ'.vars "or.v" = σ.vars "or.v" + 1 ∧
      K' ≤ 24 + 20 * (offF (σ.vars "or.v" + 1) - offF (σ.vars "or.v")) := by
  obtain ⟨hv0, hj0, hf0, hd0, hr0, -, -, -⟩ := orScalars_ne hnN
  obtain ⟨hfr, hvle, hcnv⟩ := hO
  obtain ⟨k, hkeq⟩ : ∃ k, σ.vars "or.v" = k := ⟨_, rfl⟩
  rw [hkeq] at hvle hcnv hlt
  have hslots : offF N = 2 * arcCount (baseOr G π) := hfr.slots
  have harc : 2 * arcCount (baseOr G π) ≤ N * N := two_mul_arcCount_le_sq G π
  have hoffk : offF k ≤ offF N := hfr.off_le (by omega)
  have hoff1 : offF (k + 1) ≤ offF N := hfr.off_le (by omega)
  have hmono : offF k ≤ offF (k + 1) := hfr.mono (k + 1) hlt k (by omega)
  have hNB : N < B := by omega
  have hoffB : offF N < B := by omega
  have hrkB : rankAt π k < B := by have := rankAt_lt π hlt; omega
  -- `or.j := ao[or.v]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "or.j" (offF k) := ⟨_, rfl⟩
  have r1 : Run B (.assign "or.j" (.get ao (.var "or.v"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign₃ (evB_get₃ (evB_var₃ hkeq (by omega)) (hfr.offGet k (by omega))
      (by omega)) (by simp)
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  have h1v : σ1.vars "or.v" = k := by rw [hσ1]; simp [hkeq]
  -- `or.f := ao[or.v + 1]`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "or.f" (offF (k + 1)) := ⟨_, rfl⟩
  have r2 : Run B (.assign "or.f" (.get ao (.add (.var "or.v") (.lit 1)))) σ1 σ2 5 := by
    rw [hσ2]
    refine run_assign₃ (evB_get₃ (evB_add₃ (evB_var₃ h1v (by omega))
      (evB_lit₃ (by omega)) (by omega)) ?_ (by omega)) (by simp)
    rw [h1a]; exact hfr.offGet (k + 1) (by omega)
  have h2a : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  have h2v : σ2.vars "or.v" = k := by rw [hσ2]; simp [h1v]
  -- `or.r := ra[or.v]`
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "or.r" (rankAt π k) := ⟨_, rfl⟩
  have r3 : Run B (.assign "or.r" (.get ra (.var "or.v"))) σ2 σ3 3 := by
    rw [hσ3]
    refine run_assign₃ (evB_get₃ (evB_var₃ h2v (by omega)) ?_ (by omega)) (by simp)
    rw [h2a]; exact hfr.raGet k hlt
  -- `or.d := 0`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setVar "or.d" 0 := ⟨_, rfl⟩
  have r4 : Run B (.assign "or.d" (.lit 0)) σ3 σ4 2 := by
    rw [hσ4]; exact run_assign₃ (evB_lit₃ (by omega)) (by simp)
  have h4a : σ4.arrs = σ.arrs := by rw [hσ4, hσ3, hσ2, hσ1]; simp
  have h4n : σ4.vars nN = σ.vars nN := by
    rw [hσ4, hσ3, hσ2, hσ1]; simp [hj0, hf0, hd0, hr0]
  have h4j : σ4.vars "or.j" = offF k := by rw [hσ4, hσ3, hσ2, hσ1]; simp
  have h4v : σ4.vars "or.v" = k := by rw [hσ4, hσ3, hσ2, hσ1]; simp [hkeq]
  have h4f : σ4.vars "or.f" = offF (k + 1) := by rw [hσ4, hσ3, hσ2]; simp
  have h4r : σ4.vars "or.r" = rankAt π k := by rw [hσ4, hσ3]; simp
  have h4d : σ4.vars "or.d" = 0 := by rw [hσ4]; simp
  have hI4 : OrCntI nN ao aj ra io it cn G π offF ajF k σ4 ∧ σ4.vars "or.j" = offF k := by
    refine ⟨⟨hfr.of_eq h4n (by rw [h4a]) (by rw [h4a]) (by rw [h4a]) (by rw [h4a])
        (by rw [h4a]) (by rw [h4a]), ?_, h4v, h4f, h4r, ?_, ?_, ?_⟩, h4j⟩
    · intro i hi; rw [h4a]; exact hcnv i hi
    · rw [h4j]
    · rw [h4j]; exact hmono
    · rw [h4j, h4d, orCnt_self]
  obtain ⟨σ5, r5, hI5, hj5⟩ :=
    (orCntIn_scan (nN := nN) (ao := ao) (io := io) (it := it) (cn := cn)
      hnN hlt hB (by omega)).run hI4
  obtain ⟨hfr5, hcnv5, h5v, -, -, -, -, h5d⟩ := hI5
  rw [hj5] at h5d
  -- `cn[or.v] := or.d`
  have hdle : orCnt ajF π (rankAt π k) (offF k) (offF (k + 1)) ≤ offF (k + 1) - offF k :=
    orCnt_le ajF π (rankAt π k) (offF k) (offF (k + 1))
  have h5cn : k < (σ5.arrs cn).length := lt_of_lt_of_le hlt hfr5.cnLen
  obtain ⟨σ6, hσ6⟩ : ∃ τ, τ = σ5.setArr cn k
      (orCnt ajF π (rankAt π k) (offF k) (offF (k + 1))) := ⟨_, rfl⟩
  have r6 : Run B (.store cn (.var "or.v") (.var "or.d")) σ5 σ6 3 := by
    rw [hσ6]
    exact run_store₃ (evB_var₃ h5v (by omega)) (evB_var₃ h5d (by omega)) h5cn (by simp)
  have h6v : σ6.vars "or.v" = k := by rw [hσ6]; simp [h5v]
  -- `or.v := or.v + 1`
  obtain ⟨σ7, hσ7⟩ : ∃ τ, τ = σ6.setVar "or.v" (k + 1) := ⟨_, rfl⟩
  have r7 : Run B (.assign "or.v" (.add (.var "or.v") (.lit 1))) σ6 σ7 4 := by
    rw [hσ7]
    exact run_assign₃ (evB_add₃ (evB_var₃ h6v (by omega)) (evB_lit₃ (by omega))
      (by omega)) (by simp)
  have h7a : ∀ b, σ7.arrs b = σ6.arrs b := by intro b; rw [hσ7]; simp
  have h7v : σ7.vars "or.v" = k + 1 := by rw [hσ7]; simp
  have h7cn : σ7.arrs cn = (σ5.arrs cn).set k
      (orCnt ajF π (rankAt π k) (offF k) (offF (k + 1))) := by
    rw [hσ7, hσ6]; simp
  refine ⟨σ7, 3 + (5 + (3 + (2 + ((20 * (offF (k + 1) - offF k) + 4) + (3 + 4))))),
    r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7))))), ⟨?_, ?_, ?_⟩,
    by rw [h7v, hkeq], by rw [hkeq]; omega⟩
  · refine hfr5.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hσ7, hσ6]; simp [hv0]
    · rw [h7a, hσ6]; simp [Ne.symm hnm.cn_ao]
    · rw [h7a, hσ6]; simp [Ne.symm hnm.cn_aj]
    · rw [h7a, hσ6]; simp [Ne.symm hnm.cn_ra]
    · rw [h7a, hσ6]; simp only [length_arrs_setArr]
    · rw [h7a, hσ6]; simp only [length_arrs_setArr]
    · rw [h7a, hσ6]; simp only [length_arrs_setArr]
  · rw [h7v]; omega
  · intro i hi
    rw [h7v] at hi
    rw [h7cn]
    by_cases hik : i = k
    · subst hik
      rw [getD_set_self₃ h5cn, inDegAt, dif_pos hlt]
      exact orCnt_row hfr5 ⟨i, hlt⟩
    · rw [getD_set_of_ne₃ (Ne.symm hik)]
      exact hcnv5 i (by omega)

/-- **The count's outer scan**: `28` a vertex and `20` a source slot. -/
private theorem orCnt_scan {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars) (hB : N * N + N < B) :
    Spec B (fun σ => OrCntO nN ao aj ra io it cn G π offF ajF σ ∧ σ.vars "or.v" = 0)
      (Csr.scan "or.v" nN (orCntOut ao aj ra cn))
      (fun _ σ' => OrCntO nN ao aj ra io it cn G π offF ajF σ' ∧ σ'.vars "or.v" = N)
      (28 * N + 20 * offF N + 4) := by
  have hNB : N < B := by omega
  refine (Spec.while_potential (b := .lt (.var "or.v") (.var nN))
    (fun σ => OrCntO nN ao aj ra io it cn G π offF ajF σ)
    (fun σ => 28 * (N - σ.vars "or.v") + 20 * (offF N - offF (σ.vars "or.v")))
    (fun σ hO => evalB_condLt_vars (by have := hO.2.1; omega)
      (by have := hO.1.carrier; omega)) ?_ (fun σ h => h.1) ?_).post ?_
  · intro σ hO hc
    have hlt : σ.vars "or.v" < N := by
      have h1 := lt_of_condLt_true hc
      have h2 := hO.1.carrier
      omega
    obtain ⟨σ', K', hrun, hO', hv', hK'⟩ := orCntOut_step hnm hnN hB hO hlt
    refine ⟨σ', K', hrun, hO', ?_⟩
    have hm : offF (σ.vars "or.v") ≤ offF (σ.vars "or.v" + 1) :=
      hO.1.mono (σ.vars "or.v" + 1) hlt (σ.vars "or.v") (by omega)
    have hle : offF (σ.vars "or.v" + 1) ≤ offF N := hO.1.off_le hlt
    simp only [size_condLt, size_var]
    rw [hv']
    omega
  · intro σ h
    have hz := h.2
    have h0 : offF 0 = 0 := h.1.1.off0
    simp only [size_condLt, size_var]
    rw [hz, h0]
    omega
  · rintro σ σ' - ⟨hO', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hO'.1.carrier
    have h3 := hO'.2.1
    exact ⟨hO', by omega⟩

/-- **The count sweep, discharged**: `cn[v]` ends at `v`'s in-degree in
`baseOr G π`. -/
private theorem orCnt_spec {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars) (hB : N * N + N < B) :
    Spec B (fun σ => OrFrame nN ao aj ra io it cn G π offF ajF σ)
      (orCntCom nN ao aj ra cn)
      (fun _ σ' => OrFrame nN ao aj ra io it cn G π offF ajF σ' ∧
        ∀ i, i < N → (σ'.arrs cn).getD i 0 = inDegAt (baseOr G π) i)
      (28 * N + 20 * offF N + 6) := by
  obtain ⟨hv0, -, -, -, -, -, -, -⟩ := orScalars_ne hnN
  have hNB : N < B := by omega
  have hstart : Spec B (fun σ => OrFrame nN ao aj ra io it cn G π offF ajF σ)
      (.assign "or.v" (.lit 0))
      (fun _ σ' => OrCntO nN ao aj ra io it cn G π offF ajF σ' ∧ σ'.vars "or.v" = 0) 2 := by
    refine Spec.of_exists (fun σ hfr => ?_)
    refine ⟨_, 2, run_assign₃ (evB_lit₃ (by omega)) (by simp), le_rfl, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact hfr.of_eq (by simp [hv0]) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp)
    · simp
    · intro i hi
      simp only [vars_setVar] at hi
      exact absurd hi (Nat.not_lt_zero i)
    · simp
  refine ((Spec.seq hstart (orCnt_scan hnm hnN hB) (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => ?_)).mono (by omega))
  obtain ⟨⟨hfr, -, hcnv⟩, hend⟩ := hq
  rw [hend] at hcnv
  exact ⟨hfr, hcnv⟩

/-! ## §7 The prefix sweep

The in-degrees become the row starts, and the total — the arc count —
lands both in the last offset and in the cell `nA`.  It is a *result* of
the pass, so nothing reads it beforehand (Finding 3). -/

/-- The carried state of the prefix sweep: below the counter `io` holds
the offsets, the running sum is the offset at the counter, and `cn`
still holds the degrees. -/
private def OrOffI (nN ao aj ra io it cn : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (σ : Env) : Prop :=
  OrFrame nN ao aj ra io it cn G π offF ajF σ ∧ σ.vars "or.v" ≤ N ∧
    σ.vars "or.a" = inOff (baseOr G π) (σ.vars "or.v") ∧
    (∀ i, i < σ.vars "or.v" → (σ.arrs io).getD i 0 = inOff (baseOr G π) i) ∧
    (∀ i, i < N → (σ.arrs cn).getD i 0 = inDegAt (baseOr G π) i)

/-- **One turn of the prefix sweep**, at `12`. -/
private theorem orOff_body {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars) (hB : N * N + N < B) :
    Spec B (fun σ => OrOffI nN ao aj ra io it cn G π offF ajF σ ∧ σ.vars "or.v" < N)
      (.seq (.store io (.var "or.v") (.var "or.a"))
        (.seq (.assign "or.a" (.add (.var "or.a") (.get cn (.var "or.v"))))
          (.assign "or.v" (.add (.var "or.v") (.lit 1)))))
      (fun σ σ' => OrOffI nN ao aj ra io it cn G π offF ajF σ' ∧
        σ'.vars "or.v" = σ.vars "or.v" + 1) 12 := by
  obtain ⟨hv0, -, -, -, -, -, ha0, -⟩ := orScalars_ne hnN
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hfr, hvle, hav, hiov, hcnv⟩, hlt⟩ := hσ
  obtain ⟨k, hkeq⟩ : ∃ k, σ.vars "or.v" = k := ⟨_, rfl⟩
  rw [hkeq] at hvle hav hiov hlt
  have harc : 2 * arcCount (baseOr G π) ≤ N * N := two_mul_arcCount_le_sq G π
  have hNB : N < B := by omega
  have hik : inOff (baseOr G π) k ≤ arcCount (baseOr G π) := inOff_le_arcCount _ (by omega)
  have hik1 : inOff (baseOr G π) (k + 1) ≤ arcCount (baseOr G π) :=
    inOff_le_arcCount _ (by omega)
  have hsucc : inOff (baseOr G π) (k + 1)
      = inOff (baseOr G π) k + inDegAt (baseOr G π) k := inOff_succ _ _
  have hioL : k < (σ.arrs io).length := by have := hfr.ioLen; omega
  have hcnL : k < (σ.arrs cn).length := by have := hfr.cnLen; omega
  have hcnget : (σ.arrs cn)[k]? = some (inDegAt (baseOr G π) k) := by
    rw [← hcnv k hlt]; exact getElem?_of_lt₃ _ _ hcnL
  -- `io[or.v] := or.a`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setArr io k (inOff (baseOr G π) k) := ⟨_, rfl⟩
  have r1 : Run B (.store io (.var "or.v") (.var "or.a")) σ σ1 3 := by
    rw [hσ1]
    exact run_store₃ (evB_var₃ hkeq (by omega)) (evB_var₃ hav (by omega)) hioL (by simp)
  have h1v : σ1.vars "or.v" = k := by rw [hσ1]; simp [hkeq]
  have h1a : σ1.vars "or.a" = inOff (baseOr G π) k := by rw [hσ1]; simp [hav]
  have h1cn : σ1.arrs cn = σ.arrs cn := by rw [hσ1]; simp [Ne.symm hnm.io_cn]
  -- `or.a := or.a + cn[or.v]`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "or.a"
      (inOff (baseOr G π) k + inDegAt (baseOr G π) k) := ⟨_, rfl⟩
  have r2 : Run B (.assign "or.a" (.add (.var "or.a") (.get cn (.var "or.v")))) σ1 σ2 5 := by
    rw [hσ2]
    refine run_assign₃ (evB_add₃ (evB_var₃ h1a (by omega)) ?_ (by omega)) (by simp)
    exact evB_get₃ (evB_var₃ h1v (by omega)) (by rw [h1cn]; exact hcnget) (by omega)
  have h2v : σ2.vars "or.v" = k := by rw [hσ2]; simp [h1v]
  -- `or.v := or.v + 1`
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "or.v" (k + 1) := ⟨_, rfl⟩
  have r3 : Run B (.assign "or.v" (.add (.var "or.v") (.lit 1))) σ2 σ3 4 := by
    rw [hσ3]
    exact run_assign₃ (evB_add₃ (evB_var₃ h2v (by omega)) (evB_lit₃ (by omega))
      (by omega)) (by simp)
  have h3ar : ∀ b, σ3.arrs b = σ1.arrs b := by intro b; rw [hσ3, hσ2]; simp
  have h3io : σ3.arrs io = (σ.arrs io).set k (inOff (baseOr G π) k) := by
    rw [h3ar, hσ1]; simp
  have h3v : σ3.vars "or.v" = k + 1 := by rw [hσ3]; simp
  refine ⟨σ3, 3 + (5 + 4), r1.seq (r2.seq r3), le_rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine hfr.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hσ3, hσ2, hσ1]; simp [hv0, ha0]
    · rw [h3ar, hσ1]; simp [Ne.symm hnm.io_ao]
    · rw [h3ar, hσ1]; simp [Ne.symm hnm.io_aj]
    · rw [h3ar, hσ1]; simp [Ne.symm hnm.io_ra]
    · rw [h3ar, hσ1]; simp only [length_arrs_setArr]
    · rw [h3ar, hσ1]; simp only [length_arrs_setArr]
    · rw [h3ar, hσ1]; simp only [length_arrs_setArr]
  · rw [h3v]; omega
  · rw [h3v, hσ3, hσ2]
    simp only [vars_setVar, String.reduceEq, if_false, if_true]
    exact hsucc.symm
  · intro i hi
    rw [h3v] at hi
    rw [h3io]
    by_cases hik' : i = k
    · subst hik'; rw [getD_set_self₃ hioL]
    · rw [getD_set_of_ne₃ (Ne.symm hik')]; exact hiov i (by omega)
  · intro i hi; rw [h3ar, h1cn]; exact hcnv i hi
  · rw [h3v, hkeq]

/-- **The prefix sweep, discharged**: `io` holds `inOff (baseOr G π)` on
`[0, N]` and the arc count lands in `nA`. -/
private theorem orOff_spec {B : ℕ} {nN nA ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars) (hnA : nA ∉ orScalars)
    (hAN : nA ≠ nN) (hB : N * N + N < B) :
    Spec B (fun σ => OrFrame nN ao aj ra io it cn G π offF ajF σ ∧
        ∀ i, i < N → (σ.arrs cn).getD i 0 = inDegAt (baseOr G π) i)
      (orOffCom nN nA io cn)
      (fun _ σ' => OrFrame nN ao aj ra io it cn G π offF ajF σ' ∧
        (∀ i, i ≤ N → (σ'.arrs io).getD i 0 = inOff (baseOr G π) i) ∧
        σ'.vars nA = arcCount (baseOr G π))
      (16 * N + 13) := by
  obtain ⟨hv0, -, -, -, -, -, ha0, -⟩ := orScalars_ne hnN
  obtain ⟨hAv, -, -, -, -, -, hAa, -⟩ := orScalars_ne hnA
  have harc : 2 * arcCount (baseOr G π) ≤ N * N := two_mul_arcCount_le_sq G π
  have hNB : N < B := by omega
  -- `or.a := 0`
  have hstart : Spec B (fun σ => OrFrame nN ao aj ra io it cn G π offF ajF σ ∧
        ∀ i, i < N → (σ.arrs cn).getD i 0 = inDegAt (baseOr G π) i)
      (.assign "or.a" (.lit 0))
      (fun _ σ' => OrOffI nN ao aj ra io it cn G π offF ajF (σ'.setVar "or.v" 0)) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hcnv⟩ := hσ
    refine ⟨_, 2, run_assign₃ (evB_lit₃ (by omega)) (by simp), le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact hfr.of_eq (by simp [hv0, ha0]) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp)
    · simp
    · simp [inOff_zero]
    · intro i hi
      simp only [vars_setVar] at hi
      exact absurd hi (Nat.not_lt_zero i)
    · intro i hi; simpa using hcnv i hi
  -- the scan
  have hloop := Spec.forRangeZero (B := B) "or.v" nN
    (OrOffI nN ao aj ra io it cn G π offF ajF) N 12 hNB
    (fun σ hI => hI.2.1) (fun σ hI => hI.1.carrier) (orOff_body hnm hnN hB)
  -- `io[nN] := or.a` and `nA := or.a`
  have hfin : Spec B
      (fun σ => OrOffI nN ao aj ra io it cn G π offF ajF σ ∧ σ.vars "or.v" = N)
      (.seq (.store io (.var nN) (.var "or.a")) (.assign nA (.var "or.a")))
      (fun _ σ' => OrFrame nN ao aj ra io it cn G π offF ajF σ' ∧
        (∀ i, i ≤ N → (σ'.arrs io).getD i 0 = inOff (baseOr G π) i) ∧
        σ'.vars nA = arcCount (baseOr G π)) 5 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, -, hav, hiov, -⟩, hend⟩ := hσ
    rw [hend] at hav hiov
    have hlast : inOff (baseOr G π) N = arcCount (baseOr G π) := inOff_last _
    have hioL : N < (σ.arrs io).length := by have := hfr.ioLen; omega
    obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setArr io N (inOff (baseOr G π) N) := ⟨_, rfl⟩
    have r1 : Run B (.store io (.var nN) (.var "or.a")) σ σ1 3 := by
      rw [hσ1]
      exact run_store₃ (evB_var₃ hfr.carrier (by omega))
        (evB_var₃ hav (by omega)) hioL (by simp)
    have h1a : σ1.vars "or.a" = inOff (baseOr G π) N := by rw [hσ1]; simp [hav]
    obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar nA (inOff (baseOr G π) N) := ⟨_, rfl⟩
    have r2 : Run B (.assign nA (.var "or.a")) σ1 σ2 2 := by
      rw [hσ2]; exact run_assign₃ (evB_var₃ h1a (by omega)) (by simp)
    have h2io : σ2.arrs io = (σ.arrs io).set N (inOff (baseOr G π) N) := by
      rw [hσ2, hσ1]; simp
    refine ⟨σ2, 3 + 2, r1.seq r2, le_rfl, ?_, ?_, ?_⟩
    · refine hfr.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hσ2, hσ1]; simp [Ne.symm hAN]
      · rw [hσ2, hσ1]; simp [Ne.symm hnm.io_ao]
      · rw [hσ2, hσ1]; simp [Ne.symm hnm.io_aj]
      · rw [hσ2, hσ1]; simp [Ne.symm hnm.io_ra]
      · rw [hσ2, hσ1]; simp only [arrs_setVar, length_arrs_setArr]
      · rw [hσ2, hσ1]; simp only [arrs_setVar, length_arrs_setArr]
      · rw [hσ2, hσ1]; simp only [arrs_setVar, length_arrs_setArr]
    · intro i hi
      rw [h2io]
      by_cases hiN : i = N
      · subst hiN; rw [getD_set_self₃ hioL]
      · rw [getD_set_of_ne₃ (Ne.symm hiN)]; exact hiov i (by omega)
    · rw [hσ2]; simp [hlast]
  refine ((Spec.seq hstart (Spec.seq hloop hfin (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => hq)) (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => hq)).mono (by omega))

/-! ## §8 The scatter

The cursor is a scalar, so a row is filled by the outer turn that owns
it and no cursor array exists.  What is carried is an **address**, not a
set (`transposeIn_tpCom`'s Finding 2): the qualifying source slot `q` of
row `v` lands at `inOff D v + orCnt … (offF v) q`, which is exactly
where the cursor stands when the loop reaches `q`. -/

/-- Rows below `k` are complete: every slot holds an in-neighbour of its
row, and every qualifying source slot has landed at its own address. -/
private def OrScSt (it : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (k : ℕ) (σ : Env) : Prop :=
  (∀ v, v < k → ∀ p, inOff (baseOr G π) v ≤ p → p < inOff (baseOr G π) (v + 1) →
      (σ.arrs it).getD p 0 ∈ inNAt (baseOr G π) v) ∧
  (∀ v, v < k → ∀ q, offF v ≤ q → q < offF (v + 1) → rankAt π (ajF q) < rankAt π v →
      (σ.arrs it).getD
        (inOff (baseOr G π) v + orCnt ajF π (rankAt π v) (offF v) q) 0 = ajF q)

/-- The same two clauses for row `k` alone, up to the source pointer. -/
private def OrScRow (it : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (k j : ℕ) (σ : Env) : Prop :=
  (∀ p, inOff (baseOr G π) k ≤ p →
      p < inOff (baseOr G π) k + orCnt ajF π (rankAt π k) (offF k) j →
      (σ.arrs it).getD p 0 ∈ inNAt (baseOr G π) k) ∧
  (∀ q, offF k ≤ q → q < j → rankAt π (ajF q) < rankAt π k →
      (σ.arrs it).getD
        (inOff (baseOr G π) k + orCnt ajF π (rankAt π k) (offF k) q) 0 = ajF q)

/-- The carried state of one outer turn of the scatter. -/
private def OrScI (nN ao aj ra io it cn : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (k : ℕ) (σ : Env) : Prop :=
  OrFrame nN ao aj ra io it cn G π offF ajF σ ∧
    (∀ i, i ≤ N → (σ.arrs io).getD i 0 = inOff (baseOr G π) i) ∧
    σ.vars "or.v" = k ∧ σ.vars "or.f" = offF (k + 1) ∧ σ.vars "or.r" = rankAt π k ∧
    offF k ≤ σ.vars "or.j" ∧ σ.vars "or.j" ≤ offF (k + 1) ∧
    σ.vars "or.c" = inOff (baseOr G π) k
      + orCnt ajF π (rankAt π k) (offF k) (σ.vars "or.j") ∧
    OrScSt it G π offF ajF k σ ∧ OrScRow it G π offF ajF k (σ.vars "or.j") σ

/-- **One inner turn of the scatter**, at `19`. -/
private theorem orScatIn_step {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    {k : ℕ} {σ : Env} (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars)
    (hk : k < N) (hB : N * N + N < B)
    (hI : OrScI nN ao aj ra io it cn G π offF ajF k σ)
    (hlt : σ.vars "or.j" < offF (k + 1)) :
    ∃ σ' K', Run B (orScatIn aj ra it) σ σ' K' ∧
      OrScI nN ao aj ra io it cn G π offF ajF k σ' ∧
      σ'.vars "or.j" = σ.vars "or.j" + 1 ∧ K' ≤ 19 := by
  obtain ⟨-, hj0, -, -, -, hu0, -, hc0⟩ := orScalars_ne hnN
  obtain ⟨hfr, hiov, hvv, hfv, hrv, hj1, hj2, hcv, hst, hrow⟩ := hI
  obtain ⟨j, hjeq⟩ : ∃ j, σ.vars "or.j" = j := ⟨_, rfl⟩
  rw [hjeq] at hj1 hj2 hcv hlt hrow
  -- the figures
  have hslots : offF N = 2 * arcCount (baseOr G π) := hfr.slots
  have harc : 2 * arcCount (baseOr G π) ≤ N * N := two_mul_arcCount_le_sq G π
  have hoff1 : offF (k + 1) ≤ offF N := hfr.off_le (by omega)
  have hNB : N < B := by omega
  have hoffB : offF N < B := by omega
  have hrkB : rankAt π k < B := by have := rankAt_lt π hk; omega
  have hdeg : orCnt ajF π (rankAt π k) (offF k) (offF (k + 1))
      = inDegAt (baseOr G π) k := by
    rw [inDegAt, dif_pos hk]; exact orCnt_row hfr ⟨k, hk⟩
  have hsucc : inOff (baseOr G π) (k + 1)
      = inOff (baseOr G π) k + inDegAt (baseOr G π) k := inOff_succ _ _
  have hio1 : inOff (baseOr G π) (k + 1) ≤ arcCount (baseOr G π) :=
    inOff_le_arcCount _ (by omega)
  have hitL : arcCount (baseOr G π) ≤ (σ.arrs it).length := hfr.itLen
  obtain ⟨w, hadj, hw⟩ := hfr.sound ⟨k, hk⟩ j hj1 hlt
  have huN : ajF j < N := by rw [hw]; exact w.isLt
  -- `or.u := aj[or.j]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "or.u" (ajF j) := ⟨_, rfl⟩
  have r1 : Run B (.assign "or.u" (.get aj (.var "or.j"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign₃ (evB_get₃ (evB_var₃ hjeq (by omega))
      (hfr.ajGet j (by omega)) (by omega)) (by simp)
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  have h1u : σ1.vars "or.u" = ajF j := by rw [hσ1]; simp
  have h1r : σ1.vars "or.r" = rankAt π k := by rw [hσ1]; simp [hrv]
  have h1c : σ1.vars "or.c"
      = inOff (baseOr G π) k + orCnt ajF π (rankAt π k) (offF k) j := by
    rw [hσ1]; simp [hcv]
  have h1j : σ1.vars "or.j" = j := by rw [hσ1]; simp [hjeq]
  -- the rank test, with its effect stated uniformly
  have hcltB : inOff (baseOr G π) k + orCnt ajF π (rankAt π k) (offF k) j < B ∨
      ¬ rankAt π (ajF j) < rankAt π k := by
    by_cases hc : rankAt π (ajF j) < rankAt π k
    · refine Or.inl ?_
      have h1 : orCnt ajF π (rankAt π k) (offF k) (j + 1)
          = orCnt ajF π (rankAt π k) (offF k) j + 1 := by
        rw [orCnt_succ ajF π (rankAt π k) (offF k) j hj1, if_pos hc]
      have h2 : orCnt ajF π (rankAt π k) (offF k) (j + 1)
          ≤ orCnt ajF π (rankAt π k) (offF k) (offF (k + 1)) :=
        orCnt_mono ajF π (rankAt π k) (offF k) (by omega)
      rw [hdeg] at h2
      omega
    · exact Or.inr hc
  have htrue : rankAt π (ajF j) < rankAt π k →
      ∃ τ K', Run B (.seq (.store it (.var "or.c") (.var "or.u"))
          (.assign "or.c" (.add (.var "or.c") (.lit 1)))) σ1 τ K' ∧ K' ≤ 7 ∧
        ((∀ y, y ≠ "or.c" → τ.vars y = σ1.vars y) ∧
          τ.vars "or.c" = σ1.vars "or.c"
            + (if rankAt π (ajF j) < rankAt π k then 1 else 0) ∧
          (∀ b, b ≠ it → τ.arrs b = σ1.arrs b) ∧
          (τ.arrs it).length = (σ1.arrs it).length ∧
          (∀ p, p ≠ σ1.vars "or.c" → (τ.arrs it).getD p 0 = (σ1.arrs it).getD p 0) ∧
          ((if rankAt π (ajF j) < rankAt π k then 1 else 0) = 1 →
            (τ.arrs it).getD (σ1.vars "or.c") 0 = ajF j)) := by
    intro hc
    have h1 : orCnt ajF π (rankAt π k) (offF k) (j + 1)
        = orCnt ajF π (rankAt π k) (offF k) j + 1 := by
      rw [orCnt_succ ajF π (rankAt π k) (offF k) j hj1, if_pos hc]
    have h2 : orCnt ajF π (rankAt π k) (offF k) (j + 1)
        ≤ orCnt ajF π (rankAt π k) (offF k) (offF (k + 1)) :=
      orCnt_mono ajF π (rankAt π k) (offF k) (by omega)
    rw [hdeg] at h2
    have hcB : σ1.vars "or.c" < B := by rw [h1c]; omega
    have hcB1 : σ1.vars "or.c" + 1 < B := by rw [h1c]; omega
    have hcL : σ1.vars "or.c" < (σ1.arrs it).length := by
      rw [h1a, h1c]; omega
    obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ1.setArr it (σ1.vars "or.c") (ajF j) := ⟨_, rfl⟩
    have s1 : Run B (.store it (.var "or.c") (.var "or.u")) σ1 τ1 3 := by
      rw [hτ1]
      exact run_store₃ (evB_var₃ rfl hcB) (evB_var₃ h1u (by omega)) hcL (by simp)
    have hτ1c : τ1.vars "or.c" = σ1.vars "or.c" := by rw [hτ1]; simp
    obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "or.c" (σ1.vars "or.c" + 1) := ⟨_, rfl⟩
    have s2 : Run B (.assign "or.c" (.add (.var "or.c") (.lit 1))) τ1 τ2 4 := by
      rw [hτ2]
      exact run_assign₃ (evB_add₃ (evB_var₃ hτ1c hcB) (evB_lit₃ (by omega)) hcB1)
        (by simp)
    refine ⟨τ2, 3 + 4, s1.seq s2, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy; rw [hτ2, hτ1]; simp [hy]
    · rw [hτ2, if_pos hc]; simp
    · intro b hb; rw [hτ2, hτ1]; simp [hb]
    · rw [hτ2, hτ1]; simp only [arrs_setVar, length_arrs_setArr]
    · intro p hp; rw [hτ2, hτ1]; simp only [arrs_setVar, arrs_setArr]
      exact getD_set_of_ne₃ (Ne.symm hp)
    · intro _; rw [hτ2, hτ1]; simp only [arrs_setVar, arrs_setArr]
      exact getD_set_self₃ hcL
  have hfalse : ¬ rankAt π (ajF j) < rankAt π k →
      ∃ τ K', Run B .skip σ1 τ K' ∧ K' ≤ 7 ∧
        ((∀ y, y ≠ "or.c" → τ.vars y = σ1.vars y) ∧
          τ.vars "or.c" = σ1.vars "or.c"
            + (if rankAt π (ajF j) < rankAt π k then 1 else 0) ∧
          (∀ b, b ≠ it → τ.arrs b = σ1.arrs b) ∧
          (τ.arrs it).length = (σ1.arrs it).length ∧
          (∀ p, p ≠ σ1.vars "or.c" → (τ.arrs it).getD p 0 = (σ1.arrs it).getD p 0) ∧
          ((if rankAt π (ajF j) < rankAt π k then 1 else 0) = 1 →
            (τ.arrs it).getD (σ1.vars "or.c") 0 = ajF j)) := by
    intro hc
    exact ⟨σ1, 1, Run.skip, by omega,
      fun y _ => rfl, by simp [hc], fun b _ => rfl, rfl, fun p _ => rfl,
      by simp [hc]⟩
  obtain ⟨σ2, K2, r2, hK2, h2v, h2c, h2b, h2len, h2ne, h2eq⟩ :=
    orTest h1u h1r huN hNB hrkB (by rw [h1a]; exact hfr.raGet) htrue hfalse
  -- `or.j := or.j + 1`
  have h2jv : σ2.vars "or.j" = j := by rw [h2v "or.j" (by decide), h1j]
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "or.j" (j + 1) := ⟨_, rfl⟩
  have r3 : Run B (.assign "or.j" (.add (.var "or.j") (.lit 1))) σ2 σ3 4 := by
    rw [hσ3]
    exact run_assign₃ (evB_add₃ (evB_var₃ h2jv (by omega)) (evB_lit₃ (by omega))
      (by omega)) (by simp)
  have h3v : ∀ y, y ≠ "or.j" → σ3.vars y = σ2.vars y := by
    intro y hy; rw [hσ3]; simp [hy]
  have h3b : ∀ b, σ3.arrs b = σ2.arrs b := by intro b; rw [hσ3]; simp
  have h3it : ∀ p, p ≠ σ1.vars "or.c" →
      (σ3.arrs it).getD p 0 = (σ.arrs it).getD p 0 := by
    intro p hp; rw [h3b, h2ne p hp, h1a]
  have hcstand : σ1.vars "or.c"
      = inOff (baseOr G π) k + orCnt ajF π (rankAt π k) (offF k) j := h1c
  have hnext : orCnt ajF π (rankAt π k) (offF k) (j + 1)
      = orCnt ajF π (rankAt π k) (offF k) j
        + (if rankAt π (ajF j) < rankAt π k then 1 else 0) :=
    orCnt_succ ajF π (rankAt π k) (offF k) j hj1
  have h3j : σ3.vars "or.j" = j + 1 := by rw [hσ3]; simp
  refine ⟨σ3, 3 + (K2 + 4), r1.seq (r2.seq r3), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [h3j, hjeq], by omega⟩
  · refine hfr.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [h3v nN (by simpa using hj0), h2v nN (by simpa using hc0),
        hσ1]; simp [hu0]
    · rw [h3b, h2b ao (Ne.symm hnm.it_ao), h1a]
    · rw [h3b, h2b aj (Ne.symm hnm.it_aj), h1a]
    · rw [h3b, h2b ra (Ne.symm hnm.it_ra), h1a]
    · rw [h3b, h2b io (Ne.symm hnm.it_io), h1a]
    · rw [h3b, h2len, h1a]
    · rw [h3b, h2b cn (Ne.symm hnm.it_cn), h1a]
  · intro i hi
    rw [h3b, h2b io (Ne.symm hnm.it_io), h1a]
    exact hiov i hi
  · rw [h3v _ (by decide), h2v _ (by decide), hσ1]; simp [hvv]
  · rw [h3v _ (by decide), h2v _ (by decide), hσ1]; simp [hfv]
  · rw [h3v _ (by decide), h2v _ (by decide), hσ1]; simp [hrv]
  · rw [h3j]; omega
  · rw [h3j]; omega
  · rw [h3j, h3v _ (by decide), h2c, hcstand, hnext]; omega
  · -- rows below `k` are untouched: the write is at or above `inOff D k`
    refine ⟨fun v hv p hp1 hp2 => ?_, fun v hv q hq1 hq2 hq3 => ?_⟩
    · have hle : inOff (baseOr G π) (v + 1) ≤ inOff (baseOr G π) k :=
        inOff_mono _ (by omega)
      rw [h3it p (by rw [hcstand]; omega)]
      exact hst.1 v hv p hp1 hp2
    · have hle : inOff (baseOr G π) (v + 1) ≤ inOff (baseOr G π) k :=
        inOff_mono _ (by omega)
      have hvN : v < N := by omega
      have hlt' : orCnt ajF π (rankAt π v) (offF v) q < inDegAt (baseOr G π) v := by
        have h1 : orCnt ajF π (rankAt π v) (offF v) (q + 1)
            = orCnt ajF π (rankAt π v) (offF v) q + 1 := by
          rw [orCnt_succ ajF π (rankAt π v) (offF v) q hq1, if_pos hq3]
        have h2 : orCnt ajF π (rankAt π v) (offF v) (q + 1)
            ≤ orCnt ajF π (rankAt π v) (offF v) (offF (v + 1)) :=
          orCnt_mono ajF π (rankAt π v) (offF v) (by omega)
        have h3 : orCnt ajF π (rankAt π v) (offF v) (offF (v + 1))
            = inDegAt (baseOr G π) v := by
          rw [inDegAt, dif_pos hvN]; exact orCnt_row hfr ⟨v, hvN⟩
        omega
      have hs : inOff (baseOr G π) (v + 1)
          = inOff (baseOr G π) v + inDegAt (baseOr G π) v := inOff_succ _ _
      rw [h3it _ (by rw [hcstand]; omega)]
      exact hst.2 v hv q hq1 hq2 hq3
  · -- row `k`, one slot further
    rw [h3j]
    refine ⟨fun p hp1 hp2 => ?_, fun q hq1 hq2 hq3 => ?_⟩
    · rw [hnext] at hp2
      by_cases hpc : p = σ1.vars "or.c"
      · have hcq : rankAt π (ajF j) < rankAt π k := by
          by_contra hc
          rw [if_neg hc] at hp2
          rw [hcstand] at hpc
          omega
        rw [hpc, h3b, h2eq (if_pos hcq), mem_inNAt hk]
        refine ⟨huN, ?_⟩
        have hwe : (⟨ajF j, huN⟩ : Fin N) = w := Fin.ext hw
        rw [hwe, mem_baseOr]
        refine ⟨hadj.symm, ?_⟩
        rw [Fin.lt_def, ← rankAt_coe π w, ← rankAt_coe π (⟨k, hk⟩ : Fin N), ← hw]
        exact hcq
      · rw [h3it p hpc]
        refine hrow.1 p hp1 ?_
        rw [hcstand] at hpc
        by_cases hc : rankAt π (ajF j) < rankAt π k
        · rw [if_pos hc] at hp2; omega
        · rw [if_neg hc] at hp2; omega
    · by_cases hqj : q = j
      · have hq3' : rankAt π (ajF j) < rankAt π k := by rw [← hqj]; exact hq3
        rw [hqj, ← hcstand, h3b, h2eq (if_pos hq3')]
      · have hlt' : orCnt ajF π (rankAt π k) (offF k) q
            < orCnt ajF π (rankAt π k) (offF k) j := by
          have h1 : orCnt ajF π (rankAt π k) (offF k) (q + 1)
              = orCnt ajF π (rankAt π k) (offF k) q + 1 := by
            rw [orCnt_succ ajF π (rankAt π k) (offF k) q hq1, if_pos hq3]
          have h2 : orCnt ajF π (rankAt π k) (offF k) (q + 1)
              ≤ orCnt ajF π (rankAt π k) (offF k) j :=
            orCnt_mono ajF π (rankAt π k) (offF k) (by omega)
          omega
        rw [h3it _ (by rw [hcstand]; omega)]
        exact hrow.2 q hq1 (by omega) hq3

/-- **The scatter's inner scan**: `23` a source slot. -/
private theorem orScatIn_scan {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    {k : ℕ} (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars)
    (hk : k < N) (hB : N * N + N < B) (hoffB : offF (k + 1) < B) :
    Spec B (fun σ => OrScI nN ao aj ra io it cn G π offF ajF k σ ∧
        σ.vars "or.j" = offF k)
      (Csr.scan "or.j" "or.f" (orScatIn aj ra it))
      (fun _ σ' => OrScI nN ao aj ra io it cn G π offF ajF k σ' ∧
        σ'.vars "or.j" = offF (k + 1))
      (23 * (offF (k + 1) - offF k) + 4) :=
  Csr.rowScan_spec B _ (offF (k + 1)) 19 "or.j" "or.f" (orScatIn aj ra it)
    (fun σ => OrScI nN ao aj ra io it cn G π offF ajF k σ) hoffB
    (fun _ hI => ⟨hI.2.2.2.1, hI.2.2.2.2.2.2.1⟩)
    (fun _ hI hlt => orScatIn_step hnm hnN hk hB hI hlt)
    (fun _ h => h.1) (fun _ h => by simp only [h.2]; omega)

/-- The carried state of the scatter's outer scan. -/
private def OrScO (nN ao aj ra io it cn : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (offF ajF : ℕ → ℕ) (σ : Env) : Prop :=
  OrFrame nN ao aj ra io it cn G π offF ajF σ ∧
    (∀ i, i ≤ N → (σ.arrs io).getD i 0 = inOff (baseOr G π) i) ∧
    σ.vars "or.v" ≤ N ∧ OrScSt it G π offF ajF (σ.vars "or.v") σ

/-- **One outer turn of the scatter**: load the row, the head's rank and
the row's own offset, then fill the row. -/
private theorem orScatOut_step {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    {σ : Env} (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars)
    (hB : N * N + N < B)
    (hO : OrScO nN ao aj ra io it cn G π offF ajF σ) (hlt : σ.vars "or.v" < N) :
    ∃ σ' K', Run B (orScatOut ao aj ra io it) σ σ' K' ∧
      OrScO nN ao aj ra io it cn G π offF ajF σ' ∧
      σ'.vars "or.v" = σ.vars "or.v" + 1 ∧
      K' ≤ 22 + 23 * (offF (σ.vars "or.v" + 1) - offF (σ.vars "or.v")) := by
  obtain ⟨hv0, hj0, hf0, -, hr0, -, -, hc0⟩ := orScalars_ne hnN
  obtain ⟨hfr, hiov, hvle, hst⟩ := hO
  obtain ⟨k, hkeq⟩ : ∃ k, σ.vars "or.v" = k := ⟨_, rfl⟩
  rw [hkeq] at hvle hlt hst
  have hslots : offF N = 2 * arcCount (baseOr G π) := hfr.slots
  have harc : 2 * arcCount (baseOr G π) ≤ N * N := two_mul_arcCount_le_sq G π
  have hoffk : offF k ≤ offF N := hfr.off_le (by omega)
  have hoff1 : offF (k + 1) ≤ offF N := hfr.off_le (by omega)
  have hmono : offF k ≤ offF (k + 1) := hfr.mono (k + 1) hlt k (by omega)
  have hNB : N < B := by omega
  have hoffB : offF N < B := by omega
  have hrkB : rankAt π k < B := by have := rankAt_lt π hlt; omega
  have hiok : inOff (baseOr G π) k ≤ arcCount (baseOr G π) :=
    inOff_le_arcCount _ (by omega)
  have hioget : (σ.arrs io)[k]? = some (inOff (baseOr G π) k) := by
    rw [← hiov k (by omega)]
    exact getElem?_of_lt₃ _ _ (by have := hfr.ioLen; omega)
  -- `or.j := ao[or.v]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "or.j" (offF k) := ⟨_, rfl⟩
  have r1 : Run B (.assign "or.j" (.get ao (.var "or.v"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign₃ (evB_get₃ (evB_var₃ hkeq (by omega)) (hfr.offGet k (by omega))
      (by omega)) (by simp)
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  have h1v : σ1.vars "or.v" = k := by rw [hσ1]; simp [hkeq]
  -- `or.f := ao[or.v + 1]`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "or.f" (offF (k + 1)) := ⟨_, rfl⟩
  have r2 : Run B (.assign "or.f" (.get ao (.add (.var "or.v") (.lit 1)))) σ1 σ2 5 := by
    rw [hσ2]
    refine run_assign₃ (evB_get₃ (evB_add₃ (evB_var₃ h1v (by omega))
      (evB_lit₃ (by omega)) (by omega)) ?_ (by omega)) (by simp)
    rw [h1a]; exact hfr.offGet (k + 1) (by omega)
  have h2a : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  have h2v : σ2.vars "or.v" = k := by rw [hσ2]; simp [h1v]
  -- `or.r := ra[or.v]`
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "or.r" (rankAt π k) := ⟨_, rfl⟩
  have r3 : Run B (.assign "or.r" (.get ra (.var "or.v"))) σ2 σ3 3 := by
    rw [hσ3]
    refine run_assign₃ (evB_get₃ (evB_var₃ h2v (by omega)) ?_ (by omega)) (by simp)
    rw [h2a]; exact hfr.raGet k hlt
  have h3a : σ3.arrs = σ.arrs := by rw [hσ3, hσ2, hσ1]; simp
  have h3v : σ3.vars "or.v" = k := by rw [hσ3]; simp [h2v]
  -- `or.c := io[or.v]`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setVar "or.c" (inOff (baseOr G π) k) := ⟨_, rfl⟩
  have r4 : Run B (.assign "or.c" (.get io (.var "or.v"))) σ3 σ4 3 := by
    rw [hσ4]
    refine run_assign₃ (evB_get₃ (evB_var₃ h3v (by omega)) ?_ (by omega)) (by simp)
    rw [h3a]; exact hioget
  have h4a : σ4.arrs = σ.arrs := by rw [hσ4, hσ3, hσ2, hσ1]; simp
  have h4n : σ4.vars nN = σ.vars nN := by
    rw [hσ4, hσ3, hσ2, hσ1]; simp [hj0, hf0, hr0, hc0]
  have h4j : σ4.vars "or.j" = offF k := by rw [hσ4, hσ3, hσ2, hσ1]; simp
  have h4v : σ4.vars "or.v" = k := by rw [hσ4]; simp [h3v]
  have h4f : σ4.vars "or.f" = offF (k + 1) := by rw [hσ4, hσ3, hσ2]; simp
  have h4r : σ4.vars "or.r" = rankAt π k := by rw [hσ4, hσ3]; simp
  have h4c : σ4.vars "or.c" = inOff (baseOr G π) k := by rw [hσ4]; simp
  have hI4 : OrScI nN ao aj ra io it cn G π offF ajF k σ4 ∧ σ4.vars "or.j" = offF k := by
    refine ⟨⟨hfr.of_eq h4n (by rw [h4a]) (by rw [h4a]) (by rw [h4a]) (by rw [h4a])
        (by rw [h4a]) (by rw [h4a]), ?_, h4v, h4f, h4r, ?_, ?_, ?_, ?_, ?_⟩, h4j⟩
    · intro i hi; rw [h4a]; exact hiov i hi
    · rw [h4j]
    · rw [h4j]; exact hmono
    · rw [h4j, h4c, orCnt_self]; omega
    · rw [OrScSt, h4a]; exact hst
    · rw [h4j, OrScRow, h4a, orCnt_self]
      exact ⟨fun p hp1 hp2 => by omega, fun q hq1 hq2 => by omega⟩
  obtain ⟨σ5, r5, hI5, hj5⟩ :=
    (orScatIn_scan (nN := nN) (cn := cn) hnm hnN hlt hB (by omega)).run hI4
  obtain ⟨hfr5, hiov5, h5v, -, -, -, -, -, hst5, hrow5⟩ := hI5
  rw [hj5] at hrow5
  have hdeg : orCnt ajF π (rankAt π k) (offF k) (offF (k + 1))
      = inDegAt (baseOr G π) k := by
    rw [inDegAt, dif_pos hlt]; exact orCnt_row hfr5 ⟨k, hlt⟩
  have hsucc : inOff (baseOr G π) (k + 1)
      = inOff (baseOr G π) k + inDegAt (baseOr G π) k := inOff_succ _ _
  -- `or.v := or.v + 1`
  obtain ⟨σ6, hσ6⟩ : ∃ τ, τ = σ5.setVar "or.v" (k + 1) := ⟨_, rfl⟩
  have r6 : Run B (.assign "or.v" (.add (.var "or.v") (.lit 1))) σ5 σ6 4 := by
    rw [hσ6]
    exact run_assign₃ (evB_add₃ (evB_var₃ h5v (by omega)) (evB_lit₃ (by omega))
      (by omega)) (by simp)
  have h6a : ∀ b, σ6.arrs b = σ5.arrs b := by intro b; rw [hσ6]; simp
  have h6v : σ6.vars "or.v" = k + 1 := by rw [hσ6]; simp
  refine ⟨σ6, 3 + (5 + (3 + (3 + ((23 * (offF (k + 1) - offF k) + 4) + 4)))),
    r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6)))), ⟨?_, ?_, ?_, ?_⟩,
    by rw [h6v, hkeq], by rw [hkeq]; omega⟩
  · exact hfr5.of_eq (by rw [hσ6]; simp [hv0]) (by rw [h6a]) (by rw [h6a])
      (by rw [h6a]) (by rw [h6a]) (by rw [h6a]) (by rw [h6a])
  · intro i hi; rw [h6a]; exact hiov5 i hi
  · rw [h6v]; omega
  · rw [h6v, OrScSt]
    refine ⟨fun v hv p hp1 hp2 => ?_, fun v hv q hq1 hq2 hq3 => ?_⟩
    · rw [h6a]
      rcases Nat.lt_or_ge v k with hvk | hvk
      · exact hst5.1 v hvk p hp1 hp2
      · obtain rfl : v = k := by omega
        exact hrow5.1 p hp1 (by rw [hdeg]; omega)
    · rw [h6a]
      rcases Nat.lt_or_ge v k with hvk | hvk
      · exact hst5.2 v hvk q hq1 hq2 hq3
      · obtain rfl : v = k := by omega
        exact hrow5.2 q hq1 hq2 hq3

/-- **The scatter's outer scan**: `26` a vertex and `23` a source
slot. -/
private theorem orScat_scan {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars) (hB : N * N + N < B) :
    Spec B (fun σ => OrScO nN ao aj ra io it cn G π offF ajF σ ∧ σ.vars "or.v" = 0)
      (Csr.scan "or.v" nN (orScatOut ao aj ra io it))
      (fun _ σ' => OrScO nN ao aj ra io it cn G π offF ajF σ' ∧ σ'.vars "or.v" = N)
      (26 * N + 23 * offF N + 4) := by
  have hNB : N < B := by omega
  refine (Spec.while_potential (b := .lt (.var "or.v") (.var nN))
    (fun σ => OrScO nN ao aj ra io it cn G π offF ajF σ)
    (fun σ => 26 * (N - σ.vars "or.v") + 23 * (offF N - offF (σ.vars "or.v")))
    (fun σ hO => evalB_condLt_vars (by have := hO.2.2.1; omega)
      (by have := hO.1.carrier; omega)) ?_ (fun σ h => h.1) ?_).post ?_
  · intro σ hO hc
    have hlt : σ.vars "or.v" < N := by
      have h1 := lt_of_condLt_true hc
      have h2 := hO.1.carrier
      omega
    obtain ⟨σ', K', hrun, hO', hv', hK'⟩ := orScatOut_step hnm hnN hB hO hlt
    refine ⟨σ', K', hrun, hO', ?_⟩
    have hm : offF (σ.vars "or.v") ≤ offF (σ.vars "or.v" + 1) :=
      hO.1.mono (σ.vars "or.v" + 1) hlt (σ.vars "or.v") (by omega)
    have hle : offF (σ.vars "or.v" + 1) ≤ offF N := hO.1.off_le hlt
    simp only [size_condLt, size_var]
    rw [hv']
    omega
  · intro σ h
    have hz := h.2
    have h0 : offF 0 = 0 := h.1.1.off0
    simp only [size_condLt, size_var]
    rw [hz, h0]
    omega
  · rintro σ σ' - ⟨hO', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hO'.1.carrier
    have h3 := hO'.2.2.1
    exact ⟨hO', by omega⟩

/-- **The scatter, discharged**: every row of `it` lists the
in-neighbours of its head. -/
private theorem orScat_spec {B : ℕ} {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars) (hB : N * N + N < B) :
    Spec B (fun σ => OrFrame nN ao aj ra io it cn G π offF ajF σ ∧
        ∀ i, i ≤ N → (σ.arrs io).getD i 0 = inOff (baseOr G π) i)
      (orScatCom nN ao aj ra io it)
      (fun _ σ' => OrFrame nN ao aj ra io it cn G π offF ajF σ' ∧
        (∀ i, i ≤ N → (σ'.arrs io).getD i 0 = inOff (baseOr G π) i) ∧
        OrScSt it G π offF ajF N σ')
      (26 * N + 23 * offF N + 6) := by
  obtain ⟨hv0, -, -, -, -, -, -, -⟩ := orScalars_ne hnN
  have hNB : N < B := by omega
  have hstart : Spec B (fun σ => OrFrame nN ao aj ra io it cn G π offF ajF σ ∧
        ∀ i, i ≤ N → (σ.arrs io).getD i 0 = inOff (baseOr G π) i)
      (.assign "or.v" (.lit 0))
      (fun _ σ' => OrScO nN ao aj ra io it cn G π offF ajF σ' ∧ σ'.vars "or.v" = 0) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hiov⟩ := hσ
    refine ⟨_, 2, run_assign₃ (evB_lit₃ (by omega)) (by simp), le_rfl,
      ⟨?_, ?_, ?_, ?_⟩, by simp⟩
    · exact hfr.of_eq (by simp [hv0]) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp)
    · intro i hi; simpa using hiov i hi
    · simp
    · rw [OrScSt]
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩ <;>
        · simp only [vars_setVar] at hv
          exact absurd hv (Nat.not_lt_zero v)
  refine ((Spec.seq hstart (orScat_scan hnm hnN hB) (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => ?_)).mono (by omega))
  obtain ⟨⟨hfr, hiov, -, hst⟩, hend⟩ := hq
  rw [hend] at hst
  exact ⟨hfr, hiov, hst⟩

/-! ## §9 The three sweeps, as one in-neighbour CSR -/

/-- **What the scatter leaves is a `TrInCsr` of `baseOr G π`.**
Soundness and completeness come off the two carried clauses; injectivity
is pigeonhole, since row `v` has exactly `(D.inN v).card` slots and every
in-neighbour is in one. -/
theorem trInCsr_of_scat {nN ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ} {σ : Env}
    (hfr : OrFrame nN ao aj ra io it cn G π offF ajF σ)
    (hiov : ∀ i, i ≤ N → (σ.arrs io).getD i 0 = inOff (baseOr G π) i)
    (hst : OrScSt it G π offF ajF N σ) :
    TrInCsr io it (baseOr G π) (arcCount (baseOr G π)) (inOff (baseOr G π))
      (fun p => (σ.arrs it).getD p 0) σ := by
  classical
  -- every in-neighbour of `v` sits in a slot of row `v`
  have hcomp : ∀ (v u : Fin N), u ∈ (baseOr G π).inN v →
      ∃ p, inOff (baseOr G π) (v : ℕ) ≤ p ∧ p < inOff (baseOr G π) ((v : ℕ) + 1) ∧
        (σ.arrs it).getD p 0 = (u : ℕ) := by
    intro v u hu
    obtain ⟨hadj, hlt⟩ := mem_baseOr.1 hu
    obtain ⟨q, hq1, hq2, hq3⟩ := hfr.complete v u hadj.symm
    have hq4 : rankAt π (ajF q) < rankAt π (v : ℕ) := by
      rw [hq3, rankAt_coe, rankAt_coe]
      exact Fin.lt_def.1 hlt
    have hdeg : orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) (offF ((v : ℕ) + 1))
        = inDegAt (baseOr G π) (v : ℕ) := by
      rw [inDegAt, dif_pos v.isLt]; exact orCnt_row hfr v
    have h1 : orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) (q + 1)
        = orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) q + 1 := by
      rw [orCnt_succ ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) q hq1, if_pos hq4]
    have h2 : orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) (q + 1)
        ≤ orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) (offF ((v : ℕ) + 1)) :=
      orCnt_mono ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) (by omega)
    have hs : inOff (baseOr G π) ((v : ℕ) + 1)
        = inOff (baseOr G π) (v : ℕ) + inDegAt (baseOr G π) (v : ℕ) := inOff_succ _ _
    refine ⟨inOff (baseOr G π) (v : ℕ)
      + orCnt ajF π (rankAt π (v : ℕ)) (offF (v : ℕ)) q, by omega, by omega, ?_⟩
    rw [hst.2 (v : ℕ) v.isLt q hq1 hq2 hq4, hq3]
  refine
    { zero := inOff_zero _
      step := fun v => by rw [inOff_succ, inDegAt_coe]
      last := inOff_last _
      offLen := hfr.ioLen
      tgtLen := hfr.itLen
      offGet := ?_
      tgtGet := ?_
      tgtLt := ?_
      sound := ?_
      complete := hcomp
      inj := ?_ }
  · intro i hi
    rw [← hiov i hi]
    exact getElem?_of_lt₃ _ _ (by have := hfr.ioLen; omega)
  · intro p hp
    exact getElem?_of_lt₃ _ _ (by have := hfr.itLen; omega)
  · intro p hp
    rw [← inOff_last (baseOr G π)] at hp
    obtain ⟨v, hv1, hv2, hv3⟩ := exists_inRow (baseOr G π) N p hp
    exact lt_of_mem_inNAt (hst.1 v hv1 p hv2 hv3)
  · intro v p h1 h2 h
    obtain ⟨hu, hmem⟩ := (mem_inNAt v.isLt).1 (hst.1 (v : ℕ) v.isLt p h1 h2)
    exact hmem
  · intro v p r hp1 hp2 hr1 hr2 hpr
    have hcard : (Finset.Ico (inOff (baseOr G π) (v : ℕ))
        (inOff (baseOr G π) ((v : ℕ) + 1))).card ≤ (inNAt (baseOr G π) (v : ℕ)).card := by
      rw [Nat.card_Ico, card_inNAt, inOff_succ]
      omega
    have hmaps : Set.MapsTo (fun p => (σ.arrs it).getD p 0)
        ↑(Finset.Ico (inOff (baseOr G π) (v : ℕ)) (inOff (baseOr G π) ((v : ℕ) + 1)))
        ↑(inNAt (baseOr G π) (v : ℕ)) := by
      intro a ha
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha
      exact hst.1 (v : ℕ) v.isLt a ha.1 ha.2
    have hsurj : Set.SurjOn (fun p => (σ.arrs it).getD p 0)
        ↑(Finset.Ico (inOff (baseOr G π) (v : ℕ)) (inOff (baseOr G π) ((v : ℕ) + 1)))
        ↑(inNAt (baseOr G π) (v : ℕ)) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := (mem_inNAt v.isLt).1 (by simpa using hu)
      obtain ⟨p', hp'1, hp'2, hp'3⟩ := hcomp v ⟨u, hu1⟩ hu2
      exact ⟨p', by simp only [Finset.coe_Ico, Set.mem_Ico]; exact ⟨hp'1, hp'2⟩, hp'3⟩
    have hinj := Finset.injOn_of_surjOn_of_card_le _ hmaps hsurj hcard
    exact hinj (by simp only [Finset.coe_Ico, Set.mem_Ico]; exact ⟨hp1, hp2⟩)
      (by simp only [Finset.coe_Ico, Set.mem_Ico]; exact ⟨hr1, hr2⟩) hpr

private theorem not_mem_wvars_orScatCom {nN ao aj ra io it y : String}
    (h : y ∉ orScalars) : y ∉ (orScatCom nN ao aj ra io it).wvars := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := orScalars_ne h
  simp [orScatCom, orScatOut, orScatIn, Csr.scan, Com.wvars, h1, h2, h3, h5, h6, h8]

/-- **The pass, discharged at the level of the three regions**: from the
digested frame, `orCom` leaves an in-neighbour CSR of `baseOr G π` in the
pair `(io, it)` with its arc count in `nA`, at `70·N + 43·offF N + 25`
— and `offF N` is `2·arcCount`, so the arc coefficient is `86`. -/
theorem orCom_spec {B : ℕ} {nN nA ao aj ra io it cn : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {offF ajF : ℕ → ℕ}
    (hnm : OrNames ao aj ra io it cn) (hnN : nN ∉ orScalars) (hnA : nA ∉ orScalars)
    (hAN : nA ≠ nN) (hB : N * N + N < B) :
    Spec B (fun σ => OrFrame nN ao aj ra io it cn G π offF ajF σ)
      (orCom nN nA ao aj ra io it cn)
      (fun _ σ' => TrInCsr io it (baseOr G π) (arcCount (baseOr G π))
          (inOff (baseOr G π)) (fun p => (σ'.arrs it).getD p 0) σ' ∧
        σ'.vars nA = arcCount (baseOr G π))
      (70 * N + 43 * offF N + 25) := by
  rw [orCom]
  have hscat := (orScat_spec (G := G) (π := π) (offF := offF) (ajF := ajF)
    hnm hnN hB).frame
  have hcost : 28 * N + 20 * offF N + 6
      + ((16 * N + 13) + (26 * N + 23 * offF N + 6))
      ≤ 70 * N + 43 * offF N + 25 := by omega
  have hinner := Spec.seq (orOff_spec hnm hnN hnA hAN hB) hscat
    (R := fun (_ : Env) (τ : Env) =>
      TrInCsr io it (baseOr G π) (arcCount (baseOr G π)) (inOff (baseOr G π))
        (fun p => (τ.arrs it).getD p 0) τ ∧ τ.vars nA = arcCount (baseOr G π))
    (fun σ σ' _ hq => ⟨hq.1, hq.2.1⟩)
    (fun σ σ' σ'' _ hq hq' => by
      obtain ⟨-, -, hnAv⟩ := hq
      obtain ⟨⟨hfr, hiov, hst⟩, hfv, -, -, -⟩ := hq'
      exact ⟨trInCsr_of_scat hfr hiov hst,
        by rw [hfv nA (not_mem_wvars_orScatCom hnA), hnAv]⟩)
  exact (Spec.seq (orCnt_spec hnm hnN hB) hinner
    (R := fun (_ : Env) (τ : Env) =>
      TrInCsr io it (baseOr G π) (arcCount (baseOr G π)) (inOff (baseOr G π))
        (fun p => (τ.arrs it).getD p 0) τ ∧ τ.vars nA = arcCount (baseOr G π))
    (fun σ σ' _ hq => hq) (fun σ σ' σ'' _ _ hq => hq)).mono hcost

/-- **The budget, read at the arc count.**  `orCom_spec` is stated at the
*source* slot space `offF N`, which is `A.G`'s degree sum; the handshake
(`SolveAugFrameProg` §1) says that is `2·arcCount (baseOr G π)`, so the
two per-slot constants `20 + 23 = 43` become the arc coefficient `86`. -/
theorem orK_eq {N : ℕ} {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)}
    {offF : ℕ → ℕ} (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    70 * N + 43 * offF N + 25 = orK N (arcCount (baseOr G π)) := by
  rw [offF_last_eq (π := π) h0 hstep, orK]; ring

/-! ## §10 `AugBaseOrientIn`, discharged

The frame's own names, the arena's allocations, and the landed
contract. -/

private theorem not_mem_warrs_orCom {nN nA ao aj ra io it cn b : String}
    (h1 : b ≠ io) (h2 : b ≠ it) (h3 : b ≠ cn) :
    b ∉ (orCom nN nA ao aj ra io it cn).warrs := by
  simp [orCom, orCntCom, orCntOut, orCntIn, orOffCom, orScatCom, orScatOut, orScatIn,
    Csr.scan, Com.warrs, h1, h2, h3]

private theorem not_mem_wvars_orCom {nN nA ao aj ra io it cn y : String}
    (h : y ∉ orScalars) (hA : y ≠ nA) :
    y ∉ (orCom nN nA ao aj ra io it cn).wvars := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := orScalars_ne h
  simp [orCom, orCntCom, orCntOut, orCntIn, orOffCom, orScatCom, orScatOut, orScatIn,
    Csr.scan, Com.wvars, h1, h2, h3, h4, h5, h6, h7, h8, hA]

private theorem lv_ne_lit₃ {s b : String} (hlen : s.length = b.length)
    (hne : s ≠ b) (j : ℕ) : lv s j ≠ b :=
  fun h => hne (lv_inj hlen (h.trans (lv_zero b).symm)).1

/-- The level's two figure cells are never the orientation pass's
scratch — the `lv` mechanism's distinctness at bases of one length. -/
theorem arenaNames_nN_notMem_orScalars (j : ℕ) : (arenaNames j).nN ∉ orScalars := by
  show lv "sv.n" j ∉ orScalars
  simp only [orScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_lit₃ (by decide) (by decide) j

theorem arenaNames_nS_notMem_orScalars (j : ℕ) : (arenaNames j).nS ∉ orScalars := by
  show lv "sv.m" j ∉ orScalars
  simp only [orScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_lit₃ (by decide) (by decide) j

end Lax3Proofs.Prog

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation baseOr baseOr_orients)
open Lax3Proofs.CoverRoutine (MinDegSel selPerm selChain)

/-- **The orientation region, windowed.**  `SolveAugCompose` §7's
`augStInN` asks for `InNCsr`, whose `Lib.Csr` clause pins the two array
lengths *exactly*; a pass has only `≤`, and the slot count is its own
output, so no allocation can be that long (Finding 1).  This is the
`CsrPrefix` reading of it — the exact relation of the **truncation** —
together with the un-windowed `TrInCsr` (`SolveAugTrans`), which is what
`TransposeIn` consumes and which carries the windowed convention in its
own clauses. -/
def augStInNW (io it nA : ℕ → String) (j : ℕ) {Λ n₀ : ℕ} (A : Arena Λ n₀)
    (D : Orientation A.N) (σ : Env) : Prop :=
  (∃ off tgt, TrInCsr (io j) (it j) D (arcCount D) off tgt σ) ∧
    InNCsr (io j) (it j) D (arcCount D)
      (winA (inWs (io j) (it j) A.N (arcCount D)) σ) ∧
    σ.vars (nA j) = arcCount D

/-- The two figures of an admissible arena, with the carrier's square
*and* the carrier inside the word bound — the shape the orientation's
value bounds are stated at. -/
private theorem sq_add_lt_mcB {x : List ℕ} {m : ℕ} {G : SimpleGraph (Fin m)} {q : ℕ}
    (henc : EncodesGraph x m G) (hq : 1 ≤ q) : m * m + m < mcB q x := by
  have hlen := henc.length_eq
  have h2 : (x.length + 1) ^ 2 ≤ mcB q x := by
    rw [mcB]
    exact Nat.le_mul_of_pos_left _ hq
  rw [pow_two] at h2
  have h4 : (m + 1) * (m + 1) ≤ (x.length + 1) * (x.length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  omega

open Classical in
/-- **`AugBaseOrientIn`, discharged** — the third of the base pass's
three, at the program `orCom` and the budget
`70·A.N + 86·arcCount (selChain sel A.G 0) + 25`.

From the deletable adjacency region of `A.G` at the empty deleted set
and the rank array of `selPerm sel A.G`, the pass leaves an in-neighbour
CSR of `baseOr A.G (selPerm sel A.G)` — round `0` of the chain
(`selChain_zero`) — in the pair `(io j, it j)`, with its arc count in
`nA j`, leaving the arena, the two allocations and both scratch
descriptors intact.

The arc coefficient is `86` and not `43` because the pass walks the
*source* slot space, which is the degree sum, and the degree sum is
twice the arc count (`SolveAugFrameProg` §1's handshake, read at the
region's own last offset).  Against
`augChainCost_le_selChainCharge`'s `bn ≤ k`, `ba ≤ 3·k` this pass alone
closes at `k = 70`. -/
theorem augBaseOrientIn_orCom (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt bra : ℕ → String)
    (io it cn nA : ℕ → String)
    (Sbd Srd Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnm : ∀ j, OrNames (bao j) (baj j) (bra j) (io j) (it j) (cn j))
    (hnA : ∀ j, nA j ∉ orScalars)
    (hAN : ∀ j, nA j ≠ (arenaNames j).nN)
    (hAS : ∀ j, nA j ≠ (arenaNames j).nS)
    (hcol : ∀ j, ∀ b ∈ [io j, it j, cn j],
      b ≠ (arenaNames j).off ∧ b ≠ (arenaNames j).tgt ∧ b ≠ (arenaNames j).col ∧
      b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist)
    (hSbd : ∀ j σ, Sbd j σ →
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (io j)).length ∧
      σ.vars (arenaNames j).nS ≤ (σ.arrs (it j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (cn j)).length)
    (hSrd : ∀ (j : ℕ) (σ σ' : Env), Sbd j σ →
      (∀ b, b ≠ io j → b ≠ it j → b ≠ cn j → σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ nA j :: orScalars → σ'.vars y = σ.vars y) → Srd j σ')
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b, b ≠ io j → b ≠ it j → b ≠ cn j → σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ nA j :: orScalars → σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b, b ≠ io j → b ≠ it j → b ≠ cn j → σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ nA j :: orScalars → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugBaseOrientIn C hC φ sel G c w q ℓp htabF hbf Adm ca co
      bao baj bdg bmt bra (fun j A => augStInNW io it nA j A) Sbd Srd Smp Ssw
      (fun j => orCom (arenaNames j).nN (nA j) (bao j) (baj j) (bra j)
        (io j) (it j) (cn j))
      70 86 25 := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hArena, hdel, hra, hSb, hcaL, hcoL, hSm, hSw⟩ := hσ
  have henc : EncodesGraph x n G := hx.1
  have hnNv : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  have hNn : A.N ≤ n := hArena.st.N_le_root
  have hsq : n * n + n < mcB q x := sq_add_lt_mcB henc hq
  have hB : A.N * A.N + A.N < mcB q x := by
    have h : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
    omega
  -- the arena's slot count is twice round `0`'s arc count
  have hot : (arenaNames j).tgt ≠ (arenaNames j).off :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  have hoL : A.N + 1 ≤ (σ.arrs (arenaNames j).off).length :=
    hArena.fits _ _ arenaWs_off
  have htL : σ.vars (arenaNames j).nS ≤ (σ.arrs (arenaNames j).tgt).length :=
    hArena.fits _ _ (arenaWs_tgt hot)
  have hcsrw : GraphCsr (arenaNames j).off (arenaNames j).tgt A.G
      (σ.vars (arenaNames j).nS)
      (winA (arenaWs (arenaNames j) ((Headline.headlineSetup C hC φ).pal j) (ℓp j)
        (hbf j) A.N (σ.vars (arenaNames j).nS)) σ) := hArena.st.csr
  obtain ⟨soff, stgt, hsrc⟩ :=
    srcCsr_of_graphCsr hcsrw hoL htL
      (fun i hi => by
        rw [arrs_winA_some arenaWs_off, List.getElem?_take_of_lt (by omega)])
      (fun p hp => by
        rw [arrs_winA_some (arenaWs_tgt hot), List.getElem?_take_of_lt hp])
  have hns : σ.vars (arenaNames j).nS
      = 2 * arcCount (baseOr A.G (selPerm (sel A.N) A.G)) := by
    rw [hsrc.ns_eq_sum]
    exact sum_ncard_neighborSet_eq_two_mul_arcCount
      (baseOr_orients A.G (selPerm (sel A.N) A.G))
  -- the three output allocations
  obtain ⟨hioL, hitL, hcnL⟩ := hSbd j σ hSb
  rw [hnNv] at hioL hcnL
  rw [hns] at hitL
  -- the region and the rank array, digested
  obtain ⟨offF, hfr⟩ := orFrame_of_region (nN := (arenaNames j).nN)
    (io := io j) (it := it j) (cn := cn j) hnNv hdel hra hioL (by omega) hcnL
  -- the pass
  obtain ⟨σ', hrun, ⟨⟨htr, hnAv⟩, hfv, hfa, -, -⟩, hlen⟩ :=
    (specArrsLength (orCom_spec (B := mcB q x) (nA := nA j) (hnm j)
      (arenaNames_nN_notMem_orScalars j) (hnA j) (hAN j) hB).frame).run hfr
  have hfa' : ∀ b, b ≠ io j → b ≠ it j → b ≠ cn j → σ'.arrs b = σ.arrs b :=
    fun b h1 h2 h3 => hfa b (not_mem_warrs_orCom h1 h2 h3)
  have hfv' : ∀ y, y ∉ nA j :: orScalars → σ'.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, not_or] at hy
    exact hfv y (not_mem_wvars_orCom hy.2 hy.1)
  obtain ⟨hcolO, hupO, hhistO⟩ : _ ∧ _ ∧ _ := by
    have h := hcol j (io j) (by simp); exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨hcolT, hupT, hhistT⟩ : _ ∧ _ ∧ _ := by
    have h := hcol j (it j) (by simp); exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨hcolN, hupN, hhistN⟩ : _ ∧ _ ∧ _ := by
    have h := hcol j (cn j) (by simp); exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hoffO := (hcol j (io j) (by simp)).1
  have htgtO := (hcol j (io j) (by simp)).2.1
  have hoffT := (hcol j (it j) (by simp)).1
  have htgtT := (hcol j (it j) (by simp)).2.1
  have hoffN := (hcol j (cn j) (by simp)).1
  have htgtN := (hcol j (cn j) (by simp)).2.1
  have hnNmem : (arenaNames j).nN ∉ nA j :: orScalars := by
    simp only [List.mem_cons, not_or]
    exact ⟨fun h => (hAN j) h.symm, arenaNames_nN_notMem_orScalars j⟩
  have hnSmem : (arenaNames j).nS ∉ nA j :: orScalars := by
    simp only [List.mem_cons, not_or]
    exact ⟨fun h => (hAS j) h.symm, arenaNames_nS_notMem_orScalars j⟩
  refine ⟨σ', hrun.mono ?_, ?_, ⟨⟨inOff (baseOr A.G (selPerm (sel A.N) A.G)), _, htr⟩,
    inNCsr_winA_of_trInCsr (hnm j).it_io htr, hnAv⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- the budget: the source slot space is twice round `0`'s arc count
    have hslots : offF A.N = 2 * arcCount (baseOr A.G (selPerm (sel A.N) A.G)) :=
      hfr.slots
    rw [selChain_zero, hslots]
    omega
  · exact arenaStW_of_eq hArena (hfv' _ hnNmem) (hfv' _ hnSmem)
      (hfa' _ (Ne.symm hoffO) (Ne.symm hoffT) (Ne.symm hoffN))
      (hfa' _ (Ne.symm htgtO) (Ne.symm htgtT) (Ne.symm htgtN))
      (hfa' _ (Ne.symm hcolO) (Ne.symm hcolT) (Ne.symm hcolN))
      (hfa' _ (Ne.symm hupO) (Ne.symm hupT) (Ne.symm hupN))
      (hfa' _ (Ne.symm hhistO) (Ne.symm hhistT) (Ne.symm hhistN))
  · exact hSrd j σ σ' hSb hfa' hfv'
  · rw [hlen (ca j)]; exact hcaL
  · rw [hlen (co j)]; exact hcoL
  · exact hSmp j σ σ' hSm hfa' hfv'
  · exact hSsw j σ σ' hSw hfa' hfv'

/-! ## §11 Axiom audit -/

#print axioms inNCsr_winA_of_trInCsr

#print axioms orCnt_row

#print axioms trInCsr_of_scat

#print axioms orCom_spec

#print axioms orK_eq

#print axioms augBaseOrientIn_orCom

end Lax3Proofs.Prog
